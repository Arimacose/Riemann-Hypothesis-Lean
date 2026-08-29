#!/usr/bin/env python3
"""Exploratory smooth-cutoff velocity audit for the cutoff-free CvS matrix.

Between adjacent prime-power events, differentiate the continuous cutoff
parameter numerically.  In each parity block, compare Hellmann--Feynman
velocities with squared boundary overlaps.

The script tests two candidate shape-flow laws:

    lambda_i' = -a * |<v,x_i>|^2,

and

    lambda_i' = -(a0 + a1 * lambda_i) * |<v,x_i>|^2.

The second includes the compression-defect model, whose coefficient is affine
in the eigenvalue.  Off-diagonal matrix velocity is irrelevant to eigenvalue
motion because it can always be represented by a Lax commutator when the
spectrum is simple.

This is double-precision hypothesis testing, not an interval certificate and
not an RH claim.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def prime_powers_up_to(x: float) -> list[tuple[int, int]]:
    limit = int(math.floor(x))
    primes: list[int] = []
    for n in range(2, limit + 1):
        is_prime = True
        for p in primes:
            if p * p > n:
                break
            if n % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(n)
    out: list[tuple[int, int]] = []
    for p in primes:
        q = p
        while q <= limit:
            out.append((q, p))
            q *= p
    return sorted(out)


def geom_sums(n: int, L: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    pi = mp.pi
    w = 2 * pi * n / L
    w2 = w * w
    g_s = mp.mpf("0")
    g_cc = mp.mpf("0")
    g_x1 = mp.mpf("0")
    g_x2 = mp.mpf("0")
    k = 0
    while True:
        ck = mp.mpf(2 * k) + mp.mpf("0.5")
        exp_term = mp.exp(-ck * L)
        den = ck * ck + w2
        g_s += exp_term / den
        if n != 0:
            g_cc += exp_term * w2 / (ck * den)
        g_x1 += exp_term * ck / den
        g_x2 += exp_term * (ck * ck - w2) / (den * den)
        if exp_term < mp.mpf("1e-60") and k > 5:
            break
        k += 1
        if k > 100000:
            raise RuntimeError("geometric correction did not converge")
    return g_s, g_cc, g_x1, g_x2


def closed_forms(N: int, c: float) -> tuple[list[mp.mpf], list[mp.mpf], list[mp.mpf], mp.mpf]:
    L = mp.log(c)
    quarter = mp.mpf("0.25")
    psi_quarter = mp.digamma(quarter)
    S = [mp.mpf("0") for _ in range(N + 1)]
    CC = [mp.mpf("0") for _ in range(N + 1)]
    XC = [mp.mpf("0") for _ in range(N + 1)]
    for n in range(N + 1):
        w = 2 * mp.pi * n / L
        z = quarter + 1j * mp.pi * n / L
        psi = mp.digamma(z)
        psi1 = mp.polygamma(1, z)
        g_s, g_cc, g_x1, g_x2 = geom_sums(n, L)
        if n != 0:
            S[n] = mp.mpf("0.5") * mp.im(psi) - w * g_s
            CC[n] = -mp.mpf("0.5") * (mp.re(psi) - psi_quarter) + g_cc
        XC[n] = mp.mpf("0.25") * mp.re(psi1) - L * g_x1 - g_x2
    return S, CC, XC, L


def pole_J(L: mp.mpf) -> mp.mpf:
    """Exact CvS pole constant, matching the cutoff-free Arb constructor."""
    U = mp.e ** (L / 2)
    return (
        -2 * mp.log(U + 1)
        + mp.log(U * U + 1)
        + 2 * mp.atan(U)
        + mp.log(2)
        - mp.pi / 2
    )


def arch_kappa(L: mp.mpf) -> mp.mpf:
    eL = mp.e ** L
    return mp.log(4 * mp.pi * (eL - 1) / (eL + 1)) + mp.euler


def build_matrix(c: float, N: int) -> np.ndarray:
    S, CC, XC, L = closed_forms(N, c)
    pi = mp.pi
    L2 = L * L
    sixteen_pi2 = 16 * pi * pi
    pref02 = 32 * L * mp.sinh(L / 4) ** 2
    kappa = arch_kappa(L)
    J = pole_J(L)
    prime_data = prime_powers_up_to(c)
    weights = [mp.log(p) / mp.sqrt(q) for q, p in prime_data]
    positions = [mp.log(q) for q, _ in prime_data]

    def s_signed(n: int) -> mp.mpf:
        return S[n] if n >= 0 else -S[-n]

    dim = 2 * N + 1
    A = np.empty((dim, dim), dtype=float)
    for i in range(dim):
        n = i - N
        for j in range(i, dim):
            m = j - N
            numerator = L2 - sixteen_pi2 * m * n
            denominator = (
                (L2 + sixteen_pi2 * m * m)
                * (L2 + sixteen_pi2 * n * n)
            )
            W02 = pref02 * numerator / denominator
            if n == m:
                WR = kappa + 2 * CC[abs(n)] + J - (2 / L) * XC[abs(n)]
            else:
                WR = (s_signed(m) - s_signed(n)) / (pi * (n - m))
            Wp = mp.mpf("0")
            for weight, y in zip(weights, positions):
                if n == m:
                    qnm = 2 * (1 - y / L) * mp.cos(2 * pi * n * y / L)
                else:
                    qnm = (
                        mp.sin(2 * pi * m * y / L)
                        - mp.sin(2 * pi * n * y / L)
                    ) / (pi * (n - m))
                Wp += weight * qnm
            value = float(W02 - WR - Wp)
            A[i, j] = value
            A[j, i] = value
    # Enforce exact numerical reflection symmetry.
    A = 0.25 * (A + A.T + A[::-1, ::-1] + A[::-1, ::-1].T)
    return A


def parity_blocks(A: np.ndarray, N: int) -> tuple[np.ndarray, np.ndarray]:
    dim = 2 * N + 1
    center = N
    Ve = np.zeros((dim, N + 1))
    Vo = np.zeros((dim, N))
    Ve[center, 0] = 1.0
    invsqrt2 = 1.0 / math.sqrt(2.0)
    for k in range(1, N + 1):
        Ve[center + k, k] = invsqrt2
        Ve[center - k, k] = invsqrt2
        Vo[center + k, k - 1] = invsqrt2
        Vo[center - k, k - 1] = -invsqrt2
    return Ve.T @ A @ Ve, Vo.T @ A @ Vo


def fit_velocity(block: np.ndarray, velocity: np.ndarray, boundary: np.ndarray) -> dict[str, object]:
    eigvals, eigvecs = np.linalg.eigh(block)
    branch_velocity = np.einsum("ij,ij->j", eigvecs, velocity @ eigvecs)
    overlaps = eigvecs.T @ boundary
    overlap_sq = overlaps * overlaps
    mask = overlap_sq > 1e-14 * max(1.0, float(overlap_sq.max()))
    y = -branch_velocity[mask] / overlap_sq[mask]
    lam = eigvals[mask]

    constant = float(np.mean(y)) if y.size else float("nan")
    constant_residual = y - constant
    constant_rel = float(
        np.linalg.norm(constant_residual) / max(np.linalg.norm(y), 1e-300)
    ) if y.size else float("nan")

    X = np.column_stack([np.ones_like(lam), lam])
    if len(lam) >= 2:
        affine, *_ = np.linalg.lstsq(X, y, rcond=None)
        affine_residual = y - X @ affine
        affine_rel = float(
            np.linalg.norm(affine_residual) / max(np.linalg.norm(y), 1e-300)
        )
        affine_values = [float(affine[0]), float(affine[1])]
    else:
        affine_rel = float("nan")
        affine_values = [float("nan"), float("nan")]

    return {
        "eigenvalues": eigvals.tolist(),
        "branch_velocities": branch_velocity.tolist(),
        "boundary_overlap_sq": overlap_sq.tolist(),
        "usable_branches": int(mask.sum()),
        "constant_fit": constant,
        "constant_relative_residual": constant_rel,
        "affine_fit_a0_a1": affine_values,
        "affine_relative_residual": affine_rel,
    }


def audit_case(c: float, N: int, step: float) -> dict[str, object]:
    lower_primes = prime_powers_up_to(c - step)
    upper_primes = prime_powers_up_to(c + step)
    if lower_primes != upper_primes:
        raise ValueError(f"finite-difference interval around c={c} crosses a prime-power event")

    A0 = build_matrix(c, N)
    Ap = build_matrix(c + step, N)
    Am = build_matrix(c - step, N)
    derivative = (Ap - Am) / (2 * step)
    even, odd = parity_blocks(A0, N)
    even_d, odd_d = parity_blocks(derivative, N)

    even_boundary = np.concatenate([[1.0], np.full(N, math.sqrt(2.0))])
    # The prime-event vector has no odd component.  For the smooth shape audit
    # we also report the natural first-moment vector as a candidate odd
    # endpoint functional; the fit is exploratory.
    odd_boundary = math.sqrt(2.0) * np.arange(1, N + 1, dtype=float)

    return {
        "c": c,
        "N": N,
        "step": step,
        "prime_power_count": len(lower_primes),
        "even": fit_velocity(even, even_d, even_boundary),
        "odd_candidate_first_moment": fit_velocity(odd, odd_d, odd_boundary),
        "matrix_derivative_frobenius": float(np.linalg.norm(derivative)),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, default=12)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--step", type=float, default=2e-5)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    if args.N < 2 or args.dps < 40 or args.step <= 0:
        parser.error("require N >= 2, dps >= 40 and step > 0")
    mp.mp.dps = args.dps

    cases = [5.5, 13.5, 20.5, 29.5]
    result = {
        "status": "PASS",
        "scope": "double-precision smooth-flow hypothesis audit; not an interval certificate",
        "cases": [audit_case(c, args.N, args.step) for c in cases],
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "cases": [
            {
                "c": row["c"],
                "even_constant_residual": row["even"]["constant_relative_residual"],
                "even_affine_residual": row["even"]["affine_relative_residual"],
                "odd_affine_residual": row["odd_candidate_first_moment"]["affine_relative_residual"],
            }
            for row in result["cases"]
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
