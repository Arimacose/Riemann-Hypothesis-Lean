#!/usr/bin/env python3
"""Exact/symbolic audit for the logarithmic high-mode CvS decomposition.

Checks:
1. the pole matrix is the difference of two rank-one kernels;
2. a prime-event matrix equals the self-adjoint part of a truncated translation
   in the normalized Fourier basis;
3. explicit elementary constants are emitted for selected cutoffs.

The script audits algebra and normalization.  It does not prove the standard
coth summation formula, the discrete Hilbert-transform norm, or the digamma
series lower bound; those are proved in the accompanying research note.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def prime_powers_up_to(c: int) -> list[tuple[int, int]]:
    primes: list[int] = []
    for n in range(2, c + 1):
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
    out: list[tuple[int, int]] = []
    for p in primes:
        q = p
        while q <= c:
            out.append((q, p))
            q *= p
    return sorted(out)


def symbolic_checks() -> dict[str, bool]:
    L, m, n, pi = sp.symbols(
        "L m n pi", nonzero=True, real=True
    )
    den_m = L**2 + 16 * pi**2 * m**2
    den_n = L**2 + 16 * pi**2 * n**2
    a_m = L / den_m
    a_n = L / den_n
    b_m = 4 * pi * m / den_m
    b_n = 4 * pi * n / den_n
    pole_entry = (
        L**2 - 16 * pi**2 * m * n
    ) / (den_m * den_n)
    assert sp.simplify(pole_entry - (a_m * a_n - b_m * b_n)) == 0

    alpha, beta, k = sp.symbols(
        "alpha beta k", real=True, nonzero=True
    )
    translation_entry = (
        sp.exp(sp.I * alpha) - sp.exp(sp.I * beta)
    ) / (2 * sp.pi * sp.I * k)
    symmetric_part = sp.simplify(
        translation_entry + sp.conjugate(translation_entry)
    )
    target = (
        sp.sin(alpha) - sp.sin(beta)
    ) / (sp.pi * k)
    assert sp.simplify(
        sp.expand_complex(symmetric_part - target)
    ) == 0

    return {
        "pole_rank_two_identity": True,
        "prime_translation_offdiagonal_identity": True,
    }


def numerical_translation_check() -> str:
    mp.mp.dps = 80
    max_error = mp.mpf("0")
    for L in [mp.log(5), mp.log(13), mp.mpf("3.7")]:
        for fraction in [
            mp.mpf("0.13"),
            mp.mpf("0.41"),
            mp.mpf("0.77"),
        ]:
            y = L * fraction
            for n in range(-4, 5):
                for m in range(-4, 5):
                    if n == m:
                        formula = 2 * (1 - y / L) * mp.cos(
                            2 * mp.pi * n * y / L
                        )
                        direct = 2 * mp.re(
                            (1 - y / L)
                            * mp.exp(2j * mp.pi * n * y / L)
                        )
                    else:
                        formula = (
                            mp.sin(2 * mp.pi * m * y / L)
                            - mp.sin(2 * mp.pi * n * y / L)
                        ) / (mp.pi * (n - m))
                        k = m - n
                        entry = (
                            mp.exp(2j * mp.pi * n * y / L)
                            - mp.exp(2j * mp.pi * m * y / L)
                        ) / (2j * mp.pi * k)
                        direct = entry + mp.conj(entry)
                    max_error = max(max_error, abs(formula - direct))
    assert max_error < mp.mpf("1e-70")
    return mp.nstr(max_error, 20)


def constants(c: int) -> dict[str, object]:
    mp.mp.dps = 100
    L = mp.log(c)
    a = mp.mpf(1) / 4
    R = mp.exp(-L / 2) / (1 - mp.exp(-2 * L))
    kappa = (
        mp.log(4 * mp.pi * (c - 1) / (c + 1)) + mp.euler
    )
    U = mp.sqrt(c)
    J = (
        -2 * mp.log(U + 1)
        + mp.log(U * U + 1)
        + 2 * mp.atan(U)
        + mp.log(2)
        - mp.pi / 2
    )
    C_psi = mp.euler + mp.mpf(4) / 5 + mp.log(mp.mpf(8) / 5)
    D_L = (
        C_psi
        + mp.digamma(a)
        + kappa
        + J
        + 8 * R
        + 8 * R / L
        + mp.polygamma(1, a) / (2 * L)
        + mp.log(L / mp.pi)
    )
    prime_weight = mp.fsum(
        mp.log(p) / mp.sqrt(q)
        for q, p in prime_powers_up_to(c)
    )
    S_bound = 1 + mp.pi / 4 + R
    arch_bound = 2 * S_bound
    pole_bound = 4 * mp.sinh(L / 2)
    prime_bound = 2 * prime_weight

    def text(x: mp.mpf) -> str:
        return mp.nstr(x, 50)

    return {
        "c": c,
        "L": text(L),
        "R_L": text(R),
        "C_psi": text(C_psi),
        "D_L": text(D_L),
        "S_sup_bound": text(S_bound),
        "arch_offdiagonal_bound": text(arch_bound),
        "pole_norm_bound": text(pole_bound),
        "prime_weight_sum": text(prime_weight),
        "prime_norm_bound": text(prime_bound),
        "bounded_perturbation_B_L": text(
            arch_bound + pole_bound + prime_bound
        ),
    }


def boundary_weyl_schur_probe(
    *,
    c: int,
    fixed_cutoff: int,
    low_gap_text: str,
    shift_gain_text: str,
    margin_text: str,
    eta_norm_sq_text: str,
) -> dict[str, object]:
    """Evaluate the conservative log-tail constants in the V23 Weyl budget.

    The Lean high-gap-oriented sufficient condition is

        epsilon^2 * (etaNormSq + margin * lowGap)
          <= margin * lowGap^2 * highGap.

    Here ``epsilon`` is instantiated by the elementary bound ``B_L`` and the
    shifted high gap at a retained cutoff ``M`` is

        log(M+1) - D_L - B_L + shiftGain.

    The audit keeps the retained cutoff and the boundary-vector norm
    synchronized: ``etaNormSq = 2*M+1``.  It checks the actual fixed cutoff and
    then verifies a slope/intercept obstruction for every self-consistent
    larger cutoff under the same dimension-independent coupling bound.  This
    is a conditional arithmetic audit of the supplied operator bounds; it does
    not establish the operator inequalities themselves.
    """
    mp.mp.dps = 100
    record = constants(c)
    D_L = mp.mpf(record["D_L"])
    B_L = mp.mpf(record["bounded_perturbation_B_L"])
    low_gap = mp.mpf(low_gap_text)
    shift_gain = mp.mpf(shift_gain_text)
    margin = mp.mpf(margin_text)
    eta_norm_sq = mp.mpf(eta_norm_sq_text)
    cutoff = mp.mpf(fixed_cutoff)
    if fixed_cutoff < 0:
        raise ValueError("Schur fixed cutoff must be nonnegative")
    if low_gap <= 0 or margin <= 0:
        raise ValueError("Schur low gap and margin must be positive")
    if shift_gain < 0 or eta_norm_sq < 0:
        raise ValueError("Schur shift gain and eta norm square must be nonnegative")
    expected_eta_norm_sq = 2 * cutoff + 1
    if eta_norm_sq != expected_eta_norm_sq:
        raise ValueError(
            "Schur eta norm square must equal 2 * fixed cutoff + 1"
        )

    epsilon_sq = B_L**2
    scale = margin * low_gap**2
    boundary_offset = margin * low_gap
    fixed_high_gap = (
        mp.log(cutoff + 1) - D_L - B_L + shift_gain
    )
    fixed_budget_left = epsilon_sq * (
        eta_norm_sq + boundary_offset
    )
    fixed_budget_right = scale * fixed_high_gap
    fixed_small_coupling_margin = (
        low_gap * fixed_high_gap - epsilon_sq
    )

    # For a self-consistent retained cutoff M, etaNormSq = 2*M+1.  Since
    # log(M+1) <= M and D_L+B_L > 0, the elementary high floor is at most
    # M+shiftGain.  The Lean no-go theorem applies when the two coefficient
    # margins below are positive.
    slope_margin = 2 * epsilon_sq - scale
    intercept_margin = epsilon_sq - scale * shift_gain
    self_consistent_no_go = (
        D_L + B_L > 0
        and slope_margin > 0
        and intercept_margin > 0
    )
    if not self_consistent_no_go:
        raise RuntimeError("conservative Schur no-go coefficient check failed")

    def text(x: mp.mpf) -> str:
        return mp.nstr(x, 70)

    return {
        "status": "PASS",
        "scope": (
            "conditional arithmetic instantiation of the V23 Lean Schur "
            "budget using the elementary log-tail bounds"
        ),
        "inputs": {
            "c": c,
            "fixed_retained_cutoff": fixed_cutoff,
            "low_gap": text(low_gap),
            "spectral_shift_gain": text(shift_gain),
            "finite_half_margin": text(margin),
            "eta_norm_sq": text(eta_norm_sq),
            "eta_norm_sq_formula": "2 * fixed_retained_cutoff + 1",
            "epsilon_choice": "B_L",
        },
        "constants": {
            "D_L": text(D_L),
            "B_L": text(B_L),
            "B_L_sq": text(epsilon_sq),
        },
        "lean_high_gap_budget": (
            "epsilon^2 * (etaNormSq + margin * lowGap) "
            "<= margin * lowGap^2 * highGap"
        ),
        "fixed_cutoff_probe": {
            "shifted_high_gap": text(fixed_high_gap),
            "small_coupling_margin_lowGap_times_highGap_minus_epsilonSq": text(
                fixed_small_coupling_margin
            ),
            "high_gap_budget_left": text(fixed_budget_left),
            "high_gap_budget_right": text(fixed_budget_right),
            "high_gap_positive": bool(fixed_high_gap > 0),
            "small_coupling_condition": bool(
                fixed_small_coupling_margin > 0
            ),
            "high_gap_budget_holds": bool(
                fixed_budget_left <= fixed_budget_right
            ),
        },
        "self_consistent_cutoff_obstruction": {
            "boundary_norm_growth": "etaNormSq = 2*M+1",
            "high_gap_majorant": "highGap <= M + shiftGain",
            "right_side_scale_margin_times_lowGapSq": text(scale),
            "slope_margin_2epsilonSq_minus_scale": text(slope_margin),
            "intercept_margin_epsilonSq_minus_scaleTimesShift": text(
                intercept_margin
            ),
            "lean_theorem": (
                "RiemannCvs.BoundaryWeylSchurTail."
                "highGapBudget_false_of_linearBoundaryGrowth"
            ),
            "no_cutoff_satisfies_conservative_budget": True,
        },
        "interpretation": (
            "the fixed N=20 complement lacks a positive elementary high "
            "floor, while increasing the retained cutoff also grows the "
            "boundary norm linearly; the dimension-independent B_L coupling "
            "therefore does not close this Weyl budget at any synchronized "
            "cutoff, so a cutoff-decaying coupling or weighted boundary "
            "estimate is the quantitative next target"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument("--schur-c", type=int, default=13)
    parser.add_argument("--schur-fixed-cutoff", type=int, default=20)
    parser.add_argument("--schur-low-gap", default="0.0009765625")
    parser.add_argument("--schur-shift-gain", default="0.0009765625")
    parser.add_argument(
        "--schur-margin",
        default="0.0175525530977914393795820608",
    )
    parser.add_argument("--schur-eta-norm-sq", default="41")
    args = parser.parse_args()

    result = {
        "status": "PASS",
        "scope": (
            "Exact algebra and high-precision normalization audit; "
            "not an RH claim."
        ),
        "symbolic": symbolic_checks(),
        "translation_max_error": numerical_translation_check(),
        "constants": [constants(c) for c in [5, 13, 29, 100]],
        "boundary_weyl_schur_probe": boundary_weyl_schur_probe(
            c=args.schur_c,
            fixed_cutoff=args.schur_fixed_cutoff,
            low_gap_text=args.schur_low_gap,
            shift_gain_text=args.schur_shift_gain,
            margin_text=args.schur_margin,
            eta_norm_sq_text=args.schur_eta_norm_sq,
        ),
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "translation_max_error": result[
                    "translation_max_error"
                ],
                "boundary_weyl_schur_probe": result[
                    "boundary_weyl_schur_probe"
                ],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
