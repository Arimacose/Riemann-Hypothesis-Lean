#!/usr/bin/env python3
"""Certify the rank-86 compressed norms for the first adjacent CvS bridge.

For ``K=1920`` the combined Archimedean/prime Loewner crossblock is split into
same-sign and reflected pieces.  The logarithmic-shift ADI telescope gives
explicit factorizations ``C = U V^T`` of their compressed matrices.  This
script constructs every factor entry with Arb and proves the four norm caps

    same <= 8881/10000, reflected <= 22301/100000,
    even <= 93223/100000, odd <= 93223/100000.

For each factor pair let ``G_U=U^T U`` and ``G_V=V^T V``.  A floating
Cholesky factor only selects a matrix ``R``; its saved doubles are reloaded
byte-for-byte and embedded as exact dyadic Arb numbers.  Two independently
checked Loewner inequalities then imply the operator bound:

    G_U < R R^T,
    R^T G_V R < epsilon^2 I.

Indeed, on an arbitrary target vector, ``G_U <= R R^T`` first majorizes the
pulled-back quadratic form, and the second inequality bounds
``V R R^T V^T`` by ``epsilon^2 I``.  Both small
positive matrices are proved by exact-dyadic congruence and strict interval
Gershgorin rows.  Floating arithmetic is selector data, never proof evidence.

The scalar rational-residual certificate and the Lean ADI telescoping identity
are separate artifacts.  This file certifies only the compressed Gram bounds.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gc
import hashlib
import json
import math
import os
import platform
import subprocess
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np
from certify_direct_parity_relative_shell import DirectParityKernel
from certify_odd_fixed_base_channel import _certify_positive_matrix
from certify_preconditioned_relative_shell import (
    _fraction_arb,
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
)
from flint import arb, arb_mat, ctx


def _progress(message: str) -> None:
    print(f"[k1920-compressed-gram] {message}", flush=True)


def _git_sha() -> str | None:
    github_sha = os.environ.get("GITHUB_SHA")
    if github_sha:
        return github_sha
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            text=True,
            encoding="utf-8",
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def _exact_dyadic(value: float) -> arb:
    if not math.isfinite(value):
        raise ValueError("selector contains a non-finite entry")
    numerator, denominator = value.as_integer_ratio()
    exact = arb(numerator) / denominator
    if exact.rad() != 0:
        raise RuntimeError("exact dyadic embedding unexpectedly has radius")
    return exact


def _exact_lower_triangular(matrix: np.ndarray) -> arb_mat:
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("Gram majorant selector must be square")
    dimension = matrix.shape[0]
    result = arb_mat(dimension, dimension)
    for i in range(dimension):
        for j in range(i + 1):
            result[i, j] = _exact_dyadic(float(matrix[i, j]))
    return result


def _save_exact_lower_selector(path: Path, selector: np.ndarray) -> arb_mat:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.save(path, selector, allow_pickle=False)
    reloaded = np.load(path, allow_pickle=False)
    if not np.array_equal(reloaded, selector):
        raise RuntimeError("Gram majorant selector does not replay byte-for-byte")
    result = _exact_lower_triangular(reloaded)
    del reloaded
    return result


def _mobius_coefficients(
    endpoints: tuple[Fraction, Fraction, Fraction, Fraction], alpha: arb
) -> tuple[arb, arb, arb, arb, dict[str, Any]]:
    """Map four endpoints to ``(-alpha,-1,1,alpha)`` with ``d=1``."""

    source = [_fraction_arb(value) for value in endpoints]
    target = [-alpha, arb(-1), arb(1), alpha]
    matrix = arb_mat(3, 3)
    rhs = arb_mat(3, 1)
    for row in range(3):
        matrix[row, 0] = source[row]
        matrix[row, 1] = 1
        matrix[row, 2] = -target[row] * source[row]
        rhs[row, 0] = target[row]
    solution = matrix.solve(rhs, algorithm="precond")
    a, b, c = (solution[index, 0] for index in range(3))
    d = arb(1)

    residuals: list[str] = []
    for x, y in zip(source, target, strict=True):
        residual = a * x + b - y * (c * x + d)
        if not residual.contains(0):
            raise RuntimeError("Mobius endpoint residual misses exact zero")
        denominator = c * x + d
        if denominator.contains(0):
            raise RuntimeError("Mobius endpoint denominator contains zero")
        residuals.append(str(residual))
    return a, b, c, d, {
        "normalized_endpoints": [str(value) for value in endpoints],
        "endpoint_residuals_contain_zero": 4,
        "endpoint_residuals": residuals,
    }


def _inverse_mobius(
    coefficients: tuple[arb, arb, arb, arb], value: arb
) -> arb:
    a, b, c, d = coefficients
    denominator = a - value * c
    if denominator.contains(0):
        raise RuntimeError("inverse Mobius denominator contains zero")
    return (value * d - b) / denominator


def _roots_and_poles(
    *,
    endpoints: tuple[Fraction, Fraction, Fraction, Fraction],
    factors: int,
    inverse: bool,
) -> tuple[list[arb], list[arb], dict[str, Any]]:
    a, b, c, d = endpoints
    gamma_q = ((c - a) * (d - b)) / ((c - b) * (d - a))
    gamma = _fraction_arb(gamma_q)
    alpha = -1 + 2 * gamma + 2 * (gamma * gamma - gamma).sqrt()
    coeff = _mobius_coefficients(endpoints, alpha)
    coefficients = coeff[:4]
    roots: list[arb] = []
    poles: list[arb] = []
    for index in range(factors):
        exponent = Fraction(2 * index + 1, 2 * factors)
        shift = (alpha.log() * _fraction_arb(exponent)).exp()
        root = _inverse_mobius(coefficients, -shift)
        pole = _inverse_mobius(coefficients, shift)
        if inverse:
            root, pole = pole, root
        roots.append(root)
        poles.append(pole)
    return roots, poles, {
        "cross_ratio": str(gamma_q),
        "alpha": str(alpha),
        "factor_count": factors,
        "inverse_rational_function": inverse,
        "mobius_verification": coeff[4],
    }


def _adi_factors(
    *,
    diagonal_left: list[arb],
    diagonal_right: list[arb],
    generator_left: list[tuple[arb, arb]],
    generator_right: list[tuple[arb, arb]],
    roots: list[arb],
    poles: list[arb],
) -> tuple[arb_mat, arb_mat]:
    if len(roots) != len(poles):
        raise ValueError("ADI roots and poles have different lengths")
    if len(generator_left) != len(diagonal_left):
        raise ValueError("left generator has the wrong length")
    if len(generator_right) != len(diagonal_right):
        raise ValueError("right generator has the wrong length")

    rank = 2 * len(roots)
    left = arb_mat(len(diagonal_left), rank)
    right = arb_mat(len(diagonal_right), rank)
    left_product = [arb(1) for _ in diagonal_left]
    right_inverse_product = [arb(1) for _ in diagonal_right]

    for factor, (root, pole) in enumerate(zip(roots, poles, strict=True)):
        for row, value in enumerate(diagonal_left):
            denominator = value - pole
            if denominator.contains(0):
                raise RuntimeError("left ADI denominator contains zero")
            scale = left_product[row] * (pole - root) / denominator
            left[row, 2 * factor] = scale * generator_left[row][0]
            left[row, 2 * factor + 1] = scale * generator_left[row][1]
            left_product[row] *= (value - root) / denominator
        for column, value in enumerate(diagonal_right):
            denominator = value - root
            if denominator.contains(0):
                raise RuntimeError("right ADI denominator contains zero")
            scale = right_inverse_product[column] / denominator
            right[column, 2 * factor] = scale * generator_right[column][0]
            right[column, 2 * factor + 1] = scale * generator_right[column][1]
            right_inverse_product[column] *= (value - pole) / denominator
    return left, right


def _rational_value(value: arb, roots: list[arb], poles: list[arb]) -> arb:
    result = arb(1)
    for root, pole in zip(roots, poles, strict=True):
        denominator = value - pole
        if denominator.contains(0):
            raise RuntimeError("rational-function denominator contains zero")
        result *= (value - root) / denominator
    return result


def _sample_indices(length: int) -> list[int]:
    candidates = {0, 1, length // 4, length // 2, 3 * length // 4, length - 2, length - 1}
    return sorted(index for index in candidates if 0 <= index < length)


def _verify_factor_samples(
    *,
    label: str,
    left: arb_mat,
    right: arb_mat,
    diagonal_left: list[arb],
    diagonal_right: list[arb],
    roots: list[arb],
    poles: list[arb],
    row_modes: list[int],
    column_modes: list[int],
    symbol: list[arb],
    pi: arb,
    reflected: bool,
) -> dict[str, Any]:
    checked = 0
    max_midpoint_abs = 0.0
    max_radius = 0.0
    for i in _sample_indices(len(row_modes)):
        p = row_modes[i]
        rational_left = _rational_value(diagonal_left[i], roots, poles)
        for j in _sample_indices(len(column_modes)):
            q = column_modes[j]
            rational_right = _rational_value(diagonal_right[j], roots, poles)
            if rational_right.contains(0):
                raise RuntimeError("sample rational denominator contains zero")
            if reflected:
                full = (-symbol[q] - symbol[p]) / (pi * (p + q))
            else:
                full = (symbol[q] - symbol[p]) / (pi * (p - q))
            compressed = full * (1 - rational_left / rational_right)
            factor_entry = arb(0)
            for index in range(left.ncols()):
                factor_entry += left[i, index] * right[j, index]
            residual = compressed - factor_entry
            if not residual.contains(0):
                raise RuntimeError(f"{label} sampled factor residual misses zero")
            checked += 1
            max_midpoint_abs = max(max_midpoint_abs, abs(float(residual.mid())))
            max_radius = max(max_radius, float(residual.rad()))
    return {
        "label": label,
        "sampled_entries": checked,
        "residuals_containing_zero": checked,
        "max_midpoint_abs": max_midpoint_abs,
        "max_radius": max_radius,
        "formula": "X*(1-r(A)/r(B)) minus the explicit ADI factor product",
    }


def _column_stack(
    first: arb_mat,
    second: arb_mat,
    *,
    first_sign: int = 1,
    second_sign: int = 1,
) -> arb_mat:
    if first.nrows() != second.nrows():
        raise ValueError("factor row dimensions do not match")
    result = arb_mat(first.nrows(), first.ncols() + second.ncols())
    for i in range(result.nrows()):
        for j in range(first.ncols()):
            result[i, j] = first_sign * first[i, j]
        for j in range(second.ncols()):
            result[i, first.ncols() + j] = second_sign * second[i, j]
    return result


def _identity(dimension: int, scale: arb | None = None) -> arb_mat:
    if scale is None:
        scale = arb(1)
    result = arb_mat(dimension, dimension)
    for i in range(dimension):
        result[i, i] = scale
    return result


def _max_radius(matrix: arb_mat) -> float:
    value = 0.0
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            value = max(value, float(matrix[i, j].rad()))
    return value


def _certify_factor_norm(
    *,
    label: str,
    left: arb_mat,
    right: arb_mat,
    epsilon: Fraction,
    delta: Fraction,
    artifact_stem: Path,
) -> dict[str, Any]:
    started = time.time()
    if left.ncols() != right.ncols():
        raise ValueError(f"{label} factors have different ranks")
    rank = left.ncols()

    gram_started = time.time()
    gram_left = left.transpose() * left
    gram_right = right.transpose() * right
    _symmetrize_enclosure(gram_left)
    _symmetrize_enclosure(gram_right)
    gram_seconds = time.time() - gram_started

    midpoint_left = _midpoint_numpy(gram_left)
    midpoint_right = _midpoint_numpy(gram_right)
    delta_float = float(delta)
    selector_midpoint = np.linalg.cholesky(
        midpoint_left + delta_float * np.eye(rank)
    )
    selector_path = artifact_stem.with_name(
        artifact_stem.name + f"_{label}_gram_majorant.npy"
    )
    selector = _save_exact_lower_selector(selector_path, selector_midpoint)

    left_margin = selector * selector.transpose() - gram_left
    _symmetrize_enclosure(left_margin)
    epsilon_arb = _fraction_arb(epsilon)
    right_margin = _identity(rank, epsilon_arb * epsilon_arb) - (
        selector.transpose() * (gram_right * selector)
    )
    _symmetrize_enclosure(right_margin)

    left_preconditioner = artifact_stem.with_name(
        artifact_stem.name + f"_{label}_left_margin_preconditioner.npy"
    )
    right_preconditioner = artifact_stem.with_name(
        artifact_stem.name + f"_{label}_right_margin_preconditioner.npy"
    )
    _progress(f"proving {label}: G_U < R R^T")
    left_certificate = _certify_positive_matrix(
        matrix=left_margin,
        label=f"{label} Gram majorant minus left Gram",
        preconditioner_path=left_preconditioner,
    )
    _progress(f"proving {label}: R^T G_V R < epsilon^2 I")
    right_certificate = _certify_positive_matrix(
        matrix=right_margin,
        label=f"{label} epsilon squared identity minus transformed right Gram",
        preconditioner_path=right_preconditioner,
    )

    transformed_midpoint = selector_midpoint.T @ midpoint_right @ selector_midpoint
    diagnostic_norm = math.sqrt(
        max(0.0, float(np.linalg.eigvalsh(transformed_midpoint)[-1]))
    )
    del (
        gram_left,
        gram_right,
        left_margin,
        right_margin,
        selector,
        midpoint_left,
        midpoint_right,
        transformed_midpoint,
    )
    gc.collect()
    return {
        "status": "PASS",
        "label": label,
        "rank": rank,
        "left_rows": left.nrows(),
        "right_rows": right.nrows(),
        "operator_norm_upper": str(epsilon),
        "gram_majorant_delta": str(delta),
        "gram_majorant_selector": {
            "path": str(selector_path.resolve()),
            "sha256": _sha256(selector_path),
            "dtype": str(selector_midpoint.dtype),
            "shape": list(selector_midpoint.shape),
            "lower_triangular": True,
            "all_entries_exact_dyadic_after_embedding": True,
            "all_diagonal_entries_positive": bool(
                np.all(np.diag(selector_midpoint) > 0)
            ),
        },
        "left_gram_max_radius": _max_radius(left.transpose() * left),
        "right_gram_max_radius": _max_radius(right.transpose() * right),
        "left_margin_certificate": left_certificate,
        "right_margin_certificate": right_certificate,
        "midpoint_transformed_norm_diagnostic": diagnostic_norm,
        "proof_consequence": (
            "G_U < R R^T and R^T G_V R < epsilon^2 I imply "
            "the operator norm of U*V^T is strictly below epsilon"
        ),
        "timings_seconds": {
            "gram_products": round(gram_seconds, 3),
            "total": round(time.time() - started, 3),
        },
    }


def certify(
    *,
    c: int,
    mode: int,
    same_factors: int,
    reflected_factors: int,
    same_cap: Fraction,
    reflected_cap: Fraction,
    total_cap: Fraction,
    delta: Fraction,
    precision: int,
    threads: int,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1 or mode < 1:
        raise ValueError("c must exceed one and mode must be positive")
    if same_factors < 1 or reflected_factors < 1:
        raise ValueError("factor counts must be positive")
    if not 0 < same_cap < 1 or not 0 < reflected_cap < 1:
        raise ValueError("component norm caps must lie in (0,1)")
    if not 0 < total_cap < 1 or delta <= 0:
        raise ValueError("total cap must lie in (0,1) and delta be positive")
    if precision < 128 or threads < 1:
        raise ValueError("precision must be >=128 and threads positive")

    ctx.prec = precision
    ctx.threads = threads
    started = time.time()
    kernel = DirectParityKernel.build(c=c, cutoff=4 * mode, precision=precision)
    _progress(
        f"built cutoff-{c} one-dimensional Arb symbol through {4 * mode} "
        f"in {kernel.build_seconds:.3f}s"
    )

    row_modes = list(range(mode + 1, 2 * mode + 1))
    column_modes = list(range(2 * mode + 1, 4 * mode + 1))
    diagonal_left = [_fraction_arb(Fraction(value, mode)) for value in row_modes]
    diagonal_same = [
        _fraction_arb(Fraction(value, mode)) for value in column_modes
    ]
    diagonal_reflected = [
        -_fraction_arb(Fraction(value, mode)) for value in column_modes
    ]
    scale = arb(mode).sqrt()
    g = [kernel.S[index] + kernel.prime_sine[index] for index in range(4 * mode + 1)]
    generator_left = [
        (-g[value] / (kernel.pi * scale), 1 / scale) for value in row_modes
    ]
    generator_same = [
        (1 / scale, g[value] / (kernel.pi * scale)) for value in column_modes
    ]
    generator_reflected = [
        (1 / scale, -g[value] / (kernel.pi * scale)) for value in column_modes
    ]

    same_endpoints = (
        Fraction(mode + 1, mode),
        Fraction(2),
        Fraction(2 * mode + 1, mode),
        Fraction(4),
    )
    reflected_endpoints = (
        Fraction(-4),
        Fraction(-(2 * mode + 1), mode),
        Fraction(mode + 1, mode),
        Fraction(2),
    )
    same_roots, same_poles, same_geometry = _roots_and_poles(
        endpoints=same_endpoints, factors=same_factors, inverse=False
    )
    reflected_roots, reflected_poles, reflected_geometry = _roots_and_poles(
        endpoints=reflected_endpoints,
        factors=reflected_factors,
        inverse=True,
    )
    _progress("constructing explicit same-sign Arb ADI factors")
    left_same, right_same = _adi_factors(
        diagonal_left=diagonal_left,
        diagonal_right=diagonal_same,
        generator_left=generator_left,
        generator_right=generator_same,
        roots=same_roots,
        poles=same_poles,
    )
    _progress("constructing explicit reflected Arb ADI factors")
    left_reflected, right_reflected = _adi_factors(
        diagonal_left=diagonal_left,
        diagonal_right=diagonal_reflected,
        generator_left=generator_left,
        generator_right=generator_reflected,
        roots=reflected_roots,
        poles=reflected_poles,
    )

    factor_reconstruction = [
        _verify_factor_samples(
            label="same_sign",
            left=left_same,
            right=right_same,
            diagonal_left=diagonal_left,
            diagonal_right=diagonal_same,
            roots=same_roots,
            poles=same_poles,
            row_modes=row_modes,
            column_modes=column_modes,
            symbol=g,
            pi=kernel.pi,
            reflected=False,
        ),
        _verify_factor_samples(
            label="reflected",
            left=left_reflected,
            right=right_reflected,
            diagonal_left=diagonal_left,
            diagonal_right=diagonal_reflected,
            roots=reflected_roots,
            poles=reflected_poles,
            row_modes=row_modes,
            column_modes=column_modes,
            symbol=g,
            pi=kernel.pi,
            reflected=True,
        ),
    ]
    _progress("sampled entrywise compression/factor identities contain zero")

    artifact_stem = json_out.with_suffix("")
    certificates = []
    certificates.append(
        _certify_factor_norm(
            label="same_sign",
            left=left_same,
            right=right_same,
            epsilon=same_cap,
            delta=delta,
            artifact_stem=artifact_stem,
        )
    )
    certificates.append(
        _certify_factor_norm(
            label="reflected",
            left=left_reflected,
            right=right_reflected,
            epsilon=reflected_cap,
            delta=delta,
            artifact_stem=artifact_stem,
        )
    )

    combined_left = _column_stack(left_same, left_reflected)
    even_right = _column_stack(
        right_same, right_reflected, first_sign=-1, second_sign=-1
    )
    odd_right = _column_stack(
        right_same, right_reflected, first_sign=-1, second_sign=1
    )
    certificates.append(
        _certify_factor_norm(
            label="even_total",
            left=combined_left,
            right=even_right,
            epsilon=total_cap,
            delta=delta,
            artifact_stem=artifact_stem,
        )
    )
    certificates.append(
        _certify_factor_norm(
            label="odd_total",
            left=combined_left,
            right=odd_right,
            epsilon=total_cap,
            delta=delta,
            artifact_stem=artifact_stem,
        )
    )

    script_path = Path(__file__).resolve()
    return {
        "status": "PASS",
        "rigorous_interval_gram_certificate": True,
        "scope": "rank-86 compressed Loewner factors at the first K=1920 bridge",
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": _git_sha(),
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest().upper(),
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "precision_bits": precision,
        "flint_threads": threads,
        "c": c,
        "mode": mode,
        "middle_shell_modes": [mode + 1, 2 * mode],
        "new_shell_modes": [2 * mode + 1, 4 * mode],
        "same_sign_factor_count": same_factors,
        "reflected_factor_count": reflected_factors,
        "combined_rank_upper": 2 * same_factors + 2 * reflected_factors,
        "same_sign_operator_norm_cap": str(same_cap),
        "reflected_operator_norm_cap": str(reflected_cap),
        "parity_total_operator_norm_cap": str(total_cap),
        "gram_majorant_delta": str(delta),
        "same_sign_geometry": same_geometry,
        "reflected_geometry": reflected_geometry,
        "factor_reconstruction_samples": factor_reconstruction,
        "certificates": certificates,
        "proof_formula": (
            "for C=U*V^T, G_U<R*R^T and "
            "R^T*G_V*R<epsilon^2*I imply ||C||<epsilon"
        ),
        "lean_targets": [
            "RiemannCvs.oddDifferenceKernel_adi_factorization_rescaled",
            "v23_k1920_twoLoewnerCompression_posterior",
            "relativeCoupling_of_k1920_rank86Compression",
        ],
        "remaining_boundary": (
            "bind the literal K1920 Arb root/pole lists and their noncollision "
            "certificates to the generic Lean factor theorem, plus the old-core "
            "1/15 channel bound before the rebalanced 4/27 shell step"
        ),
        "timings_seconds": {
            "kernel_build": round(kernel.build_seconds, 3),
            "total": round(time.time() - started, 3),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--mode", type=int, default=1920)
    parser.add_argument("--same-factors", type=int, default=31)
    parser.add_argument("--reflected-factors", type=int, default=12)
    parser.add_argument("--same-cap", default="8881/10000")
    parser.add_argument("--reflected-cap", default="22301/100000")
    parser.add_argument("--total-cap", default="93223/100000")
    parser.add_argument("--gram-majorant-delta", default="1/100000000")
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    payload = certify(
        c=args.c,
        mode=args.mode,
        same_factors=args.same_factors,
        reflected_factors=args.reflected_factors,
        same_cap=_positive_fraction(args.same_cap, "same-cap"),
        reflected_cap=_positive_fraction(args.reflected_cap, "reflected-cap"),
        total_cap=_positive_fraction(args.total_cap, "total-cap"),
        delta=_positive_fraction(args.gram_majorant_delta, "gram-majorant-delta"),
        precision=args.prec,
        threads=args.threads,
        json_out=args.json_out,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        "K1920 adjacent compressed Gram certificate PASS: "
        f"rank={payload['combined_rank_upper']} precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
