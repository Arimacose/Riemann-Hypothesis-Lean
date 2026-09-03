#!/usr/bin/env python3
"""Certify compressed norms for one finite adjacent CvS bridge.

For a source mode ``K`` the combined Archimedean/prime Loewner crossblock from
``(K,2K]`` to ``(2K,4K]`` is split into same-sign and reflected pieces.  The
logarithmic-shift ADI telescope gives explicit factorizations ``C = U V^T`` of
their compressed matrices.  This script constructs every factor entry with
Arb and proves user-supplied caps for the same-sign, reflected, even-total, and
odd-total compressed operators.

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
An optional lower-precision JSON is audited structurally so a higher-precision
run must replay the exact same dyadic selectors and preconditioners.
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
    print(f"[adjacent-compressed-gram] {message}", flush=True)


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


def _bridge_scope(mode: int, rank: int) -> str:
    return f"rank-{rank} compressed Loewner factors at the K={mode} adjacent bridge"


def _lean_targets(mode: int) -> list[str]:
    targets = [
        "RiemannCvs.CvSParityDisplacement."
        "oddDifferenceKernel_adi_factorization_rescaled",
    ]
    if mode == 1920:
        targets.extend(
            [
                "RiemannCvs.K1920AdiShiftBinding.same_factorization",
                "RiemannCvs.V23BoundaryWeylMainline."
                "v23_k1920_twoLoewnerCompression_posterior",
                "RiemannCvs.V23BoundaryWeylMainline."
                "relativeCoupling_of_k1920_rank86Compression",
            ]
        )
    elif mode == 3840:
        targets.extend(
            [
                "RiemannCvs.K3840AdiShiftBinding.same_factorization",
                "RiemannCvs.V23BoundaryWeylMainline."
                "v23_k3840_twoLoewnerCompression_posterior",
                "RiemannCvs.V23BoundaryWeylMainline."
                "relativeCoupling_of_k3840_rank152Compression",
            ]
        )
    elif mode == 7680:
        targets.extend(
            [
                "RiemannCvs.K7680AdiShiftBinding.same_factorization",
                "RiemannCvs.V23BoundaryWeylMainline."
                "v23_k7680_twoLoewnerCompression_posterior",
                "RiemannCvs.V23BoundaryWeylMainline."
                "relativeCoupling_of_k7680_rank152Compression",
            ]
        )
    else:
        targets.append(
            "RiemannCvs.V23BoundaryWeylMainline."
            "relativeCoupling_of_twoLoewnerCompression"
        )
    return targets


def _remaining_boundary(mode: int) -> str:
    if mode == 1920:
        return (
            "the finite Arb Gram inequalities remain explicit certificate premises; "
            "K1920 literal shifts, noncollision, posterior arithmetic, and the old-core "
            "source-Gram adapter are separately kernel-checked"
        )
    if mode == 3840:
        return (
            "the finite Arb Gram and literal K3840 shift-cell inequalities remain named "
            "certificate premises; later finite bridges, the uniform coefficient ledger, "
            "source-specific form convergence, and the closed-operator limit remain open"
        )
    if mode == 7680:
        return (
            "the finite Arb Gram and literal K7680 shift-cell inequalities remain named "
            "certificate premises; eleven later finite bridges, the uniform coefficient "
            "ledger, source-specific form convergence, and the closed-operator limit remain open"
        )
    return (
        "bind this finite Arb artifact to a literal shift-cell transcript and a Lean "
        "energy adapter; uniform summation and the closed-operator limit remain open"
    )


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


def _strict_rows(certificate: dict[str, Any], side: str) -> int:
    return certificate[f"{side}_margin_certificate"]["gershgorin"][
        "strictly_positive_rows"
    ]


def _certificate_hashes(certificate: dict[str, Any]) -> dict[str, str]:
    return {
        "gram_majorant_selector": certificate["gram_majorant_selector"]["sha256"],
        "left_margin_preconditioner": certificate["left_margin_certificate"][
            "preconditioner"
        ]["sha256"],
        "right_margin_preconditioner": certificate["right_margin_certificate"][
            "preconditioner"
        ]["sha256"],
    }


def _reference_audit(reference_path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    reference = json.loads(reference_path.read_text(encoding="utf-8"))
    if reference.get("status") != "PASS":
        raise RuntimeError("reference artifact is not PASS")
    if not reference.get("rigorous_interval_gram_certificate"):
        raise RuntimeError("reference artifact is not a rigorous Gram certificate")
    reference_precision = reference.get("precision_bits")
    if not isinstance(reference_precision, int):
        raise RuntimeError("reference artifact has no integer precision")
    if reference_precision >= payload["precision_bits"]:
        raise RuntimeError("reference precision must be lower than replay precision")

    scalar_fields = (
        "c",
        "mode",
        "middle_shell_modes",
        "new_shell_modes",
        "same_sign_factor_count",
        "reflected_factor_count",
        "combined_rank_upper",
        "same_sign_operator_norm_cap",
        "reflected_operator_norm_cap",
        "parity_total_operator_norm_cap",
        "gram_majorant_delta",
    )
    for field in scalar_fields:
        if reference.get(field) != payload.get(field):
            raise RuntimeError(f"reference mismatch for {field}")

    reference_samples = {
        item["label"]: item for item in reference["factor_reconstruction_samples"]
    }
    payload_samples = {
        item["label"]: item for item in payload["factor_reconstruction_samples"]
    }
    if reference_samples.keys() != payload_samples.keys():
        raise RuntimeError("reference factor-reconstruction labels differ")
    for label in payload_samples:
        for field in ("sampled_entries", "residuals_containing_zero"):
            if reference_samples[label].get(field) != payload_samples[label].get(field):
                raise RuntimeError(
                    f"reference factor-reconstruction mismatch for {label}.{field}"
                )

    reference_certificates = {
        item["label"]: item for item in reference["certificates"]
    }
    payload_certificates = {item["label"]: item for item in payload["certificates"]}
    expected_labels = ("same_sign", "reflected", "even_total", "odd_total")
    if tuple(reference_certificates) != expected_labels:
        raise RuntimeError("reference certificate labels are not canonical")
    if tuple(payload_certificates) != expected_labels:
        raise RuntimeError("replay certificate labels are not canonical")

    replay_hashes: dict[str, dict[str, str]] = {}
    strict_rows: dict[str, dict[str, int]] = {}
    for label in expected_labels:
        old = reference_certificates[label]
        new = payload_certificates[label]
        for field in ("rank", "left_rows", "right_rows", "operator_norm_upper"):
            if old.get(field) != new.get(field):
                raise RuntimeError(f"reference mismatch for {label}.{field}")
        for side in ("left", "right"):
            old_dimension = old[f"{side}_margin_certificate"].get("dimension")
            new_dimension = new[f"{side}_margin_certificate"].get("dimension")
            if old_dimension != new_dimension:
                raise RuntimeError(
                    f"reference dimension mismatch for {label}.{side}"
                )
            old_rows = _strict_rows(old, side)
            new_rows = _strict_rows(new, side)
            if old_rows != old_dimension or new_rows != new_dimension:
                raise RuntimeError(
                    f"non-full strict row count for {label}.{side} margin"
                )
            if old_rows != new_rows:
                raise RuntimeError(
                    f"reference strict-row mismatch for {label}.{side}"
                )
        old_hashes = _certificate_hashes(old)
        new_hashes = _certificate_hashes(new)
        if old_hashes != new_hashes:
            raise RuntimeError(f"reference selector hash mismatch for {label}")
        replay_hashes[label] = new_hashes
        strict_rows[label] = {
            "left": _strict_rows(new, "left"),
            "right": _strict_rows(new, "right"),
        }

    return {
        "status": "PASS",
        "path": str(reference_path.resolve()),
        "sha256": _sha256(reference_path.resolve()),
        "precision_bits": reference_precision,
        "factor_reconstruction_sample_counts_identical": True,
        "certificate_dimensions_and_strict_rows_identical": True,
        "exact_dyadic_selector_and_preconditioner_hashes_identical": True,
        "strict_rows": strict_rows,
        "replayed_hashes": replay_hashes,
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
    reference_json: Path | None,
) -> dict[str, Any]:
    if c <= 1 or mode < 1:
        raise ValueError("c must exceed one and mode must be positive")
    if same_factors < 1 or reflected_factors < 1:
        raise ValueError("factor counts must be positive")
    # These cap compressed operators, not relative residuals.  They need only
    # be positive: later adjacent bridges can have rigorous norms above one.
    if same_cap <= 0 or reflected_cap <= 0:
        raise ValueError("component norm caps must be positive")
    if total_cap <= 0 or delta <= 0:
        raise ValueError("total cap and delta must be positive")
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
    combined_rank = 2 * same_factors + 2 * reflected_factors
    payload: dict[str, Any] = {
        "status": "PASS",
        "rigorous_interval_gram_certificate": True,
        "scope": _bridge_scope(mode, combined_rank),
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
        "combined_rank_upper": combined_rank,
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
        "lean_targets": _lean_targets(mode),
        "remaining_boundary": _remaining_boundary(mode),
        "timings_seconds": {
            "kernel_build": round(kernel.build_seconds, 3),
            "total": round(time.time() - started, 3),
        },
    }
    if reference_json is not None:
        payload["reference_precision_audit"] = _reference_audit(
            reference_json, payload
        )
    return payload


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
    parser.add_argument("--reference-json", type=Path)
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
        reference_json=args.reference_json,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        "Adjacent compressed Gram certificate PASS: "
        f"K={payload['mode']} rank={payload['combined_rank_upper']} "
        f"precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
