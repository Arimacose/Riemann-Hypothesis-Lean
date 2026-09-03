#!/usr/bin/env python3
"""Certify scalable rigorous Grams for finite adjacent ADI bridges.

The explicit certifier materializes K-by-rank and 2K-by-rank Arb matrices.
This certifier instead writes every scalar ADI weight in its simple-pole
partial-fraction basis. Products of basis functions need only finite sums of

    exp(i*n*theta) / (n-t)       and
    exp(i*n*theta) / (n-t)^2.

Every Lerch value is evaluated from its Laplace integral on a finite interval.
The omitted positive ray is bounded explicitly using the lower endpoint of the
real parameter and a rigorous lower bound for the denominator.

The Archimedean symbol is split as

    (S_n + P_n) / pi = 1/4 + P_n/pi + delta_n,
    abs(delta_n) <= 1/(12*n),

using the separately checked all-mode bound abs(S_n-pi/4)<=1/(4*n) and pi>3.
The referenced Archimedean certificate is validated before this consequence
is used. A Young inequality produces a one-sided PSD Gram majorant without
destroying the common row correlation carried by delta_n.

The output matrices are PSD majorants of the exact Grams, not entrywise
enclosures of them. Small exact-dyadic selectors and preconditioners are saved
as NPY artifacts and replayed byte-for-byte at higher precision.
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
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

import flint
import numpy as np
from flint import acb, arb, arb_mat, ctx


ROOT = Path(__file__).resolve().parents[2]
NUMERIC = Path(__file__).resolve().parent
sys.path.insert(0, str(NUMERIC))

from certify_adjacent_compressed_gram import (  # noqa: E402
    _exact_lower_triangular,
    _fraction_arb,
    _identity,
    _roots_and_poles,
)
from certify_parity_gap import prime_powers_up_to  # noqa: E402
from certify_preconditioned_relative_shell import (  # noqa: E402
    _exact_upper_triangular,
    _gershgorin_certificate,
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
)


FrequencyKey = tuple[int, int, int, int, int]
PRIMES = (2, 3, 5, 7, 11)
ZERO_KEY: FrequencyKey = (0, 0, 0, 0, 0)


def progress(message: str) -> None:
    print(f"[adjacent-scalable-gram] {message}", flush=True)


def git_sha() -> str | None:
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


def script_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def interval_record(value: arb, digits: int = 40) -> dict[str, str]:
    return {
        "ball": value.str(digits, radius=True),
        "lower": value.lower().str(digits, radius=True),
        "upper": value.upper().str(digits, radius=True),
    }


def adi_weights(
    value: arb,
    roots: list[arb],
    poles: list[arb],
    *,
    side: str,
) -> list[arb]:
    if len(roots) != len(poles):
        raise ValueError("roots and poles differ in length")
    weights: list[arb] = []
    product = arb(1)
    if side == "left":
        for root, pole in zip(roots, poles, strict=True):
            denominator = value - pole
            if denominator.contains(0):
                raise RuntimeError("left ADI denominator contains zero")
            weights.append(product * (pole - root) / denominator)
            product *= (value - root) / denominator
    elif side == "right":
        for root, pole in zip(roots, poles, strict=True):
            denominator = value - root
            if denominator.contains(0):
                raise RuntimeError("right ADI denominator contains zero")
            weights.append(product / denominator)
            product *= (value - pole) / denominator
    else:
        raise ValueError("side must be left or right")
    return weights


def principal(matrix: arb_mat, start: int, size: int) -> arb_mat:
    result = arb_mat(size, size)
    for i in range(size):
        for j in range(size):
            result[i, j] = matrix[start + i, start + j]
    return result


def assemble_left(h0: arb_mat, h1: arb_mat, h2: arb_mat) -> arb_mat:
    factors = h0.nrows()
    result = arb_mat(2 * factors, 2 * factors)
    for i in range(factors):
        for j in range(factors):
            result[2 * i, 2 * j] = h2[i, j]
            result[2 * i, 2 * j + 1] = -h1[i, j]
            result[2 * i + 1, 2 * j] = -h1[i, j]
            result[2 * i + 1, 2 * j + 1] = h0[i, j]
    _symmetrize_enclosure(result)
    return result


def assemble_right(
    h0: arb_mat,
    h1: arb_mat,
    h2: arb_mat,
    symbol_signs: list[int],
    column_signs: list[int] | None = None,
) -> arb_mat:
    factors = h0.nrows()
    if len(symbol_signs) != factors:
        raise ValueError("wrong symbol sign count")
    if column_signs is None:
        column_signs = [1] * factors
    if len(column_signs) != factors:
        raise ValueError("wrong column sign count")
    result = arb_mat(2 * factors, 2 * factors)
    for i in range(factors):
        for j in range(factors):
            pair_sign = column_signs[i] * column_signs[j]
            result[2 * i, 2 * j] = pair_sign * h0[i, j]
            result[2 * i, 2 * j + 1] = (
                pair_sign * symbol_signs[j] * h1[i, j]
            )
            result[2 * i + 1, 2 * j] = (
                pair_sign * symbol_signs[i] * h1[i, j]
            )
            result[2 * i + 1, 2 * j + 1] = (
                pair_sign * symbol_signs[i] * symbol_signs[j] * h2[i, j]
            )
    _symmetrize_enclosure(result)
    return result


def gram_radius_stats(matrix: arb_mat) -> dict[str, float]:
    row_sums = [
        sum(float(matrix[i, j].rad()) for j in range(matrix.ncols()))
        for i in range(matrix.nrows())
    ]
    return {
        "max_entry_radius": max(
            float(matrix[i, j].rad())
            for i in range(matrix.nrows())
            for j in range(matrix.ncols())
        ),
        "max_row_radius_sum": max(row_sums),
    }


def selector_data(
    gram_left: arb_mat, delta: Fraction
) -> tuple[np.ndarray, np.ndarray]:
    rank = gram_left.nrows()
    midpoint_left = _midpoint_numpy(gram_left)
    radius_row_sums = np.array(
        [
            sum(float(gram_left[i, j].rad()) for j in range(rank))
            for i in range(rank)
        ],
        dtype=float,
    )
    radius_row_sums = np.nextafter(radius_row_sums, np.inf)
    selector = np.linalg.cholesky(
        midpoint_left
        + np.diag(radius_row_sums)
        + float(delta) * np.eye(rank)
    )
    return selector, radius_row_sums


def diagnose_gram_pair(
    *, label: str, gram_left: arb_mat, gram_right: arb_mat, delta: Fraction
) -> dict[str, Any]:
    if gram_left.nrows() != gram_left.ncols():
        raise ValueError(f"{label} left Gram is not square")
    if gram_right.nrows() != gram_right.ncols():
        raise ValueError(f"{label} right Gram is not square")
    if gram_left.nrows() != gram_right.nrows():
        raise ValueError(f"{label} Gram dimensions differ")
    selector, radius_row_sums = selector_data(gram_left, delta)
    transformed = selector.T @ _midpoint_numpy(gram_right) @ selector
    diagnostic_norm = math.sqrt(
        max(0.0, float(np.linalg.eigvalsh(transformed)[-1]))
    )
    return {
        "label": label,
        "rank": gram_left.nrows(),
        "midpoint_transformed_norm_diagnostic": diagnostic_norm,
        "left_radius_row_sum_max": float(radius_row_sums.max()),
        "warning": "float64 route-selection diagnostic; not proof evidence",
    }


def save_exact_lower_selector(path: Path, selector: np.ndarray) -> arb_mat:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.save(path, selector, allow_pickle=False)
    reloaded = np.load(path, allow_pickle=False)
    if not np.array_equal(reloaded, selector):
        raise RuntimeError("Gram selector does not replay byte-for-byte")
    result = _exact_lower_triangular(reloaded)
    del reloaded
    return result


def resolve_reference_npy(
    reference_json: Path, metadata: dict[str, Any]
) -> Path:
    recorded = Path(metadata["path"])
    candidates = (recorded, reference_json.resolve().parent / recorded.name)
    expected_hash = metadata["sha256"]
    for candidate in candidates:
        if candidate.is_file() and _sha256(candidate) == expected_hash:
            return candidate.resolve()
    raise RuntimeError(
        f"reference NPY is unavailable or has the wrong hash: {recorded.name}"
    )


def replay_npy(
    *,
    reference_json: Path,
    metadata: dict[str, Any],
    destination: Path,
) -> np.ndarray:
    source = resolve_reference_npy(reference_json, metadata)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if source != destination.resolve():
        shutil.copyfile(source, destination)
    if _sha256(destination) != metadata["sha256"]:
        raise RuntimeError("replayed NPY hash differs from the reference")
    array = np.load(destination, allow_pickle=False)
    if list(array.shape) != metadata["shape"] or str(array.dtype) != metadata["dtype"]:
        raise RuntimeError("replayed NPY dtype or shape differs from the reference")
    return array


def certify_positive_matrix(
    *,
    matrix: arb_mat,
    label: str,
    preconditioner_path: Path,
    reference_json: Path | None = None,
    reference_metadata: dict[str, Any] | None = None,
) -> dict[str, Any]:
    dimension = matrix.nrows()
    if matrix.ncols() != dimension:
        raise ValueError(f"{label} matrix must be square")
    midpoint_started = time.time()
    if reference_json is None:
        midpoint = _midpoint_numpy(matrix)
        cholesky = np.linalg.cholesky(midpoint)
        preconditioner_midpoint = np.triu(np.linalg.inv(cholesky.T))
        del midpoint, cholesky
        selection = "selected from the current midpoint"
        preconditioner_path.parent.mkdir(parents=True, exist_ok=True)
        np.save(preconditioner_path, preconditioner_midpoint, allow_pickle=False)
    else:
        if reference_metadata is None:
            raise ValueError("reference preconditioner metadata is required")
        preconditioner_midpoint = replay_npy(
            reference_json=reference_json,
            metadata=reference_metadata,
            destination=preconditioner_path,
        )
        selection = "replayed byte-for-byte from the lower-precision artifact"
    midpoint_seconds = time.time() - midpoint_started
    reloaded = np.load(preconditioner_path, allow_pickle=False)
    if not np.array_equal(reloaded, preconditioner_midpoint):
        raise RuntimeError(f"saved {label} preconditioner does not replay")
    del reloaded

    exact_started = time.time()
    preconditioner = _exact_upper_triangular(preconditioner_midpoint)
    diagonal_midpoints: list[float] = []
    for i in range(dimension):
        diagonal = preconditioner[i, i]
        if diagonal.rad() != 0 or not diagonal > 0:
            raise RuntimeError(
                f"{label} exact dyadic preconditioner has a nonpositive diagonal"
            )
        diagonal_midpoints.append(float(diagonal.mid()))
    exact_seconds = time.time() - exact_started

    congruence_started = time.time()
    preconditioned = preconditioner.transpose() * (matrix * preconditioner)
    congruence_seconds = time.time() - congruence_started
    gershgorin_started = time.time()
    gershgorin = _gershgorin_certificate(preconditioned)
    gershgorin_seconds = time.time() - gershgorin_started
    del preconditioner, preconditioned
    gc.collect()
    return {
        "status": "PASS",
        "label": label,
        "dimension": dimension,
        "preconditioner": {
            "path": str(preconditioner_path.resolve()),
            "sha256": _sha256(preconditioner_path),
            "dtype": str(preconditioner_midpoint.dtype),
            "shape": list(preconditioner_midpoint.shape),
            "storage": "NumPy .npy; every float is embedded as an exact dyadic",
            "upper_triangular": True,
            "all_dyadic_radii_zero": True,
            "all_diagonal_entries_positive": True,
            "min_diagonal_midpoint": min(diagonal_midpoints),
            "selection": selection,
        },
        "gershgorin": gershgorin,
        "proof_consequence": (
            "the fixed exact-dyadic congruence is strictly diagonally "
            "dominant with positive diagonal, so the symmetric matrix is "
            "strictly positive definite"
        ),
        "timings_seconds": {
            "midpoint_basis_selection_or_replay": round(midpoint_seconds, 3),
            "exact_dyadic_embedding": round(exact_seconds, 3),
            "arb_congruence": round(congruence_seconds, 3),
            "gershgorin": round(gershgorin_seconds, 3),
        },
    }


def certify_gram_pair(
    *,
    label: str,
    gram_left: arb_mat,
    gram_right: arb_mat,
    cap: Fraction,
    delta: Fraction,
    stem: Path,
    reference_json: Path | None = None,
    reference_certificate: dict[str, Any] | None = None,
) -> dict[str, Any]:
    started = time.time()
    if gram_left.nrows() != gram_right.nrows():
        raise ValueError(f"{label} Gram dimensions differ")
    rank = gram_left.nrows()
    candidate_selector, radius_row_sums = selector_data(gram_left, delta)
    selector_path = stem.with_name(stem.name + f"_{label}_gram_majorant.npy")
    if reference_json is None:
        selector_midpoint = candidate_selector
        selector = save_exact_lower_selector(selector_path, selector_midpoint)
        selector_selection = "selected from the current midpoint"
    else:
        if reference_certificate is None:
            raise ValueError("reference Gram certificate is required")
        selector_midpoint = replay_npy(
            reference_json=reference_json,
            metadata=reference_certificate["gram_majorant_selector"],
            destination=selector_path,
        )
        selector = _exact_lower_triangular(selector_midpoint)
        selector_selection = (
            "replayed byte-for-byte from the lower-precision artifact"
        )
    del candidate_selector

    left_margin = selector * selector.transpose() - gram_left
    _symmetrize_enclosure(left_margin)
    cap_arb = _fraction_arb(cap)
    right_margin = _identity(rank, cap_arb * cap_arb) - (
        selector.transpose() * (gram_right * selector)
    )
    _symmetrize_enclosure(right_margin)

    left_preconditioner = stem.with_name(
        stem.name + f"_{label}_left_margin_preconditioner.npy"
    )
    right_preconditioner = stem.with_name(
        stem.name + f"_{label}_right_margin_preconditioner.npy"
    )
    progress(f"proving {label}: G_U < R R^T")
    left_reference = (
        reference_certificate["left_margin_certificate"]["preconditioner"]
        if reference_certificate is not None
        else None
    )
    right_reference = (
        reference_certificate["right_margin_certificate"]["preconditioner"]
        if reference_certificate is not None
        else None
    )
    left_certificate = certify_positive_matrix(
        matrix=left_margin,
        label=f"{label} PSD majorant selector minus left Gram majorant",
        preconditioner_path=left_preconditioner,
        reference_json=reference_json,
        reference_metadata=left_reference,
    )
    progress(f"proving {label}: R^T G_V R < cap^2 I")
    right_certificate = certify_positive_matrix(
        matrix=right_margin,
        label=f"{label} cap squared identity minus transformed right majorant",
        preconditioner_path=right_preconditioner,
        reference_json=reference_json,
        reference_metadata=right_reference,
    )

    transformed = (
        selector_midpoint.T
        @ _midpoint_numpy(gram_right)
        @ selector_midpoint
    )
    diagnostic_norm = math.sqrt(
        max(0.0, float(np.linalg.eigvalsh(transformed)[-1]))
    )
    return {
        "status": "PASS",
        "label": label,
        "rank": rank,
        "left_rows": rank,
        "right_rows": rank,
        "operator_norm_upper": str(cap),
        "gram_majorant_delta": str(delta),
        "gram_majorant_selector": {
            "path": str(selector_path.resolve()),
            "sha256": _sha256(selector_path.resolve()),
            "dtype": str(selector_midpoint.dtype),
            "shape": list(selector_midpoint.shape),
            "lower_triangular": True,
            "all_entries_exact_dyadic_after_embedding": True,
            "all_diagonal_entries_positive": bool(
                np.all(np.diag(selector_midpoint) > 0)
            ),
            "selection": selector_selection,
        },
        "left_margin_certificate": left_certificate,
        "right_margin_certificate": right_certificate,
        "midpoint_transformed_norm_diagnostic": diagnostic_norm,
        "left_radius_row_sum_max": float(radius_row_sums.max()),
        "left_gram_majorant_radii": gram_radius_stats(gram_left),
        "right_gram_majorant_radii": gram_radius_stats(gram_right),
        "proof_consequence": (
            "G_U <= G_U_majorant < R*R^T and "
            "R^T*G_V_majorant*R < cap^2*I imply ||U*V^T|| < cap"
        ),
        "timings_seconds": {"total": round(time.time() - started, 3)},
    }


def complex_error(radius: arb) -> acb:
    upper = radius.upper()
    return acb(arb(0, upper), arb(0, upper))


def key_add(left: FrequencyKey, right: FrequencyKey) -> FrequencyKey:
    return tuple(a + b for a, b in zip(left, right, strict=True))  # type: ignore[return-value]


def key_neg(key: FrequencyKey) -> FrequencyKey:
    return tuple(-value for value in key)  # type: ignore[return-value]


def key_is_positive(key: FrequencyKey) -> bool:
    for value in key:
        if value:
            return value > 0
    return False


def factor_key(value: int) -> FrequencyKey:
    remaining = value
    exponents: list[int] = []
    for prime in PRIMES:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        exponents.append(exponent)
    if remaining != 1:
        raise ValueError(f"frequency base {value} has an unsupported prime factor")
    return tuple(exponents)  # type: ignore[return-value]


def add_coefficient(
    target: dict[FrequencyKey, acb], key: FrequencyKey, value: acb
) -> None:
    target[key] = target.get(key, acb(0)) + value


def frequency_term_record(key: FrequencyKey, coefficient: acb) -> dict[str, Any]:
    return {
        "prime_exponents": list(key),
        "coefficient_real": interval_record(coefficient.real),
        "coefficient_imaginary": interval_record(coefficient.imag),
    }


def symbol_fourier(
    c: int,
) -> tuple[
    acb,
    dict[FrequencyKey, acb],
    acb,
    dict[FrequencyKey, acb],
    dict[str, Any],
]:
    """Return constant/positive-frequency coefficients for s0 and s0^2."""

    pi = arb.pi()
    full: dict[FrequencyKey, acb] = {ZERO_KEY: acb(arb(1) / 4)}
    prime_powers: list[dict[str, Any]] = []
    for q, p in prime_powers_up_to(c):
        if q >= c:
            continue
        key = factor_key(q)
        amplitude = arb(p).log() / (pi * arb(q).sqrt())
        prime_powers.append(
            {"base": q, "prime": p, "prime_exponents": list(key)}
        )
        add_coefficient(full, key, acb(0, -amplitude / 2))
        add_coefficient(full, key_neg(key), acb(0, amplitude / 2))

    square: dict[FrequencyKey, acb] = {}
    for left_key, left_value in full.items():
        for right_key, right_value in full.items():
            add_coefficient(
                square,
                key_add(left_key, right_key),
                left_value * right_value,
            )

    first_terms = {
        key: value for key, value in full.items() if key_is_positive(key)
    }
    square_terms = {
        key: value for key, value in square.items() if key_is_positive(key)
    }
    first_keys = sorted(first_terms)
    square_keys = sorted(square_terms)
    metadata = {
        "frequency_basis_primes": list(PRIMES),
        "prime_powers_below_cutoff": prime_powers,
        "s0_constant": frequency_term_record(ZERO_KEY, full[ZERO_KEY]),
        "s0_positive_terms": [
            frequency_term_record(key, first_terms[key]) for key in first_keys
        ],
        "s0_squared_constant": frequency_term_record(ZERO_KEY, square[ZERO_KEY]),
        "s0_squared_positive_terms": [
            frequency_term_record(key, square_terms[key]) for key in square_keys
        ],
        "s0_positive_keys": [list(key) for key in first_keys],
        "s0_squared_positive_keys": [list(key) for key in square_keys],
    }
    return (
        full[ZERO_KEY],
        first_terms,
        square[ZERO_KEY],
        square_terms,
        metadata,
    )


def frequency_angle(key: FrequencyKey, *, c: int) -> arb:
    logarithm = arb(0)
    for exponent, prime in zip(key, PRIMES, strict=True):
        logarithm += exponent * arb(prime).log()
    return 2 * arb.pi() * logarithm / arb(c).log()


def phase_separation(theta: arb) -> arb:
    cosine = theta.cos()
    if bool(cosine < 0):
        return arb(1)
    separation = abs(theta.sin()).lower()
    if not bool(separation > 0):
        raise RuntimeError("frequency separation from the positive real ray is not strict")
    return separation


def integral_lerch(
    *, z: acb, a: arb, s: int, target: arb
) -> tuple[acb, dict[str, arb]]:
    if s not in {1, 2}:
        raise ValueError("only Lerch orders one and two are supported")
    if not bool(a > 0) or not bool(target > 0):
        raise ValueError("Lerch parameter and target must be positive")
    if (1 - z).contains(0):
        raise RuntimeError("Lerch integral denominator contains zero at the origin")

    a_lower = a.lower()
    z_upper = abs(z).upper()
    target_float = float(target.upper())
    initial = (
        -math.log(target_float) + 24 + math.log1p(float(a_lower))
    ) / float(a_lower)
    endpoint = arb(str(max(initial, 2.0 ** -40)))
    tail = arb(0)
    for _ in range(32):
        exponential = (-endpoint).exp()
        denominator = 1 - z_upper * exponential
        if bool(denominator > 0):
            if s == 1:
                tail = (-a_lower * endpoint).exp() / (
                    a_lower * denominator
                )
            else:
                tail = (
                    (-a_lower * endpoint).exp()
                    * (endpoint / a_lower + 1 / a_lower**2)
                    / denominator
                )
            if bool(tail < target / 4):
                break
        endpoint *= 2
    else:
        raise RuntimeError("failed to obtain a strict Lerch integral tail bound")

    parameter = acb(a)

    def integrand(value: acb, _analytic: bool) -> acb:
        return (
            value ** (s - 1)
            * (-parameter * value).exp()
            / (1 - z * (-value).exp())
        )

    value = acb.integral(
        integrand,
        acb(0),
        acb(endpoint),
        abs_tol=target / 4,
        rel_tol=target / 4,
        eval_limit=200_000,
        depth_limit=40,
        use_heap=True,
    )
    if not value.is_finite():
        raise RuntimeError("Arb Lerch integral evaluation is nonfinite")
    result = value + complex_error(tail)
    return result, {
        "endpoint": endpoint,
        "tail_upper": tail.upper(),
        "parameter_lower": a_lower,
        "result_radius": max(result.real.rad(), result.imag.rad()),
    }


@dataclass
class PoleLocation:
    normalized: arb
    scaled: arb
    side: str
    distance: arb


class FiniteMomentEvaluator:
    def __init__(
        self,
        *,
        mode: int,
        lo: int,
        hi: int,
        poles: list[arb],
        c: int,
        precision: int,
    ) -> None:
        self.mode = mode
        self.lo = lo
        self.hi = hi
        self.count = hi - lo + 1
        self.c = c
        self.precision = precision
        self.target = arb(2) ** (-(precision - 16))
        self.poles: list[PoleLocation] = []
        for pole in poles:
            scaled = mode * pole
            if bool(scaled < lo):
                side = "lower"
                distance = arb(lo) - scaled
            elif bool(scaled > hi):
                side = "upper"
                distance = scaled - arb(hi)
            else:
                raise RuntimeError(
                    "partial-fraction pole is not separated from the summation grid"
                )
            if not bool(distance > 0):
                raise RuntimeError("partial-fraction pole distance is not positive")
            self.poles.append(PoleLocation(pole, scaled, side, distance))
        self._constant_cache: dict[tuple[int, int], arb] = {}
        self._oscillatory_cache: dict[tuple[FrequencyKey, int, int], acb] = {}
        self.method_counts = {"finite_laplace_integral": 0}
        self.minimum_phase_separation = math.inf
        self.minimum_endpoint: arb | None = None
        self.maximum_endpoint: arb | None = None
        self.maximum_tail_upper = arb(0)
        self.maximum_result_radius = arb(0)

    def record_quadrature(self, audit: dict[str, arb]) -> None:
        endpoint = audit["endpoint"]
        if self.minimum_endpoint is None or bool(endpoint < self.minimum_endpoint):
            self.minimum_endpoint = endpoint
        if self.maximum_endpoint is None or bool(self.maximum_endpoint < endpoint):
            self.maximum_endpoint = endpoint
        self.maximum_tail_upper = max(
            self.maximum_tail_upper, audit["tail_upper"]
        )
        self.maximum_result_radius = max(
            self.maximum_result_radius, audit["result_radius"]
        )
        self.method_counts["finite_laplace_integral"] += 1

    def audit_record(self) -> dict[str, Any]:
        if self.minimum_endpoint is None or self.maximum_endpoint is None:
            raise RuntimeError("no oscillatory quadrature was recorded")
        distances = [location.distance for location in self.poles]
        lower_count = sum(location.side == "lower" for location in self.poles)
        upper_count = len(self.poles) - lower_count
        return {
            "method_counts": self.method_counts,
            "quadrature_target": interval_record(self.target),
            "finite_interval_endpoint_minimum": interval_record(
                self.minimum_endpoint
            ),
            "finite_interval_endpoint_maximum": interval_record(
                self.maximum_endpoint
            ),
            "maximum_positive_ray_tail_upper": interval_record(
                self.maximum_tail_upper
            ),
            "maximum_lerch_result_radius": interval_record(
                self.maximum_result_radius
            ),
            "minimum_phase_separation": self.minimum_phase_separation,
            "pole_count": len(self.poles),
            "lower_side_poles": lower_count,
            "upper_side_poles": upper_count,
            "minimum_scaled_grid_distance": interval_record(min(distances)),
            "maximum_scaled_grid_distance": interval_record(max(distances)),
            "integral_formula": (
                "Phi(z,s,a)=integral_0^infinity "
                "t^(s-1)*exp(-a*t)/(1-z*exp(-t)) dt"
            ),
            "tail_bound": (
                "the omitted positive ray is bounded using a_lower and "
                "1-|z|*exp(-T)>0"
            ),
        }

    def constant_sum(self, pole_index: int, s: int) -> arb:
        cache_key = (pole_index, s)
        if cache_key in self._constant_cache:
            return self._constant_cache[cache_key]
        location = self.poles[pole_index]
        d = location.distance
        if s == 1:
            value = (d + self.count).digamma() - d.digamma()
        elif s == 2:
            start = acb(d).polygamma(acb(1)).real
            end = acb(d + self.count).polygamma(acb(1)).real
            value = start - end
        else:
            raise ValueError("only moment orders one and two are supported")
        if location.side == "upper" and s % 2:
            value = -value
        self._constant_cache[cache_key] = value
        return value

    def oscillatory_sum(
        self, key: FrequencyKey, pole_index: int, s: int
    ) -> acb:
        cache_key = (key, pole_index, s)
        if cache_key in self._oscillatory_cache:
            return self._oscillatory_cache[cache_key]
        theta = frequency_angle(key, c=self.c)
        separation = phase_separation(theta)
        self.minimum_phase_separation = min(
            self.minimum_phase_separation, float(separation.lower())
        )
        location = self.poles[pole_index]
        direction = 1 if location.side == "lower" else -1
        z = acb(0, direction * theta).exp()
        first, first_audit = integral_lerch(
            z=z,
            a=location.distance,
            s=s,
            target=self.target,
        )
        tail, tail_audit = integral_lerch(
            z=z,
            a=location.distance + self.count,
            s=s,
            target=self.target,
        )
        self.record_quadrature(first_audit)
        self.record_quadrature(tail_audit)
        local = first - z ** self.count * tail
        edge = self.lo if location.side == "lower" else self.hi
        phase = acb(0, edge * theta).exp()
        sign = -1 if location.side == "upper" and s % 2 else 1
        result = sign * phase * local
        self._oscillatory_cache[cache_key] = result
        return result

    def weighted_sums(
        self,
        *,
        constant: acb,
        terms: dict[FrequencyKey, acb],
    ) -> tuple[list[arb], list[arb]]:
        if not constant.imag.contains(0):
            raise RuntimeError("Fourier constant is not real")
        first: list[arb] = []
        second: list[arb] = []
        for pole_index in range(len(self.poles)):
            value1 = constant.real * self.constant_sum(pole_index, 1)
            value2 = constant.real * self.constant_sum(pole_index, 2)
            for key, coefficient in terms.items():
                value1 += 2 * (
                    coefficient * self.oscillatory_sum(key, pole_index, 1)
                ).real
                value2 += 2 * (
                    coefficient * self.oscillatory_sum(key, pole_index, 2)
                ).real
            first.append(value1)
            second.append(value2)
        return first, second

    def basis_moment(
        self,
        *,
        constant: acb,
        terms: dict[FrequencyKey, acb],
    ) -> arb_mat:
        first, second = self.weighted_sums(constant=constant, terms=terms)
        dimension = len(self.poles)
        result = arb_mat(dimension, dimension)
        for i in range(dimension):
            result[i, i] = self.mode * second[i]
            for j in range(i):
                denominator = self.poles[i].scaled - self.poles[j].scaled
                if denominator.contains(0):
                    raise RuntimeError("distinct partial-fraction poles overlap")
                value = self.mode * (first[i] - first[j]) / denominator
                result[i, j] = value
                result[j, i] = value
        _symmetrize_enclosure(result)
        return result


def partial_fraction_transform(
    roots: list[arb],
    poles: list[arb],
    *,
    side: str,
    argument_sign: int = 1,
) -> tuple[list[arb], arb_mat]:
    if len(roots) != len(poles):
        raise ValueError("ADI roots and poles differ in length")
    count = len(roots)
    if side == "left":
        basis = poles
        numerator_nodes = roots
    elif side == "right":
        basis = roots
        numerator_nodes = poles
    else:
        raise ValueError("side must be left or right")

    coefficients = arb_mat(count, count)
    for factor in range(count):
        prefactor = (
            poles[factor] - roots[factor] if side == "left" else arb(1)
        )
        for basis_index in range(factor + 1):
            point = basis[basis_index]
            numerator = prefactor
            for index in range(factor):
                numerator *= point - numerator_nodes[index]
            denominator = arb(1)
            for index in range(factor + 1):
                if index != basis_index:
                    denominator *= point - basis[index]
            if denominator.contains(0):
                raise RuntimeError(
                    "partial-fraction residue denominator contains zero"
                )
            coefficients[factor, basis_index] = numerator / denominator

    if argument_sign == 1:
        return list(basis), coefficients
    if argument_sign != -1:
        raise ValueError("argument sign must be +1 or -1")
    transformed = arb_mat(count, count)
    for i in range(count):
        for j in range(count):
            transformed[i, j] = -coefficients[i, j]
    return [-value for value in basis], transformed


def block_diagonal(first: arb_mat, second: arb_mat) -> arb_mat:
    result = arb_mat(
        first.nrows() + second.nrows(), first.ncols() + second.ncols()
    )
    for i in range(first.nrows()):
        for j in range(first.ncols()):
            result[i, j] = first[i, j]
    for i in range(second.nrows()):
        for j in range(second.ncols()):
            result[first.nrows() + i, first.ncols() + j] = second[i, j]
    return result


def transform_moment(transform: arb_mat, basis: arb_mat) -> arb_mat:
    result = transform * basis * transform.transpose()
    _symmetrize_enclosure(result)
    return result


def verify_transform_samples(
    *,
    label: str,
    roots: list[arb],
    poles: list[arb],
    side: str,
    argument_sign: int,
    basis: list[arb],
    transform: arb_mat,
    samples: Iterable[Fraction],
) -> dict[str, Any]:
    sample_list = list(samples)
    checked = 0
    maximum_midpoint_abs = 0.0
    maximum_radius = 0.0
    for sample in sample_list:
        x = _fraction_arb(sample)
        argument = argument_sign * x
        expected = adi_weights(argument, roots, poles, side=side)
        for factor, expected_value in enumerate(expected):
            reconstructed = arb(0)
            for basis_index, pole in enumerate(basis):
                denominator = x - pole
                if denominator.contains(0):
                    raise RuntimeError("sample denominator contains zero")
                reconstructed += transform[factor, basis_index] / denominator
            residual = reconstructed - expected_value
            if not residual.contains(0):
                raise RuntimeError(
                    "partial-fraction sample reconstruction misses zero"
                )
            checked += 1
            maximum_midpoint_abs = max(
                maximum_midpoint_abs, abs(float(residual.mid()))
            )
            maximum_radius = max(maximum_radius, float(residual.rad()))
    return {
        "status": "PASS",
        "label": label,
        "side": side,
        "argument_sign": argument_sign,
        "factor_count": len(roots),
        "basis_count": len(basis),
        "samples": [str(sample) for sample in sample_list],
        "identities_checked": checked,
        "residuals_containing_zero": checked,
        "maximum_midpoint_abs": maximum_midpoint_abs,
        "maximum_radius": maximum_radius,
        "formula": "ADI scalar weight minus its simple-pole expansion",
    }


def signed_h0(h0: arb_mat, signs: list[int]) -> arb_mat:
    if len(signs) != h0.nrows():
        raise ValueError("wrong sign count for H0 congruence")
    result = arb_mat(h0.nrows(), h0.ncols())
    for i in range(h0.nrows()):
        for j in range(h0.ncols()):
            result[i, j] = signs[i] * signs[j] * h0[i, j]
    _symmetrize_enclosure(result)
    return result


def gram_upper_majorant(
    *,
    center: arb_mat,
    h0: arb_mat,
    minimum_mode: int,
    eta: Fraction,
    error_slot: str,
    signs: list[int] | None = None,
) -> arb_mat:
    if center.nrows() != 2 * h0.nrows():
        raise ValueError("center and H0 dimensions disagree")
    if eta <= 0:
        raise ValueError("Young parameter must be positive")
    dimension = h0.nrows()
    base = h0 if signs is None else signed_h0(h0, signs)
    error = arb_mat(2 * dimension, 2 * dimension)
    offset = 0 if error_slot == "first" else 1
    if error_slot not in {"first", "second"}:
        raise ValueError("error slot must be first or second")
    for i in range(dimension):
        for j in range(dimension):
            error[2 * i + offset, 2 * j + offset] = base[i, j]
    dmax_squared = _fraction_arb(
        Fraction(1, 144 * minimum_mode * minimum_mode)
    )
    eta_arb = _fraction_arb(eta)
    result = (
        (1 + eta_arb) * center
        + (1 + 1 / eta_arb) * dmax_squared * error
    )
    _symmetrize_enclosure(result)
    return result


def build_family_data(
    mode: int, same_factors: int, reflected_factors: int
) -> tuple[list[arb], list[arb], list[arb], list[arb], dict[str, Any]]:
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
        endpoints=reflected_endpoints, factors=reflected_factors, inverse=True
    )
    return (
        same_roots,
        same_poles,
        reflected_roots,
        reflected_poles,
        {
            "same_sign": same_geometry,
            "reflected": reflected_geometry,
        },
    )


def build_moments(
    *,
    mode: int,
    lo: int,
    hi: int,
    families: list[tuple[list[arb], arb_mat]],
    c: int,
    precision: int,
) -> tuple[arb_mat, arb_mat, arb_mat, dict[str, Any]]:
    poles: list[arb] = []
    transforms: list[arb_mat] = []
    for family_poles, transform in families:
        poles.extend(family_poles)
        transforms.append(transform)
    combined_transform = transforms[0]
    for transform in transforms[1:]:
        combined_transform = block_diagonal(combined_transform, transform)

    (
        s0_constant,
        s0_terms,
        s02_constant,
        s02_terms,
        frequency_metadata,
    ) = symbol_fourier(c)
    evaluator = FiniteMomentEvaluator(
        mode=mode,
        lo=lo,
        hi=hi,
        poles=poles,
        c=c,
        precision=precision,
    )
    started = time.time()
    progress(f"evaluating H0 basis on [{lo},{hi}]")
    basis0 = evaluator.basis_moment(constant=acb(1), terms={})
    progress(f"evaluating H1 basis with {len(s0_terms)} frequencies")
    basis1 = evaluator.basis_moment(constant=s0_constant, terms=s0_terms)
    progress(f"evaluating H2 basis with {len(s02_terms)} frequencies")
    basis2 = evaluator.basis_moment(constant=s02_constant, terms=s02_terms)
    progress("applying the shared partial-fraction transform")
    h0 = transform_moment(combined_transform, basis0)
    h1 = transform_moment(combined_transform, basis1)
    h2 = transform_moment(combined_transform, basis2)
    quadrature_audit = evaluator.audit_record()
    return h0, h1, h2, {
        "seconds": round(time.time() - started, 3),
        "basis_dimension": len(poles),
        "s0_positive_frequencies": len(s0_terms),
        "s0_squared_positive_frequencies": len(s02_terms),
        "frequency_metadata": frequency_metadata,
        "quadrature_audit": quadrature_audit,
        "h0_radii": gram_radius_stats(h0),
        "h1_radii": gram_radius_stats(h1),
        "h2_radii": gram_radius_stats(h2),
    }


def validate_archimedean_certificate(
    path: Path, *, c: int, mode: int, precision: int
) -> dict[str, Any]:
    resolved = path.resolve()
    data = json.loads(resolved.read_text(encoding="utf-8"))
    if data.get("status") != "PASS":
        raise RuntimeError("Archimedean reference certificate is not PASS")
    if not data.get("rigorous_constant_certificate"):
        raise RuntimeError("Archimedean reference is not a rigorous certificate")
    if data.get("c") != c:
        raise RuntimeError("Archimedean reference cutoff mismatch")
    minimum_mode = data.get("minimum_mode")
    if not isinstance(minimum_mode, int) or minimum_mode > mode + 1:
        raise RuntimeError("Archimedean envelope does not cover this bridge")
    reference_precision = data.get("precision_bits")
    if not isinstance(reference_precision, int) or reference_precision < precision:
        raise RuntimeError("Archimedean reference precision is too low")
    centered = data.get("centered_symbol_audit", {})
    if Fraction(centered.get("target_decay_coefficient", "0")) != Fraction(1, 4):
        raise RuntimeError("Archimedean centered coefficient is not 1/4")
    if not centered.get("strict_upper_pass") or not centered.get(
        "strict_lower_pass"
    ):
        raise RuntimeError("Archimedean centered certificate is not strict")
    endpoint = data.get("source_formula_endpoint_replay", {})
    if not endpoint.get("strict_centered_pass"):
        raise RuntimeError("Archimedean source endpoint replay failed")
    generator_path = NUMERIC / "certify_archimedean_tail_envelope.py"
    generator_hash = script_hash(generator_path)
    if data.get("script_sha256") != generator_hash:
        raise RuntimeError("Archimedean generator hash does not match tracked source")
    pi_minus_three = arb.pi() - 3
    if not bool(pi_minus_three > 0):
        raise RuntimeError("Arb failed to prove pi > 3")
    return {
        "status": "PASS",
        "path": str(resolved),
        "sha256": _sha256(resolved),
        "certificate_precision_bits": reference_precision,
        "certificate_minimum_mode": minimum_mode,
        "centered_decay_coefficient": "1/4",
        "pi_minus_three": interval_record(pi_minus_three),
        "derived_normalized_error": "abs(delta_n) <= 1/(12*n)",
        "derivation": (
            "abs(S_n-pi/4)<=1/(4*n) and pi>3 imply "
            "abs((S_n-pi/4)/pi)<=1/(12*n)"
        ),
        "generator_path": str(generator_path.resolve()),
        "generator_sha256": generator_hash,
        "source_git_sha": data.get("git_sha"),
    }


def strict_rows(certificate: dict[str, Any], side: str) -> int:
    return certificate[f"{side}_margin_certificate"]["gershgorin"][
        "strictly_positive_rows"
    ]


def certificate_hashes(certificate: dict[str, Any]) -> dict[str, str]:
    return {
        "gram_majorant_selector": certificate["gram_majorant_selector"]["sha256"],
        "left_margin_preconditioner": certificate["left_margin_certificate"][
            "preconditioner"
        ]["sha256"],
        "right_margin_preconditioner": certificate["right_margin_certificate"][
            "preconditioner"
        ]["sha256"],
    }


def reference_audit(reference_path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    reference = json.loads(reference_path.read_text(encoding="utf-8"))
    if reference.get("status") != "PASS":
        raise RuntimeError("reference scalable Gram artifact is not PASS")
    if not reference.get("rigorous_interval_gram_certificate"):
        raise RuntimeError("reference is not a rigorous scalable Gram certificate")
    old_precision = reference.get("precision_bits")
    if not isinstance(old_precision, int) or old_precision >= payload["precision_bits"]:
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
        "young_eta",
        "script_sha256",
        "dependency_sha256",
    )
    for field in scalar_fields:
        if reference.get(field) != payload.get(field):
            raise RuntimeError(f"reference mismatch for {field}")
    for side in ("source_moments", "target_moments"):
        old_frequency = reference[side]["frequency_metadata"]
        new_frequency = payload[side]["frequency_metadata"]
        for field in (
            "frequency_basis_primes",
            "prime_powers_below_cutoff",
            "s0_positive_keys",
            "s0_squared_positive_keys",
        ):
            if old_frequency.get(field) != new_frequency.get(field):
                raise RuntimeError(f"reference frequency mismatch for {side}.{field}")
        if reference[side].get("basis_dimension") != payload[side].get(
            "basis_dimension"
        ):
            raise RuntimeError(f"reference basis dimension mismatch for {side}")
    old_samples = {
        item["label"]: item for item in reference["partial_fraction_sample_audits"]
    }
    new_samples = {
        item["label"]: item for item in payload["partial_fraction_sample_audits"]
    }
    if old_samples.keys() != new_samples.keys():
        raise RuntimeError("reference partial-fraction labels differ")
    for label in new_samples:
        for field in (
            "factor_count",
            "basis_count",
            "samples",
            "identities_checked",
            "residuals_containing_zero",
        ):
            if old_samples[label].get(field) != new_samples[label].get(field):
                raise RuntimeError(
                    f"reference partial-fraction mismatch for {label}.{field}"
                )
    old_certificates = {
        item["label"]: item for item in reference["certificates"]
    }
    new_certificates = {
        item["label"]: item for item in payload["certificates"]
    }
    labels = ("same_sign", "reflected", "even_total", "odd_total")
    if tuple(old_certificates) != labels or tuple(new_certificates) != labels:
        raise RuntimeError("certificate labels are not canonical")
    replay_hashes: dict[str, dict[str, str]] = {}
    row_counts: dict[str, dict[str, int]] = {}
    for label in labels:
        old = old_certificates[label]
        new = new_certificates[label]
        for field in ("rank", "left_rows", "right_rows", "operator_norm_upper"):
            if old.get(field) != new.get(field):
                raise RuntimeError(f"reference mismatch for {label}.{field}")
        for side in ("left", "right"):
            dimension = new[f"{side}_margin_certificate"]["dimension"]
            old_dimension = old[f"{side}_margin_certificate"]["dimension"]
            if dimension != old_dimension:
                raise RuntimeError(f"reference dimension mismatch for {label}.{side}")
            old_rows = strict_rows(old, side)
            new_rows = strict_rows(new, side)
            if old_rows != dimension or new_rows != dimension:
                raise RuntimeError(f"non-full strict rows for {label}.{side}")
        old_hashes = certificate_hashes(old)
        new_hashes = certificate_hashes(new)
        if old_hashes != new_hashes:
            raise RuntimeError(f"reference selector hash mismatch for {label}")
        replay_hashes[label] = new_hashes
        row_counts[label] = {
            "left": strict_rows(new, "left"),
            "right": strict_rows(new, "right"),
        }
    resolved = reference_path.resolve()
    return {
        "status": "PASS",
        "path": str(resolved),
        "sha256": _sha256(resolved),
        "precision_bits": old_precision,
        "partial_fraction_and_frequency_structure_identical": True,
        "certificate_dimensions_and_strict_rows_identical": True,
        "exact_dyadic_selector_and_preconditioner_hashes_identical": True,
        "strict_rows": row_counts,
        "replayed_hashes": replay_hashes,
    }


def lean_targets(mode: int) -> list[str]:
    return [
        f"RiemannCvs.FiniteAdjacentAdiShiftBindings.K{mode}.same_factorization",
        f"RiemannCvs.FiniteAdjacentAdiShiftBindings.K{mode}.reflected_factorization",
        (
            "RiemannCvs.V23BoundaryWeylMainline."
            f"v23_k{mode}_twoLoewnerCompression_posterior"
        ),
        (
            "RiemannCvs.V23BoundaryWeylMainline."
            f"relativeCoupling_of_k{mode}_rank152Compression"
        ),
    ]


def certify_scalable(
    *,
    c: int,
    mode: int,
    same_factors: int,
    reflected_factors: int,
    same_cap: Fraction,
    reflected_cap: Fraction,
    total_cap: Fraction,
    delta: Fraction,
    eta: Fraction,
    precision: int,
    threads: int,
    archimedean_certificate: Path,
    json_out: Path,
    reference_json: Path | None,
    diagnostics_only: bool,
) -> dict[str, Any]:
    if c != 13:
        raise ValueError("the current scalable Fourier ledger is specialized to c=13")
    if mode < 960:
        raise ValueError("the Archimedean centered envelope requires mode >= 960")
    if same_factors < 1 or reflected_factors < 1:
        raise ValueError("factor counts must be positive")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if threads != 1:
        raise ValueError(
            "Arb callback quadrature must run with exactly one FLINT thread"
        )
    ctx.prec = precision
    ctx.threads = 1
    started = time.time()
    archimedean_audit = validate_archimedean_certificate(
        archimedean_certificate, c=c, mode=mode, precision=precision
    )

    (
        same_roots,
        same_poles,
        reflected_roots,
        reflected_poles,
        geometry,
    ) = build_family_data(mode, same_factors, reflected_factors)

    left_same_basis, left_same_transform = partial_fraction_transform(
        same_roots, same_poles, side="left"
    )
    left_reflected_basis, left_reflected_transform = partial_fraction_transform(
        reflected_roots, reflected_poles, side="left"
    )
    right_same_basis, right_same_transform = partial_fraction_transform(
        same_roots, same_poles, side="right"
    )
    right_reflected_basis, right_reflected_transform = partial_fraction_transform(
        reflected_roots,
        reflected_poles,
        side="right",
        argument_sign=-1,
    )

    sample_audits = [
        verify_transform_samples(
            label="same_sign_left",
            roots=same_roots,
            poles=same_poles,
            side="left",
            argument_sign=1,
            basis=left_same_basis,
            transform=left_same_transform,
            samples=(Fraction(mode + 1, mode), Fraction(3, 2), Fraction(2)),
        ),
        verify_transform_samples(
            label="reflected_left",
            roots=reflected_roots,
            poles=reflected_poles,
            side="left",
            argument_sign=1,
            basis=left_reflected_basis,
            transform=left_reflected_transform,
            samples=(Fraction(mode + 1, mode), Fraction(3, 2), Fraction(2)),
        ),
        verify_transform_samples(
            label="same_sign_right",
            roots=same_roots,
            poles=same_poles,
            side="right",
            argument_sign=1,
            basis=right_same_basis,
            transform=right_same_transform,
            samples=(Fraction(2 * mode + 1, mode), Fraction(3), Fraction(4)),
        ),
        verify_transform_samples(
            label="reflected_right",
            roots=reflected_roots,
            poles=reflected_poles,
            side="right",
            argument_sign=-1,
            basis=right_reflected_basis,
            transform=right_reflected_transform,
            samples=(Fraction(2 * mode + 1, mode), Fraction(3), Fraction(4)),
        ),
    ]
    progress("partial-fraction sample identities contain zero")

    left_h0, left_h1, left_h2, left_stats = build_moments(
        mode=mode,
        lo=mode + 1,
        hi=2 * mode,
        families=[
            (left_same_basis, left_same_transform),
            (left_reflected_basis, left_reflected_transform),
        ],
        c=c,
        precision=precision,
    )
    progress(
        f"source moments complete in {left_stats['seconds']}s; "
        f"basis={left_stats['basis_dimension']}"
    )
    right_h0, right_h1, right_h2, right_stats = build_moments(
        mode=mode,
        lo=2 * mode + 1,
        hi=4 * mode,
        families=[
            (right_same_basis, right_same_transform),
            (right_reflected_basis, right_reflected_transform),
        ],
        c=c,
        precision=precision,
    )
    progress(
        f"target moments complete in {right_stats['seconds']}s; "
        f"basis={right_stats['basis_dimension']}"
    )

    same_left_h0 = principal(left_h0, 0, same_factors)
    same_left_center = assemble_left(
        same_left_h0,
        principal(left_h1, 0, same_factors),
        principal(left_h2, 0, same_factors),
    )
    same_left = gram_upper_majorant(
        center=same_left_center,
        h0=same_left_h0,
        minimum_mode=mode + 1,
        eta=eta,
        error_slot="first",
    )
    reflected_left_h0 = principal(left_h0, same_factors, reflected_factors)
    reflected_left_center = assemble_left(
        reflected_left_h0,
        principal(left_h1, same_factors, reflected_factors),
        principal(left_h2, same_factors, reflected_factors),
    )
    reflected_left = gram_upper_majorant(
        center=reflected_left_center,
        h0=reflected_left_h0,
        minimum_mode=mode + 1,
        eta=eta,
        error_slot="first",
    )
    combined_left_center = assemble_left(left_h0, left_h1, left_h2)
    combined_left = gram_upper_majorant(
        center=combined_left_center,
        h0=left_h0,
        minimum_mode=mode + 1,
        eta=eta,
        error_slot="first",
    )

    same_right_h0 = principal(right_h0, 0, same_factors)
    same_right_center = assemble_right(
        same_right_h0,
        principal(right_h1, 0, same_factors),
        principal(right_h2, 0, same_factors),
        [1] * same_factors,
    )
    same_right = gram_upper_majorant(
        center=same_right_center,
        h0=same_right_h0,
        minimum_mode=2 * mode + 1,
        eta=eta,
        error_slot="second",
        signs=[1] * same_factors,
    )
    reflected_right_h0 = principal(
        right_h0, same_factors, reflected_factors
    )
    reflected_right_center = assemble_right(
        reflected_right_h0,
        principal(right_h1, same_factors, reflected_factors),
        principal(right_h2, same_factors, reflected_factors),
        [-1] * reflected_factors,
    )
    reflected_right = gram_upper_majorant(
        center=reflected_right_center,
        h0=reflected_right_h0,
        minimum_mode=2 * mode + 1,
        eta=eta,
        error_slot="second",
        signs=[-1] * reflected_factors,
    )
    symbol_signs = [1] * same_factors + [-1] * reflected_factors
    even_right_center = assemble_right(
        right_h0, right_h1, right_h2, symbol_signs
    )
    even_right = gram_upper_majorant(
        center=even_right_center,
        h0=right_h0,
        minimum_mode=2 * mode + 1,
        eta=eta,
        error_slot="second",
        signs=symbol_signs,
    )
    column_signs = [-1] * same_factors + [1] * reflected_factors
    odd_right_center = assemble_right(
        right_h0,
        right_h1,
        right_h2,
        symbol_signs,
        column_signs,
    )
    odd_error_signs = [
        symbol * column
        for symbol, column in zip(symbol_signs, column_signs, strict=True)
    ]
    odd_right = gram_upper_majorant(
        center=odd_right_center,
        h0=right_h0,
        minimum_mode=2 * mode + 1,
        eta=eta,
        error_slot="second",
        signs=odd_error_signs,
    )

    gram_pairs = (
        ("same_sign", same_left, same_right, same_cap),
        ("reflected", reflected_left, reflected_right, reflected_cap),
        ("even_total", combined_left, even_right, total_cap),
        ("odd_total", combined_left, odd_right, total_cap),
    )
    radius_report = {
        "same_left": gram_radius_stats(same_left),
        "same_right": gram_radius_stats(same_right),
        "reflected_left": gram_radius_stats(reflected_left),
        "reflected_right": gram_radius_stats(reflected_right),
        "combined_left": gram_radius_stats(combined_left),
        "even_right": gram_radius_stats(even_right),
        "odd_right": gram_radius_stats(odd_right),
    }
    progress(f"PSD-majorant radius report: {radius_report}")
    diagnostics = [
        diagnose_gram_pair(
            label=label, gram_left=left, gram_right=right, delta=delta
        )
        for label, left, right, _cap in gram_pairs
    ]

    certificates: list[dict[str, Any]] = []
    if not diagnostics_only:
        stem = json_out.with_suffix("")
        reference_certificates: dict[str, dict[str, Any]] = {}
        if reference_json is not None:
            reference_payload = json.loads(
                reference_json.read_text(encoding="utf-8")
            )
            reference_certificates = {
                item["label"]: item
                for item in reference_payload.get("certificates", [])
            }
        for label, left, right, cap in gram_pairs:
            progress(f"certifying {label} with cap {cap}")
            certificates.append(
                certify_gram_pair(
                    label=label,
                    gram_left=left,
                    gram_right=right,
                    cap=cap,
                    delta=delta,
                    stem=stem,
                    reference_json=reference_json,
                    reference_certificate=reference_certificates.get(label),
                )
            )
            gc.collect()

    script_path = Path(__file__).resolve()
    dependency_paths = [
        NUMERIC / "certify_adjacent_compressed_gram.py",
        NUMERIC / "certify_parity_gap.py",
        NUMERIC / "certify_preconditioned_relative_shell.py",
        NUMERIC / "certify_archimedean_tail_envelope.py",
    ]
    combined_rank = 2 * (same_factors + reflected_factors)
    payload: dict[str, Any] = {
        "status": "DIAGNOSTIC_PASS" if diagnostics_only else "PASS",
        "rigorous_interval_gram_certificate": not diagnostics_only,
        "rigorous_psd_gram_majorants": True,
        "operator_norm_certificates_completed": not diagnostics_only,
        "scope": (
            f"scalable rank-{combined_rank} compressed Loewner factors "
            f"at the K={mode} adjacent bridge"
        ),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": git_sha(),
        "script_sha256": script_hash(script_path),
        "dependency_sha256": {
            path.name: script_hash(path) for path in dependency_paths
        },
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "precision_bits": precision,
        "flint_threads": 1,
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
        "young_eta": str(eta),
        "archimedean_certificate_audit": archimedean_audit,
        "shift_geometry": geometry,
        "partial_fraction_sample_audits": sample_audits,
        "source_moments": left_stats,
        "target_moments": right_stats,
        "gram_majorant_radii": radius_report,
        "midpoint_diagnostics": diagnostics,
        "certificates": certificates,
        "gram_semantics": (
            "each stored small matrix bounds the exact Gram in PSD order; "
            "it is not claimed to enclose the exact Gram entrywise"
        ),
        "young_majorant": {
            "formula": (
                "sum (a_n+b_n)(a_n+b_n)^T <= "
                "(1+eta) sum a_n a_n^T + "
                "(1+1/eta) sum b_n b_n^T"
            ),
            "normalized_archimedean_error": "abs(delta_n)<=1/(12*n)",
            "source_error_square_upper": str(
                Fraction(1, 144 * (mode + 1) * (mode + 1))
            ),
            "target_error_square_upper": str(
                Fraction(1, 144 * (2 * mode + 1) * (2 * mode + 1))
            ),
            "eta": str(eta),
            "proof_role": (
                "algebraic PSD domination retaining the common row correlation"
            ),
        },
        "proof_formula": (
            "partial fractions reduce finite factor Grams to constant "
            "digamma/trigamma sums and oscillatory finite Lerch sums; "
            "Laplace quadrature plus explicit tails encloses those moments; "
            "Young gives PSD Gram majorants; exact-dyadic Loewner certificates "
            "then prove the four compressed operator caps"
        ),
        "lean_targets": lean_targets(mode),
        "proof_boundary": (
            "this is one finite adjacent bridge; uniform coefficient summation, "
            "source-specific form convergence, the infinite closed boundary/Weyl "
            "operator passage, limiting no-crossing, and RH are not proved here"
        ),
        "timings_seconds": {"total": round(time.time() - started, 3)},
    }
    if reference_json is not None:
        if diagnostics_only:
            raise ValueError("reference replay requires full certificates")
        payload["reference_precision_audit"] = reference_audit(
            reference_json, payload
        )
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--mode", type=int, default=15360)
    parser.add_argument("--same-factors", type=int, default=64)
    parser.add_argument("--reflected-factors", type=int, default=12)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--same-cap", default="5/4")
    parser.add_argument("--reflected-cap", default="1/4")
    parser.add_argument("--total-cap", default="5/4")
    parser.add_argument("--gram-majorant-delta", default="1/100000000")
    parser.add_argument("--young-eta", default="1/100000")
    parser.add_argument("--archimedean-certificate", type=Path, required=True)
    parser.add_argument("--reference-json", type=Path)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument("--diagnostics-only", action="store_true")
    args = parser.parse_args()
    payload = certify_scalable(
        c=args.c,
        mode=args.mode,
        same_factors=args.same_factors,
        reflected_factors=args.reflected_factors,
        same_cap=positive_fraction(args.same_cap, "same-cap"),
        reflected_cap=positive_fraction(args.reflected_cap, "reflected-cap"),
        total_cap=positive_fraction(args.total_cap, "total-cap"),
        delta=positive_fraction(args.gram_majorant_delta, "gram-majorant-delta"),
        eta=positive_fraction(args.young_eta, "young-eta"),
        precision=args.prec,
        threads=args.threads,
        archimedean_certificate=args.archimedean_certificate,
        json_out=args.json_out,
        reference_json=args.reference_json,
        diagnostics_only=args.diagnostics_only,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"Adjacent scalable Gram {payload['status']}: "
        f"K={payload['mode']} rank={payload['combined_rank_upper']} "
        f"precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
