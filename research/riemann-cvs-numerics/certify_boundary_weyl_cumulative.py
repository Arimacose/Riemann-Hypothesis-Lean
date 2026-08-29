#!/usr/bin/env python3
"""Rigorous cumulative-residue certificate for the finite CvS Weyl ratio.

For the corrected cutoff-free CvS matrix, form its real even and odd parity
blocks ``E`` and ``O`` of dimensions ``N+1`` and ``N``.  This script certifies
the cumulative residues of the monic characteristic-polynomial ratio

    det(z I - O) / det(z I - E).

The midpoint eigensolver is used only to propose disjoint search brackets.
Every accepted eigenvalue enclosure is proved by interval LDL^T inertia:
the lower endpoint has exactly ``j`` eigenvalues below it and the upper
endpoint has exactly ``j+1``.  With certified boxes ``lambda_j`` for the even
eigenvalues and ``mu_k`` for the odd eigenvalues, interval arithmetic encloses

    r_j = prod_k (lambda_j - mu_k)
          / prod_{i != j} (lambda_j - lambda_i).

The certificate passes only when every prefix ``R_j = sum_{i <= j} r_i`` is
strictly positive.  This is the numerical hypothesis consumed by
``RiemannCvs.BoundaryWeylCumulative``.  The sign convention there is

    G(x) = sum_j r_j / (lambda_j - x)
         = -det(x I - O) / det(x I - E),  x < lambda_0.

This is a rigorous finite-matrix certificate.  Uniformity in ``N``, the
concrete rectangular displacement identity, and passage to the continuum are
separate proof obligations.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import time
from pathlib import Path
from typing import Any

import flint
import mpmath as mp
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    SOURCE_URL,
    InertiaResult,
    build_cutoff_free_matrix,
    certified_inertia,
    parity_blocks,
    reflection_symmetric_enclosure,
    shifted,
)


def _midpoint_matrix(A: arb_mat, digits: int) -> mp.matrix:
    """Convert Arb midpoints to a high-precision proposal matrix."""
    M = mp.matrix(A.nrows(), A.ncols())
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            M[i, j] = mp.mpf(A[i, j].mid().str(digits, radius=False))
    return M


def _point_ball(x: mp.mpf, digits: int) -> arb:
    """An Arb enclosure of the supplied high-precision decimal."""
    return arb(mp.nstr(x, digits, strip_zeros=False))


def _ball_record(x: arb, digits: int = 80) -> dict[str, str]:
    return {
        "ball": x.str(digits, radius=True),
        "midpoint": x.mid().str(digits, radius=False),
        "radius": x.rad().str(30, radius=False),
        "lower": x.lower().str(digits, radius=True),
        "upper": x.upper().str(digits, radius=True),
    }


def _inertia_record(result: InertiaResult) -> dict[str, Any]:
    transcript = "\n".join(result.pivots)
    return {
        "n_pos": result.n_pos,
        "n_neg": result.n_neg,
        "undetermined_pivot": result.undetermined_pivot,
        "certified": result.certified,
        "pivot_count": len(result.pivots),
        "pivot_transcript_sha256": hashlib.sha256(
            transcript.encode("utf-8")
        ).hexdigest(),
    }


def _inertia_at(
    A: arb_mat, threshold: mp.mpf, digits: int
) -> tuple[InertiaResult, arb]:
    threshold_ball = _point_ball(threshold, digits)
    return certified_inertia(shifted(A, threshold_ball)), threshold_ball


def _require_endpoint(
    label: str,
    result: InertiaResult,
    expected_negative: int,
) -> None:
    if not result.certified:
        raise RuntimeError(
            f"{label}: interval LDL stopped at pivot "
            f"{result.undetermined_pivot}"
        )
    if result.n_neg != expected_negative:
        raise RuntimeError(
            f"{label}: expected {expected_negative} negative pivots, "
            f"got {result.n_neg}"
        )


def _isolate_spectrum(
    name: str,
    A: arb_mat,
    approximations: list[mp.mpf],
    digits: int,
    iterations: int,
) -> tuple[list[arb], list[dict[str, Any]]]:
    """Isolate every ordered eigenvalue using certified endpoint inertias."""
    dimension = len(approximations)
    if A.nrows() != dimension or A.ncols() != dimension:
        raise ValueError(f"{name}: matrix/approximation dimension mismatch")
    if dimension == 0:
        return [], []

    boxes: list[arb] = []
    records: list[dict[str, Any]] = []
    for j, eigen_mid in enumerate(approximations):
        lower = (
            mp.mpf(0)
            if j == 0
            else (approximations[j - 1] + eigen_mid) / 2
        )
        if j + 1 < dimension:
            upper = (eigen_mid + approximations[j + 1]) / 2
        else:
            previous_gap = (
                eigen_mid - approximations[j - 1]
                if j > 0
                else abs(eigen_mid)
            )
            step = max(mp.mpf(1), abs(eigen_mid), previous_gap)
            upper = eigen_mid + step

        lower_result, lower_ball = _inertia_at(A, lower, digits)
        upper_result, upper_ball = _inertia_at(A, upper, digits)
        _require_endpoint(f"{name}[{j}] lower", lower_result, j)

        expansion_count = 0
        while (
            (not upper_result.certified or upper_result.n_neg != j + 1)
            and j + 1 == dimension
            and expansion_count < 12
        ):
            upper = eigen_mid + 2 * (upper - eigen_mid)
            upper_result, upper_ball = _inertia_at(A, upper, digits)
            expansion_count += 1
        _require_endpoint(f"{name}[{j}] upper", upper_result, j + 1)

        completed = 0
        for _ in range(iterations):
            midpoint = (lower + upper) / 2
            mid_result, mid_ball = _inertia_at(A, midpoint, digits)
            if not mid_result.certified:
                break
            if mid_result.n_neg == j:
                lower, lower_result, lower_ball = (
                    midpoint,
                    mid_result,
                    mid_ball,
                )
            elif mid_result.n_neg == j + 1:
                upper, upper_result, upper_ball = (
                    midpoint,
                    mid_result,
                    mid_ball,
                )
            else:
                raise RuntimeError(
                    f"{name}[{j}]: unexpected midpoint inertia "
                    f"{mid_result.n_neg}"
                )
            completed += 1

        _require_endpoint(f"{name}[{j}] final lower", lower_result, j)
        _require_endpoint(
            f"{name}[{j}] final upper", upper_result, j + 1
        )
        enclosure = lower_ball.union(upper_ball)
        boxes.append(enclosure)
        records.append(
            {
                "index": j,
                "enclosure": _ball_record(enclosure),
                "lower_threshold": _ball_record(lower_ball),
                "lower_inertia": _inertia_record(lower_result),
                "upper_threshold": _ball_record(upper_ball),
                "upper_inertia": _inertia_record(upper_result),
                "bisections_completed": completed,
                "upper_expansions": expansion_count,
            }
        )

    for j in range(dimension - 1):
        if boxes[j].overlaps(boxes[j + 1]):
            raise RuntimeError(
                f"{name}: certified boxes {j} and {j + 1} overlap"
            )
        if not boxes[j] < boxes[j + 1]:
            raise RuntimeError(
                f"{name}: certified boxes {j} and {j + 1} are unordered"
            )
    return boxes, records


def certify(
    *,
    c: int,
    N: int,
    prec: int,
    dps: int,
    iterations: int,
    margin_left: str,
    margin_right: str,
    margin_prefix_index: int,
) -> dict[str, Any]:
    if c < 2 or N < 1:
        raise ValueError("require c >= 2 and N >= 1")
    if prec < 256 or dps < 80 or iterations < 20:
        raise ValueError("require prec >= 256, dps >= 80, iterations >= 20")
    if margin_prefix_index < 0 or margin_prefix_index >= N:
        raise ValueError("require 0 <= margin_prefix_index < N")

    ctx.prec = prec
    mp.mp.dps = dps
    digits = min(dps - 10, int(prec * 0.30103) - 20)
    if digits < 60:
        raise ValueError("working precision leaves fewer than 60 decimal digits")

    started = time.time()
    raw = build_cutoff_free_matrix(c, N, prec)
    symmetric = reflection_symmetric_enclosure(raw, N)
    even, odd = parity_blocks(symmetric, N)
    build_seconds = time.time() - started

    even_values, _ = mp.eigsy(_midpoint_matrix(even, digits))
    odd_values, _ = mp.eigsy(_midpoint_matrix(odd, digits))
    even_midpoints = [mp.mpf(even_values[j]) for j in range(N + 1)]
    odd_midpoints = [mp.mpf(odd_values[j]) for j in range(N)]

    isolation_started = time.time()
    even_boxes, even_records = _isolate_spectrum(
        "even", even, even_midpoints, digits, iterations
    )
    odd_boxes, odd_records = _isolate_spectrum(
        "odd", odd, odd_midpoints, digits, iterations
    )
    isolation_seconds = time.time() - isolation_started

    if not even_boxes[0] < odd_boxes[0]:
        raise RuntimeError("lowest even box is not strictly below lowest odd box")
    if not odd_boxes[0] < even_boxes[1]:
        raise RuntimeError("lowest odd box is not strictly below second even box")

    residues: list[arb] = []
    for j, pole in enumerate(even_boxes):
        numerator = arb(1)
        denominator = arb(1)
        for zero in odd_boxes:
            numerator *= pole - zero
        for k, other_pole in enumerate(even_boxes):
            if k != j:
                denominator *= pole - other_pole
        if denominator.contains(0):
            raise RuntimeError(f"residue denominator {j} contains zero")
        residues.append(numerator / denominator)

    prefix = arb(0)
    prefixes: list[arb] = []
    residue_records: list[dict[str, Any]] = []
    for j, residue in enumerate(residues):
        prefix += residue
        prefixes.append(prefix)
        sign = (
            "positive"
            if residue > 0
            else "negative"
            if residue < 0
            else "indeterminate"
        )
        residue_records.append(
            {
                "index": j,
                "residue": _ball_record(residue),
                "residue_sign": sign,
                "cumulative": _ball_record(prefix),
                "cumulative_strictly_positive": bool(prefix > 0),
            }
        )

    failing_prefixes = [j for j, value in enumerate(prefixes) if not value > 0]
    if failing_prefixes:
        raise RuntimeError(
            f"cumulative residue intervals not positive: {failing_prefixes}"
        )
    if not prefixes[-1].contains(1):
        raise RuntimeError("total residue interval does not contain monic value 1")

    margin_left_ball = arb(margin_left)
    margin_right_ball = arb(margin_right)
    if not margin_left_ball.is_exact() or not margin_right_ball.is_exact():
        raise ValueError("compact margin endpoints must be exact point balls")
    if not margin_left_ball <= margin_right_ball:
        raise RuntimeError("compact margin interval endpoints are unordered")
    if not margin_right_ball < even_boxes[0]:
        raise RuntimeError(
            "compact margin interval is not strictly before the first pole"
        )
    k = margin_prefix_index
    left_weight_drop = (
        arb(1) / (even_boxes[k] - margin_left_ball)
        - arb(1) / (even_boxes[k + 1] - margin_left_ball)
    )
    if not left_weight_drop > 0:
        raise RuntimeError(
            f"prefix weight drop {k} is not certified positive"
        )
    compact_prefix_margin = prefixes[k] * left_weight_drop
    if not compact_prefix_margin > 0:
        raise RuntimeError(
            f"compact prefix margin {k} is not certified positive"
        )

    negative_indices = [j for j, r in enumerate(residues) if r < 0]
    indeterminate_indices = [
        j for j, r in enumerate(residues) if not (r > 0 or r < 0)
    ]
    return {
        "status": "PASS",
        "statement": (
            "all cumulative residues of det(zI-O)/det(zI-E) are strictly "
            "positive for the certified corrected finite CvS parity blocks"
        ),
        "weyl_sign_convention": (
            "G(x)=sum_j r_j/(lambda_j-x)="
            "-det(xI-O)/det(xI-E) for x below lambda_0"
        ),
        "c": c,
        "N": N,
        "full_dimension": 2 * N + 1,
        "even_dimension": N + 1,
        "odd_dimension": N,
        "prec_bits": prec,
        "midpoint_dps": dps,
        "threshold_decimal_digits": digits,
        "requested_bisections": iterations,
        "build_seconds": round(build_seconds, 3),
        "isolation_seconds": round(isolation_seconds, 3),
        "total_seconds": round(time.time() - started, 3),
        "strict_low_ordering": "lambda_even_0 < lambda_odd_0 < lambda_even_1",
        "even_eigenvalue_certificates": even_records,
        "odd_eigenvalue_certificates": odd_records,
        "residues": residue_records,
        "all_cumulative_strictly_positive": True,
        "negative_residue_indices": negative_indices,
        "indeterminate_residue_indices": indeterminate_indices,
        "total_residue_contains_one": True,
        "compact_prefix_margin_certificate": {
            "interval_left": _ball_record(margin_left_ball),
            "interval_right": _ball_record(margin_right_ball),
            "prefix_index": k,
            "cumulative_residue": _ball_record(prefixes[k]),
            "left_endpoint_reciprocal_weight_drop": _ball_record(
                left_weight_drop
            ),
            "weyl_lower_bound_on_interval": _ball_record(
                compact_prefix_margin
            ),
            "strictly_positive": True,
            "lean_theorems": [
                (
                    "RiemannCvs.BoundaryWeylCumulative."
                    "weightedSum_ge_prefixDrop"
                ),
                (
                    "RiemannCvs.BoundaryWeylCumulative."
                    "reciprocalPoleDrop_monoOnLeft"
                ),
                (
                    "RiemannCvs.BoundaryWeylCumulative."
                    "finiteBoundaryWeyl_ge_prefixDropAtLeft"
                ),
            ],
            "justification": (
                "finite Abel prefix-drop lower bound plus monotonic increase "
                "of reciprocal pole drop as x moves right before the first "
                "pole"
            ),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=20)
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--dps", type=int, default=180)
    parser.add_argument("--iterations", type=int, default=120)
    parser.add_argument("--margin-left", default="-100")
    parser.add_argument("--margin-right", default="0")
    parser.add_argument("--margin-prefix-index", type=int, default=11)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    certificate = certify(
        c=args.c,
        N=args.N,
        prec=args.prec,
        dps=args.dps,
        iterations=args.iterations,
        margin_left=args.margin_left,
        margin_right=args.margin_right,
        margin_prefix_index=args.margin_prefix_index,
    )
    certificate.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(
                timespec="seconds"
            ),
            "python_version": platform.python_version(),
            "python_flint_version": flint.__version__,
            "mpmath_version": mp.__version__,
            "platform": platform.platform(),
            "source_formula_attribution": SOURCE_URL,
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )

    output = Path(args.json_out)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8"
    )

    first_prefix = certificate["residues"][0]["cumulative"]
    print(
        json.dumps(
            {
                "status": certificate["status"],
                "c": certificate["c"],
                "N": certificate["N"],
                "statement": certificate["statement"],
                "first_cumulative_residue": first_prefix,
                "negative_residue_indices": certificate[
                    "negative_residue_indices"
                ],
                "compact_prefix_margin_certificate": certificate[
                    "compact_prefix_margin_certificate"
                ],
                "json_out": str(output),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
