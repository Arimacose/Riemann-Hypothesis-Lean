#!/usr/bin/env python3
"""Direct positive-supersolution certificate for the c=13 prime translation.

In multiplicative coordinates ``t = exp(x)`` on ``[1,13]``, the positive
self-adjoint prime translation acts pointwise by

    (T h)(t) = sum_q log(p)/sqrt(q) *
        (1_[t*q <= 13] h(t*q) + 1_[q <= t] h(t/q)).

This script uses a symmetric four-boundary-layer step function.  All layer
endpoints and heights are rational.  The eight transcendental weights are
first enclosed by simple rational upper bounds, and the resulting row ratio
is checked by exact ``Fraction`` arithmetic on every atomic open interval and
every breakpoint.  Arb independently checks the true weights and row sums.

The certificate proves the pointwise input ``T h < (10/3) h`` with ``h > 0``.
Turning that input into the L2 operator bound uses the weighted symmetric
Schur theorem; that functional-analytic bridge is formalized separately.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import platform
import subprocess
from bisect import bisect_right
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

import flint
from flint import arb, ctx

CUTOFF = Fraction(13)
TARGET = Fraction(10, 3)
THRESHOLDS = [Fraction(6, 5), Fraction(3, 2), Fraction(5, 3), Fraction(15, 8)]
HEIGHTS = [Fraction(1), Fraction(5, 6), Fraction(10, 13), Fraction(5, 7), Fraction(9, 13)]
# (q, p, exact rational upper bound for log(p)/sqrt(q))
EVENTS = [
    (2, 2, Fraction(491, 1000)),
    (4, 2, Fraction(347, 1000)),
    (8, 2, Fraction(246, 1000)),
    (3, 3, Fraction(635, 1000)),
    (9, 3, Fraction(367, 1000)),
    (5, 5, Fraction(720, 1000)),
    (7, 7, Fraction(736, 1000)),
    (11, 11, Fraction(724, 1000)),
]


def _frac_text(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def _frac_arb(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


def _arb_record(x: arb, digits: int = 50) -> dict[str, str]:
    return {
        "midpoint": x.mid().str(digits, radius=False),
        "radius": x.rad().str(16, radius=False),
    }


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _git_sha() -> str | None:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            text=True,
            encoding="utf-8",
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def height(t: Fraction) -> Fraction:
    """Symmetric rational layer height, with a deterministic breakpoint convention."""
    if not Fraction(1) <= t <= CUTOFF:
        raise ValueError("height argument is outside [1,13]")
    symmetric_radius = min(t, CUTOFF / t)
    return HEIGHTS[bisect_right(THRESHOLDS, symmetric_radius)]


def breakpoints() -> list[Fraction]:
    """All rational points at which a row signature can change."""
    cuts = {Fraction(1), CUTOFF}
    for a in THRESHOLDS:
        cuts.update((a, CUTOFF / a))
    for q_int, _p, _upper in EVENTS:
        q = Fraction(q_int)
        cuts.update((q, CUTOFF / q))
        for a in THRESHOLDS:
            # h(t*q), h(t/q), and their reflected-layer boundaries.
            cuts.update((a / q, CUTOFF / (a * q), a * q, CUTOFF * q / a))
    return sorted(x for x in cuts if Fraction(1) <= x <= CUTOFF)


def row_signature(t: Fraction, *, closed_support: bool) -> tuple[Any, ...]:
    signature: list[Any] = [height(t)]
    for q_int, _p, _upper in EVENTS:
        q = Fraction(q_int)
        plus = t * q <= CUTOFF if closed_support else t * q < CUTOFF
        minus = q <= t if closed_support else q < t
        signature.append(height(t * q) if plus else None)
        signature.append(height(t / q) if minus else None)
    return tuple(signature)


def rational_row(t: Fraction, *, closed_support: bool) -> Fraction:
    total = Fraction(0)
    for q_int, _p, upper in EVENTS:
        q = Fraction(q_int)
        plus = t * q <= CUTOFF if closed_support else t * q < CUTOFF
        minus = q <= t if closed_support else q < t
        if plus:
            total += upper * height(t * q)
        if minus:
            total += upper * height(t / q)
    return total


def actual_row(
    t: Fraction,
    weights: list[arb],
    *,
    closed_support: bool,
) -> arb:
    total = arb(0)
    for (q_int, _p, _upper), weight in zip(EVENTS, weights):
        q = Fraction(q_int)
        plus = t * q <= CUTOFF if closed_support else t * q < CUTOFF
        minus = q <= t if closed_support else q < t
        if plus:
            total += weight * _frac_arb(height(t * q))
        if minus:
            total += weight * _frac_arb(height(t / q))
    return total


def _row_record(
    kind: str,
    left: Fraction,
    right: Fraction,
    sample: Fraction,
    *,
    closed_support: bool,
    weights: list[arb],
) -> dict[str, Any]:
    h = height(sample)
    rational_ratio = rational_row(sample, closed_support=closed_support) / h
    actual_ratio = actual_row(sample, weights, closed_support=closed_support) / _frac_arb(h)
    return {
        "kind": kind,
        "left": _frac_text(left),
        "right": _frac_text(right),
        "sample": _frac_text(sample),
        "height": _frac_text(h),
        "rational_upper_ratio": _frac_text(rational_ratio),
        "actual_ratio": _arb_record(actual_ratio),
        "rational_ratio_below_target": rational_ratio < TARGET,
        "actual_ratio_below_target": bool(actual_ratio < _frac_arb(TARGET)),
    }


def certify(*, precision: int) -> dict[str, Any]:
    ctx.prec = precision
    weights = [arb(p).log() / arb(q).sqrt() for q, p, _upper in EVENTS]
    weight_records = []
    for (q, p, upper), weight in zip(EVENTS, weights):
        upper_arb = _frac_arb(upper)
        if not weight < upper_arb:
            raise RuntimeError(f"weight upper bound failed for q={q}")
        weight_records.append(
            {
                "q": q,
                "p": p,
                "actual_weight": _arb_record(weight),
                "rational_upper": _frac_text(upper),
                "strictly_below_upper": True,
            }
        )

    cuts = breakpoints()
    open_records: list[dict[str, Any]] = []
    endpoint_records: list[dict[str, Any]] = []

    for left, right in zip(cuts, cuts[1:]):
        if not left < right:
            raise AssertionError("breakpoint order is not strict")
        sample = (left + right) / 2
        sample_left = (2 * left + right) / 3
        sample_right = (left + 2 * right) / 3
        signature = row_signature(sample, closed_support=False)
        if row_signature(sample_left, closed_support=False) != signature:
            raise AssertionError("row signature changed inside an atomic interval")
        if row_signature(sample_right, closed_support=False) != signature:
            raise AssertionError("row signature changed inside an atomic interval")
        open_records.append(
            _row_record(
                "open_interval",
                left,
                right,
                sample,
                closed_support=False,
                weights=weights,
            )
        )

    for point in cuts:
        endpoint_records.append(
            _row_record(
                "closed_endpoint",
                point,
                point,
                point,
                closed_support=True,
                weights=weights,
            )
        )

    records = open_records + endpoint_records
    if not records:
        raise RuntimeError("no atomic rows were generated")
    if not all(row["rational_ratio_below_target"] for row in records):
        raise RuntimeError("an exact rational row missed the target")
    if not all(row["actual_ratio_below_target"] for row in records):
        raise RuntimeError("an Arb row missed the target")

    def ratio_fraction(row: dict[str, Any]) -> Fraction:
        return Fraction(row["rational_upper_ratio"])

    rational_max = max(records, key=ratio_fraction)
    rational_max_value = ratio_fraction(rational_max)
    actual_midpoint_max = max(
        records,
        key=lambda row: float(arb(row["actual_ratio"]["midpoint"])),
    )
    exact_slack = TARGET - rational_max_value
    if rational_max_value != Fraction(33223, 10000):
        raise AssertionError("the expected exact maximum changed")
    if exact_slack != Fraction(331, 30000):
        raise AssertionError("the expected exact slack changed")

    transcript = hashlib.sha256()
    for row in records:
        transcript.update(
            (
                f"{row['kind']} {row['left']} {row['right']} {row['sample']} "
                f"{row['height']} {row['rational_upper_ratio']}\n"
            ).encode("ascii")
        )

    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "exact rational atomic geometry and row arithmetic, plus Arb "
            "verification of the true c=13 prime weights"
        ),
        "cutoff": 13,
        "target_operator_norm": _frac_text(TARGET),
        "precision_bits": precision,
        "thresholds": [_frac_text(x) for x in THRESHOLDS],
        "heights": [_frac_text(x) for x in HEIGHTS],
        "minimum_height": _frac_text(min(HEIGHTS)),
        "symmetric_height_identity": "h(t)=h(13/t)",
        "prime_events": weight_records,
        "unique_rational_breakpoints": len(cuts),
        "open_intervals_checked": len(open_records),
        "closed_endpoints_checked": len(endpoint_records),
        "all_row_signatures_constant_on_atomic_intervals": True,
        "all_rational_upper_rows_strictly_below_target": True,
        "all_actual_arb_rows_strictly_below_target": True,
        "largest_rational_upper_ratio": {
            "value": _frac_text(rational_max_value),
            "exact_slack_to_target": _frac_text(exact_slack),
            "location": rational_max,
        },
        "largest_actual_midpoint_ratio": actual_midpoint_max,
        "row_transcript_sha256": transcript.hexdigest().upper(),
        "rows": records,
        "operator_consequence_interface": (
            "weighted symmetric Schur: positive h and T h <= B h imply ||T|| <= B"
        ),
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "platform": platform.platform(),
        "git_sha": _git_sha(),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "script_sha256": _sha256(Path(__file__).resolve()),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    result = certify(precision=args.prec)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": result["status"],
                "unique_rational_breakpoints": result["unique_rational_breakpoints"],
                "open_intervals_checked": result["open_intervals_checked"],
                "closed_endpoints_checked": result["closed_endpoints_checked"],
                "largest_rational_upper_ratio": result["largest_rational_upper_ratio"],
                "largest_actual_midpoint_ratio": result["largest_actual_midpoint_ratio"],
                "artifact": str(args.json_out.resolve()),
                "sha256": _sha256(args.json_out.resolve()),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
