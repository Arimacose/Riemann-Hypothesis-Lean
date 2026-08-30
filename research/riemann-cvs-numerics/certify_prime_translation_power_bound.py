#!/usr/bin/env python3
"""Rigorous path-power bound for the finite prime-translation operator.

For ``L = log(c)`` and every prime power ``q = p^a < c``, let

    (U_q f)(x) = 1_[0,L-log(q)](x) f(x + log(q)).

The prime part of the cutoff-free CvS operator is

    T_c = sum_q log(p)/sqrt(q) * (U_q + U_q^*).

It is a self-adjoint operator with a nonnegative distributional kernel.  A
length-``m`` path in ``T_c^m`` is a sequence of multiplicative steps ``q`` or
``1/q``.  Such a path is available from a starting point ``x`` precisely when
all partial products remain in ``[1,c]`` after a common rescaling by ``exp(x)``.
The admissible starting interval is therefore determined by exact rational
products; no floating comparison of logarithms is needed.

The script enumerates all admissible paths, sweeps their exact starting
intervals, and sums their positive weights as Arb balls.  If every row sum of
``T_c^m`` is strictly below ``B^m``, the symmetric Schur test and spectral
calculus give ``||T_c|| < B``.  For the V23 cutoff ``c=13``, power six certifies
the convenient rational bound ``B=10/3``.

This is a rigorous finite combinatorial/interval certificate for the stated
operator-norm reduction.  Its functional-analytic use still relies on the
path-kernel expansion and Schur-test theorem recorded in the research note and
Lean interface.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import platform
import subprocess
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
from flint import arb, ctx

from certify_parity_gap import prime_powers_up_to


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def _fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


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


def _arb_record(value: arb, digits: int = 50) -> dict[str, str]:
    return {
        "midpoint": value.mid().str(digits, radius=False),
        "radius": value.rad().str(16, radius=False),
    }


def _decode_counts(code: int, event_count: int, base: int) -> tuple[int, ...]:
    counts: list[int] = []
    for _ in range(event_count):
        counts.append(code % base)
        code //= base
    if code:
        raise AssertionError("monomial code exceeds the configured event count")
    return tuple(counts)


def certify(
    *,
    c: int,
    power: int,
    target: Fraction,
    precision: int,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if power <= 0:
        raise ValueError("power must be strictly positive")
    ctx.prec = precision

    # q=c has translation length L and hence zero L2 support.  It is removed
    # exactly rather than represented by a measure-zero endpoint path.
    all_prime_data = prime_powers_up_to(c)
    prime_data = [(q, p) for q, p in all_prime_data if q < c]
    event_count = len(prime_data)
    code_base = power + 1
    code_places = [code_base**index for index in range(event_count)]
    directed_steps: list[tuple[Fraction, int]] = []
    for index, (q, _p) in enumerate(prime_data):
        directed_steps.append((Fraction(q, 1), index))
        directed_steps.append((Fraction(1, q), index))

    # State = current partial product, minimum/maximum partial product, and a
    # base-(power+1) encoding of the event multiplicities in the path weight.
    paths: list[tuple[Fraction, Fraction, Fraction, int]] = [
        (Fraction(1), Fraction(1), Fraction(1), 0)
    ]
    path_counts_by_depth = [1]
    for _depth in range(power):
        next_paths: list[tuple[Fraction, Fraction, Fraction, int]] = []
        for ratio, minimum, maximum, code in paths:
            for factor, event_index in directed_steps:
                new_ratio = ratio * factor
                new_minimum = min(minimum, new_ratio)
                new_maximum = max(maximum, new_ratio)
                # log(max/min) < log(c) is exactly max < c*min.
                if new_maximum < c * new_minimum:
                    next_paths.append(
                        (
                            new_ratio,
                            new_minimum,
                            new_maximum,
                            code + code_places[event_index],
                        )
                    )
        paths = next_paths
        path_counts_by_depth.append(len(paths))

    # An admissible path is active for
    #   log(1/minimum) < x < log(c/maximum).
    # Log is increasing, so the sweep can sort the exact rational arguments.
    changes: dict[Fraction, Counter[int]] = defaultdict(Counter)
    for _ratio, minimum, maximum, code in paths:
        lower_argument = Fraction(1, 1) / minimum
        upper_argument = Fraction(c, 1) / maximum
        if not lower_argument < upper_argument:
            raise AssertionError("zero-width path survived strict pruning")
        changes[lower_argument][code] += 1
        changes[upper_argument][code] -= 1

    start_events = sum(
        multiplicity
        for endpoint_changes in changes.values()
        for multiplicity in endpoint_changes.values()
        if multiplicity > 0
    )
    end_events = -sum(
        multiplicity
        for endpoint_changes in changes.values()
        for multiplicity in endpoint_changes.values()
        if multiplicity < 0
    )
    if start_events != len(paths) or end_events != len(paths):
        raise AssertionError("path endpoint multiplicities do not balance")
    net_changes: Counter[int] = Counter()
    for endpoint_changes in changes.values():
        net_changes.update(endpoint_changes)
    nonzero_net_changes = {
        code: multiplicity
        for code, multiplicity in net_changes.items()
        if multiplicity != 0
    }
    if nonzero_net_changes:
        raise AssertionError("path endpoint sweep has nonzero net changes")

    weights = [arb(p).log() / arb(q).sqrt() for q, p in prime_data]
    monomial_cache: dict[int, arb] = {}

    def monomial(code: int) -> arb:
        cached = monomial_cache.get(code)
        if cached is not None:
            return cached
        value = arb(1)
        for weight, count in zip(
            weights, _decode_counts(code, event_count, code_base)
        ):
            if count:
                value *= weight**count
        monomial_cache[code] = value
        return value

    target_power = _fraction_arb(target) ** power
    active = arb(0)
    active_counts: Counter[int] = Counter()
    checked_intervals = 0
    largest_midpoint = float("-inf")
    largest_argument: Fraction | None = None
    largest_counts: Counter[int] | None = None
    transcript = hashlib.sha256()
    ordered_arguments = sorted(changes)

    for argument_index, argument in enumerate(ordered_arguments):
        for code, multiplicity in changes[argument].items():
            if multiplicity:
                active += multiplicity * monomial(code)
                active_counts[code] += multiplicity
                if active_counts[code] == 0:
                    del active_counts[code]
                elif active_counts[code] < 0:
                    raise AssertionError(
                        "path sweep produced a negative multiplicity"
                    )

        # The value after applying changes is the row sum on the next open
        # interval.  There is no interval after the final endpoint.
        if argument_index + 1 == len(ordered_arguments):
            continue
        next_argument = ordered_arguments[argument_index + 1]
        if not argument < next_argument:
            raise AssertionError("endpoint ordering is not strict")
        checked_intervals += 1
        if not active < target_power:
            raise RuntimeError(
                "power row-sum target failed after endpoint "
                f"{argument}: active={active}, target={target_power}"
            )
        midpoint = float(active.mid())
        if midpoint > largest_midpoint:
            largest_midpoint = midpoint
            largest_argument = argument
            largest_counts = active_counts.copy()
        transcript.update(
            (
                f"{argument.numerator}/{argument.denominator} "
                f"{active.mid().str(40, radius=False)} "
                f"{active.rad().str(12, radius=False)}\n"
            ).encode("ascii")
        )

    if active_counts:
        raise AssertionError("path sweep ended with active combinatorial paths")

    if largest_counts is None or largest_argument is None:
        raise RuntimeError("path sweep did not produce a nonempty interval")

    largest_value = arb(0)
    for code, multiplicity in largest_counts.items():
        largest_value += multiplicity * monomial(code)
    if not largest_value < target_power:
        raise RuntimeError("fresh largest-candidate recomputation missed the target")

    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "exact rational path geometry plus Arb positive-weight summation "
            "for a power-Schur bound on the finite prime-translation operator"
        ),
        "c": c,
        "power": power,
        "target_operator_norm": str(target),
        "target_power": str(target**power),
        "precision_bits": precision,
        "prime_events": [
            {"q": q, "p": p, "weight": _arb_record(weight)}
            for (q, p), weight in zip(prime_data, weights)
        ],
        "zero_support_events_removed": [
            {"q": q, "p": p} for q, p in all_prime_data if q == c
        ],
        "path_counts_by_depth": path_counts_by_depth,
        "admissible_power_paths": len(paths),
        "path_start_events": start_events,
        "path_end_events": end_events,
        "path_endpoint_net_changes_zero": True,
        "distinct_path_weight_monomials": len(monomial_cache),
        "unique_rational_endpoints": len(ordered_arguments),
        "open_intervals_checked": checked_intervals,
        "all_power_row_sums_strictly_below_target_power": True,
        "largest_midpoint_interval": {
            "left_endpoint_log_argument": (
                f"{largest_argument.numerator}/{largest_argument.denominator}"
            ),
            "row_sum": _arb_record(largest_value),
            "strictly_below_target_power": bool(largest_value < target_power),
        },
        "target_power_arb": _arb_record(target_power),
        "interval_transcript_sha256": transcript.hexdigest().upper(),
        "operator_consequence": (
            f"the symmetric Schur test gives ||T_{c}||^{power} < "
            f"({target})^{power}, hence ||T_{c}|| < {target}"
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
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--power", type=int, default=6)
    parser.add_argument("--target", default="10/3")
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    target = _positive_fraction(args.target, "target")
    result = certify(
        c=args.c,
        power=args.power,
        target=target,
        precision=args.prec,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "path_counts_by_depth": result["path_counts_by_depth"],
                "open_intervals_checked": result["open_intervals_checked"],
                "largest_midpoint_interval": result[
                    "largest_midpoint_interval"
                ],
                "operator_consequence": result["operator_consequence"],
                "artifact": str(args.json_out.resolve()),
                "sha256": _sha256(args.json_out.resolve()),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
