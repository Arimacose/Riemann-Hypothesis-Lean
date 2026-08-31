#!/usr/bin/env python3
"""Midpoint probe for a multiscale previous-core CvS channel.

For a transition with a separate middle shell, this script decomposes the
previous core into its already constructed historical shells and measures each
coupling to the new shell against the corresponding block-diagonal energies.
If

    C_previous = sum_i C_i,
    C_i^2 <= q_i E_i T,

then ``relativeCoupling_of_finsetChannelBudgets`` combines the channels with
coefficient ``sum_i q_i``.  The additional candidate

    q_i <= q0 * 2^(-i)

is the source input consumed by ``relativeCoupling_of_dyadicChannelBudgets``.

All matrices in this script are formed from Arb midpoint evaluations and then
processed with float64 linear algebra.  The output is therefore a route-selection
diagnostic, not an interval certificate.  In particular, a failed geometric
envelope remains visible as a finite exception rather than being rounded into
a claimed proof.  When ``--previous-probe`` is supplied, consecutive scales are
also compared band by band against the transport target
``q_(n+1,d+1) < q_(n,d)/2``.  ``--require-half-transport`` makes that diagnostic
a regression gate while preserving the explicit non-rigorous status marker.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import platform
import subprocess
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np

from probe_dyadic_shell_scaling import (
    _direct_midpoint_parity_blocks,
    _parity_dimension,
    _whitened_largest_singular_squared,
)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


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


def _segments(cutoffs: list[int]) -> list[tuple[int, int]]:
    segments = [(0, cutoffs[0])]
    segments.extend(
        (previous + 1, current)
        for previous, current in zip(cutoffs, cutoffs[1:])
    )
    return segments


def _load_probe(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"failed to load previous probe {path}: {exc}") from exc
    if payload.get("status") != "MIDPOINT_DIAGNOSTIC_ONLY":
        raise ValueError("previous probe is not a midpoint diagnostic")
    if payload.get("rigorous_certificate") is not False:
        raise ValueError("previous probe has an inconsistent rigor marker")
    return payload


def _scale_transport_diagnostic(
    *,
    current: dict[str, Any],
    previous_path: Path,
    exception_budget: Fraction | None,
    expected_exception_sector: str | None,
    expected_exception_modes: tuple[int, int] | None,
) -> dict[str, Any]:
    """Compare repeated historical bands across two consecutive scales."""
    previous = _load_probe(previous_path)
    if previous.get("c") != current.get("c"):
        raise ValueError("previous/current probes use different c values")
    for key in ("reference_q", "shift_gain"):
        if previous.get(key) != current.get(key):
            raise ValueError(f"previous/current probes use different {key}")
    if previous.get("candidate", {}).get("leading_squared_coefficient") != (
        current.get("candidate", {}).get("leading_squared_coefficient")
    ):
        raise ValueError("previous/current probes use different leading budgets")

    previous_transition = previous.get("transition", {})
    current_transition = current.get("transition", {})
    if previous_transition.get("new_cutoff") != current_transition.get(
        "middle_cutoff"
    ):
        raise ValueError("probes are not consecutive at the new/middle cutoff")
    expected_cutoffs = list(previous.get("historical_cutoffs", [])) + [
        int(previous_transition.get("middle_cutoff"))
    ]
    if expected_cutoffs != current.get("historical_cutoffs"):
        raise ValueError("current historical cutoffs do not extend the previous list")

    previous_sectors = {
        sector["sector"]: sector for sector in previous.get("sectors", [])
    }
    sector_records: list[dict[str, Any]] = []
    all_newest_below_leading = True
    all_repeated_strictly_below_half = True
    repeated_channel_count = 0
    for current_sector in current.get("sectors", []):
        name = current_sector["sector"]
        if name not in previous_sectors:
            raise ValueError(f"previous probe lacks sector {name}")
        previous_channels = {
            tuple(channel["modes"]): channel
            for channel in previous_sectors[name].get("channels", [])
        }
        current_channels = current_sector.get("channels", [])
        newest = [channel for channel in current_channels if channel["distance"] == 0]
        if len(newest) != 1:
            raise ValueError(f"{name} sector does not have exactly one newest channel")
        newest_pass = bool(newest[0]["below_candidate_envelope"])
        all_newest_below_leading = all_newest_below_leading and newest_pass

        repeated: list[dict[str, Any]] = []
        for channel in current_channels:
            modes = tuple(channel["modes"])
            if modes not in previous_channels:
                continue
            old = previous_channels[modes]
            if channel["distance"] != old["distance"] + 1:
                raise ValueError(
                    f"{name} channel {modes} did not move outward by one distance"
                )
            current_kappa = float(channel["kappa_midpoint"])
            previous_kappa = float(old["kappa_midpoint"])
            if previous_kappa <= 0:
                raise ValueError("previous channel coefficient is not positive")
            strict_half = current_kappa < 0.5 * previous_kappa
            all_repeated_strictly_below_half = (
                all_repeated_strictly_below_half and strict_half
            )
            repeated_channel_count += 1
            repeated.append(
                {
                    "modes": list(modes),
                    "previous_distance": old["distance"],
                    "current_distance": channel["distance"],
                    "previous_kappa_midpoint": previous_kappa,
                    "current_kappa_midpoint": current_kappa,
                    "doubling_ratio_midpoint": current_kappa / previous_kappa,
                    "strictly_below_one_half": strict_half,
                }
            )
        if len(repeated) != len(previous_channels):
            raise ValueError(f"{name} sector lost a historical channel")
        sector_records.append(
            {
                "sector": name,
                "newest_channel": {
                    "modes": newest[0]["modes"],
                    "kappa_midpoint": newest[0]["kappa_midpoint"],
                    "leading_budget": newest[0]["candidate_envelope"],
                    "strictly_below_leading": newest_pass,
                },
                "repeated_channels": repeated,
            }
        )

    exception_records: list[dict[str, Any]] = []
    all_exceptions_below_budget = True
    if exception_budget is not None:
        budget_float = float(exception_budget)
        sectors = {
            sector["sector"]: sector for sector in current.get("sectors", [])
        }
        for exception in current.get("route_decision", {}).get(
            "finite_exceptions", []
        ):
            sector = sectors[exception["sector"]]
            channel = next(
                channel
                for channel in sector["channels"]
                if channel["distance"] == exception["distance"]
                and channel["modes"] == exception["modes"]
            )
            kappa = float(channel["kappa_midpoint"])
            passed = kappa < budget_float
            all_exceptions_below_budget = all_exceptions_below_budget and passed
            exception_records.append(
                {
                    "sector": exception["sector"],
                    "distance": exception["distance"],
                    "modes": exception["modes"],
                    "kappa_midpoint": kappa,
                    "exception_budget": str(exception_budget),
                    "strictly_below_exception_budget": passed,
                    "exception_slack_midpoint": budget_float - kappa,
                }
            )

    expected_exception_match = True
    if expected_exception_sector is not None and expected_exception_modes is not None:
        expected_exception_match = len(exception_records) == 1 and (
            exception_records[0]["sector"] == expected_exception_sector
            and tuple(exception_records[0]["modes"]) == expected_exception_modes
        )

    all_checks = (
        all_newest_below_leading
        and all_repeated_strictly_below_half
        and all_exceptions_below_budget
        and expected_exception_match
    )
    return {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "previous_probe": {
            "path": str(previous_path.resolve()),
            "sha256": _sha256(previous_path.resolve()),
            "git_sha": previous.get("git_sha"),
            "transition": previous_transition,
        },
        "current_transition": current_transition,
        "transport_target": "q_(scale+1,distance+1) < (1/2)*q_(scale,distance)",
        "newest_target": "q_(scale,0) < leading",
        "repeated_channel_count": repeated_channel_count,
        "all_newest_channels_strictly_below_leading": all_newest_below_leading,
        "all_repeated_channels_strictly_below_half": (
            all_repeated_strictly_below_half
        ),
        "exception_budget": (
            str(exception_budget) if exception_budget is not None else None
        ),
        "all_geometric_exceptions_strictly_below_exception_budget": (
            all_exceptions_below_budget
        ),
        "expected_exception": (
            {
                "sector": expected_exception_sector,
                "modes": list(expected_exception_modes),
                "exact_match": expected_exception_match,
            }
            if expected_exception_sector is not None
            and expected_exception_modes is not None
            else None
        ),
        "all_selected_diagnostics_pass": all_checks,
        "sectors": sector_records,
        "geometric_exceptions": exception_records,
        "interpretation": (
            "route-selection regression only; the CvS source kernel still "
            "requires an interval or analytic transport proof"
        ),
    }


def _row_bounds(sector: str, low_mode: int, high_mode: int) -> tuple[int, int]:
    start = (
        0
        if low_mode == 0
        else _parity_dimension(sector, low_mode - 1)
    )
    return start, _parity_dimension(sector, high_mode)


def probe(
    *,
    c: int,
    historical_cutoffs: list[int],
    middle_cutoff: int,
    new_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    candidate_leading: Fraction,
    previous_probe: Path | None = None,
    exception_budget: Fraction | None = None,
    expected_exception_sector: str | None = None,
    expected_exception_modes: tuple[int, int] | None = None,
    require_half_transport: bool = False,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not historical_cutoffs:
        raise ValueError("at least one historical cutoff is required")
    if historical_cutoffs[0] < 1:
        raise ValueError("the first historical cutoff must be positive")
    if any(
        left >= right
        for left, right in zip(historical_cutoffs, historical_cutoffs[1:])
    ):
        raise ValueError("historical cutoffs must be strictly increasing")
    if not historical_cutoffs[-1] < middle_cutoff < new_cutoff:
        raise ValueError(
            "require final historical cutoff < middle cutoff < new cutoff"
        )
    if not 0 < reference_q < 1:
        raise ValueError("reference_q must lie strictly between zero and one")
    if shift_gain < 0:
        raise ValueError("shift_gain must be nonnegative")
    if exception_budget is not None and not 0 < exception_budget < 1:
        raise ValueError("exception_budget must lie strictly between zero and one")
    if require_half_transport and previous_probe is None:
        raise ValueError("require_half_transport needs a previous_probe")
    if (expected_exception_sector is None) != (expected_exception_modes is None):
        raise ValueError("expected exception sector and modes must be supplied together")
    if expected_exception_sector is not None and exception_budget is None:
        raise ValueError("an expected exception needs an exception_budget")

    started = time.time()
    leading = float(candidate_leading)
    aggregate_target = 2.0 * leading
    even, odd, construction = _direct_midpoint_parity_blocks(
        c=c, cutoff=new_cutoff, precision=precision
    )
    historical_segments = _segments(historical_cutoffs)
    report: dict[str, Any] = {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "scope": (
            "float64 generalized coupling norms after Arb midpoint assembly "
            "for a dyadic decomposition of the previous-core channel"
        ),
        "c": c,
        "transition": {
            "previous_cutoff": historical_cutoffs[-1],
            "middle_cutoff": middle_cutoff,
            "new_cutoff": new_cutoff,
            "new_shell_modes": [middle_cutoff + 1, new_cutoff],
        },
        "historical_cutoffs": historical_cutoffs,
        "historical_segments": [list(segment) for segment in historical_segments],
        "distance_convention": (
            "distance zero is the most recent historical shell; distance "
            "increases toward the fixed base"
        ),
        "reference_energy_convention": (
            "the fixed base block is scaled by reference_q; later historical "
            "shells and the new shell use their shifted diagonal blocks"
        ),
        "reference_q": str(reference_q),
        "shift_gain": str(shift_gain),
        "precision_bits_for_arb_midpoints": precision,
        "candidate": {
            "leading_squared_coefficient": str(candidate_leading),
            "envelope": "q_i <= leading * (1/2)^distance",
            "aggregate_budget": str(2 * candidate_leading),
            "lean_sum_adapter": (
                "RiemannCvs.BoundaryWeylSchurTail."
                "dyadicChannelBudget_sum_le_two"
            ),
            "lean_coupling_adapter": (
                "RiemannCvs.BoundaryWeylSchurTail."
                "relativeCoupling_of_dyadicChannelBudgets"
            ),
        },
        "construction": construction,
        "sectors": [],
    }

    for sector, block in (("even", even), ("odd", odd)):
        sector_started = time.time()
        block.flat[:: block.shape[0] + 1] += float(shift_gain)
        new_start = _parity_dimension(sector, middle_cutoff)
        new_end = _parity_dimension(sector, new_cutoff)
        new_energy = block[new_start:new_end, new_start:new_end]
        new_cholesky_started = time.time()
        new_cholesky = np.linalg.cholesky(new_energy)
        new_cholesky_seconds = time.time() - new_cholesky_started

        previous_end = _parity_dimension(sector, historical_cutoffs[-1])
        coupling_pieces = [
            block[row_start:row_end, new_start:new_end]
            for low_mode, high_mode in historical_segments
            for row_start, row_end in [
                _row_bounds(sector, low_mode, high_mode)
            ]
        ]
        reconstructed = np.vstack(coupling_pieces)
        full_previous_coupling = block[:previous_end, new_start:new_end]
        reconstruction_error = float(
            np.max(np.abs(reconstructed - full_previous_coupling))
        )
        reconstruction_tolerance = (
            32.0
            * np.finfo(np.float64).eps
            * max(1.0, float(np.max(np.abs(full_previous_coupling))))
        )
        if reconstruction_error > reconstruction_tolerance:
            raise RuntimeError(
                f"{sector} historical-shell reconstruction error "
                f"{reconstruction_error} exceeds {reconstruction_tolerance}"
            )

        channels: list[dict[str, Any]] = []
        for distance, (low_mode, high_mode) in enumerate(
            reversed(historical_segments)
        ):
            effective_low_mode = (
                1 if sector == "odd" and low_mode == 0 else low_mode
            )
            row_start, row_end = _row_bounds(
                sector, low_mode, high_mode
            )
            energy = block[row_start:row_end, row_start:row_end].copy()
            if low_mode == 0:
                energy *= float(reference_q)
            cholesky_started = time.time()
            cholesky = np.linalg.cholesky(energy)
            cholesky_seconds = time.time() - cholesky_started
            coupling = block[row_start:row_end, new_start:new_end]
            kappa, linear_algebra = _whitened_largest_singular_squared(
                core_cholesky_blocks=[
                    (slice(0, row_end - row_start), cholesky)
                ],
                coupling=coupling,
                shell_cholesky=new_cholesky,
            )
            envelope = leading * (0.5**distance)
            channels.append(
                {
                    "distance": distance,
                    "modes": [effective_low_mode, high_mode],
                    "dimension": row_end - row_start,
                    "base_reference_scaled": low_mode == 0,
                    "kappa_midpoint": kappa,
                    "operator_norm_midpoint": math.sqrt(kappa),
                    "candidate_envelope": envelope,
                    "below_candidate_envelope": kappa < envelope,
                    "envelope_slack_midpoint": envelope - kappa,
                    "block_cholesky_seconds": round(cholesky_seconds, 3),
                    "linear_algebra": linear_algebra,
                }
            )

        sum_kappa = sum(channel["kappa_midpoint"] for channel in channels)
        exceptions = [
            {
                "distance": channel["distance"],
                "modes": channel["modes"],
                "excess_midpoint": -channel["envelope_slack_midpoint"],
            }
            for channel in channels
            if not channel["below_candidate_envelope"]
        ]
        report["sectors"].append(
            {
                "sector": sector,
                "new_shell_dimension": new_end - new_start,
                "new_shell_cholesky_seconds": round(
                    new_cholesky_seconds, 3
                ),
                "previous_core_dimension": previous_end,
                "partition_dimension": sum(
                    channel["dimension"] for channel in channels
                ),
                "coupling_reconstruction_error": reconstruction_error,
                "coupling_reconstruction_tolerance": reconstruction_tolerance,
                "channels": channels,
                "sum_kappa_midpoint": sum_kappa,
                "candidate_aggregate_budget": aggregate_target,
                "below_candidate_aggregate_budget": (
                    sum_kappa < aggregate_target
                ),
                "aggregate_slack_midpoint": aggregate_target - sum_kappa,
                "all_channels_below_geometric_envelope": not exceptions,
                "geometric_envelope_exceptions": exceptions,
                "seconds": round(time.time() - sector_started, 3),
            }
        )

    envelope_exceptions = [
        {"sector": sector["sector"], **exception}
        for sector in report["sectors"]
        for exception in sector["geometric_envelope_exceptions"]
    ]
    report["route_decision"] = {
        "all_sector_sums_below_aggregate_budget": all(
            sector["below_candidate_aggregate_budget"]
            for sector in report["sectors"]
        ),
        "pure_geometric_envelope_passes_at_this_cutoff": (
            not envelope_exceptions
        ),
        "finite_exceptions": envelope_exceptions,
        "recommended_formal_split": (
            "keep each listed finite exception as a separate channel and use "
            "the geometric envelope only on the remaining dyadic tail"
            if envelope_exceptions
            else "use the geometric envelope for every historical shell"
        ),
    }
    if previous_probe is not None:
        comparison = _scale_transport_diagnostic(
            current=report,
            previous_path=previous_probe,
            exception_budget=exception_budget,
            expected_exception_sector=expected_exception_sector,
            expected_exception_modes=expected_exception_modes,
        )
        report["scale_transport_diagnostic"] = comparison
        if require_half_transport and not comparison[
            "all_selected_diagnostics_pass"
        ]:
            raise RuntimeError("selected half-transport midpoint diagnostics failed")
    report["seconds"] = round(time.time() - started, 3)
    report["numpy_version"] = np.__version__
    report["python_flint_version"] = flint.__version__
    report["python_version"] = platform.python_version()
    report["platform"] = platform.platform()
    report["git_sha"] = _git_sha()
    report["created_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
    report["script_sha256"] = _sha256(Path(__file__).resolve())
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument(
        "--historical-cutoffs",
        nargs="+",
        type=int,
        default=[20, 120, 240, 480, 960],
    )
    parser.add_argument("--middle-cutoff", type=int, default=1920)
    parser.add_argument("--new-cutoff", type=int, default=3840)
    parser.add_argument("--prec", type=int, default=160)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--reference-q", default="249/250")
    parser.add_argument("--candidate-leading", default="1/30")
    parser.add_argument("--previous-probe", type=Path)
    parser.add_argument("--exception-budget")
    parser.add_argument("--expected-exception-sector", choices=("even", "odd"))
    parser.add_argument("--expected-exception-modes", nargs=2, type=int)
    parser.add_argument("--require-half-transport", action="store_true")
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    result = probe(
        c=args.c,
        historical_cutoffs=args.historical_cutoffs,
        middle_cutoff=args.middle_cutoff,
        new_cutoff=args.new_cutoff,
        precision=args.prec,
        shift_gain=Fraction(args.shift_gain),
        reference_q=Fraction(args.reference_q),
        candidate_leading=_positive_fraction(
            args.candidate_leading, "candidate_leading"
        ),
        previous_probe=(
            args.previous_probe.resolve() if args.previous_probe is not None else None
        ),
        exception_budget=(
            _positive_fraction(args.exception_budget, "exception_budget")
            if args.exception_budget is not None
            else None
        ),
        expected_exception_sector=args.expected_exception_sector,
        expected_exception_modes=(
            tuple(args.expected_exception_modes)
            if args.expected_exception_modes is not None
            else None
        ),
        require_half_transport=args.require_half_transport,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "route_decision": result["route_decision"],
                "scale_transport_diagnostic": result.get(
                    "scale_transport_diagnostic"
                ),
                "sector_summaries": [
                    {
                        "sector": sector["sector"],
                        "sum_kappa_midpoint": sector["sum_kappa_midpoint"],
                        "aggregate_slack_midpoint": sector[
                            "aggregate_slack_midpoint"
                        ],
                        "geometric_envelope_exceptions": sector[
                            "geometric_envelope_exceptions"
                        ],
                    }
                    for sector in result["sectors"]
                ],
                "artifact": str(args.json_out.resolve()),
                "artifact_sha256": _sha256(args.json_out.resolve()),
                "script_sha256": result["script_sha256"],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
