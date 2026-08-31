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

The optional ``--source-component-diagnostic`` splits every crossblock into its
prime, Archimedean, and rank-two pole matrices before whitening them against the
same full shifted energies.  It verifies that the three pieces reconstruct the
total crossblock and records both their individual generalized norms and the
triangle-inequality loss.  Comparing two probes then decides whether a future
analytic proof can allocate the source pieces independently or must retain
cancellation in their structured sum.
``--require-regular-loewner-pole-half-transport`` gates the selected split:
the combined Archimedean/prime Loewner block plus the separate pole must have a
two-piece triangle coefficient below one half of the preceding total coefficient
for every regular channel, while the declared fixed exception remains separate.
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

from certify_parity_gap import closed_forms, prime_powers_up_to
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


def _source_component_data(
    *, c: int, cutoff: int, precision: int
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Build one-dimensional midpoint data for off-diagonal source pieces."""
    started = time.time()
    flint.ctx.prec = precision
    source_s, _, _, source_l = closed_forms(cutoff, c, precision)
    s_values = np.array(
        [float(value.mid()) for value in source_s], dtype=np.float64
    )
    length = float(source_l.mid())
    pi = math.pi
    modes = np.arange(0, cutoff + 1, dtype=np.float64)
    denominator = length * length + 16.0 * pi * pi * modes * modes
    pole_a = length / denominator
    pole_b = 4.0 * pi * modes / denominator

    prime_powers = prime_powers_up_to(c)
    prime_sine = np.zeros(cutoff + 1, dtype=np.float64)
    positive_modes = modes[1:]
    for q, p in prime_powers:
        weight = math.log(p) / math.sqrt(q)
        y = math.log(q)
        angles = 2.0 * pi * positive_modes * y / length
        prime_sine[1:] += weight * np.sin(angles)

    data: dict[str, Any] = {
        "length": length,
        "pi": pi,
        "prefactor": 32.0 * length * math.sinh(length / 4.0) ** 2,
        "sqrt_two": math.sqrt(2.0),
        "source_s": s_values,
        "pole_a": pole_a,
        "pole_b": pole_b,
        "prime_sine": prime_sine,
    }
    metadata = {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "cutoff": cutoff,
        "precision_bits_for_arb_midpoints": precision,
        "prime_power_count": len(prime_powers),
        "component_names": ["prime", "archimedean", "pole"],
        "crossblock_scope": (
            "off-diagonal historical-band/new-shell entries only; all three "
            "pieces are whitened against the same full shifted CvS energies"
        ),
        "seconds": round(time.time() - started, 3),
    }
    return data, metadata


def _source_component_couplings(
    *,
    data: dict[str, Any],
    sector: str,
    low_mode: int,
    high_mode: int,
    shell_low_mode: int,
    shell_high_mode: int,
) -> dict[str, np.ndarray]:
    """Return prime, Archimedean, and pole crossblocks at midpoints."""
    if not low_mode <= high_mode < shell_low_mode <= shell_high_mode:
        raise ValueError("source component blocks must be strictly separated")
    if sector == "odd" and low_mode == 0:
        low_mode = 1

    row_modes = np.arange(low_mode, high_mode + 1, dtype=np.int64)
    shell_modes = np.arange(
        shell_low_mode, shell_high_mode + 1, dtype=np.int64
    )
    shape = (len(row_modes), len(shell_modes))
    prime = np.zeros(shape, dtype=np.float64)
    archimedean = np.zeros(shape, dtype=np.float64)
    pole = np.zeros(shape, dtype=np.float64)

    positive_mask = row_modes > 0
    positive_rows = row_modes[positive_mask]
    if len(positive_rows):
        row = positive_rows[:, None]
        column = shell_modes[None, :]
        same_denominator = data["pi"] * (row - column)
        reflected_denominator = data["pi"] * (row + column)

        source_s = data["source_s"]
        prime_sine = data["prime_sine"]
        arch_same = (
            source_s[column] - source_s[row]
        ) / same_denominator
        arch_reflected = (
            -source_s[column] - source_s[row]
        ) / reflected_denominator
        prime_same = (
            prime_sine[column] - prime_sine[row]
        ) / same_denominator
        prime_reflected = (
            -prime_sine[column] - prime_sine[row]
        ) / reflected_denominator

        if sector == "even":
            pole_positive = (
                2.0
                * data["prefactor"]
                * data["pole_a"][row]
                * data["pole_a"][column]
            )
            arch_positive = -arch_same - arch_reflected
            prime_positive = -prime_same - prime_reflected
        elif sector == "odd":
            pole_positive = (
                -2.0
                * data["prefactor"]
                * data["pole_b"][row]
                * data["pole_b"][column]
            )
            arch_positive = -arch_same + arch_reflected
            prime_positive = -prime_same + prime_reflected
        else:
            raise ValueError(f"unknown parity sector {sector}")

        pole[positive_mask, :] = pole_positive
        archimedean[positive_mask, :] = arch_positive
        prime[positive_mask, :] = prime_positive

    zero_rows = np.flatnonzero(row_modes == 0)
    if len(zero_rows):
        if sector != "even" or len(zero_rows) != 1:
            raise ValueError("only the even sector may contain one zero mode")
        columns = shell_modes
        pole[zero_rows[0], :] = (
            data["sqrt_two"]
            * data["prefactor"]
            * data["pole_a"][0]
            * data["pole_a"][columns]
        )
        archimedean[zero_rows[0], :] = (
            data["sqrt_two"]
            * data["source_s"][columns]
            / (data["pi"] * columns)
        )
        prime[zero_rows[0], :] = (
            data["sqrt_two"]
            * data["prime_sine"][columns]
            / (data["pi"] * columns)
        )

    return {
        "prime": prime,
        "archimedean": archimedean,
        "pole": pole,
    }


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
    component_transport_available: bool | None = None
    all_source_components_strictly_below_half = True
    component_ratios: dict[str, list[float]] = {}
    all_loewner_pole_triangle_below_half_previous_total = True
    all_regular_loewner_pole_triangle_below_half_previous_total = True
    regular_two_piece_channel_count = 0
    excluded_fixed_exception_count = 0
    structured_group_ratios: dict[str, list[float]] = {}
    all_newest_source_triangles_below_leading = True
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
        newest_source = newest[0].get("source_component_diagnostic")
        newest_source_record: dict[str, Any] | None = None
        if newest_source is not None:
            newest_two_piece = float(
                newest_source[
                    "loewner_pole_triangle_coefficient_upper_midpoint"
                ]
            )
            newest_source_pass = newest_two_piece < float(
                newest[0]["candidate_envelope"]
            )
            all_newest_source_triangles_below_leading = (
                all_newest_source_triangles_below_leading
                and newest_source_pass
            )
            newest_source_record = {
                "loewner_pole_triangle_coefficient_midpoint": newest_two_piece,
                "leading_budget": newest[0]["candidate_envelope"],
                "strictly_below_leading": newest_source_pass,
            }

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
            repeated_record: dict[str, Any] = {
                "modes": list(modes),
                "previous_distance": old["distance"],
                "current_distance": channel["distance"],
                "previous_kappa_midpoint": previous_kappa,
                "current_kappa_midpoint": current_kappa,
                "doubling_ratio_midpoint": current_kappa / previous_kappa,
                "strictly_below_one_half": strict_half,
            }

            old_source = old.get("source_component_diagnostic")
            current_source = channel.get("source_component_diagnostic")
            available_here = old_source is not None and current_source is not None
            if (old_source is None) != (current_source is None):
                raise ValueError(
                    f"{name} channel {modes} has mismatched source diagnostics"
                )
            if component_transport_available is None:
                component_transport_available = available_here
            elif component_transport_available != available_here:
                raise ValueError("source component diagnostics are not uniform")

            if available_here:
                old_components = {
                    component["name"]: component
                    for component in old_source["components"]
                }
                current_components = {
                    component["name"]: component
                    for component in current_source["components"]
                }
                if old_components.keys() != current_components.keys():
                    raise ValueError(
                        f"{name} channel {modes} changed source components"
                    )
                component_records: list[dict[str, Any]] = []
                for component_name in sorted(old_components):
                    old_value = float(
                        old_components[component_name]["kappa_midpoint"]
                    )
                    current_value = float(
                        current_components[component_name]["kappa_midpoint"]
                    )
                    if old_value <= 0:
                        raise ValueError(
                            f"{component_name} source coefficient is not positive"
                        )
                    ratio = current_value / old_value
                    component_half = ratio < 0.5
                    all_source_components_strictly_below_half = (
                        all_source_components_strictly_below_half
                        and component_half
                    )
                    component_ratios.setdefault(component_name, []).append(ratio)
                    component_records.append(
                        {
                            "name": component_name,
                            "previous_kappa_midpoint": old_value,
                            "current_kappa_midpoint": current_value,
                            "doubling_ratio_midpoint": ratio,
                            "strictly_below_one_half": component_half,
                        }
                    )
                repeated_record["source_component_transport"] = component_records

                old_groups = {
                    group["name"]: group
                    for group in old_source.get("structured_groups", [])
                }
                current_groups = {
                    group["name"]: group
                    for group in current_source.get("structured_groups", [])
                }
                if old_groups.keys() != current_groups.keys():
                    raise ValueError(
                        f"{name} channel {modes} changed structured groups"
                    )
                group_records: list[dict[str, Any]] = []
                for group_name in sorted(old_groups):
                    old_value = float(old_groups[group_name]["kappa_midpoint"])
                    current_value = float(
                        current_groups[group_name]["kappa_midpoint"]
                    )
                    if old_value <= 0:
                        raise ValueError(
                            f"{group_name} structured coefficient is not positive"
                        )
                    ratio = current_value / old_value
                    structured_group_ratios.setdefault(group_name, []).append(
                        ratio
                    )
                    group_records.append(
                        {
                            "name": group_name,
                            "previous_kappa_midpoint": old_value,
                            "current_kappa_midpoint": current_value,
                            "doubling_ratio_midpoint": ratio,
                            "strictly_below_one_half": ratio < 0.5,
                        }
                    )
                two_piece_coefficient = float(
                    current_source[
                        "loewner_pole_triangle_coefficient_upper_midpoint"
                    ]
                )
                two_piece_ratio = two_piece_coefficient / previous_kappa
                two_piece_half = two_piece_ratio < 0.5
                all_loewner_pole_triangle_below_half_previous_total = (
                    all_loewner_pole_triangle_below_half_previous_total
                    and two_piece_half
                )
                is_expected_exception = (
                    expected_exception_sector is not None
                    and expected_exception_modes is not None
                    and name == expected_exception_sector
                    and modes == expected_exception_modes
                )
                if is_expected_exception:
                    excluded_fixed_exception_count += 1
                else:
                    regular_two_piece_channel_count += 1
                    all_regular_loewner_pole_triangle_below_half_previous_total = (
                        all_regular_loewner_pole_triangle_below_half_previous_total
                        and two_piece_half
                    )
                repeated_record["structured_source_transport"] = {
                    "groups": group_records,
                    "current_loewner_pole_triangle_coefficient_midpoint": (
                        two_piece_coefficient
                    ),
                    "previous_total_kappa_midpoint": previous_kappa,
                    "triangle_over_previous_total": two_piece_ratio,
                    "strictly_below_one_half_previous_total": two_piece_half,
                    "excluded_as_expected_fixed_exception": (
                        is_expected_exception
                    ),
                }
            repeated.append(repeated_record)
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
                    "structured_source": newest_source_record,
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
    component_ratio_ranges = {
        name: {
            "count": len(ratios),
            "minimum": min(ratios),
            "maximum": max(ratios),
            "all_strictly_below_one_half": all(ratio < 0.5 for ratio in ratios),
        }
        for name, ratios in sorted(component_ratios.items())
    }
    structured_group_ratio_ranges = {
        name: {
            "count": len(ratios),
            "minimum": min(ratios),
            "maximum": max(ratios),
            "all_strictly_below_one_half": all(ratio < 0.5 for ratio in ratios),
        }
        for name, ratios in sorted(structured_group_ratios.items())
    }
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
        "source_component_transport": {
            "available": bool(component_transport_available),
            "all_components_strictly_below_half": (
                all_source_components_strictly_below_half
                if component_transport_available
                else None
            ),
            "ratio_ranges": component_ratio_ranges,
            "structured_group_ratio_ranges": structured_group_ratio_ranges,
            "all_newest_loewner_pole_triangle_bounds_below_leading": (
                all_newest_source_triangles_below_leading
                if component_transport_available
                else None
            ),
            "all_loewner_pole_triangle_bounds_below_half_previous_total": (
                all_loewner_pole_triangle_below_half_previous_total
                if component_transport_available
                else None
            ),
            "regular_two_piece_channel_count": regular_two_piece_channel_count,
            "excluded_expected_fixed_exception_count": (
                excluded_fixed_exception_count
            ),
            "all_regular_loewner_pole_triangle_bounds_below_half_previous_total": (
                all_regular_loewner_pole_triangle_below_half_previous_total
                if component_transport_available
                else None
            ),
            "route_implication": (
                "for regular channels, retain the arch-prime Loewner block and "
                "separate the rank-two pole; their two-piece triangle bound "
                "preserves half transport, while the expected fixed exception "
                "stays in its independent budget"
                if component_transport_available
                and all_regular_loewner_pole_triangle_below_half_previous_total
                and all_newest_source_triangles_below_leading
                and excluded_fixed_exception_count <= 1
                else (
                    "the regular two-piece Loewner/pole triangle route misses "
                    "half transport; retain more of the structured source sum"
                    if component_transport_available
                    else "source component diagnostics were not requested"
                )
            ),
        },
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


def _source_component_channel_diagnostic(
    *,
    data: dict[str, Any],
    sector: str,
    low_mode: int,
    high_mode: int,
    shell_low_mode: int,
    shell_high_mode: int,
    total_coupling: np.ndarray,
    total_kappa: float,
    core_cholesky: np.ndarray,
    shell_cholesky: np.ndarray,
) -> dict[str, Any]:
    """Whiten each source component and verify total crossblock reconstruction."""
    pieces = _source_component_couplings(
        data=data,
        sector=sector,
        low_mode=low_mode,
        high_mode=high_mode,
        shell_low_mode=shell_low_mode,
        shell_high_mode=shell_high_mode,
    )
    reconstructed = sum(pieces.values(), start=np.zeros_like(total_coupling))
    reconstruction_error = float(
        np.max(np.abs(reconstructed - total_coupling))
    )
    reconstruction_scale = max(
        1.0, float(np.max(np.abs(total_coupling)))
    )
    reconstruction_tolerance = (
        512.0 * np.finfo(np.float64).eps * reconstruction_scale
    )
    if reconstruction_error > reconstruction_tolerance:
        raise RuntimeError(
            f"{sector} source reconstruction error {reconstruction_error} "
            f"exceeds {reconstruction_tolerance} for [{low_mode},{high_mode}]"
        )

    component_records: list[dict[str, Any]] = []
    component_norm_sum = 0.0
    component_kappa: dict[str, float] = {}
    for name in ("prime", "archimedean", "pole"):
        kappa, linear_algebra = _whitened_largest_singular_squared(
            core_cholesky_blocks=[
                (slice(0, total_coupling.shape[0]), core_cholesky)
            ],
            coupling=pieces[name],
            shell_cholesky=shell_cholesky,
        )
        operator_norm = math.sqrt(kappa)
        component_kappa[name] = kappa
        component_norm_sum += operator_norm
        component_records.append(
            {
                "name": name,
                "kappa_midpoint": kappa,
                "operator_norm_midpoint": operator_norm,
                "linear_algebra": linear_algebra,
            }
        )

    triangle_coefficient = component_norm_sum * component_norm_sum
    if triangle_coefficient + 1e-12 * max(1.0, total_kappa) < total_kappa:
        raise RuntimeError("source component triangle bound fell below total")

    loewner_coupling = pieces["prime"] + pieces["archimedean"]
    loewner_kappa, loewner_linear_algebra = (
        _whitened_largest_singular_squared(
            core_cholesky_blocks=[
                (slice(0, total_coupling.shape[0]), core_cholesky)
            ],
            coupling=loewner_coupling,
            shell_cholesky=shell_cholesky,
        )
    )
    loewner_norm = math.sqrt(loewner_kappa)
    pole_norm = math.sqrt(component_kappa["pole"])
    two_piece_triangle_coefficient = (loewner_norm + pole_norm) ** 2
    if two_piece_triangle_coefficient + 1e-12 * max(1.0, total_kappa) < total_kappa:
        raise RuntimeError("Loewner/pole triangle bound fell below total")
    return {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "energy_denominator": (
            "same full shifted historical-band and new-shell energies as the "
            "total coupling coefficient"
        ),
        "reconstruction_error": reconstruction_error,
        "reconstruction_tolerance": reconstruction_tolerance,
        "reconstruction_pass": True,
        "components": component_records,
        "structured_groups": [
            {
                "name": "arch_prime_loewner",
                "members": ["archimedean", "prime"],
                "kappa_midpoint": loewner_kappa,
                "operator_norm_midpoint": loewner_norm,
                "linear_algebra": loewner_linear_algebra,
                "formula_role": (
                    "combined difference-quotient/reflected symbol block; "
                    "retains prime-Archimedean cancellation"
                ),
            }
        ],
        "component_operator_norm_sum": component_norm_sum,
        "triangle_coefficient_upper_midpoint": triangle_coefficient,
        "loewner_pole_operator_norm_sum": loewner_norm + pole_norm,
        "loewner_pole_triangle_coefficient_upper_midpoint": (
            two_piece_triangle_coefficient
        ),
        "total_kappa_midpoint": total_kappa,
        "triangle_to_total_ratio": (
            triangle_coefficient / total_kappa if total_kappa > 0 else None
        ),
        "loewner_pole_triangle_to_total_ratio": (
            two_piece_triangle_coefficient / total_kappa
            if total_kappa > 0
            else None
        ),
        "interpretation": (
            "individual component norms discard cancellation; the triangle "
            "coefficient is a diagnostic upper route, not interval evidence"
        ),
    }


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
    source_component_diagnostic: bool = False,
    require_regular_loewner_pole_half_transport: bool = False,
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
    if require_regular_loewner_pole_half_transport and previous_probe is None:
        raise ValueError(
            "require_regular_loewner_pole_half_transport needs a previous_probe"
        )
    if (
        require_regular_loewner_pole_half_transport
        and not source_component_diagnostic
    ):
        raise ValueError(
            "require_regular_loewner_pole_half_transport needs "
            "source_component_diagnostic"
        )
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
    source_data: dict[str, Any] | None = None
    source_metadata: dict[str, Any] | None = None
    source_component_started: float | None = None
    if source_component_diagnostic:
        source_component_started = time.time()
        source_data, source_metadata = _source_component_data(
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
    if source_metadata is not None:
        report["source_component_diagnostic"] = source_metadata

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
            channel_record: dict[str, Any] = {
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
            if source_data is not None:
                channel_record["source_component_diagnostic"] = (
                    _source_component_channel_diagnostic(
                        data=source_data,
                        sector=sector,
                        low_mode=low_mode,
                        high_mode=high_mode,
                        shell_low_mode=middle_cutoff + 1,
                        shell_high_mode=new_cutoff,
                        total_coupling=coupling,
                        total_kappa=kappa,
                        core_cholesky=cholesky,
                        shell_cholesky=new_cholesky,
                    )
                )
            channels.append(channel_record)

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

    if source_metadata is not None:
        source_channels = [
            channel["source_component_diagnostic"]
            for sector in report["sectors"]
            for channel in sector["channels"]
        ]
        source_metadata.update(
            {
                "channel_count": len(source_channels),
                "all_crossblocks_reconstructed": all(
                    channel["reconstruction_pass"]
                    for channel in source_channels
                ),
                "maximum_reconstruction_error": max(
                    channel["reconstruction_error"]
                    for channel in source_channels
                ),
                "maximum_reconstruction_error_over_tolerance": max(
                    channel["reconstruction_error"]
                    / channel["reconstruction_tolerance"]
                    for channel in source_channels
                ),
                "triangle_to_total_ratio_range": {
                    "minimum": min(
                        channel["triangle_to_total_ratio"]
                        for channel in source_channels
                    ),
                    "maximum": max(
                        channel["triangle_to_total_ratio"]
                        for channel in source_channels
                    ),
                },
                "loewner_pole_triangle_to_total_ratio_range": {
                    "minimum": min(
                        channel["loewner_pole_triangle_to_total_ratio"]
                        for channel in source_channels
                    ),
                    "maximum": max(
                        channel["loewner_pole_triangle_to_total_ratio"]
                        for channel in source_channels
                    ),
                },
                "newest_loewner_pole_triangle_bounds": [
                    {
                        "sector": sector["sector"],
                        "modes": newest["modes"],
                        "coefficient_midpoint": newest[
                            "source_component_diagnostic"
                        ]["loewner_pole_triangle_coefficient_upper_midpoint"],
                        "leading_budget": newest["candidate_envelope"],
                        "strictly_below_leading": newest[
                            "source_component_diagnostic"
                        ]["loewner_pole_triangle_coefficient_upper_midpoint"]
                        < newest["candidate_envelope"],
                    }
                    for sector in report["sectors"]
                    for newest in [
                        next(
                            channel
                            for channel in sector["channels"]
                            if channel["distance"] == 0
                        )
                    ]
                ],
                "total_seconds": round(
                    time.time() - source_component_started, 3
                ),
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
        if require_regular_loewner_pole_half_transport:
            source_comparison = comparison["source_component_transport"]
            loewner_range = source_comparison[
                "structured_group_ratio_ranges"
            ].get("arch_prime_loewner")
            if (
                not source_comparison[
                    "all_regular_loewner_pole_triangle_bounds_below_half_previous_total"
                ]
                or not source_comparison[
                    "all_newest_loewner_pole_triangle_bounds_below_leading"
                ]
                or loewner_range is None
                or not loewner_range["all_strictly_below_one_half"]
            ):
                raise RuntimeError(
                    "regular Loewner/pole half-transport midpoint diagnostics failed"
                )
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
    parser.add_argument("--source-component-diagnostic", action="store_true")
    parser.add_argument(
        "--require-regular-loewner-pole-half-transport", action="store_true"
    )
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
        source_component_diagnostic=args.source_component_diagnostic,
        require_regular_loewner_pole_half_transport=(
            args.require_regular_loewner_pole_half_transport
        ),
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
                "source_component_diagnostic": result.get(
                    "source_component_diagnostic"
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
