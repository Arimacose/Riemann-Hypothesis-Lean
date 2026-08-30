#!/usr/bin/env python3
"""Probe later CvS dyadic shells without constructing the full Arb matrix.

The rigorous shell certifiers first build a ``(2 * N + 1)``-dimensional Arb
matrix and then compress it into the even and odd reflection sectors.  That is
the right production path, but it is unnecessarily expensive when the sole
purpose is to choose the next analytic shell bound.  The exact reflection
formulas give, for positive Fourier indices ``k,l``,

    A_even[k,l] = A[k,l] + A[k,-l],
    A_odd [k,l] = A[k,l] - A[k,-l].

This script evaluates those formulas directly at Arb midpoints and stores only
the two parity blocks.  It then measures

    sup C(s,t)^2 / (R_q(s,s) H_shell(t,t))

for direct core-relative energies, and the analogous coefficient against the
block-diagonal reference energy ``q_ref * L + H_core``.  The result is a
midpoint diagnostic, not a proof.  Its role is to reveal post-N1920 scaling and
select a rational majorant for a later interval or analytic certificate.

When ``--previous-cutoff`` is supplied, the script also measures the coupling
against the recursive dyadic reference

    diag(R_q(previous_cutoff), H_[previous_cutoff,core_cutoff]).

A preceding ``rho=1/12`` shell controls two thirds of exactly this reference,
so the next ``rho=1/12`` shell needs a reference coefficient at most ``1/18``.

An optional small-cutoff replay compares every directly assembled parity entry
with the canonical Arb full-matrix construction.  This guards the optimized
formula path without pretending that discarded Arb radii certify positivity.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np
from flint import arb, ctx

from certify_parity_gap import (
    arch_kappa,
    build_cutoff_free_matrix,
    closed_forms,
    parity_blocks,
    pole_J,
    prime_powers_up_to,
    reflection_symmetric_enclosure,
)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    return value


def _midpoint(value: arb) -> float:
    return float(value.mid())


def _parity_dimension(sector: str, cutoff: int) -> int:
    return cutoff + 1 if sector == "even" else cutoff


def _canonical_midpoint(matrix: Any) -> np.ndarray:
    return np.array(
        [
            [_midpoint(matrix[i, j]) for j in range(matrix.ncols())]
            for i in range(matrix.nrows())
        ],
        dtype=np.float64,
    )


def _direct_midpoint_parity_blocks(
    *, c: int, cutoff: int, precision: int
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    """Assemble the exact parity formulas after taking Arb midpoints."""
    started = time.time()
    ctx.prec = precision
    S_arb, CC_arb, XC_arb, L_arb = closed_forms(cutoff, c, precision)
    S = np.array([_midpoint(value) for value in S_arb], dtype=np.float64)
    CC = np.array([_midpoint(value) for value in CC_arb], dtype=np.float64)
    XC = np.array([_midpoint(value) for value in XC_arb], dtype=np.float64)
    L = _midpoint(L_arb)
    pi = math.pi
    prefactor = 32.0 * L * math.sinh(L / 4.0) ** 2
    kappa = _midpoint(arch_kappa(L_arb))
    pole_constant = _midpoint(pole_J(L_arb))
    prime_data = prime_powers_up_to(c)

    indices = np.arange(1, cutoff + 1, dtype=np.float64)
    denominators = L * L + 16.0 * pi * pi * indices * indices
    pole_a = L / denominators
    pole_b = 4.0 * pi * indices / denominators

    pole_b_outer = np.outer(pole_b, pole_b)
    same = np.outer(pole_a, pole_a)
    same -= pole_b_outer
    same *= prefactor
    reflected = np.outer(pole_a, pole_a)
    reflected += pole_b_outer
    reflected *= prefactor
    del pole_b_outer

    row = indices[:, None]
    column = indices[None, :]
    same_denominator = pi * (row - column)
    reflected_denominator = pi * (row + column)

    with np.errstate(divide="ignore", invalid="ignore"):
        arch_same = (
            S[1:][None, :] - S[1:][:, None]
        ) / same_denominator
    np.fill_diagonal(
        arch_same,
        kappa + 2.0 * CC[1:] + pole_constant - (2.0 / L) * XC[1:],
    )
    same -= arch_same
    del arch_same

    arch_reflected = (
        -S[1:][None, :] - S[1:][:, None]
    ) / reflected_denominator
    reflected -= arch_reflected
    del arch_reflected

    for q, p in prime_data:
        weight = math.log(p) / math.sqrt(q)
        y = math.log(q)
        angles = 2.0 * pi * indices * y / L
        sine = np.sin(angles)
        cosine = np.cos(angles)
        with np.errstate(divide="ignore", invalid="ignore"):
            prime_same = (
                sine[None, :] - sine[:, None]
            ) / same_denominator
        np.fill_diagonal(prime_same, 2.0 * (1.0 - y / L) * cosine)
        same -= weight * prime_same
        del prime_same

        prime_reflected = (
            -sine[None, :] - sine[:, None]
        ) / reflected_denominator
        reflected -= weight * prime_reflected
        del prime_reflected

    odd = same - reflected
    same += reflected
    del reflected, same_denominator, reflected_denominator

    even = np.empty((cutoff + 1, cutoff + 1), dtype=np.float64)
    even[1:, 1:] = same
    del same

    zero_pole_a = 1.0 / L
    pole_zero_positive = prefactor * zero_pole_a * pole_a
    arch_zero_positive = -S[1:] / (pi * indices)
    prime_zero_positive = np.zeros(cutoff, dtype=np.float64)
    prime_zero_zero = 0.0
    for q, p in prime_data:
        weight = math.log(p) / math.sqrt(q)
        y = math.log(q)
        sine = np.sin(2.0 * pi * indices * y / L)
        prime_zero_positive += weight * (-sine / (pi * indices))
        prime_zero_zero += weight * 2.0 * (1.0 - y / L)

    zero_positive = (
        pole_zero_positive - arch_zero_positive - prime_zero_positive
    )
    even[0, 1:] = math.sqrt(2.0) * zero_positive
    even[1:, 0] = even[0, 1:]
    even[0, 0] = (
        prefactor * zero_pole_a * zero_pole_a
        - (kappa + pole_constant - (2.0 / L) * XC[0])
        - prime_zero_zero
    )

    symmetry_error = max(
        float(np.max(np.abs(even - even.T))),
        float(np.max(np.abs(odd - odd.T))),
    )
    if not np.isfinite(even).all() or not np.isfinite(odd).all():
        raise RuntimeError("direct parity construction produced nonfinite entries")
    if symmetry_error > 32.0 * np.finfo(np.float64).eps:
        raise RuntimeError(
            f"direct parity construction lost symmetry: {symmetry_error}"
        )

    return even, odd, {
        "cutoff": cutoff,
        "even_dimension": cutoff + 1,
        "odd_dimension": cutoff,
        "matrix_bytes": int(even.nbytes + odd.nbytes),
        "max_symmetry_error": symmetry_error,
        "seconds": round(time.time() - started, 3),
        "formula": (
            "even[k,l]=A[k,l]+A[k,-l], "
            "odd[k,l]=A[k,l]-A[k,-l]"
        ),
    }


def _validate_direct_construction(
    *, c: int, cutoff: int, precision: int
) -> dict[str, Any]:
    direct_even, direct_odd, direct_record = _direct_midpoint_parity_blocks(
        c=c, cutoff=cutoff, precision=precision
    )
    started = time.time()
    raw = build_cutoff_free_matrix(c, cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, cutoff)
    canonical_even, canonical_odd = parity_blocks(symmetric, cutoff)
    canonical_even_mid = _canonical_midpoint(canonical_even)
    canonical_odd_mid = _canonical_midpoint(canonical_odd)
    even_error = float(np.max(np.abs(direct_even - canonical_even_mid)))
    odd_error = float(np.max(np.abs(direct_odd - canonical_odd_mid)))
    scale = max(
        1.0,
        float(np.max(np.abs(canonical_even_mid))),
        float(np.max(np.abs(canonical_odd_mid))),
    )
    tolerance = 4096.0 * np.finfo(np.float64).eps * cutoff * scale
    passed = even_error <= tolerance and odd_error <= tolerance
    if not passed:
        raise RuntimeError(
            "direct parity formula replay exceeded its floating tolerance: "
            f"even={even_error}, odd={odd_error}, tolerance={tolerance}"
        )
    return {
        "status": "PASS",
        "cutoff": cutoff,
        "precision_bits_for_arb_construction": precision,
        "direct_construction": direct_record,
        "even_max_abs_midpoint_error": even_error,
        "odd_max_abs_midpoint_error": odd_error,
        "scale": scale,
        "tolerance": tolerance,
        "seconds_for_canonical_replay": round(time.time() - started, 3),
    }


def _whitened_largest_singular_squared(
    *,
    core_cholesky_blocks: list[tuple[slice, np.ndarray]],
    coupling: np.ndarray,
    shell_cholesky: np.ndarray,
) -> tuple[float, dict[str, Any]]:
    """Return the generalized coupling norm squared at float midpoints."""
    started = time.time()
    core_whitened = np.empty_like(coupling)
    for rows, cholesky in core_cholesky_blocks:
        core_whitened[rows, :] = np.linalg.solve(
            cholesky, coupling[rows, :]
        )
    core_solve_seconds = time.time() - started

    shell_started = time.time()
    whitened_transpose = np.linalg.solve(
        shell_cholesky, core_whitened.T
    )
    del core_whitened
    shell_solve_seconds = time.time() - shell_started

    svd_started = time.time()
    singular_values = np.linalg.svd(
        whitened_transpose, compute_uv=False
    )
    largest = float(singular_values[0])
    second = float(singular_values[1]) if len(singular_values) > 1 else 0.0
    smallest = float(singular_values[-1])
    svd_seconds = time.time() - svd_started
    return largest * largest, {
        "largest_singular_value": largest,
        "second_singular_value": second,
        "smallest_singular_value": smallest,
        "core_triangular_solve_seconds": round(core_solve_seconds, 3),
        "shell_triangular_solve_seconds": round(shell_solve_seconds, 3),
        "svd_seconds": round(svd_seconds, 3),
        "seconds": round(time.time() - started, 3),
    }


def _probe_sector(
    *,
    sector: str,
    block: np.ndarray,
    low_cutoff: int,
    core_cutoff: int,
    shell_cutoff: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    direct_qs: list[Fraction],
    reserve: Fraction | None,
    candidate_rho: Fraction | None,
    previous_cutoff: int | None,
    dyadic_reference_q: Fraction,
    dyadic_reserve: Fraction | None,
) -> dict[str, Any]:
    started = time.time()
    shifted = block.copy()
    shifted.flat[:: shifted.shape[0] + 1] += float(shift_gain)

    low_dimension = _parity_dimension(sector, low_cutoff)
    core_dimension = _parity_dimension(sector, core_cutoff)
    full_dimension = _parity_dimension(sector, shell_cutoff)
    core_raw = shifted[:core_dimension, :core_dimension]
    coupling = shifted[:core_dimension, core_dimension:full_dimension]
    shell = shifted[core_dimension:full_dimension, core_dimension:full_dimension]
    shell_cholesky_started = time.time()
    shell_cholesky = np.linalg.cholesky(shell)
    shell_cholesky_seconds = time.time() - shell_cholesky_started

    reference_started = time.time()
    low_cholesky = np.linalg.cholesky(
        float(reference_q)
        * core_raw[:low_dimension, :low_dimension]
    )
    high_cholesky = np.linalg.cholesky(
        core_raw[low_dimension:, low_dimension:]
    )
    reference_cholesky_seconds = time.time() - reference_started
    reference_kappa, reference_linear_algebra = (
        _whitened_largest_singular_squared(
            core_cholesky_blocks=[
                (slice(0, low_dimension), low_cholesky),
                (slice(low_dimension, core_dimension), high_cholesky),
            ],
            coupling=coupling,
            shell_cholesky=shell_cholesky,
        )
    )

    direct_records: list[dict[str, Any]] = []
    for q in direct_qs:
        direct_core = core_raw.copy()
        direct_core[:low_dimension, :low_dimension] *= float(q)
        direct_started = time.time()
        direct_cholesky = np.linalg.cholesky(direct_core)
        direct_cholesky_seconds = time.time() - direct_started
        rho, linear_algebra = _whitened_largest_singular_squared(
            core_cholesky_blocks=[
                (slice(0, core_dimension), direct_cholesky)
            ],
            coupling=coupling,
            shell_cholesky=shell_cholesky,
        )
        record: dict[str, Any] = {
            "q": str(q),
            "rho_midpoint": rho,
            "core_cholesky_seconds": round(direct_cholesky_seconds, 3),
            "linear_algebra": linear_algebra,
        }
        if candidate_rho is not None:
            record["candidate_rho"] = str(candidate_rho)
            record["midpoint_below_candidate"] = rho < float(candidate_rho)
            record["candidate_slack_midpoint"] = float(candidate_rho) - rho
        direct_records.append(record)

    dyadic_reference = None
    if previous_cutoff is not None:
        previous_dimension = _parity_dimension(sector, previous_cutoff)
        previous_core = core_raw[
            :previous_dimension, :previous_dimension
        ].copy()
        previous_core[:low_dimension, :low_dimension] *= float(
            dyadic_reference_q
        )
        middle_shell = core_raw[
            previous_dimension:core_dimension,
            previous_dimension:core_dimension,
        ]
        dyadic_started = time.time()
        previous_cholesky = np.linalg.cholesky(previous_core)
        middle_cholesky = np.linalg.cholesky(middle_shell)
        dyadic_cholesky_seconds = time.time() - dyadic_started
        dyadic_kappa, dyadic_linear_algebra = (
            _whitened_largest_singular_squared(
                core_cholesky_blocks=[
                    (slice(0, previous_dimension), previous_cholesky),
                    (
                        slice(previous_dimension, core_dimension),
                        middle_cholesky,
                    ),
                ],
                coupling=coupling,
                shell_cholesky=shell_cholesky,
            )
        )
        dyadic_reference = {
            "previous_cutoff": previous_cutoff,
            "previous_core_dimension": previous_dimension,
            "middle_shell_dimension": core_dimension - previous_dimension,
            "new_shell_dimension": full_dimension - core_dimension,
            "q": str(dyadic_reference_q),
            "kappa_midpoint": dyadic_kappa,
            "cholesky_seconds": round(dyadic_cholesky_seconds, 3),
            "linear_algebra": dyadic_linear_algebra,
        }
        if dyadic_reserve is not None and candidate_rho is not None:
            required_budget = dyadic_reserve * candidate_rho
            dyadic_reference.update(
                {
                    "reserve": str(dyadic_reserve),
                    "candidate_rho": str(candidate_rho),
                    "required_budget": str(required_budget),
                    "midpoint_below_required_budget": (
                        dyadic_kappa < float(required_budget)
                    ),
                    "required_budget_slack_midpoint": (
                        float(required_budget) - dyadic_kappa
                    ),
                }
            )

    result: dict[str, Any] = {
        "sector": sector,
        "full_dimension": full_dimension,
        "core_dimension": core_dimension,
        "shell_dimension": full_dimension - core_dimension,
        "low_dimension": low_dimension,
        "reference_q": str(reference_q),
        "reference_kappa_midpoint": reference_kappa,
        "reference_cholesky_seconds": round(reference_cholesky_seconds, 3),
        "reference_linear_algebra": reference_linear_algebra,
        "shell_cholesky_seconds": round(shell_cholesky_seconds, 3),
        "direct_core_ratios": direct_records,
        "seconds": round(time.time() - started, 3),
    }
    if dyadic_reference is not None:
        result["dyadic_reference"] = dyadic_reference
    if reserve is not None:
        result["reserve"] = str(reserve)
        result["minimum_rho_via_reserve_midpoint"] = (
            reference_kappa / float(reserve)
        )
        result["reserve_route_below_one_at_midpoint"] = (
            reference_kappa < float(reserve)
        )
        result["reserve_slack_midpoint"] = float(reserve) - reference_kappa
    return result


def probe(
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shell_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    direct_qs: list[Fraction],
    reserve: Fraction | None,
    candidate_rho: Fraction | None,
    validation_cutoff: int | None,
    previous_cutoff: int | None,
    dyadic_reference_q: Fraction,
    dyadic_reserve: Fraction | None,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if not 1 <= low_cutoff < core_cutoff < shell_cutoff:
        raise ValueError(
            "require 1 <= low_cutoff < core_cutoff < shell_cutoff"
        )
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < reference_q < 1:
        raise ValueError("reference_q must lie strictly between zero and one")
    if not direct_qs or any(not 0 < q < 1 for q in direct_qs):
        raise ValueError("every direct_q must lie strictly between zero and one")
    if reserve is not None and not 0 < reserve < 1:
        raise ValueError("reserve must lie strictly between zero and one")
    if candidate_rho is not None and not 0 < candidate_rho < 1:
        raise ValueError("candidate_rho must lie strictly between zero and one")
    if validation_cutoff is not None and validation_cutoff < 1:
        raise ValueError("validation_cutoff must be positive")
    if previous_cutoff is not None and not (
        low_cutoff < previous_cutoff < core_cutoff
    ):
        raise ValueError(
            "previous_cutoff must lie strictly between low and core cutoffs"
        )
    if not 0 < dyadic_reference_q < 1:
        raise ValueError(
            "dyadic_reference_q must lie strictly between zero and one"
        )
    if dyadic_reserve is not None and not 0 < dyadic_reserve <= 1:
        raise ValueError("dyadic_reserve must lie in (0,1]")

    started = time.time()
    validation = None
    if validation_cutoff is not None:
        validation = _validate_direct_construction(
            c=c,
            cutoff=validation_cutoff,
            precision=precision,
        )

    even, odd, construction = _direct_midpoint_parity_blocks(
        c=c, cutoff=shell_cutoff, precision=precision
    )
    records: list[dict[str, Any]] = []
    for sector, block in (("even", even), ("odd", odd)):
        records.append(
            _probe_sector(
                sector=sector,
                block=block,
                low_cutoff=low_cutoff,
                core_cutoff=core_cutoff,
                shell_cutoff=shell_cutoff,
                shift_gain=shift_gain,
                reference_q=reference_q,
                direct_qs=direct_qs,
                reserve=reserve,
                candidate_rho=candidate_rho,
                previous_cutoff=previous_cutoff,
                dyadic_reference_q=dyadic_reference_q,
                dyadic_reserve=dyadic_reserve,
            )
        )

    payload: dict[str, Any] = {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "scope": (
            "direct parity midpoint exploration used to measure later-shell "
            "scaling; all Arb radii are discarded before dense linear algebra"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "core_cutoff": core_cutoff,
        "shell_cutoff": shell_cutoff,
        "precision_bits_for_closed_forms": precision,
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "direct_qs": [str(q) for q in direct_qs],
        "previous_cutoff": previous_cutoff,
        "dyadic_reference_q": str(dyadic_reference_q),
        "dyadic_reserve": (
            str(dyadic_reserve) if dyadic_reserve is not None else None
        ),
        "construction": construction,
        "sectors": records,
        "total_seconds": round(time.time() - started, 3),
    }
    if validation is not None:
        payload["canonical_formula_replay"] = validation
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--core-cutoff", type=int, required=True)
    parser.add_argument("--shell-cutoff", type=int, required=True)
    parser.add_argument("--prec", type=int, default=160)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--reference-q", default="999/1000")
    parser.add_argument(
        "--previous-cutoff",
        type=int,
        default=None,
        help=(
            "optional previous dyadic cutoff for the reference "
            "diag(R_q(previous),H_[previous,core])"
        ),
    )
    parser.add_argument(
        "--dyadic-reference-q",
        default=None,
        help="q used inside the previous recursive core; defaults to direct-q",
    )
    parser.add_argument(
        "--dyadic-reserve",
        default="2/3",
        help="core reserve against the dyadic reference; empty string omits",
    )
    parser.add_argument(
        "--direct-q",
        action="append",
        default=None,
        help=(
            "repeatable direct core coefficient; defaults to 249/250"
        ),
    )
    parser.add_argument(
        "--reserve",
        default="1/666",
        help="reference-energy reserve; pass an empty string to omit",
    )
    parser.add_argument(
        "--candidate-rho",
        default=None,
        help="optional rational direct-shell coefficient to compare",
    )
    parser.add_argument(
        "--validate-cutoff",
        type=int,
        default=120,
        help="small cutoff for direct-formula versus canonical Arb replay",
    )
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    direct_qs = [
        _positive_fraction(text, "direct_q")
        for text in (args.direct_q or ["249/250"])
    ]
    reserve = (
        _positive_fraction(args.reserve, "reserve")
        if args.reserve
        else None
    )
    candidate_rho = (
        _positive_fraction(args.candidate_rho, "candidate_rho")
        if args.candidate_rho is not None
        else None
    )
    dyadic_reference_q = (
        _positive_fraction(args.dyadic_reference_q, "dyadic_reference_q")
        if args.dyadic_reference_q is not None
        else direct_qs[0]
    )
    dyadic_reserve = (
        _positive_fraction(args.dyadic_reserve, "dyadic_reserve")
        if args.dyadic_reserve
        else None
    )
    payload = probe(
        c=args.c,
        low_cutoff=args.low_cutoff,
        core_cutoff=args.core_cutoff,
        shell_cutoff=args.shell_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        reference_q=_positive_fraction(args.reference_q, "reference_q"),
        direct_qs=direct_qs,
        reserve=reserve,
        candidate_rho=candidate_rho,
        validation_cutoff=args.validate_cutoff,
        previous_cutoff=args.previous_cutoff,
        dyadic_reference_q=dyadic_reference_q,
        dyadic_reserve=dyadic_reserve,
    )
    payload.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(
                timespec="seconds"
            ),
            "python_version": platform.python_version(),
            "numpy_version": np.__version__,
            "python_flint_version": flint.__version__,
            "platform": platform.platform(),
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")
    digest = hashlib.sha256(args.json_out.read_bytes()).hexdigest().upper()

    print(
        "dyadic shell midpoint scaling diagnostic: "
        f"core={args.core_cutoff}, shell={args.shell_cutoff}, "
        f"x=-{payload['shift_gain']}"
    )
    if "canonical_formula_replay" in payload:
        replay = payload["canonical_formula_replay"]
        print(
            "  canonical replay "
            f"N={replay['cutoff']} even_error="
            f"{replay['even_max_abs_midpoint_error']} odd_error="
            f"{replay['odd_max_abs_midpoint_error']}"
        )
    for sector in payload["sectors"]:
        print(
            f"  {sector['sector']} reference_kappa_midpoint="
            f"{sector['reference_kappa_midpoint']}"
        )
        if "minimum_rho_via_reserve_midpoint" in sector:
            print(
                "    minimum_rho_via_reserve_midpoint="
                f"{sector['minimum_rho_via_reserve_midpoint']}"
            )
        for direct in sector["direct_core_ratios"]:
            print(
                f"    q={direct['q']} "
                f"rho_midpoint={direct['rho_midpoint']}"
            )
        if "dyadic_reference" in sector:
            dyadic = sector["dyadic_reference"]
            print(
                "    dyadic_reference_kappa_midpoint="
                f"{dyadic['kappa_midpoint']}"
            )
            if "required_budget" in dyadic:
                print(
                    "      required_budget="
                    f"{dyadic['required_budget']} "
                    "below="
                    f"{dyadic['midpoint_below_required_budget']}"
                )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
