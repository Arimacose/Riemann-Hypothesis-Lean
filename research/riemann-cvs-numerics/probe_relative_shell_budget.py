#!/usr/bin/env python3
"""Explore the next recursive relative-energy shell at Arb midpoints.

This script is deliberately separated from the rigorous interval-LDL
certifier.  It constructs the same exact-form Arb enclosure, discards interval
radii when converting entries to floating-point midpoints, and computes the
generalized coupling norms that choose the next rational certificate.

For a core/shell split, it reports

    sup C(s,t)^2 / (R_q(s,s) H_shell(t,t))

for each requested direct coefficient ``q``.  It also replaces the core by the
block-diagonal reference energy ``q_ref * L + H_core`` and reports the
coefficient ``kappa`` consumed by ``relativeShell_of_referenceReserve``.  None
of these midpoint values is a proof; pass the selected rational bound to
``certify_recursive_relative_energy_shells.py`` for a rigorous certificate.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    parity_blocks,
    reflection_symmetric_enclosure,
)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    return value


def _midpoint_numpy(matrix: arb_mat) -> np.ndarray:
    """Discard radii explicitly and return a float64 midpoint matrix."""
    return np.array(
        [
            [float(matrix[i, j].mid()) for j in range(matrix.ncols())]
            for i in range(matrix.nrows())
        ],
        dtype=np.float64,
    )


def _relative_coupling_squared(
    core: np.ndarray,
    coupling: np.ndarray,
    shell: np.ndarray,
) -> float:
    """Return the midpoint generalized coupling norm squared.

    Cholesky factors also reject a midpoint core or shell that is not positive
    definite.  If ``core = C_C C_C^T`` and ``shell = C_H C_H^T``, the desired
    value is the squared largest singular value of
    ``C_C^-1 coupling C_H^-T``.
    """
    core_cholesky = np.linalg.cholesky(core)
    shell_cholesky = np.linalg.cholesky(shell)
    whitened_transpose = np.linalg.solve(
        shell_cholesky,
        np.linalg.solve(core_cholesky, coupling).T,
    )
    largest = np.linalg.svd(whitened_transpose, compute_uv=False)[0]
    return float(largest * largest)


def _parity_dimension(sector: str, cutoff: int) -> int:
    return cutoff + 1 if sector == "even" else cutoff


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

    started = time.time()
    ctx.prec = precision
    raw = build_cutoff_free_matrix(c, shell_cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, shell_cutoff)
    even, odd = parity_blocks(symmetric, shell_cutoff)
    matrix_seconds = time.time() - started
    shift_float = float(shift_gain)
    reference_q_float = float(reference_q)

    records: list[dict[str, Any]] = []
    for sector, block, low_dimension in (
        ("even", even, low_cutoff + 1),
        ("odd", odd, low_cutoff),
    ):
        sector_started = time.time()
        full = _midpoint_numpy(block)
        full += np.eye(full.shape[0], dtype=np.float64) * shift_float

        core_dimension = _parity_dimension(sector, core_cutoff)
        shell_dimension = _parity_dimension(sector, shell_cutoff)
        core_raw = full[:core_dimension, :core_dimension]
        coupling = full[:core_dimension, core_dimension:shell_dimension]
        shell = full[
            core_dimension:shell_dimension,
            core_dimension:shell_dimension,
        ]

        low = core_raw[:low_dimension, :low_dimension]
        high_core = core_raw[low_dimension:, low_dimension:]
        reference = np.zeros_like(core_raw)
        reference[:low_dimension, :low_dimension] = reference_q_float * low
        reference[low_dimension:, low_dimension:] = high_core
        reference_kappa = _relative_coupling_squared(
            reference, coupling, shell
        )

        direct_records: list[dict[str, Any]] = []
        for q in direct_qs:
            direct_core = core_raw.copy()
            direct_core[:low_dimension, :low_dimension] *= float(q)
            ratio = _relative_coupling_squared(
                direct_core, coupling, shell
            )
            direct_record: dict[str, Any] = {
                "q": str(q),
                "rho_midpoint": ratio,
            }
            if candidate_rho is not None:
                direct_record["candidate_rho"] = str(candidate_rho)
                direct_record["midpoint_below_candidate"] = (
                    ratio < float(candidate_rho)
                )
            direct_records.append(direct_record)

        record: dict[str, Any] = {
            "sector": sector,
            "core_dimension": core_dimension,
            "shell_dimension": shell_dimension - core_dimension,
            "reference_q": str(reference_q),
            "reference_kappa_midpoint": reference_kappa,
            "direct_core_ratios": direct_records,
            "seconds": round(time.time() - sector_started, 3),
        }
        if reserve is not None:
            record["reserve"] = str(reserve)
            record["minimum_rho_via_reserve_midpoint"] = (
                reference_kappa / float(reserve)
            )
            record["reserve_route_below_one_at_midpoint"] = (
                reference_kappa < float(reserve)
            )
        records.append(record)

    return {
        "status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "rigorous_certificate": False,
        "scope": (
            "Arb midpoint exploration used only to select rational bounds; "
            "all interval radii are discarded before linear algebra"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "core_cutoff": core_cutoff,
        "shell_cutoff": shell_cutoff,
        "precision_bits_for_arb_construction": precision,
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "direct_qs": [str(q) for q in direct_qs],
        "matrix_seconds": round(matrix_seconds, 3),
        "sectors": records,
        "total_seconds": round(time.time() - started, 3),
    }


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
        "--direct-q",
        action="append",
        default=None,
        help="repeatable direct core coefficient; defaults to 999/1000 and 249/250",
    )
    parser.add_argument(
        "--reserve",
        default=None,
        help="optional reserve coefficient, for example 1/666",
    )
    parser.add_argument(
        "--candidate-rho",
        default=None,
        help="optional rational rho to compare with midpoint direct ratios",
    )
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    direct_q_texts = args.direct_q or ["999/1000", "249/250"]
    direct_qs = [
        _positive_fraction(text, "direct_q") for text in direct_q_texts
    ]
    reserve = (
        _positive_fraction(args.reserve, "reserve")
        if args.reserve is not None
        else None
    )
    candidate_rho = (
        _positive_fraction(args.candidate_rho, "candidate_rho")
        if args.candidate_rho is not None
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
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")
    digest = hashlib.sha256(args.json_out.read_bytes()).hexdigest().upper()

    print(
        "relative shell midpoint diagnostic: "
        f"core={args.core_cutoff}, shell={args.shell_cutoff}, "
        f"x=-{payload['shift_gain']}"
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
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
