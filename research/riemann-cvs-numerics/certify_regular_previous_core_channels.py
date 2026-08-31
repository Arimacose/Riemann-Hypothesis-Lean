#!/usr/bin/env python3
"""Certify the regular previous-core channels at the first V23 transition.

For the shifted direct-parity CvS form at ``c = 13``, the already certified
``1920 -> 3840`` transition has new shell ``[1921,3840]``.  Decompose the old
core into the historical source bands

    d=0: [481,960],  d=1: [241,480],
    d=2: [121,240],  d=3: [21,120],

and, in the even sector only,

    d=4: [0,20].

The odd ``[1,20]`` band is the separately certified finite exception.  This
script validates that exception certificate and proves each of the remaining
nine regular inequalities with the dyadic budgets

    q_d = (1/30) * 2^(-d).

The proof uses a reverse Schur complement.  For each parity sector it:

1. builds the common shifted new-shell matrix ``B`` by direct Arb formulas;
2. proves ``B > 0`` by an exact-dyadic congruence and strict Gershgorin rows;
3. performs one verified solve ``B X = C^T`` for all regular source bands;
4. checks every residual interval contains exact zero;
5. proves every small Schur complement

       q_d E_d - C_d B^-1 C_d^T > 0

   by another exact-dyadic congruence and strict Gershgorin rows.

For the even fixed base, ``E_4`` includes the reference factor ``249/250``.
Floating Cholesky only selects bases.  Every stored float is embedded as an
exact dyadic Arb value before the positivity checks, so floating arithmetic is
not proof evidence.  A small canonical replay additionally checks that every
direct-minus-canonical parity entry interval contains zero.

This is a rigorous finite certificate for the first ``1920 -> 3840`` source
decomposition.  It deliberately does not assert the all-scale dyadic envelope
or the recursive-core energy normalization; those remain analytic inputs to
the existing Lean adapter.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gc
import hashlib
import json
import os
import platform
import subprocess
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Literal

import flint
import numpy as np
from flint import arb, arb_mat, ctx

from certify_direct_parity_relative_shell import (
    DirectParityKernel,
    _validate_direct_construction,
)
from certify_odd_fixed_base_channel import _certify_positive_matrix
from certify_preconditioned_relative_shell import (
    _fraction_arb,
    _sha256,
    _symmetrize_enclosure,
    _verify_solve_residual,
)


Sector = Literal["even", "odd"]


def _progress(message: str) -> None:
    print(f"[regular-previous-core] {message}", flush=True)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


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


def _dependency_record(path: Path) -> dict[str, str]:
    return {
        "path": str(path.resolve()),
        "sha256": _sha256(path.resolve()),
    }


def _resolve_certificate_artifact(
    *,
    certificate_path: Path,
    recorded_path: object,
    derived_suffix: str,
) -> Path:
    candidates: list[Path] = []
    if isinstance(recorded_path, str) and recorded_path:
        recorded = Path(recorded_path)
        candidates.append(recorded)
        if not recorded.is_absolute():
            candidates.append(certificate_path.parent / recorded)
            candidates.append(certificate_path.parent / recorded.name)
        else:
            candidates.append(certificate_path.parent / recorded.name)
    stem = certificate_path.with_suffix("")
    candidates.append(stem.with_name(stem.name + derived_suffix))

    seen: set[Path] = set()
    for candidate in candidates:
        candidate = candidate.resolve()
        if candidate in seen:
            continue
        seen.add(candidate)
        if candidate.is_file():
            return candidate
    rendered = ", ".join(str(path) for path in candidates)
    raise FileNotFoundError(
        "exception certificate preconditioner artifact is missing; checked "
        + rendered
    )


def _validate_positive_certificate(
    *,
    certificate_path: Path,
    certificate: object,
    dimension: int,
    derived_suffix: str,
    label: str,
) -> dict[str, Any]:
    if not isinstance(certificate, dict):
        raise ValueError(f"exception {label} certificate must be an object")
    if certificate.get("status") != "PASS":
        raise ValueError(f"exception {label} certificate status is not PASS")
    if certificate.get("dimension") != dimension:
        raise ValueError(f"exception {label} certificate has the wrong dimension")

    gershgorin = certificate.get("gershgorin")
    if not isinstance(gershgorin, dict):
        raise ValueError(f"exception {label} Gershgorin record is missing")
    if gershgorin.get("dimension") != dimension:
        raise ValueError(f"exception {label} Gershgorin dimension is wrong")
    if gershgorin.get("strictly_positive_rows") != dimension:
        raise ValueError(
            f"exception {label} certificate lacks all positive rows"
        )

    preconditioner = certificate.get("preconditioner")
    if not isinstance(preconditioner, dict):
        raise ValueError(f"exception {label} preconditioner record is missing")
    expected_flags = {
        "upper_triangular": True,
        "all_dyadic_radii_zero": True,
        "all_diagonal_entries_positive": True,
    }
    for key, expected in expected_flags.items():
        if preconditioner.get(key) is not expected:
            raise ValueError(
                f"exception {label} preconditioner field {key!r} is wrong"
            )
    if preconditioner.get("shape") != [dimension, dimension]:
        raise ValueError(f"exception {label} preconditioner shape is wrong")

    artifact = _resolve_certificate_artifact(
        certificate_path=certificate_path,
        recorded_path=preconditioner.get("path"),
        derived_suffix=derived_suffix,
    )
    artifact_hash = _sha256(artifact)
    if preconditioner.get("sha256") != artifact_hash:
        raise ValueError(
            f"exception {label} preconditioner hash does not match its file"
        )
    return {
        "status": "PASS",
        "dimension": dimension,
        "strictly_positive_rows": dimension,
        "margin_transcript_sha256": gershgorin.get(
            "margin_transcript_sha256"
        ),
        "preconditioner": {
            "path": str(artifact),
            "sha256": artifact_hash,
            "shape": [dimension, dimension],
        },
    }


def _validate_exception_certificate(
    *,
    path: Path,
    c: int,
    base_cutoff: int,
    middle_cutoff: int,
    new_cutoff: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    exception_budget: Fraction,
    regular_leading: Fraction,
    previous_channel_budget: Fraction,
) -> dict[str, Any]:
    path = path.resolve()
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("exception certificate root must be an object")

    expected: dict[str, Any] = {
        "status": "PASS",
        "rigorous_certificate": True,
        "c": c,
        "sector": "odd",
        "base_cutoff": base_cutoff,
        "middle_cutoff": middle_cutoff,
        "new_cutoff": new_cutoff,
        "base_modes": [1, base_cutoff],
        "new_shell_modes": [middle_cutoff + 1, new_cutoff],
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "exception_budget": str(exception_budget),
        "candidate_regular_leading": str(regular_leading),
        "previous_channel_budget": str(previous_channel_budget),
    }
    for key, value in expected.items():
        if payload.get(key) != value:
            raise ValueError(
                f"exception certificate field {key!r}: expected {value!r}, "
                f"got {payload.get(key)!r}"
            )

    precision_bits = payload.get("precision_bits")
    if not isinstance(precision_bits, int) or precision_bits < 128:
        raise ValueError("exception certificate precision record is invalid")

    script_path = Path(__file__).resolve()
    odd_script = script_path.with_name("certify_odd_fixed_base_channel.py")
    if payload.get("script_sha256") != _sha256(odd_script):
        raise ValueError(
            "exception certificate script hash does not match the tracked "
            "odd fixed-base certifier"
        )

    github_sha = os.environ.get("GITHUB_SHA")
    if github_sha is not None and payload.get("git_sha") != github_sha:
        raise ValueError("exception certificate git_sha does not match GITHUB_SHA")

    dependency_paths = {
        "direct_parity": script_path.with_name(
            "certify_direct_parity_relative_shell.py"
        ),
        "preconditioned_schur": script_path.with_name(
            "certify_preconditioned_relative_shell.py"
        ),
    }
    dependencies = payload.get("source_dependencies")
    if not isinstance(dependencies, dict):
        raise ValueError("exception certificate source dependencies are missing")
    validated_dependencies: dict[str, dict[str, str]] = {}
    for key, source_path in dependency_paths.items():
        record = dependencies.get(key)
        if not isinstance(record, dict):
            raise ValueError(f"exception source dependency {key!r} is missing")
        source_hash = _sha256(source_path)
        if record.get("sha256") != source_hash:
            raise ValueError(
                f"exception source dependency {key!r} hash is stale"
            )
        validated_dependencies[key] = {
            "path": str(source_path.resolve()),
            "sha256": source_hash,
        }

    shell_dimension = new_cutoff - middle_cutoff
    base_certificate = _validate_positive_certificate(
        certificate_path=path,
        certificate=payload.get("base_certificate"),
        dimension=base_cutoff,
        derived_suffix="_base_preconditioner.npy",
        label="base",
    )
    schur_certificate = _validate_positive_certificate(
        certificate_path=path,
        certificate=payload.get("schur_certificate"),
        dimension=shell_dimension,
        derived_suffix="_schur_preconditioner.npy",
        label="Schur",
    )

    residual = payload.get("solve_residual")
    expected_entries = base_cutoff * shell_dimension
    if not isinstance(residual, dict):
        raise ValueError("exception verified-solve residual record is missing")
    if residual.get("entry_count") != expected_entries:
        raise ValueError("exception residual entry count is wrong")
    if residual.get("entries_containing_zero") != expected_entries:
        raise ValueError("exception residual record lacks all zero enclosures")

    return {
        "status": "PASS",
        "path": str(path),
        "sha256": _sha256(path),
        "git_sha": payload.get("git_sha"),
        "precision_bits": precision_bits,
        "script_sha256": payload.get("script_sha256"),
        "base_certificate": base_certificate,
        "solve_residual": {
            "entry_count": expected_entries,
            "entries_containing_zero": expected_entries,
            "max_midpoint_abs": residual.get("max_midpoint_abs"),
            "max_radius": residual.get("max_radius"),
        },
        "schur_certificate": schur_certificate,
        "source_dependencies": validated_dependencies,
        "proof_consequence": (
            "the odd fixed base [1,base_cutoff] is a separately certified "
            "exception with coefficient exception_budget"
        ),
    }


def _regular_segments(
    historical_cutoffs: list[int],
) -> list[tuple[int, int]]:
    return [
        (historical_cutoffs[index - 1] + 1, historical_cutoffs[index])
        for index in range(len(historical_cutoffs) - 1, 0, -1)
    ]


def _build_shell(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    shell_modes: list[int],
    shift_gain: arb,
) -> tuple[arb_mat, dict[str, Any]]:
    started = time.time()
    shell = arb_mat(len(shell_modes), len(shell_modes))
    for i, k in enumerate(shell_modes):
        for j in range(i, len(shell_modes)):
            value = kernel.parity_entry(sector, k, shell_modes[j])
            if i == j:
                value += shift_gain
            shell[i, j] = value
            shell[j, i] = value
    return shell, {
        "modes": [shell_modes[0], shell_modes[-1]],
        "dimension": len(shell_modes),
        "direct_entry_evaluations": (
            len(shell_modes) * (len(shell_modes) + 1) // 2
        ),
        "seconds": round(time.time() - started, 3),
    }


def _build_regular_channels(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    historical_cutoffs: list[int],
    shell_modes: list[int],
    shift_gain: arb,
    reference_q: Fraction,
    regular_leading: Fraction,
) -> tuple[arb_mat, list[dict[str, Any]], dict[str, Any]]:
    started = time.time()
    base_cutoff = historical_cutoffs[0]
    segments = _regular_segments(historical_cutoffs)
    if sector == "even":
        segments.append((0, base_cutoff))

    total_dimension = sum(high - low + 1 for low, high in segments)
    coupling_t = arb_mat(len(shell_modes), total_dimension)
    records: list[dict[str, Any]] = []
    offset = 0
    direct_energy_entries = 0
    direct_coupling_entries = 0

    for distance, (low, high) in enumerate(segments):
        modes = list(range(low, high + 1))
        dimension = len(modes)
        budget = regular_leading * Fraction(1, 2) ** distance
        reference_scale = (
            reference_q if sector == "even" and low == 0 else Fraction(1)
        )
        energy_scale = budget * reference_scale
        energy = arb_mat(dimension, dimension)

        for i, k in enumerate(modes):
            for j in range(i, dimension):
                value = kernel.parity_entry(sector, k, modes[j])
                if i == j:
                    value += shift_gain
                value *= _fraction_arb(energy_scale)
                energy[i, j] = value
                energy[j, i] = value
        direct_energy_entries += dimension * (dimension + 1) // 2

        for j, k in enumerate(modes):
            for i, ell in enumerate(shell_modes):
                coupling_t[i, offset + j] = kernel.parity_entry(
                    sector, k, ell
                )
        direct_coupling_entries += dimension * len(shell_modes)

        records.append(
            {
                "distance": distance,
                "modes": [low, high],
                "dimension": dimension,
                "offset": offset,
                "budget": budget,
                "reference_scale": reference_scale,
                "energy_scale": energy_scale,
                "energy": energy,
            }
        )
        offset += dimension

    return coupling_t, records, {
        "sector": sector,
        "regular_channel_count": len(records),
        "combined_source_dimension": total_dimension,
        "coupling_transpose_shape": [len(shell_modes), total_dimension],
        "direct_energy_entry_evaluations": direct_energy_entries,
        "direct_coupling_entry_evaluations": direct_coupling_entries,
        "seconds": round(time.time() - started, 3),
    }


def _copy_channel_blocks(
    *,
    coupling_t: arb_mat,
    solution: arb_mat,
    offset: int,
    dimension: int,
) -> tuple[arb_mat, arb_mat]:
    shell_dimension = coupling_t.nrows()
    coupling = arb_mat(dimension, shell_dimension)
    channel_solution = arb_mat(shell_dimension, dimension)
    for j in range(dimension):
        for i in range(shell_dimension):
            coupling[j, i] = coupling_t[i, offset + j]
            channel_solution[i, j] = solution[i, offset + j]
    return coupling, channel_solution


def _certify_sector(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    historical_cutoffs: list[int],
    middle_cutoff: int,
    new_cutoff: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    regular_leading: Fraction,
    output_stem: Path,
) -> dict[str, Any]:
    started = time.time()
    shell_modes = list(range(middle_cutoff + 1, new_cutoff + 1))
    shell, shell_construction = _build_shell(
        kernel=kernel,
        sector=sector,
        shell_modes=shell_modes,
        shift_gain=_fraction_arb(shift_gain),
    )
    _progress(
        f"{sector}: built shifted shell {shell.nrows()}x{shell.ncols()} "
        f"in {shell_construction['seconds']:.3f}s"
    )

    coupling_t, channels, channel_construction = _build_regular_channels(
        kernel=kernel,
        sector=sector,
        historical_cutoffs=historical_cutoffs,
        shell_modes=shell_modes,
        shift_gain=_fraction_arb(shift_gain),
        reference_q=reference_q,
        regular_leading=regular_leading,
    )
    _progress(
        f"{sector}: built joint coupling transpose "
        f"{coupling_t.nrows()}x{coupling_t.ncols()} for "
        f"{len(channels)} channels"
    )

    shell_preconditioner = output_stem.with_name(
        f"{output_stem.name}_{sector}_shell_preconditioner.npy"
    )
    _progress(f"{sector}: proving the common shifted new shell positive")
    shell_certificate = _certify_positive_matrix(
        matrix=shell,
        label=f"shifted {sector} new shell",
        preconditioner_path=shell_preconditioner,
    )

    solve_started = time.time()
    solution = shell.solve(coupling_t, algorithm="precond")
    solve_seconds = time.time() - solve_started
    residual_started = time.time()
    residual = _verify_solve_residual(shell, solution, coupling_t)
    residual_seconds = time.time() - residual_started
    _progress(
        f"{sector}: all {residual['entry_count']} verified-solve residual "
        "entries contain zero"
    )

    channel_results: list[dict[str, Any]] = []
    for record in channels:
        distance = record["distance"]
        dimension = record["dimension"]
        channel_started = time.time()
        coupling, channel_solution = _copy_channel_blocks(
            coupling_t=coupling_t,
            solution=solution,
            offset=record["offset"],
            dimension=dimension,
        )
        schur = record["energy"] - coupling * channel_solution
        _symmetrize_enclosure(schur)
        schur_seconds = time.time() - channel_started

        preconditioner_path = output_stem.with_name(
            f"{output_stem.name}_{sector}_d{distance}_preconditioner.npy"
        )
        certificate = _certify_positive_matrix(
            matrix=schur,
            label=f"{sector} regular channel distance {distance} Schur",
            preconditioner_path=preconditioner_path,
        )
        channel_results.append(
            {
                "status": "PASS",
                "distance": distance,
                "modes": record["modes"],
                "dimension": dimension,
                "budget": str(record["budget"]),
                "reference_scale": str(record["reference_scale"]),
                "energy_scale": str(record["energy_scale"]),
                "matrix_condition": (
                    "energy_scale*H_source - "
                    "C_source,new*H_new^-1*C_source,new^T is strictly "
                    "positive definite"
                ),
                "discriminant_consequence": (
                    "C_source,new(s,t)^2 < budget * "
                    "reference_scale * H_source(s,s) * H_new(t,t)"
                ),
                "schur_certificate": certificate,
                "timings_seconds": {
                    "schur_enclosure": round(schur_seconds, 3),
                    "total": round(time.time() - channel_started, 3),
                },
            }
        )
        gershgorin = certificate["gershgorin"]
        _progress(
            f"{sector} d={distance} modes={record['modes'][0]}.."
            f"{record['modes'][1]} budget={record['budget']}: PASS "
            f"{gershgorin['strictly_positive_rows']}/"
            f"{gershgorin['dimension']}"
        )
        del coupling, channel_solution, schur, record["energy"]
        gc.collect()

    del shell, coupling_t, solution
    gc.collect()
    return {
        "status": "PASS",
        "sector": sector,
        "new_shell_modes": [middle_cutoff + 1, new_cutoff],
        "shell_construction": shell_construction,
        "channel_construction": channel_construction,
        "shell_certificate": shell_certificate,
        "solve_algorithm": "arb_mat.solve(precond)",
        "solve_residual": residual,
        "channels": channel_results,
        "timings_seconds": {
            "verified_solve": round(solve_seconds, 3),
            "residual_check": round(residual_seconds, 3),
            "total": round(time.time() - started, 3),
        },
    }


def certify(
    *,
    c: int,
    historical_cutoffs: list[int],
    middle_cutoff: int,
    new_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    regular_leading: Fraction,
    exception_budget: Fraction,
    previous_channel_budget: Fraction,
    threads: int,
    validate_cutoff: int | None,
    exception_certificate_path: Path,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if len(historical_cutoffs) < 2:
        raise ValueError("at least two historical cutoffs are required")
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
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if shift_gain <= 0:
        raise ValueError("shift_gain must be strictly positive")
    if not 0 < reference_q < 1:
        raise ValueError("reference_q must lie strictly between zero and one")
    if not 0 < regular_leading < 1:
        raise ValueError(
            "regular_leading must lie strictly between zero and one"
        )
    if not 0 < exception_budget < 1:
        raise ValueError(
            "exception_budget must lie strictly between zero and one"
        )
    if not 0 < previous_channel_budget < 1:
        raise ValueError(
            "previous_channel_budget must lie strictly between zero and one"
        )
    if threads < 1:
        raise ValueError("threads must be positive")
    if validate_cutoff is not None and not (
        1 <= validate_cutoff <= historical_cutoffs[0]
    ):
        raise ValueError(
            "validate_cutoff must lie between one and the base cutoff"
        )

    regular_distance_count = len(historical_cutoffs) - 1
    even_regular_sum = sum(
        regular_leading * Fraction(1, 2) ** distance
        for distance in range(regular_distance_count + 1)
    )
    odd_regular_sum = sum(
        regular_leading * Fraction(1, 2) ** distance
        for distance in range(regular_distance_count)
    )
    odd_with_exception = exception_budget + odd_regular_sum
    infinite_conservative_allocation = exception_budget + 2 * regular_leading
    even_slack = previous_channel_budget - even_regular_sum
    odd_slack = previous_channel_budget - odd_with_exception
    infinite_conservative_slack = (
        previous_channel_budget - infinite_conservative_allocation
    )
    if even_slack <= 0:
        raise ValueError("finite even regular budgets exceed the allocation")
    if odd_slack <= 0:
        raise ValueError(
            "finite odd regular budgets plus the exception exceed the allocation"
        )
    if infinite_conservative_slack <= 0:
        raise ValueError(
            "exception plus the infinite geometric bound exceeds the allocation"
        )

    exception_certificate = _validate_exception_certificate(
        path=exception_certificate_path,
        c=c,
        base_cutoff=historical_cutoffs[0],
        middle_cutoff=middle_cutoff,
        new_cutoff=new_cutoff,
        shift_gain=shift_gain,
        reference_q=reference_q,
        exception_budget=exception_budget,
        regular_leading=regular_leading,
        previous_channel_budget=previous_channel_budget,
    )
    _progress(
        "validated the exceptional odd fixed-base JSON, both linked "
        "preconditioners, and every recorded solve residual"
    )

    ctx.prec = precision
    ctx.threads = threads
    validation = (
        _validate_direct_construction(
            c=c,
            cutoff=validate_cutoff,
            precision=precision,
        )
        if validate_cutoff is not None
        else None
    )
    if validation is not None:
        _progress(
            f"canonical direct-parity replay passed through {validate_cutoff}"
        )

    started = time.time()
    kernel = DirectParityKernel.build(
        c=c,
        cutoff=new_cutoff,
        precision=precision,
    )
    _progress(
        f"built direct-parity kernel through {new_cutoff} in "
        f"{kernel.build_seconds:.3f}s"
    )

    output_stem = json_out.with_suffix("")
    sector_results: list[dict[str, Any]] = []
    for sector in ("even", "odd"):
        sector_results.append(
            _certify_sector(
                kernel=kernel,
                sector=sector,
                historical_cutoffs=historical_cutoffs,
                middle_cutoff=middle_cutoff,
                new_cutoff=new_cutoff,
                shift_gain=shift_gain,
                reference_q=reference_q,
                regular_leading=regular_leading,
                output_stem=output_stem,
            )
        )

    script_path = Path(__file__).resolve()
    direct_script = script_path.with_name(
        "certify_direct_parity_relative_shell.py"
    )
    preconditioned_script = script_path.with_name(
        "certify_preconditioned_relative_shell.py"
    )
    odd_script = script_path.with_name("certify_odd_fixed_base_channel.py")
    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "rigorous finite direct-parity interval certificates for all nine "
            "regular previous-core source channels at the first "
            "1920-to-3840 transition"
        ),
        "c": c,
        "historical_cutoffs": historical_cutoffs,
        "middle_cutoff": middle_cutoff,
        "new_cutoff": new_cutoff,
        "new_shell_modes": [middle_cutoff + 1, new_cutoff],
        "precision_bits": precision,
        "flint_threads": threads,
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "regular_leading": str(regular_leading),
        "exception_budget": str(exception_budget),
        "previous_channel_budget": str(previous_channel_budget),
        "regular_channel_count": sum(
            len(sector["channels"]) for sector in sector_results
        ),
        "budget_allocation": {
            "regular_formula": "q_d = regular_leading * (1/2)^d",
            "even_regular_sum": str(even_regular_sum),
            "even_slack_inside_previous_channel": str(even_slack),
            "odd_regular_sum": str(odd_regular_sum),
            "odd_regular_plus_exception": str(odd_with_exception),
            "odd_slack_inside_previous_channel": str(odd_slack),
            "infinite_conservative_exception_plus_two_leading": str(
                infinite_conservative_allocation
            ),
            "infinite_conservative_slack": str(
                infinite_conservative_slack
            ),
            "all_strict": True,
        },
        "exception_certificate": exception_certificate,
        "direct_formula_validation": validation,
        "kernel": {
            "cutoff": new_cutoff,
            "precision_bits": precision,
            "prime_powers": [
                {"q": q, "base_prime": p}
                for q, p in kernel.prime_powers
            ],
            "prime_power_count": len(kernel.prime_powers),
            "one_dimensional_prime_aggregation": True,
            "build_seconds": round(kernel.build_seconds, 3),
        },
        "sectors": sector_results,
        "matrix_condition": (
            "for each regular source channel, the reverse Schur block "
            "[[energy_scale*H_source,C],[C^T,H_new]] is strictly positive "
            "definite"
        ),
        "proof_chain": [
            "the exception JSON, source hashes, linked NPY hashes, positivity rows, and residual counts replay exactly",
            "direct Arb formulas enclose the exact even and odd parity entries",
            "the full prime sum is retained in aggregated interval sequences",
            "the canonical cutoff replay encloses zero in every direct-minus-canonical entry",
            "an exact-dyadic congruence proves each common shifted new shell positive",
            "one Arb verified solve encloses all regular inverse actions per sector",
            "every verified-solve residual interval contains exact zero",
            "Arb arithmetic encloses every symmetric reverse Schur complement",
            "exact-dyadic congruences prove all nine channel Schur complements positive",
            "the block discriminants give the nine finite relative coupling inequalities",
        ],
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_finsetChannelBudgets",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_exception_and_finsetChannelBudgets",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_v23OddFixedBaseAndDyadicBudgets",
        ],
        "source_dependencies": {
            "direct_parity": _dependency_record(direct_script),
            "preconditioned_schur": _dependency_record(
                preconditioned_script
            ),
            "positive_matrix_helper": _dependency_record(odd_script),
        },
        "timings_seconds": {
            "total": round(time.time() - started, 3),
        },
        "remaining_boundary": (
            "prove the regular dyadic envelope at every scale, compare the "
            "sum of source-band energies with the recursive core energy, and "
            "then discharge the finite middle bridges and closed-tail operator "
            "passage"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument(
        "--historical-cutoffs",
        type=int,
        nargs="+",
        default=[20, 120, 240, 480, 960],
    )
    parser.add_argument("--middle-cutoff", type=int, default=1920)
    parser.add_argument("--new-cutoff", type=int, default=3840)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--reference-q", default="249/250")
    parser.add_argument("--regular-leading", default="1/30")
    parser.add_argument("--exception-budget", default="1/384")
    parser.add_argument("--previous-channel-budget", default="2/27")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--exception-certificate", type=Path, required=True)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument(
        "--validate-cutoff",
        type=int,
        default=12,
        help="small canonical direct-parity replay cutoff; use 0 to omit",
    )
    args = parser.parse_args()

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = certify(
        c=args.c,
        historical_cutoffs=args.historical_cutoffs,
        middle_cutoff=args.middle_cutoff,
        new_cutoff=args.new_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        reference_q=_positive_fraction(args.reference_q, "reference_q"),
        regular_leading=_positive_fraction(
            args.regular_leading, "regular_leading"
        ),
        exception_budget=_positive_fraction(
            args.exception_budget, "exception_budget"
        ),
        previous_channel_budget=_positive_fraction(
            args.previous_channel_budget, "previous_channel_budget"
        ),
        threads=args.threads,
        validate_cutoff=(args.validate_cutoff or None),
        exception_certificate_path=args.exception_certificate,
        json_out=args.json_out,
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
            "git_sha": _git_sha(),
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest().upper(),
        }
    )
    encoded = json.dumps(payload, indent=2, sort_keys=True, allow_nan=False)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")

    print(
        "regular previous-core interval certificate PASS: "
        f"channels={payload['regular_channel_count']}, "
        f"new_shell={payload['new_shell_modes'][0]}.."
        f"{payload['new_shell_modes'][1]}"
    )
    allocation = payload["budget_allocation"]
    print(
        "  even_sum="
        f"{allocation['even_regular_sum']} "
        f"slack={allocation['even_slack_inside_previous_channel']}"
    )
    print(
        "  odd_sum_plus_exception="
        f"{allocation['odd_regular_plus_exception']} "
        f"slack={allocation['odd_slack_inside_previous_channel']}"
    )
    for sector in payload["sectors"]:
        shell_gershgorin = sector["shell_certificate"]["gershgorin"]
        print(
            f"  {sector['sector']} shell: strict_gershgorin="
            f"{shell_gershgorin['strictly_positive_rows']}/"
            f"{shell_gershgorin['dimension']} "
            f"verified_residual="
            f"{sector['solve_residual']['entries_containing_zero']}/"
            f"{sector['solve_residual']['entry_count']}"
        )
        for channel in sector["channels"]:
            gershgorin = channel["schur_certificate"]["gershgorin"]
            print(
                f"    d={channel['distance']} "
                f"modes={channel['modes'][0]}..{channel['modes'][1]} "
                f"budget={channel['budget']} "
                f"strict_gershgorin="
                f"{gershgorin['strictly_positive_rows']}/"
                f"{gershgorin['dimension']}"
            )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
