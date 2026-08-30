#!/usr/bin/env python3
"""Certify one large recursive relative-energy shell by a Schur argument.

The existing recursive certificate proves that the scaled core form

    R_q(K) = [[q L, B_K], [B_K^T, H_K]]

is positive definite through ``core_cutoff``.  For one new shell this script
constructs the exact-form Arb enclosure of

    M = [[rho R_q(K), C], [C^T, H_shell]],       0 < rho < 1.

Instead of replaying a cubic Python-level interval LDL factorization on the
whole enlarged matrix, it performs the following rigorous chain:

1. validate and hash the prior positive-core certificate;
2. use Arb's verified preconditioned solve to enclose
   ``X = (rho R_q(K))^-1 C``;
3. enclose the symmetric Schur complement ``S = H_shell - C^T X``;
4. compute a floating Cholesky preconditioner only as a *choice* of basis;
5. convert that basis to one fixed exact dyadic upper-triangular matrix ``P``;
6. enclose the exact congruence ``P^T S P`` with Arb;
7. prove every Gershgorin lower margin strictly positive.

The exact dyadic ``P`` is invertible because all of its diagonal entries are
strictly positive.  Positive definiteness of ``P^T S P`` therefore proves
positive definiteness of ``S``; the Schur-complement theorem then proves that
``M`` is positive definite.  The floating calculation never supplies a proof
step: it only selects the exact dyadic preconditioner subsequently checked by
Arb interval arithmetic.
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


def _fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _parity_dimension(sector: str, cutoff: int) -> int:
    return cutoff + 1 if sector == "even" else cutoff


def _midpoint_numpy(matrix: arb_mat) -> np.ndarray:
    return np.array(
        [
            [float(matrix[i, j].mid()) for j in range(matrix.ncols())]
            for i in range(matrix.nrows())
        ],
        dtype=np.float64,
    )


def _exact_dyadic(value: float) -> arb:
    """Embed one finite float as its exact binary rational value."""
    if not math.isfinite(value):
        raise ValueError("preconditioner contains a non-finite entry")
    numerator, denominator = value.as_integer_ratio()
    exact = arb(numerator) / denominator
    if exact.rad() != 0:
        raise RuntimeError("dyadic embedding unexpectedly acquired a radius")
    return exact


def _exact_upper_triangular(matrix: np.ndarray) -> arb_mat:
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("preconditioner must be square")
    dimension = matrix.shape[0]
    exact = arb_mat(dimension, dimension)
    for i in range(dimension):
        for j in range(i, dimension):
            exact[i, j] = _exact_dyadic(float(matrix[i, j]))
    return exact


def _build_sector_blocks(
    block: arb_mat,
    *,
    low_dimension: int,
    core_dimension: int,
    shift_gain: arb,
    q: arb,
    rho: arb,
) -> tuple[arb_mat, arb_mat, arb_mat]:
    """Return ``rho R_core``, the core/shell coupling, and ``H_shell``."""
    full_dimension = block.nrows()
    if block.ncols() != full_dimension:
        raise ValueError("parity block must be square")
    if not 0 < low_dimension < core_dimension < full_dimension:
        raise ValueError("invalid low/core/shell dimensions")
    shell_dimension = full_dimension - core_dimension

    core = arb_mat(core_dimension, core_dimension)
    coupling = arb_mat(core_dimension, shell_dimension)
    shell = arb_mat(shell_dimension, shell_dimension)

    for i in range(core_dimension):
        for j in range(core_dimension):
            value = block[i, j] + (shift_gain if i == j else 0)
            if i < low_dimension and j < low_dimension:
                value *= q
            core[i, j] = rho * value

    for i in range(core_dimension):
        for j in range(shell_dimension):
            coupling[i, j] = block[i, core_dimension + j]

    for i in range(shell_dimension):
        for j in range(shell_dimension):
            shell[i, j] = block[core_dimension + i, core_dimension + j] + (
                shift_gain if i == j else 0
            )

    return core, coupling, shell


def _symmetrize_enclosure(matrix: arb_mat) -> None:
    """Average transpose-related balls enclosing the same exact entry."""
    if matrix.nrows() != matrix.ncols():
        raise ValueError("symmetrization requires a square matrix")
    for i in range(matrix.nrows()):
        for j in range(i + 1, matrix.ncols()):
            value = (matrix[i, j] + matrix[j, i]) / 2
            matrix[i, j] = value
            matrix[j, i] = value


def _validate_core_certificate(
    path: Path,
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shift_gain: Fraction,
    q_upper: Fraction,
) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    expected = {
        "status": "PASS",
        "c": c,
        "low_cutoff": low_cutoff,
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
    }
    for key, value in expected.items():
        if payload.get(key) != value:
            raise ValueError(
                f"core certificate field {key!r}: "
                f"expected {value!r}, got {payload.get(key)!r}"
            )

    certified_cutoff = payload.get("largest_cutoff")
    if not isinstance(certified_cutoff, int) or certified_cutoff < core_cutoff:
        raise ValueError(
            "core certificate does not reach the requested core cutoff"
        )

    source_script = Path(__file__).with_name(
        "certify_recursive_relative_energy_shells.py"
    )
    source_hash = hashlib.sha256(source_script.read_bytes()).hexdigest()
    if payload.get("script_sha256") != source_hash:
        raise ValueError(
            "core certificate script hash does not match the tracked "
            "recursive-shell certifier"
        )

    github_sha = os.environ.get("GITHUB_SHA")
    if github_sha is not None and payload.get("git_sha") != github_sha:
        raise ValueError("core certificate git_sha does not match GITHUB_SHA")

    sectors = {sector.get("sector"): sector for sector in payload["sectors"]}
    if set(sectors) != {"even", "odd"}:
        raise ValueError("core certificate must contain even and odd sectors")

    sector_records: list[dict[str, Any]] = []
    for sector_name in ("even", "odd"):
        sector = sectors[sector_name]
        expected_dimension = _parity_dimension(sector_name, certified_cutoff)
        if sector.get("final_cutoff") != certified_cutoff:
            raise ValueError(f"{sector_name} core certificate ends at wrong cutoff")
        if sector.get("final_dimension") != expected_dimension:
            raise ValueError(f"{sector_name} core certificate has wrong dimension")

        components = [sector["base"], *sector["shells"]]
        for component in components:
            if not component.get("certified"):
                raise ValueError(f"{sector_name} contains an uncertified component")
            if component.get("n_neg") != 0:
                raise ValueError(f"{sector_name} contains a negative pivot")
            if component.get("undetermined_pivot") is not None:
                raise ValueError(f"{sector_name} contains an undetermined pivot")
            if component.get("n_pos") != component.get("dimension"):
                raise ValueError(f"{sector_name} component is not positive definite")

        sector_records.append(
            {
                "sector": sector_name,
                "final_dimension": expected_dimension,
                "component_transcript_sha256": [
                    component["pivot_transcript_sha256"]
                    for component in components
                ],
            }
        )

    return {
        "path": str(path.resolve()),
        "sha256": _sha256(path),
        "script_sha256": source_hash,
        "git_sha": payload.get("git_sha"),
        "precision_bits": payload.get("precision_bits"),
        "certified_through_cutoff": certified_cutoff,
        "requested_core_cutoff": core_cutoff,
        "principal_submatrix_consequence": (
            "positive definiteness through the certified cutoff implies "
            "positive definiteness of the requested leading core section"
        ),
        "sectors": sector_records,
    }


def _verify_solve_residual(
    core: arb_mat,
    solution: arb_mat,
    coupling: arb_mat,
) -> dict[str, Any]:
    residual = core * solution - coupling
    total = residual.nrows() * residual.ncols()
    contains_zero = 0
    max_midpoint_abs = 0.0
    max_radius = 0.0
    for i in range(residual.nrows()):
        for j in range(residual.ncols()):
            value = residual[i, j]
            if value.contains(0):
                contains_zero += 1
            max_midpoint_abs = max(
                max_midpoint_abs, abs(float(value.mid()))
            )
            max_radius = max(max_radius, float(value.rad()))
    if contains_zero != total:
        raise RuntimeError(
            "verified solve residual has an entry whose enclosure misses zero"
        )
    return {
        "entry_count": total,
        "entries_containing_zero": contains_zero,
        "max_midpoint_abs": max_midpoint_abs,
        "max_radius": max_radius,
    }


def _gershgorin_certificate(matrix: arb_mat) -> dict[str, Any]:
    if matrix.nrows() != matrix.ncols():
        raise ValueError("Gershgorin certificate requires a square matrix")
    transcripts: list[str] = []
    min_midpoint = math.inf
    max_radius = 0.0
    for i in range(matrix.nrows()):
        off_diagonal = arb(0)
        for j in range(matrix.ncols()):
            if i == j:
                continue
            symmetric_entry = (matrix[i, j] + matrix[j, i]) / 2
            off_diagonal += abs(symmetric_entry)
        margin = matrix[i, i] - off_diagonal
        if not margin > 0:
            raise RuntimeError(
                f"preconditioned Gershgorin margin {i} is not strictly positive"
            )
        midpoint = float(margin.mid())
        radius = float(margin.rad())
        min_midpoint = min(min_midpoint, midpoint)
        max_radius = max(max_radius, radius)
        transcripts.append(
            f"{i} + {margin.mid().str(50, radius=False)} "
            f"{margin.rad().str(12, radius=False)}"
        )

    encoded = "\n".join(transcripts).encode("utf-8")
    return {
        "dimension": matrix.nrows(),
        "strictly_positive_rows": matrix.nrows(),
        "min_margin_midpoint": min_midpoint,
        "max_margin_radius": max_radius,
        "margin_transcript_sha256": hashlib.sha256(encoded).hexdigest(),
        "margins": transcripts,
    }


def _certify_sector(
    *,
    sector: str,
    block: arb_mat,
    low_dimension: int,
    core_cutoff: int,
    shell_cutoff: int,
    shift_gain: arb,
    q: arb,
    rho: arb,
    preconditioner_path: Path,
) -> dict[str, Any]:
    started = time.time()
    core_dimension = _parity_dimension(sector, core_cutoff)
    full_dimension = _parity_dimension(sector, shell_cutoff)
    if block.nrows() != full_dimension:
        raise ValueError(f"{sector} parity block has the wrong dimension")

    block_started = time.time()
    core, coupling, shell = _build_sector_blocks(
        block,
        low_dimension=low_dimension,
        core_dimension=core_dimension,
        shift_gain=shift_gain,
        q=q,
        rho=rho,
    )
    block_seconds = time.time() - block_started

    solve_started = time.time()
    solution = core.solve(coupling, algorithm="precond")
    solve_seconds = time.time() - solve_started

    residual_started = time.time()
    residual_record = _verify_solve_residual(core, solution, coupling)
    residual_seconds = time.time() - residual_started

    schur_started = time.time()
    schur = shell - coupling.transpose() * solution
    _symmetrize_enclosure(schur)
    schur_seconds = time.time() - schur_started

    midpoint_started = time.time()
    schur_midpoint = _midpoint_numpy(schur)
    cholesky = np.linalg.cholesky(schur_midpoint)
    preconditioner_midpoint = np.triu(np.linalg.inv(cholesky.T))
    midpoint_seconds = time.time() - midpoint_started

    preconditioner_path.parent.mkdir(parents=True, exist_ok=True)
    np.save(preconditioner_path, preconditioner_midpoint, allow_pickle=False)
    reloaded = np.load(preconditioner_path, allow_pickle=False)
    if not np.array_equal(reloaded, preconditioner_midpoint):
        raise RuntimeError("saved preconditioner does not replay byte-for-byte")

    exact_started = time.time()
    preconditioner = _exact_upper_triangular(preconditioner_midpoint)
    diagonal_midpoints: list[float] = []
    for i in range(preconditioner.nrows()):
        diagonal = preconditioner[i, i]
        if diagonal.rad() != 0 or not diagonal > 0:
            raise RuntimeError(
                "exact dyadic preconditioner has a nonpositive diagonal"
            )
        diagonal_midpoints.append(float(diagonal.mid()))
    exact_seconds = time.time() - exact_started

    congruence_started = time.time()
    preconditioned = preconditioner.transpose() * (
        schur * preconditioner
    )
    congruence_seconds = time.time() - congruence_started

    gershgorin_started = time.time()
    gershgorin = _gershgorin_certificate(preconditioned)
    gershgorin_seconds = time.time() - gershgorin_started

    return {
        "sector": sector,
        "status": "PASS",
        "core_dimension": core_dimension,
        "shell_dimension": full_dimension - core_dimension,
        "full_dimension": full_dimension,
        "solve_algorithm": "arb_mat.solve(precond)",
        "solve_residual": residual_record,
        "preconditioner": {
            "path": str(preconditioner_path.resolve()),
            "sha256": _sha256(preconditioner_path),
            "dtype": str(preconditioner_midpoint.dtype),
            "shape": list(preconditioner_midpoint.shape),
            "storage": "NumPy .npy; each float is embedded as an exact dyadic",
            "upper_triangular": True,
            "all_dyadic_radii_zero": True,
            "all_diagonal_entries_positive": True,
            "min_diagonal_midpoint": min(diagonal_midpoints),
        },
        "gershgorin": gershgorin,
        "proof_consequence": (
            "the exact dyadic congruence is strictly positive definite; "
            "hence the Schur complement and the enlarged recursive-shell "
            "matrix are positive definite"
        ),
        "timings_seconds": {
            "build_blocks": round(block_seconds, 3),
            "verified_solve": round(solve_seconds, 3),
            "residual_check": round(residual_seconds, 3),
            "schur_enclosure": round(schur_seconds, 3),
            "midpoint_preconditioner": round(midpoint_seconds, 3),
            "exact_dyadic_embedding": round(exact_seconds, 3),
            "arb_congruence": round(congruence_seconds, 3),
            "gershgorin": round(gershgorin_seconds, 3),
            "total": round(time.time() - started, 3),
        },
    }


def certify(
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shell_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    q_upper: Fraction,
    rho_upper: Fraction,
    core_certificate_path: Path,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if not 1 <= low_cutoff < core_cutoff < shell_cutoff:
        raise ValueError(
            "require 1 <= low_cutoff < core_cutoff < shell_cutoff"
        )
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < q_upper < 1:
        raise ValueError("q_upper must lie strictly between zero and one")
    if not 0 < rho_upper < 1:
        raise ValueError("rho_upper must lie strictly between zero and one")

    core_certificate = _validate_core_certificate(
        core_certificate_path,
        c=c,
        low_cutoff=low_cutoff,
        core_cutoff=core_cutoff,
        shift_gain=shift_gain,
        q_upper=q_upper,
    )

    started = time.time()
    ctx.prec = precision
    shift_ball = _fraction_arb(shift_gain)
    q_ball = _fraction_arb(q_upper)
    rho_ball = _fraction_arb(rho_upper)

    matrix_started = time.time()
    raw = build_cutoff_free_matrix(c, shell_cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, shell_cutoff)
    del raw
    gc.collect()
    even, odd = parity_blocks(symmetric, shell_cutoff)
    matrix_seconds = time.time() - matrix_started
    del symmetric
    gc.collect()

    stem = json_out.with_suffix("")
    even_preconditioner = stem.with_name(
        stem.name + "_even_preconditioner.npy"
    )
    odd_preconditioner = stem.with_name(
        stem.name + "_odd_preconditioner.npy"
    )

    even_record = _certify_sector(
        sector="even",
        block=even,
        low_dimension=low_cutoff + 1,
        core_cutoff=core_cutoff,
        shell_cutoff=shell_cutoff,
        shift_gain=shift_ball,
        q=q_ball,
        rho=rho_ball,
        preconditioner_path=even_preconditioner,
    )
    del even
    gc.collect()

    odd_record = _certify_sector(
        sector="odd",
        block=odd,
        low_dimension=low_cutoff,
        core_cutoff=core_cutoff,
        shell_cutoff=shell_cutoff,
        shift_gain=shift_ball,
        q=q_ball,
        rho=rho_ball,
        preconditioner_path=odd_preconditioner,
    )
    del odd
    gc.collect()

    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "rigorous finite preconditioned-Schur interval certificate for "
            "one recursive relative-energy shell"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "core_cutoff": core_cutoff,
        "shell_cutoff": shell_cutoff,
        "largest_cutoff": shell_cutoff,
        "precision_bits": precision,
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
        "rho_upper": str(rho_upper),
        "core_certificate": core_certificate,
        "matrix_condition": (
            "[[rho*R_q(core),C],[C^T,H_shell]] is positive definite"
        ),
        "discriminant_consequence": (
            "C(s,t)^2 < rho*R_q(core)(s,s)*H_shell(t,t)"
        ),
        "gluing_consequence": (
            "rho<1 glues the shell to the certified positive core and "
            "preserves the same q relative-energy coefficient"
        ),
        "proof_chain": [
            "prior core artifact certifies R_q(core) positive definite",
            "rho>0 certifies rho*R_q(core) positive definite",
            "Arb verified solve encloses (rho*R_q(core))^-1*C",
            "Arb arithmetic encloses the exact symmetric Schur complement",
            "a fixed exact dyadic upper-triangular preconditioner is invertible",
            "every preconditioned Gershgorin lower margin is strictly positive",
            "Schur complement and enlarged recursive-shell matrix are positive definite",
        ],
        "sectors": [even_record, odd_record],
        "matrix_construction_seconds": round(matrix_seconds, 3),
        "total_seconds": round(time.time() - started, 3),
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.twoBlockEnergy_nonnegative",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_recursiveShell",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--core-cutoff", type=int, required=True)
    parser.add_argument("--shell-cutoff", type=int, required=True)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--q-upper", default="249/250")
    parser.add_argument("--rho-upper", required=True)
    parser.add_argument("--core-certificate", type=Path, required=True)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = certify(
        c=args.c,
        low_cutoff=args.low_cutoff,
        core_cutoff=args.core_cutoff,
        shell_cutoff=args.shell_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        q_upper=_positive_fraction(args.q_upper, "q_upper"),
        rho_upper=_positive_fraction(args.rho_upper, "rho_upper"),
        core_certificate_path=args.core_certificate,
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
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )

    encoded = json.dumps(payload, indent=2, sort_keys=True)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")
    digest = _sha256(args.json_out)

    print(
        "preconditioned recursive-shell certificate PASS: "
        f"c={args.c}, core={args.core_cutoff}, shell={args.shell_cutoff}, "
        f"q<{payload['q_upper']}, rho<{payload['rho_upper']}, "
        f"x<=-{payload['shift_gain']}"
    )
    for sector in payload["sectors"]:
        gershgorin = sector["gershgorin"]
        print(
            f"  {sector['sector']}: dimension={sector['full_dimension']} "
            f"schur_dimension={sector['shell_dimension']} "
            f"strict_gershgorin={gershgorin['strictly_positive_rows']}/"
            f"{gershgorin['dimension']} "
            f"transcript={gershgorin['margin_transcript_sha256']}"
        )
        print(
            f"    preconditioner={sector['preconditioner']['path']} "
            f"sha256={sector['preconditioner']['sha256']}"
        )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
