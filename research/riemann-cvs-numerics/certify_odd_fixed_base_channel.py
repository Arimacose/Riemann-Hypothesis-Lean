#!/usr/bin/env python3
"""Certify the exceptional odd fixed-base/new-shell CvS channel.

The previous-core midpoint decomposition for the ``1920 -> 3840`` transition
isolates one channel that narrowly misses the convenient pure geometric
envelope: odd modes ``[1, 20]`` coupled directly to the new shell
``[1921, 3840]``.  This script upgrades that one route-selection datum to a
rigorous finite interval certificate.

For the shifted odd parity form ``H`` it constructs, entirely with direct Arb
parity formulas,

    A = exception_budget * reference_q * H_[1,base_cutoff],
    C = H_[1,base_cutoff],[middle_cutoff+1,new_cutoff],
    B = H_[middle_cutoff+1,new_cutoff].

It then proves the block matrix ``[[A, C], [C^T, B]]`` strictly positive
definite.  An exact-dyadic congruence first proves ``A > 0``.  Arb's verified
solve then encloses ``A^-1 C`` with every residual interval containing zero.
Arb arithmetic encloses the symmetric Schur complement, and a second exact-
dyadic congruence proves that complement positive by strict Gershgorin margins.

Consequently, for every pair of real coefficient vectors ``s,t``,

    C(s,t)^2
      < exception_budget
        * (reference_q * H_base)(s,s)
        * H_new(t,t).

Floating Cholesky is used only to select two bases.  Every selected float is
embedded into Arb as an exact dyadic value before either positivity check, so
the floating computation is not proof evidence.  A small canonical replay also
requires every direct-minus-canonical Arb entry interval to contain exact zero.

The optional rational allocation fields record the downstream Lean condition

    exception_budget + 2 * regular_leading < previous_channel_budget

consumed by
``relativeCoupling_of_finiteException_and_dyadicChannelBudgets``.  They do not
assert the still-open all-scale regular dyadic envelope.
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
from typing import Any

import flint
import numpy as np
from flint import arb, arb_mat, ctx

from certify_direct_parity_relative_shell import (
    DirectParityKernel,
    _validate_direct_construction,
)
from certify_preconditioned_relative_shell import (
    _exact_upper_triangular,
    _fraction_arb,
    _gershgorin_certificate,
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
    _verify_solve_residual,
)


def _progress(message: str) -> None:
    print(f"[odd-fixed-base] {message}", flush=True)


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


def _build_odd_fixed_base_blocks(
    *,
    kernel: DirectParityKernel,
    base_cutoff: int,
    middle_cutoff: int,
    new_cutoff: int,
    shift_gain: arb,
    reference_q: arb,
    exception_budget: arb,
) -> tuple[arb_mat, arb_mat, arb_mat, dict[str, Any]]:
    """Build the scaled base, crossblock, and new-shell interval matrices."""

    started = time.time()
    base_modes = list(range(1, base_cutoff + 1))
    new_shell_modes = list(range(middle_cutoff + 1, new_cutoff + 1))
    base_dimension = len(base_modes)
    shell_dimension = len(new_shell_modes)
    scaled_base = arb_mat(base_dimension, base_dimension)
    coupling = arb_mat(base_dimension, shell_dimension)
    shell = arb_mat(shell_dimension, shell_dimension)
    base_scale = reference_q * exception_budget

    for i, k in enumerate(base_modes):
        for j in range(i, base_dimension):
            ell = base_modes[j]
            value = kernel.parity_entry("odd", k, ell)
            if i == j:
                value += shift_gain
            value *= base_scale
            scaled_base[i, j] = value
            scaled_base[j, i] = value

    for i, k in enumerate(base_modes):
        for j, ell in enumerate(new_shell_modes):
            coupling[i, j] = kernel.parity_entry("odd", k, ell)

    for i, k in enumerate(new_shell_modes):
        for j in range(i, shell_dimension):
            ell = new_shell_modes[j]
            value = kernel.parity_entry("odd", k, ell)
            if i == j:
                value += shift_gain
            shell[i, j] = value
            shell[j, i] = value

    upper_base = base_dimension * (base_dimension + 1) // 2
    upper_shell = shell_dimension * (shell_dimension + 1) // 2
    return scaled_base, coupling, shell, {
        "sector": "odd",
        "base_modes": [base_modes[0], base_modes[-1]],
        "skipped_middle_modes": [base_cutoff + 1, middle_cutoff],
        "new_shell_modes": [new_shell_modes[0], new_shell_modes[-1]],
        "base_dimension": base_dimension,
        "shell_dimension": shell_dimension,
        "direct_entry_evaluations": (
            upper_base
            + base_dimension * shell_dimension
            + upper_shell
        ),
        "allocated_arb_entries": (
            base_dimension * base_dimension
            + base_dimension * shell_dimension
            + shell_dimension * shell_dimension
        ),
        "avoided_full_matrix_entries": (2 * new_cutoff + 1) ** 2,
        "formula": "odd[k,l]=A[k,l]-A[k,-l]",
        "seconds": round(time.time() - started, 3),
    }


def _certify_positive_matrix(
    *,
    matrix: arb_mat,
    label: str,
    preconditioner_path: Path,
) -> dict[str, Any]:
    """Prove one symmetric Arb matrix positive by an exact congruence."""

    dimension = matrix.nrows()
    if matrix.ncols() != dimension:
        raise ValueError(f"{label} matrix must be square")

    midpoint_started = time.time()
    midpoint = _midpoint_numpy(matrix)
    cholesky = np.linalg.cholesky(midpoint)
    preconditioner_midpoint = np.triu(np.linalg.inv(cholesky.T))
    midpoint_seconds = time.time() - midpoint_started
    del midpoint, cholesky

    preconditioner_path.parent.mkdir(parents=True, exist_ok=True)
    np.save(preconditioner_path, preconditioner_midpoint, allow_pickle=False)
    reloaded = np.load(preconditioner_path, allow_pickle=False)
    if not np.array_equal(reloaded, preconditioner_midpoint):
        raise RuntimeError(
            f"saved {label} preconditioner does not replay byte-for-byte"
        )
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
    preconditioned = preconditioner.transpose() * (
        matrix * preconditioner
    )
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
        },
        "gershgorin": gershgorin,
        "proof_consequence": (
            "the fixed exact-dyadic congruence is strictly diagonally "
            "dominant with positive diagonal, so the symmetric matrix is "
            "strictly positive definite"
        ),
        "timings_seconds": {
            "midpoint_basis_selection": round(midpoint_seconds, 3),
            "exact_dyadic_embedding": round(exact_seconds, 3),
            "arb_congruence": round(congruence_seconds, 3),
            "gershgorin": round(gershgorin_seconds, 3),
        },
    }


def certify(
    *,
    c: int,
    base_cutoff: int,
    middle_cutoff: int,
    new_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    exception_budget: Fraction,
    candidate_regular_leading: Fraction,
    previous_channel_budget: Fraction,
    threads: int,
    validate_cutoff: int | None,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if not 1 <= base_cutoff < middle_cutoff < new_cutoff:
        raise ValueError(
            "require 1 <= base_cutoff < middle_cutoff < new_cutoff"
        )
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if shift_gain <= 0:
        raise ValueError("shift_gain must be strictly positive")
    if not 0 < reference_q < 1:
        raise ValueError("reference_q must lie strictly between zero and one")
    if not 0 < exception_budget < 1:
        raise ValueError(
            "exception_budget must lie strictly between zero and one"
        )
    if candidate_regular_leading <= 0:
        raise ValueError("candidate_regular_leading must be strictly positive")
    if not 0 < previous_channel_budget < 1:
        raise ValueError(
            "previous_channel_budget must lie strictly between zero and one"
        )
    if threads < 1:
        raise ValueError("threads must be positive")
    if validate_cutoff is not None and not 1 <= validate_cutoff <= base_cutoff:
        raise ValueError(
            "validate_cutoff must lie between one and base_cutoff"
        )

    allocated_budget = exception_budget + 2 * candidate_regular_leading
    allocation_slack = previous_channel_budget - allocated_budget
    if allocation_slack <= 0:
        raise ValueError(
            "exception_budget + 2*candidate_regular_leading must be "
            "strictly below previous_channel_budget"
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

    scaled_base, coupling, shell, construction = (
        _build_odd_fixed_base_blocks(
            kernel=kernel,
            base_cutoff=base_cutoff,
            middle_cutoff=middle_cutoff,
            new_cutoff=new_cutoff,
            shift_gain=_fraction_arb(shift_gain),
            reference_q=_fraction_arb(reference_q),
            exception_budget=_fraction_arb(exception_budget),
        )
    )
    _progress(
        f"constructed {construction['direct_entry_evaluations']} exact-form "
        f"entries in {construction['seconds']:.3f}s"
    )

    stem = json_out.with_suffix("")
    base_preconditioner_path = stem.with_name(
        stem.name + "_base_preconditioner.npy"
    )
    schur_preconditioner_path = stem.with_name(
        stem.name + "_schur_preconditioner.npy"
    )

    _progress("proving the scaled odd fixed-base block positive")
    base_certificate = _certify_positive_matrix(
        matrix=scaled_base,
        label="exception_budget * reference_q * shifted odd fixed base",
        preconditioner_path=base_preconditioner_path,
    )

    _progress(
        f"verified solve {scaled_base.nrows()}x{scaled_base.ncols()} by "
        f"{coupling.nrows()}x{coupling.ncols()}"
    )
    solve_started = time.time()
    solution = scaled_base.solve(coupling, algorithm="precond")
    solve_seconds = time.time() - solve_started
    residual_started = time.time()
    residual = _verify_solve_residual(
        scaled_base,
        solution,
        coupling,
    )
    residual_seconds = time.time() - residual_started
    _progress(
        f"all {residual['entry_count']} verified-solve residual entries "
        "contain zero"
    )

    schur_started = time.time()
    schur = shell - coupling.transpose() * solution
    _symmetrize_enclosure(schur)
    schur_seconds = time.time() - schur_started
    del scaled_base, coupling, shell, solution
    gc.collect()
    _progress(
        f"enclosed the {schur.nrows()}x{schur.ncols()} Schur complement in "
        f"{schur_seconds:.3f}s"
    )

    _progress("proving the Schur complement positive")
    schur_certificate = _certify_positive_matrix(
        matrix=schur,
        label="odd fixed-base/new-shell Schur complement",
        preconditioner_path=schur_preconditioner_path,
    )
    del schur
    gc.collect()

    script_path = Path(__file__).resolve()
    direct_script = script_path.with_name(
        "certify_direct_parity_relative_shell.py"
    )
    preconditioned_script = script_path.with_name(
        "certify_preconditioned_relative_shell.py"
    )
    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "rigorous finite direct-parity interval certificate for the "
            "exceptional odd fixed-base/new-shell previous-core channel"
        ),
        "c": c,
        "sector": "odd",
        "base_cutoff": base_cutoff,
        "middle_cutoff": middle_cutoff,
        "new_cutoff": new_cutoff,
        "base_modes": [1, base_cutoff],
        "new_shell_modes": [middle_cutoff + 1, new_cutoff],
        "precision_bits": precision,
        "flint_threads": threads,
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "exception_budget": str(exception_budget),
        "candidate_regular_leading": str(candidate_regular_leading),
        "previous_channel_budget": str(previous_channel_budget),
        "budget_allocation": {
            "identity": (
                "exception_budget + 2*candidate_regular_leading "
                "< previous_channel_budget"
            ),
            "allocated": str(allocated_budget),
            "slack": str(allocation_slack),
            "strict": True,
            "conditional_regular_input": (
                "the regular dyadic source coefficients still need a proof "
                "of q_i <= candidate_regular_leading*(1/2)^i"
            ),
        },
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
        "construction": construction,
        "matrix_condition": (
            "[[exception_budget*reference_q*H_base,C],"
            "[C^T,H_new]] is strictly positive definite"
        ),
        "discriminant_consequence": (
            "C_base(s,t)^2 < exception_budget * "
            "(reference_q*H_base)(s,s) * H_new(t,t)"
        ),
        "base_certificate": base_certificate,
        "solve_algorithm": "arb_mat.solve(precond)",
        "solve_residual": residual,
        "schur_certificate": schur_certificate,
        "proof_chain": [
            "direct Arb formulas enclose the exact odd parity entries",
            "the full prime sum is retained in aggregated interval sequences",
            "an exact-dyadic congruence proves the scaled fixed base positive",
            "Arb verified solve encloses the fixed-base inverse action",
            "every verified-solve residual interval contains exact zero",
            "Arb arithmetic encloses the symmetric Schur complement",
            "a second exact-dyadic congruence proves the Schur complement positive",
            "the block discriminant gives the exceptional relative coupling bound",
        ],
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_exception_and_finsetChannelBudgets",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_finiteException_and_dyadicChannelBudgets",
        ],
        "source_dependencies": {
            "direct_parity": _dependency_record(direct_script),
            "preconditioned_schur": _dependency_record(
                preconditioned_script
            ),
        },
        "timings_seconds": {
            "kernel_and_block_construction": construction["seconds"],
            "verified_solve": round(solve_seconds, 3),
            "residual_check": round(residual_seconds, 3),
            "schur_enclosure": round(schur_seconds, 3),
            "total": round(time.time() - started, 3),
        },
        "remaining_boundary": (
            "the all-scale regular previous-core dyadic envelope, its energy "
            "normalization, and the closed-tail operator passage remain "
            "separate analytic obligations"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--base-cutoff", type=int, default=20)
    parser.add_argument("--middle-cutoff", type=int, default=1920)
    parser.add_argument("--new-cutoff", type=int, default=3840)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--reference-q", default="249/250")
    parser.add_argument("--exception-budget", default="1/384")
    parser.add_argument("--candidate-regular-leading", default="1/30")
    parser.add_argument("--previous-channel-budget", default="2/27")
    parser.add_argument("--threads", type=int, default=1)
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
        base_cutoff=args.base_cutoff,
        middle_cutoff=args.middle_cutoff,
        new_cutoff=args.new_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        reference_q=_positive_fraction(args.reference_q, "reference_q"),
        exception_budget=_positive_fraction(
            args.exception_budget,
            "exception_budget",
        ),
        candidate_regular_leading=_positive_fraction(
            args.candidate_regular_leading,
            "candidate_regular_leading",
        ),
        previous_channel_budget=_positive_fraction(
            args.previous_channel_budget,
            "previous_channel_budget",
        ),
        threads=args.threads,
        validate_cutoff=(args.validate_cutoff or None),
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
        "odd fixed-base interval certificate PASS: "
        f"modes=1..{args.base_cutoff}, "
        f"new_shell={args.middle_cutoff + 1}..{args.new_cutoff}, "
        f"exception_budget={payload['exception_budget']}"
    )
    print(
        "  allocation="
        f"{payload['budget_allocation']['allocated']} "
        f"slack={payload['budget_allocation']['slack']}"
    )
    for key in ("base_certificate", "schur_certificate"):
        certificate = payload[key]
        gershgorin = certificate["gershgorin"]
        print(
            f"  {key}: strict_gershgorin="
            f"{gershgorin['strictly_positive_rows']}/"
            f"{gershgorin['dimension']} "
            f"transcript={gershgorin['margin_transcript_sha256']}"
        )
    print(
        "  verified_residual="
        f"{payload['solve_residual']['entries_containing_zero']}/"
        f"{payload['solve_residual']['entry_count']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
