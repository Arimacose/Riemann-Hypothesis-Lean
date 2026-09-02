#!/usr/bin/env python3
"""Certify the 20-dimensional source-Gram route into shell (15360,30720].

The source is kept in its full shifted/reference geometry.  Only the remote
target uses the analytic 24/5 Euclidean floor.  The certificate proves

    C C^T <= beta * S,  beta = 3/1250,

where S=(249/250)*(H_odd,[1,20]+(1/1024)I).  This implies relative coefficient
1/2000 after division by the target floor, without a 15360-dimensional source
or Schur positivity certificate.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np
from flint import arb_mat, ctx

NUMERIC_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(NUMERIC_DIR))

from certify_direct_parity_relative_shell import (  # noqa: E402
    DirectParityKernel,
    _validate_direct_construction,
)
from certify_finite_source_moment_floor import (  # noqa: E402
    _certify_positive_matrix,
)
from certify_preconditioned_relative_shell import (  # noqa: E402
    _fraction_arb,
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
)


def _progress(message: str) -> None:
    print(f"[fixed-source-gram] {message}", flush=True)


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


def _dependency(path: Path) -> dict[str, str]:
    return {"path": str(path.resolve()), "sha256": _sha256(path.resolve())}


def certify(
    *,
    c: int,
    fixed_cutoff: int,
    target_base: int,
    precision: int,
    threads: int,
    shift_gain: Fraction,
    reference_q: Fraction,
    beta: Fraction,
    relative_budget: Fraction,
    validate_cutoff: int | None,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if fixed_cutoff < 1 or target_base < 2 * fixed_cutoff:
        raise ValueError("require 1 <= fixed_cutoff and 2*fixed_cutoff <= target")
    if precision < 128 or threads < 1:
        raise ValueError("precision must be >=128 and threads positive")
    if min(shift_gain, reference_q, beta, relative_budget) <= 0:
        raise ValueError("all rational parameters must be positive")
    target_floor = Fraction(24, 5)
    if beta != relative_budget * target_floor:
        raise ValueError("beta must equal relative_budget*(24/5)")
    if validate_cutoff is not None and validate_cutoff < 1:
        raise ValueError("validate cutoff must be positive")

    ctx.prec = precision
    ctx.threads = threads
    started = time.time()
    validation = (
        _validate_direct_construction(
            c=c, cutoff=validate_cutoff, precision=precision
        )
        if validate_cutoff is not None
        else None
    )
    if validation is not None:
        _progress(f"canonical replay passed through {validate_cutoff}")

    kernel = DirectParityKernel.build(
        c=c, cutoff=2 * target_base, precision=precision
    )
    _progress(
        f"built direct parity kernel through {2 * target_base} in "
        f"{kernel.build_seconds:.3f}s"
    )

    build_started = time.time()
    source = arb_mat(fixed_cutoff, fixed_cutoff)
    coupling = arb_mat(fixed_cutoff, target_base)
    shift_ball = _fraction_arb(shift_gain)
    reference_ball = _fraction_arb(reference_q)
    for i, p in enumerate(range(1, fixed_cutoff + 1)):
        for j in range(i, fixed_cutoff):
            q = j + 1
            value = kernel.parity_entry("odd", p, q)
            if i == j:
                value += shift_ball
            value *= reference_ball
            source[i, j] = value
            source[j, i] = value
        for j, q in enumerate(range(target_base + 1, 2 * target_base + 1)):
            coupling[i, j] = kernel.parity_entry("odd", p, q)
    block_seconds = time.time() - build_started
    _progress(
        f"built source {fixed_cutoff}x{fixed_cutoff} and coupling "
        f"{fixed_cutoff}x{target_base} in {block_seconds:.3f}s"
    )

    gram_started = time.time()
    coupling_gram = coupling * coupling.transpose()
    certificate_matrix = arb_mat(fixed_cutoff, fixed_cutoff)
    beta_ball = _fraction_arb(beta)
    for i in range(fixed_cutoff):
        for j in range(fixed_cutoff):
            certificate_matrix[i, j] = (
                beta_ball * source[i, j] - coupling_gram[i, j]
            )
    _symmetrize_enclosure(certificate_matrix)
    gram_seconds = time.time() - gram_started
    _progress(f"enclosed beta*S-C*C^T in {gram_seconds:.3f}s")

    midpoint_source = _midpoint_numpy(source)
    midpoint_coupling = _midpoint_numpy(coupling)
    midpoint_certificate = _midpoint_numpy(certificate_matrix)
    source_min = float(np.linalg.eigvalsh(midpoint_source)[0])
    certificate_eigs = np.linalg.eigvalsh(midpoint_certificate)
    chol = np.linalg.cholesky(midpoint_source)
    whitened = np.linalg.solve(chol, midpoint_coupling)
    singular = np.linalg.svd(whitened, compute_uv=False)
    diagnostics = {
        "proof_status": "MIDPOINT_DIAGNOSTIC_ONLY",
        "source_min_eigenvalue": source_min,
        "certificate_min_eigenvalue": float(certificate_eigs[0]),
        "certificate_max_eigenvalue": float(certificate_eigs[-1]),
        "critical_beta_operator_sq": float(singular[0] ** 2),
        "whitened_frobenius_sq": float(np.sum(whitened * whitened)),
        "selected_beta": float(beta),
    }
    del midpoint_source, midpoint_coupling, midpoint_certificate, whitened, singular

    stem = json_out.with_suffix("")
    preconditioner_path = stem.with_name(
        stem.name + "_gram_preconditioner.npy"
    )
    positive = _certify_positive_matrix(
        matrix=certificate_matrix,
        label=(
            f"c={c} odd fixed [1,{fixed_cutoff}] source Gram into "
            f"({target_base},{2*target_base}]"
        ),
        preconditioner_path=preconditioner_path,
    )
    _progress(
        f"strict source-Gram rows: "
        f"{positive['gershgorin']['strictly_positive_rows']}/{fixed_cutoff}"
    )

    script_path = Path(__file__).resolve()
    payload: dict[str, Any] = {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": "fixed-source Gram domination with analytic remote target floor",
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": _git_sha(),
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest().upper(),
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "numpy_version": np.__version__,
        "precision_bits": precision,
        "flint_threads": threads,
        "c": c,
        "fixed_modes": [1, fixed_cutoff],
        "target_modes": [target_base + 1, 2 * target_base],
        "shift_gain": str(shift_gain),
        "reference_q": str(reference_q),
        "beta": str(beta),
        "target_energy_floor": str(target_floor),
        "relative_budget": str(relative_budget),
        "exact_budget_identity": "3/1250 = (1/2000)*(24/5)",
        "matrix_condition": "beta*S - C*C^T is strictly positive definite",
        "source_matrix": (
            "S=(249/250)*(H_odd,[1,20]+(1/1024)I)"
        ),
        "coupling_matrix": (
            "C is the exact odd full-builder block [1,20] x "
            "[15361,30720]"
        ),
        "quadratic_consequence": (
            "sum_j (sum_i C_ij*x_i)^2 <= (3/1250)*"
            "c13OddFixedReferenceEnergy(20,x)"
        ),
        "strict_positive_certificate": positive,
        "midpoint_diagnostics": diagnostics,
        "direct_formula_validation": validation,
        "kernel": {
            "cutoff": kernel.cutoff,
            "prime_power_count": len(kernel.prime_powers),
            "build_seconds": round(kernel.build_seconds, 3),
        },
        "entry_counts": {
            "source_upper_triangle": fixed_cutoff * (fixed_cutoff + 1) // 2,
            "coupling": fixed_cutoff * target_base,
            "gram_accumulation_products": fixed_cutoff * fixed_cutoff * target_base,
        },
        "proof_chain": [
            "direct Arb formulas enclose every source and coupling entry",
            "the shifted source is scaled by the exact reference factor 249/250",
            "Arb matrix multiplication encloses C*C^T",
            "an exact-dyadic congruence proves beta*S-C*C^T positive",
            "finite Cauchy converts Gram domination to a bilinear bound",
            "the Lean analytic target floor 24/5 yields relative cost 1/2000",
        ],
        "lean_targets": [
            "RiemannCvs.V23BoundaryWeylMainline.C13OddFixedSourceGramCertificate",
            "RiemannCvs.V23BoundaryWeylMainline.c13OddFixedRemoteBuilder_20_15360_relative_oneOver2000",
        ],
        "source_dependencies": {
            "direct_parity": _dependency(NUMERIC_DIR / "certify_direct_parity_relative_shell.py"),
            "finite_source": _dependency(NUMERIC_DIR / "certify_finite_source_moment_floor.py"),
            "preconditioner": _dependency(NUMERIC_DIR / "certify_preconditioned_relative_shell.py"),
        },
        "timings_seconds": {
            "block_construction": round(block_seconds, 3),
            "gram_enclosure": round(gram_seconds, 3),
            "total": round(time.time() - started, 3),
        },
        "remaining_boundary": (
            "the fourteen finite middle bridges, recursive coefficient summation, "
            "and infinite boundary-Weyl form/operator limit"
        ),
    }
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--fixed-cutoff", type=int, default=20)
    parser.add_argument("--target-base", type=int, default=15360)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--reference-q", default="249/250")
    parser.add_argument("--beta", default="3/1250")
    parser.add_argument("--relative-budget", default="1/2000")
    parser.add_argument("--validate-cutoff", type=int, default=120)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    payload = certify(
        c=args.c,
        fixed_cutoff=args.fixed_cutoff,
        target_base=args.target_base,
        precision=args.prec,
        threads=args.threads,
        shift_gain=Fraction(args.shift_gain),
        reference_q=Fraction(args.reference_q),
        beta=Fraction(args.beta),
        relative_budget=Fraction(args.relative_budget),
        validate_cutoff=(args.validate_cutoff or None),
        json_out=args.json_out,
    )
    print(
        "fixed source Gram certificate PASS: "
        f"beta={payload['beta']} relative={payload['relative_budget']} "
        f"precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
