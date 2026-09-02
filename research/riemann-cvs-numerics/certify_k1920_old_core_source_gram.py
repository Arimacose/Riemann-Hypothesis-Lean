#!/usr/bin/env python3
"""Certify the K1920 old-core/new-shell channel from a source-side Gram.

The rebalanced first boundary--Weyl bridge separates the already constructed
old core ``[0, 1920]`` (``[1, 1920]`` in the odd sector) from the new shell
``[3841, 7680]``.  A direct Schur certificate would allocate the complete
target energy matrix and prove a 3840-dimensional Schur complement positive.
That is unnecessary once the target shell has an analytic Euclidean floor.

For the complete direct-parity crossblock ``C`` and the shifted recursive
source reference ``R_q`` this script instead proves

    C C^T < beta R_q.

The matrix ``C`` contains the combined Archimedean/prime Loewner terms, the
rank-one pole term, and (in the even sector) the normalized zero-mode row.
Thus no componentwise triangle inequality discards cancellation.  Finite
Cauchy--Schwarz gives

    |s^T C t|^2 <= beta R_q(s,s) ||t||_2^2.

Together with the separately kernel-checked target floor

    (351629/96000) ||t||_2^2 <= H_new(t,t)

and ``beta=13/100 <= (1/28)*(351629/96000)``, this yields the stronger
old-core relative coefficient ``1/28``.  In particular, it strictly improves
the previously requested ``1/15`` allocation.

Every matrix entry is an Arb interval.  Floating Cholesky is used only to
select an upper-triangular basis for the positive margin
``beta R_q - C C^T``.  The saved doubles are replayed byte-for-byte, embedded
as exact radius-zero dyadics, and the resulting congruence is proved positive
by strict interval Gershgorin rows.  An optional small canonical replay also
requires every direct-minus-canonical parity interval to contain exact zero.
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
from certify_direct_parity_relative_shell import (
    DirectParityKernel,
    _sector_modes,
    _validate_direct_construction,
)
from certify_odd_fixed_base_channel import _certify_positive_matrix
from certify_preconditioned_relative_shell import (
    _fraction_arb,
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
)
from flint import arb, arb_mat, ctx

Sector = Literal["even", "odd"]


def _progress(message: str) -> None:
    print(f"[k1920-old-core-source-gram] {message}", flush=True)


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


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def _dependency_record(path: Path) -> dict[str, str]:
    return {
        "path": str(path.resolve()),
        "sha256": _sha256(path.resolve()),
    }


def _build_source_and_coupling(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    low_cutoff: int,
    source_cutoff: int,
    target_start: int,
    target_cutoff: int,
    shift_gain: arb,
    q: arb,
    beta: arb,
) -> tuple[arb_mat, arb_mat, dict[str, Any]]:
    """Build ``beta*R_q(source)`` and the complete source/target crossblock."""

    started = time.time()
    source_modes = list(_sector_modes(sector, source_cutoff))
    target_modes = list(range(target_start, target_cutoff + 1))
    source_dimension = len(source_modes)
    target_dimension = len(target_modes)
    scaled_source = arb_mat(source_dimension, source_dimension)
    coupling = arb_mat(source_dimension, target_dimension)

    for i, k in enumerate(source_modes):
        for j in range(i, source_dimension):
            ell = source_modes[j]
            value = kernel.parity_entry(sector, k, ell)
            if i == j:
                value += shift_gain
            if k <= low_cutoff and ell <= low_cutoff:
                value *= q
            value *= beta
            scaled_source[i, j] = value
            scaled_source[j, i] = value

    for i, k in enumerate(source_modes):
        for j, ell in enumerate(target_modes):
            coupling[i, j] = kernel.parity_entry(sector, k, ell)

    upper_source = source_dimension * (source_dimension + 1) // 2
    return scaled_source, coupling, {
        "sector": sector,
        "source_modes": [source_modes[0], source_modes[-1]],
        "omitted_middle_modes": [source_cutoff + 1, target_start - 1],
        "target_modes": [target_modes[0], target_modes[-1]],
        "source_dimension": source_dimension,
        "target_dimension": target_dimension,
        "direct_entry_evaluations": (
            upper_source + source_dimension * target_dimension
        ),
        "allocated_arb_entries": (
            source_dimension * source_dimension
            + source_dimension * target_dimension
        ),
        "formula": (
            "even[k,l]=A[k,l]+A[k,-l]; "
            "odd[k,l]=A[k,l]-A[k,-l]"
        ),
        "source_reference": (
            "shifted direct parity form with its low-low block multiplied by q"
        ),
        "coupling_scope": (
            "complete direct-parity crossblock: combined Archimedean/prime "
            "Loewner terms, pole term, and normalized even zero mode"
        ),
        "seconds": round(time.time() - started, 3),
    }


def certify(
    *,
    c: int,
    low_cutoff: int,
    source_cutoff: int,
    target_start: int,
    target_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    q_upper: Fraction,
    beta_upper: Fraction,
    target_floor: Fraction,
    relative_budget: Fraction,
    sectors: tuple[Sector, ...],
    threads: int,
    validate_cutoff: int | None,
    diagnose_midpoint_threshold: bool,
    json_out: Path,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if not 1 <= low_cutoff < source_cutoff < target_start <= target_cutoff:
        raise ValueError(
            "require 1 <= low_cutoff < source_cutoff < target_start <= "
            "target_cutoff"
        )
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if shift_gain <= 0:
        raise ValueError("shift_gain must be strictly positive")
    if not 0 < q_upper < 1:
        raise ValueError("q_upper must lie strictly between zero and one")
    if beta_upper <= 0 or target_floor <= 0 or relative_budget <= 0:
        raise ValueError("beta, target floor, and relative budget must be positive")
    if beta_upper > relative_budget * target_floor:
        raise ValueError(
            "beta_upper must not exceed relative_budget * target_floor"
        )
    if not sectors or any(sector not in ("even", "odd") for sector in sectors):
        raise ValueError("sectors must be a nonempty subset of even/odd")
    if len(set(sectors)) != len(sectors):
        raise ValueError("sectors must not contain duplicates")
    if threads < 1:
        raise ValueError("threads must be positive")
    if validate_cutoff is not None and not 1 <= validate_cutoff <= source_cutoff:
        raise ValueError(
            "validate_cutoff must lie between one and source_cutoff"
        )

    ctx.prec = precision
    ctx.threads = threads
    validation = (
        _validate_direct_construction(
            c=c, cutoff=validate_cutoff, precision=precision
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
        c=c, cutoff=target_cutoff, precision=precision
    )
    _progress(
        f"built direct-parity kernel through {target_cutoff} in "
        f"{kernel.build_seconds:.3f}s"
    )

    shift_ball = _fraction_arb(shift_gain)
    q_ball = _fraction_arb(q_upper)
    beta_ball = _fraction_arb(beta_upper)
    stem = json_out.with_suffix("")
    sector_records: list[dict[str, Any]] = []

    for sector in sectors:
        sector_started = time.time()
        _progress(f"{sector}: constructing beta*R_q and the complete coupling")
        scaled_source, coupling, construction = _build_source_and_coupling(
            kernel=kernel,
            sector=sector,
            low_cutoff=low_cutoff,
            source_cutoff=source_cutoff,
            target_start=target_start,
            target_cutoff=target_cutoff,
            shift_gain=shift_ball,
            q=q_ball,
            beta=beta_ball,
        )
        _progress(
            f"{sector}: constructed {construction['direct_entry_evaluations']} "
            f"exact-form entries in {construction['seconds']:.3f}s"
        )

        gram_started = time.time()
        _progress(
            f"{sector}: enclosing C*C^T as a "
            f"{scaled_source.nrows()}x{scaled_source.ncols()} source Gram"
        )
        source_gram = coupling * coupling.transpose()
        _symmetrize_enclosure(source_gram)
        gram_seconds = time.time() - gram_started
        del coupling
        gc.collect()
        _progress(f"{sector}: source Gram enclosed in {gram_seconds:.3f}s")

        midpoint_diagnostic: dict[str, Any] | None = None
        if diagnose_midpoint_threshold:
            diagnostic_started = time.time()
            _progress(
                f"{sector}: diagnosing the midpoint generalized Gram threshold"
            )
            scaled_source_midpoint = _midpoint_numpy(scaled_source)
            source_gram_midpoint = _midpoint_numpy(source_gram)
            cholesky = np.linalg.cholesky(scaled_source_midpoint)
            inverse_cholesky = np.linalg.inv(cholesky)
            whitened = inverse_cholesky @ source_gram_midpoint @ inverse_cholesky.T
            whitened = (whitened + whitened.T) / 2
            relative_to_scaled_source = float(np.linalg.eigvalsh(whitened)[-1])
            estimated_beta = float(beta_upper) * relative_to_scaled_source
            midpoint_diagnostic = {
                "rigorous_certificate": False,
                "role": "route-selection diagnostic only",
                "largest_generalized_eigenvalue_relative_to_beta_Rq": (
                    relative_to_scaled_source
                ),
                "estimated_minimal_beta_midpoint": estimated_beta,
                "candidate_beta_midpoint_slack": (
                    float(beta_upper) - estimated_beta
                ),
                "seconds": round(time.time() - diagnostic_started, 3),
            }
            _progress(
                f"{sector}: midpoint beta threshold is approximately "
                f"{estimated_beta:.12g}"
            )
            del (
                scaled_source_midpoint,
                source_gram_midpoint,
                cholesky,
                inverse_cholesky,
                whitened,
            )
            gc.collect()

        margin_started = time.time()
        margin = scaled_source - source_gram
        _symmetrize_enclosure(margin)
        margin_seconds = time.time() - margin_started
        del scaled_source, source_gram
        gc.collect()

        preconditioner_path = stem.with_name(
            stem.name + f"_{sector}_source_gram_margin_preconditioner.npy"
        )
        _progress(f"{sector}: proving beta*R_q-C*C^T strictly positive")
        positivity = _certify_positive_matrix(
            matrix=margin,
            label=f"{sector} beta*R_q minus complete source Gram",
            preconditioner_path=preconditioner_path,
        )
        del margin
        gc.collect()

        sector_records.append(
            {
                "sector": sector,
                "status": "PASS",
                "source_dimension": construction["source_dimension"],
                "target_dimension": construction["target_dimension"],
                "direct_construction": construction,
                "source_gram_product": {
                    "formula": "C*C^T",
                    "dimension": construction["source_dimension"],
                    "symmetric_interval_enclosure": True,
                    "seconds": round(gram_seconds, 3),
                },
                "midpoint_threshold_diagnostic": midpoint_diagnostic,
                "margin_construction_seconds": round(margin_seconds, 3),
                "positive_margin": positivity,
                "matrix_inequality": "C*C^T < beta*R_q(source)",
                "proof_consequence": (
                    "finite Cauchy-Schwarz gives |s^T*C*t|^2 < "
                    "beta*R_q(s,s)*||t||_2^2 for every real s,t"
                ),
                "total_seconds": round(time.time() - sector_started, 3),
            }
        )

    script_path = Path(__file__).resolve()
    direct_script = script_path.with_name(
        "certify_direct_parity_relative_shell.py"
    )
    positivity_script = script_path.with_name(
        "certify_odd_fixed_base_channel.py"
    )
    preconditioned_script = script_path.with_name(
        "certify_preconditioned_relative_shell.py"
    )
    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "rigorous full-coupling source-Gram certificate for the first "
            "old-core/new-shell CvS channel"
        ),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": _git_sha(),
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest().upper(),
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "python_flint_version": flint.__version__,
        "platform": platform.platform(),
        "precision_bits": precision,
        "flint_threads": threads,
        "c": c,
        "low_cutoff": low_cutoff,
        "source_cutoff": source_cutoff,
        "source_modes": {
            "even": [0, source_cutoff],
            "odd": [1, source_cutoff],
        },
        "omitted_middle_modes": [source_cutoff + 1, target_start - 1],
        "target_modes": [target_start, target_cutoff],
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
        "source_gram_beta_upper": str(beta_upper),
        "target_euclidean_floor": str(target_floor),
        "relative_budget": str(relative_budget),
        "budget_arithmetic": {
            "inequality": "beta <= relative_budget * target_floor",
            "left": str(beta_upper),
            "right": str(relative_budget * target_floor),
            "slack": str(relative_budget * target_floor - beta_upper),
            "strict_slack": beta_upper < relative_budget * target_floor,
        },
        "matrix_condition": "beta*R_q(source)-C*C^T is positive definite",
        "direct_formula_validation": validation,
        "kernel": {
            "cutoff": target_cutoff,
            "precision_bits": precision,
            "prime_powers": [
                {"q": q, "base_prime": p} for q, p in kernel.prime_powers
            ],
            "prime_power_count": len(kernel.prime_powers),
            "one_dimensional_prime_aggregation": True,
            "build_seconds": round(kernel.build_seconds, 3),
        },
        "sectors": sector_records,
        "proof_chain": [
            "direct Arb parity formulas enclose every source and cross entry",
            "the crossblock retains the full prime/Archimedean cancellation",
            "Arb multiplication encloses the complete source Gram C*C^T",
            "a fixed exact-dyadic congruence proves beta*R_q-C*C^T positive",
            "finite Cauchy-Schwarz turns the Gram inequality into a cross bound",
            "the Lean target-shell floor converts ||t||_2^2 to target energy",
            "exact rational arithmetic fits the resulting bound inside 1/15",
        ],
        "dependencies": [
            _dependency_record(direct_script),
            _dependency_record(positivity_script),
            _dependency_record(preconditioned_script),
        ],
        "lean_targets": [
            "RiemannCvs.V23BoundaryWeylMainline.relativeCoupling_of_sourceGramAndTargetFloor",
            "RiemannCvs.V23BoundaryWeylMainline.v23_k1920_finiteRectangular_oldCore_relative_oneOver28",
            "RiemannCvs.V23BoundaryWeylMainline.relativeCoupling_of_oneOver28_and_elevenOver135",
        ],
        "total_seconds": round(time.time() - started, 3),
        "remaining_boundary": (
            "bind this finite matrix certificate to the literal Lean parity "
            "matrix interface; later bridges and the closed operator limit "
            "remain separate"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--source-cutoff", type=int, default=1920)
    parser.add_argument("--target-start", type=int, default=3841)
    parser.add_argument("--target-cutoff", type=int, default=7680)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--q-upper", default="249/250")
    parser.add_argument("--beta-upper", default="13/100")
    parser.add_argument("--target-floor", default="351629/96000")
    parser.add_argument("--relative-budget", default="1/28")
    parser.add_argument(
        "--sectors",
        nargs="+",
        choices=("even", "odd"),
        default=["even", "odd"],
    )
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument(
        "--validate-cutoff",
        type=int,
        default=12,
        help="small canonical replay cutoff; use 0 to omit",
    )
    parser.add_argument(
        "--diagnose-midpoint-threshold",
        action="store_true",
        help="compute a non-rigorous generalized-eigenvalue selector diagnostic",
    )
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = certify(
        c=args.c,
        low_cutoff=args.low_cutoff,
        source_cutoff=args.source_cutoff,
        target_start=args.target_start,
        target_cutoff=args.target_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift-gain"),
        q_upper=_positive_fraction(args.q_upper, "q-upper"),
        beta_upper=_positive_fraction(args.beta_upper, "beta-upper"),
        target_floor=_positive_fraction(args.target_floor, "target-floor"),
        relative_budget=_positive_fraction(
            args.relative_budget, "relative-budget"
        ),
        sectors=tuple(args.sectors),
        threads=args.threads,
        validate_cutoff=(args.validate_cutoff or None),
        diagnose_midpoint_threshold=args.diagnose_midpoint_threshold,
        json_out=args.json_out,
    )
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        "K1920 old-core source-Gram certificate PASS: "
        f"sectors={','.join(args.sectors)} beta={payload['source_gram_beta_upper']} "
        f"relative={payload['relative_budget']} precision={payload['precision_bits']}"
    )
    for sector in payload["sectors"]:
        gershgorin = sector["positive_margin"]["gershgorin"]
        print(
            f"  {sector['sector']}: source={sector['source_dimension']} "
            f"target={sector['target_dimension']} "
            f"strict_gershgorin={gershgorin['strictly_positive_rows']}/"
            f"{gershgorin['dimension']} "
            f"transcript={gershgorin['margin_transcript_sha256']}"
        )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
