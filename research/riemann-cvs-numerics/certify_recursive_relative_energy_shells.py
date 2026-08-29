#!/usr/bin/env python3
"""Certify a recursive finite-shell route for the V23 relative-energy form.

Fix a low cutoff and the shifted cutoff-free CvS parity form

    A - x I = [[L, B], [B^T, H]].

The base certificate proves positive definiteness of

    R_q = [[q L, B], [B^T, H]]

through ``base_cutoff``.  Each later stage splits the corresponding principal
section of ``R_q`` into the already certified core and one new shell,

    R_q = [[R_core, C], [C^T, H_shell]],

and certifies positive definiteness of

    [[rho R_core, C], [C^T, H_shell]],       0 < rho < 1.

By the two-variable discriminant this gives

    C(s,t)^2 < rho R_core(s,s) H_shell(t,t),

so the shell glues to the positive core with strict determinant room.  The
script is a rigorous *finite recursive-shell* certificate.  A uniform analytic
bound for every later shell and the closed-form limit are separate targets.
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
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    certified_inertia,
    parity_blocks,
    reflection_symmetric_enclosure,
    result_to_json,
    shifted,
)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    return value


def _fraction_arb(value: Fraction) -> arb:
    """Construct an exact rational Arb ball after selecting the precision."""
    return arb(value.numerator) / value.denominator


def _parse_stage(text: str) -> tuple[int, Fraction]:
    """Parse ``CUTOFF:RHO`` for one recursive shell."""
    try:
        cutoff_text, rho_text = text.split(":", 1)
        cutoff = int(cutoff_text)
        rho = _positive_fraction(rho_text, "shell rho")
    except (TypeError, ValueError) as exc:
        raise argparse.ArgumentTypeError(
            "stage must have the form CUTOFF:RHO, for example 240:1/3"
        ) from exc
    if cutoff < 1:
        raise argparse.ArgumentTypeError("stage cutoff must be positive")
    if not rho < 1:
        raise argparse.ArgumentTypeError("shell rho must be strictly below one")
    return cutoff, rho


def _leading_principal(A: arb_mat, dimension: int) -> arb_mat:
    if not 0 < dimension <= A.nrows() or A.nrows() != A.ncols():
        raise ValueError("invalid leading-principal dimension")
    return arb_mat(
        dimension,
        dimension,
        [A[i, j] for i in range(dimension) for j in range(dimension)],
    )


def _relative_block_matrix(A: arb_mat, low_dimension: int, q: arb) -> arb_mat:
    """Return ``R_q`` by scaling only the retained low/low block."""
    dimension = A.nrows()
    if A.ncols() != dimension or not 0 < low_dimension < dimension:
        raise ValueError("relative-energy split must be nonempty and proper")
    out = arb_mat(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            out[i, j] = (
                q * A[i, j]
                if i < low_dimension and j < low_dimension
                else A[i, j]
            )
    return out


def _scaled_core_matrix(A: arb_mat, core_dimension: int, rho: arb) -> arb_mat:
    """Return ``[[rho*R_core,C],[C^T,H_shell]]`` from a section of ``R_q``."""
    dimension = A.nrows()
    if A.ncols() != dimension or not 0 < core_dimension < dimension:
        raise ValueError("recursive core must be nonempty and proper")
    out = arb_mat(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            out[i, j] = (
                rho * A[i, j]
                if i < core_dimension and j < core_dimension
                else A[i, j]
            )
    return out


def _certify_positive(name: str, matrix: arb_mat) -> dict[str, Any]:
    started = time.time()
    result = certified_inertia(matrix)
    if (
        not result.certified
        or result.n_neg != 0
        or result.n_pos != matrix.nrows()
    ):
        raise RuntimeError(
            f"{name}: positive-definite certificate failed: "
            f"pos={result.n_pos} neg={result.n_neg} "
            f"undetermined={result.undetermined_pivot}"
        )
    record = result_to_json(result)
    record["seconds"] = round(time.time() - started, 3)
    return record


def _parity_dimension(sector: str, cutoff: int) -> int:
    return cutoff + 1 if sector == "even" else cutoff


def certify(
    *,
    c: int,
    low_cutoff: int,
    base_cutoff: int,
    stages: list[tuple[int, Fraction]],
    precision: int,
    shift_gain: Fraction,
    q_upper: Fraction,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if low_cutoff < 1 or base_cutoff <= low_cutoff:
        raise ValueError("require 1 <= low_cutoff < base_cutoff")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < q_upper < 1:
        raise ValueError("q_upper must lie strictly between zero and one")
    if not stages:
        raise ValueError("at least one recursive shell stage is required")

    previous = base_cutoff
    for cutoff, rho in stages:
        if cutoff <= previous:
            raise ValueError("stage cutoffs must be strictly increasing")
        if not 0 < rho < 1:
            raise ValueError("every shell rho must lie strictly between zero and one")
        previous = cutoff

    ctx.prec = precision
    shift_ball = _fraction_arb(shift_gain)
    q_ball = _fraction_arb(q_upper)
    rho_balls = [_fraction_arb(rho) for _, rho in stages]

    largest_cutoff = stages[-1][0]
    started = time.time()
    raw = build_cutoff_free_matrix(c, largest_cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, largest_cutoff)
    even, odd = parity_blocks(symmetric, largest_cutoff)

    sector_records: list[dict[str, Any]] = []
    for sector, block, low_dimension in (
        ("even", even, low_cutoff + 1),
        ("odd", odd, low_cutoff),
    ):
        shifted_block = shifted(block, -shift_ball)
        base_dimension = _parity_dimension(sector, base_cutoff)
        base_section = _leading_principal(shifted_block, base_dimension)
        base_relative = _relative_block_matrix(
            base_section, low_dimension, q_ball
        )
        base_record = _certify_positive(
            f"{sector} base through {base_cutoff}", base_relative
        )
        base_record.update(
            {
                "kind": "base_relative_energy",
                "cutoff": base_cutoff,
                "dimension": base_dimension,
                "low_dimension": low_dimension,
                "high_dimension": base_dimension - low_dimension,
                "matrix_condition": "[[q*L,B],[B^T,H]] is positive definite",
                "discriminant_consequence": (
                    "B(w,z)^2 < q*L(w,w)*H(z,z) on the base section"
                ),
            }
        )

        shell_records: list[dict[str, Any]] = []
        core_cutoff = base_cutoff
        for (shell_cutoff, rho), rho_ball in zip(
            stages, rho_balls, strict=True
        ):
            shell_dimension = _parity_dimension(sector, shell_cutoff)
            core_dimension = _parity_dimension(sector, core_cutoff)
            shell_section = _leading_principal(
                shifted_block, shell_dimension
            )
            shell_relative = _relative_block_matrix(
                shell_section, low_dimension, q_ball
            )
            recursive_matrix = _scaled_core_matrix(
                shell_relative, core_dimension, rho_ball
            )
            shell_record = _certify_positive(
                f"{sector} shell {core_cutoff}->{shell_cutoff}",
                recursive_matrix,
            )
            shell_record.update(
                {
                    "kind": "recursive_shell",
                    "core_cutoff": core_cutoff,
                    "shell_cutoff": shell_cutoff,
                    "dimension": shell_dimension,
                    "core_dimension": core_dimension,
                    "shell_dimension": shell_dimension - core_dimension,
                    "rho_upper": str(rho),
                    "matrix_condition": (
                        "[[rho*R_core,C],[C^T,H_shell]] is positive definite"
                    ),
                    "discriminant_consequence": (
                        "C(s,t)^2 < rho*R_core(s,s)*H_shell(t,t)"
                    ),
                    "gluing_consequence": (
                        "rho<1 glues the new shell to the positive R_core"
                    ),
                }
            )
            shell_records.append(shell_record)
            core_cutoff = shell_cutoff

        sector_records.append(
            {
                "sector": sector,
                "base": base_record,
                "shells": shell_records,
                "final_cutoff": core_cutoff,
                "final_dimension": _parity_dimension(sector, core_cutoff),
            }
        )

    return {
        "status": "PASS",
        "scope": (
            "rigorous finite recursive-shell relative-energy certificate; "
            "not a uniform all-cutoff theorem"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "base_cutoff": base_cutoff,
        "largest_cutoff": largest_cutoff,
        "precision_bits": precision,
        "right_endpoint_x": f"-{shift_gain}",
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
        "stages": [
            {"cutoff": cutoff, "rho_upper": str(rho)}
            for cutoff, rho in stages
        ],
        "domain_extension": (
            "for x <= -shift_gain every certified scaled block gains a "
            "positive diagonal, so the same certificates remain valid"
        ),
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.twoBlockEnergy_nonnegative",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_scaledFormNonnegative",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_recursiveShell",
        ],
        "sectors": sector_records,
        "total_seconds": round(time.time() - started, 3),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--base-cutoff", type=int, default=120)
    parser.add_argument(
        "--stage",
        action="append",
        type=_parse_stage,
        default=None,
        help="recursive shell CUTOFF:RHO; may be repeated",
    )
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--q-upper", default="999/1000")
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    stages = args.stage or [(240, Fraction(1, 3)), (480, Fraction(1, 5))]
    payload = certify(
        c=args.c,
        low_cutoff=args.low_cutoff,
        base_cutoff=args.base_cutoff,
        stages=stages,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        q_upper=_positive_fraction(args.q_upper, "q_upper"),
    )
    payload.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(
                timespec="seconds"
            ),
            "python_version": platform.python_version(),
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
        "recursive relative-energy shell certificate PASS: "
        f"c={args.c}, Nlow={args.low_cutoff}, "
        f"Nbase={args.base_cutoff}, Nmax={payload['largest_cutoff']}, "
        f"q<{payload['q_upper']}, x<=-{payload['shift_gain']}"
    )
    for sector in payload["sectors"]:
        base = sector["base"]
        print(
            f"  {sector['sector']} base: dimension={base['dimension']} "
            f"positive_pivots={base['n_pos']} "
            f"transcript={base['pivot_transcript_sha256']}"
        )
        for shell in sector["shells"]:
            print(
                f"  {sector['sector']} shell "
                f"{shell['core_cutoff']}->{shell['shell_cutoff']}: "
                f"rho<{shell['rho_upper']} dimension={shell['dimension']} "
                f"positive_pivots={shell['n_pos']} "
                f"transcript={shell['pivot_transcript_sha256']}"
            )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
