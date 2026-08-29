#!/usr/bin/env python3
"""Certify a finite nested-cutoff relative-energy CvS coupling bound.

For one parity block of the shifted cutoff-free CvS matrix, write

    A - x I = [[L, B], [B^T, H]]

where the first block retains modes through ``low_cutoff`` and the full matrix
uses ``big_cutoff``.  A positive-definite interval LDL certificate for

    [[q L, B], [B^T, H]]

proves, by the discriminant of the corresponding two-variable quadratic form,

    B(w,z)^2 < q * L(w,w) * H(z,z).

The certificate is checked at ``x = -shift_gain``.  For every more negative
``x`` the same block matrix only gains the positive diagonal
``diag(q*t I, t I)``, so the bound extends to the whole left compact/tail
domain.  This script is a rigorous *finite* nested-cutoff certificate; the
all-cutoff operator estimate remains a separate analytic theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

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
    """Construct an exact rational Arb ball at the already selected precision."""
    return arb(value.numerator) / value.denominator


def relative_block_matrix(A: arb_mat, low_dim: int, q: arb) -> arb_mat:
    """Return ``[[q L, B], [B^T, H]]`` for the leading low block."""
    dim = A.nrows()
    if A.ncols() != dim:
        raise ValueError("relative block input must be square")
    if not 0 < low_dim < dim:
        raise ValueError("low block must be nonempty and proper")

    out = arb_mat(dim, dim)
    for i in range(dim):
        for j in range(dim):
            out[i, j] = q * A[i, j] if i < low_dim and j < low_dim else A[i, j]
    return out


def certify_sector(
    name: str,
    shifted_block: arb_mat,
    low_dim: int,
    q: arb,
) -> dict[str, Any]:
    """Certify the scaled block matrix positive definite by interval LDL."""
    started = time.time()
    relative_matrix = relative_block_matrix(shifted_block, low_dim, q)
    result = certified_inertia(relative_matrix)
    if (
        not result.certified
        or result.n_neg != 0
        or result.n_pos != relative_matrix.nrows()
    ):
        raise RuntimeError(
            f"{name}: relative block certificate failed: "
            f"pos={result.n_pos} neg={result.n_neg} "
            f"undetermined={result.undetermined_pivot}"
        )

    record = result_to_json(result)
    record.update(
        {
            "sector": name,
            "dimension": relative_matrix.nrows(),
            "low_dimension": low_dim,
            "high_dimension": relative_matrix.nrows() - low_dim,
            "seconds": round(time.time() - started, 3),
            "matrix_condition": "[[q*L, B], [B^T, H]] is positive definite",
            "discriminant_consequence": (
                "B(w,z)^2 < q*L(w,w)*H(z,z) for every nonzero pair"
            ),
        }
    )
    return record


def certify(
    *,
    c: int,
    low_cutoff: int,
    big_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    q_upper: Fraction,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if low_cutoff < 1:
        raise ValueError("low_cutoff must be positive")
    if big_cutoff <= low_cutoff:
        raise ValueError("big_cutoff must exceed low_cutoff")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < q_upper < 1:
        raise ValueError("q_upper must lie strictly between zero and one")

    # Set the Arb precision before constructing either rational certificate
    # parameter.  Constructing them first would retain the default-radius ball
    # and can make a later high-precision LDL pivot indeterminate.
    ctx.prec = precision
    shift_ball = _fraction_arb(shift_gain)
    q_ball = _fraction_arb(q_upper)

    started = time.time()
    raw = build_cutoff_free_matrix(c, big_cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, big_cutoff)
    even, odd = parity_blocks(symmetric, big_cutoff)

    # shifted(A, t) forms A-tI.  The right endpoint is x=-shift_gain.
    even_shifted = shifted(even, -shift_ball)
    odd_shifted = shifted(odd, -shift_ball)
    sectors = [
        certify_sector("even", even_shifted, low_cutoff + 1, q_ball),
        certify_sector("odd", odd_shifted, low_cutoff, q_ball),
    ]

    return {
        "status": "PASS",
        "scope": (
            "rigorous finite nested-cutoff relative-energy certificate; "
            "not an all-cutoff theorem"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "big_cutoff": big_cutoff,
        "precision_bits": precision,
        "right_endpoint_x": f"-{shift_gain}",
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
        "q_upper_decimal": str(float(q_upper)),
        "block_identity": "A-xI = [[L,B],[B^T,H]]",
        "certificate_matrix": "[[q*L,B],[B^T,H]]",
        "domain_extension": (
            "for x <= -shift_gain the certified matrix gains "
            "diag(q*t*I_low, t*I_high) with t >= 0"
        ),
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_formGrowth",
            "RiemannCvs.BoundaryWeylSchurTail.boundaryWeyl_mono_of_relativeEnergyCoupling",
            "RiemannCvs.BoundaryWeylSchurTail.positiveOn_of_relativeEnergyCoupling",
        ],
        "sectors": sectors,
        "total_seconds": round(time.time() - started, 3),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--big-cutoff", type=int, default=120)
    parser.add_argument("--prec", type=int, default=2000)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--q-upper", default="999/1000")
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    shift_gain = _positive_fraction(args.shift_gain, "shift_gain")
    q_upper = _positive_fraction(args.q_upper, "q_upper")
    payload = certify(
        c=args.c,
        low_cutoff=args.low_cutoff,
        big_cutoff=args.big_cutoff,
        precision=args.prec,
        shift_gain=shift_gain,
        q_upper=q_upper,
    )

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    args.json_out.write_text(encoded, encoding="utf-8")
    digest = hashlib.sha256(args.json_out.read_bytes()).hexdigest().upper()

    print(
        "relative-energy certificate PASS: "
        f"c={args.c}, Nlow={args.low_cutoff}, Nbig={args.big_cutoff}, "
        f"q<{q_upper}, x<=-{shift_gain}"
    )
    for sector in payload["sectors"]:
        print(
            f"  {sector['sector']}: dimension={sector['dimension']} "
            f"positive_pivots={sector['n_pos']} "
            f"transcript={sector['pivot_transcript_sha256']}"
        )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
