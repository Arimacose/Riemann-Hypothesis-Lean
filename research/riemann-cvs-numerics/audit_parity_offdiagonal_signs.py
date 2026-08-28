#!/usr/bin/env python3
"""Audit sign structure of cutoff-free CvS parity blocks.

This is an exploratory structural test for a possible Perron--Frobenius route
to nonvanishing boundary overlaps.  It imports the rigorous Arb matrix builder
from certify_parity_gap.py and counts interval-certified signs of off-diagonal
entries in the exact even/odd reflection blocks.

No RH claim is made.  A failure of a uniform sign pattern is useful: it rules
out the naive Z-matrix shortcut and prevents us from building a proof on an
incorrect Perron hypothesis.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    parity_blocks,
    reflection_symmetric_enclosure,
)


def sign_counts(A):
    positive = negative = straddle = zero = 0
    samples = []
    n = A.nrows()
    for i in range(n):
        for j in range(i + 1, n):
            x = A[i, j]
            if x > 0:
                positive += 1
                sign = "+"
            elif x < 0:
                negative += 1
                sign = "-"
            elif x == 0:
                zero += 1
                sign = "0"
            else:
                straddle += 1
                sign = "?"
            if len(samples) < 40:
                samples.append({
                    "i": i,
                    "j": j,
                    "sign": sign,
                    "mid": x.mid().str(30, radius=False),
                    "rad": x.rad().str(8, radius=False),
                })
    return {
        "positive": positive,
        "negative": negative,
        "zero": zero,
        "straddle": straddle,
        "all_nonpositive": positive == 0 and straddle == 0,
        "all_nonnegative": negative == 0 and straddle == 0,
        "samples": samples,
    }


def gauge_to_negative(A):
    """Try to find signs eps_i so eps_i eps_j A_ij < 0 for every certified nonzero edge."""
    n = A.nrows()
    eps = [None] * n
    eps[0] = 1
    conflicts = []
    unknown = []
    for seed in range(n):
        if eps[seed] is None:
            eps[seed] = 1
        changed = True
        while changed:
            changed = False
            for i in range(n):
                if eps[i] is None:
                    continue
                for j in range(n):
                    if i == j:
                        continue
                    x = A[i, j]
                    if x > 0:
                        required = -eps[i]
                    elif x < 0:
                        required = eps[i]
                    elif x == 0:
                        continue
                    else:
                        unknown.append((i, j))
                        continue
                    if eps[j] is None:
                        eps[j] = required
                        changed = True
                    elif eps[j] != required:
                        conflicts.append((i, j))
                        return {
                            "exists": False,
                            "signs": eps,
                            "conflicts": conflicts[:20],
                            "unknown_edges": len(set(unknown)),
                        }
    return {
        "exists": len(conflicts) == 0,
        "signs": eps,
        "conflicts": conflicts,
        "unknown_edges": len(set(unknown)),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=20)
    parser.add_argument("--prec", type=int, default=500)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    ctx.prec = args.prec
    raw = build_cutoff_free_matrix(args.c, args.N, args.prec)
    sym = reflection_symmetric_enclosure(raw, args.N)
    even, odd = parity_blocks(sym, args.N)

    result = {
        "status": "PASS",
        "scope": "exploratory sign audit; not a spectral theorem",
        "c": args.c,
        "N": args.N,
        "prec_bits": args.prec,
        "even": sign_counts(even),
        "odd": sign_counts(odd),
        "even_negative_gauge": gauge_to_negative(even),
        "odd_negative_gauge": gauge_to_negative(odd),
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "c": args.c,
        "N": args.N,
        "even": {k: v for k, v in result["even"].items() if k != "samples"},
        "odd": {k: v for k, v in result["odd"].items() if k != "samples"},
        "even_negative_gauge_exists": result["even_negative_gauge"]["exists"],
        "odd_negative_gauge_exists": result["odd_negative_gauge"]["exists"],
    }, indent=2))


if __name__ == "__main__":
    main()
