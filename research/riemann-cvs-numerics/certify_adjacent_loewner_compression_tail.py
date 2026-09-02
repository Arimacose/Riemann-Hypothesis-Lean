#!/usr/bin/env python3
"""Certify scalar residual caps for logarithmic-shift Loewner compression.

For two ordered disjoint intervals, a Mobius map sends their endpoints to
``[-alpha,-1]`` and ``[1,alpha]``.  On the symmetric pair use

    r(w) = product_j (w+s_j)/(w-s_j),
    s_j = alpha**((j+1/2)/k).

If ``t`` lies in ``[1,alpha]``, one logarithmic shift is within half a grid
spacing of ``t``.  Its factor is at most
``tanh(log(alpha)/(4*k))`` and every other factor is at most one.  Symmetry
therefore gives the rigorous Zolotarev-candidate bound

    sup_left |r| / inf_right |r|
      <= tanh(log(alpha)/(4*k))**2.

This script interval-certifies that bound for the fourteen finite adjacent
CvS bridges.  It is the scalar tail component of the rational-compression
route; the small compressed Gram matrices are a separate certificate.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
from flint import arb, ctx


def _fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


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


def _ball(value: arb) -> dict[str, Any]:
    return {
        "arb": str(value),
        "midpoint": float(value.mid()),
        "radius": float(value.rad()),
    }


def _cross_ratio(a: int, b: int, c: int, d: int) -> Fraction:
    if not a < b < c < d:
        raise ValueError(f"interval endpoints are not ordered: {a,b,c,d}")
    return Fraction((c - a) * (d - b), (c - b) * (d - a))


def _geometry_record(
    *,
    label: str,
    endpoints: tuple[int, int, int, int],
    factors: int,
    cap: Fraction,
) -> dict[str, Any]:
    gamma_q = _cross_ratio(*endpoints)
    gamma = _fraction_arb(gamma_q)
    alpha = -1 + 2 * gamma + 2 * (gamma * gamma - gamma).sqrt()
    log_spacing = alpha.log() / factors
    nearest_log_distance = log_spacing / 2
    one_factor_argument = nearest_log_distance / 2
    z_bound = one_factor_argument.tanh() ** 2
    cap_ball = _fraction_arb(cap)
    if not z_bound < cap_ball:
        raise RuntimeError(
            f"{label} compression tail does not separate from cap {cap}"
        )
    return {
        "label": label,
        "ordered_endpoints": list(endpoints),
        "cross_ratio": str(gamma_q),
        "symmetric_alpha": _ball(alpha),
        "factor_count": factors,
        "displacement_rank": 2,
        "compressed_rank_upper": 2 * factors,
        "log_shift_spacing": _ball(log_spacing),
        "nearest_log_shift_distance_upper": _ball(nearest_log_distance),
        "one_factor_tanh_argument": _ball(one_factor_argument),
        "relative_residual_z_upper": _ball(z_bound),
        "rational_cap": str(cap),
        "strict_cap_pass": True,
    }


def certify(
    *,
    start_mode: int,
    bridge_count: int,
    same_factors: int,
    reflected_factors: int,
    same_cap: Fraction,
    reflected_cap: Fraction,
    precision: int,
    threads: int,
) -> dict[str, Any]:
    if start_mode < 1 or bridge_count < 1:
        raise ValueError("start mode and bridge count must be positive")
    if same_factors < 1 or reflected_factors < 1:
        raise ValueError("factor counts must be positive")
    if not 0 < same_cap < 1 or not 0 < reflected_cap < 1:
        raise ValueError("residual caps must lie strictly between zero and one")
    if precision < 128 or threads < 1:
        raise ValueError("precision must be >=128 and threads positive")

    ctx.prec = precision
    ctx.threads = threads
    rows = []
    for index in range(bridge_count):
        mode = start_mode * 2**index
        same = _geometry_record(
            label="same_sign",
            endpoints=(mode + 1, 2 * mode, 2 * mode + 1, 4 * mode),
            factors=same_factors,
            cap=same_cap,
        )
        reflected = _geometry_record(
            label="reflected",
            endpoints=(-4 * mode, -(2 * mode + 1), mode + 1, 2 * mode),
            factors=reflected_factors,
            cap=reflected_cap,
        )
        rows.append(
            {
                "doubling_index": index,
                "mode": mode,
                "middle_shell": [mode + 1, 2 * mode],
                "new_shell": [2 * mode + 1, 4 * mode],
                "same_sign": same,
                "reflected": reflected,
                "combined_compressed_rank_upper": (
                    same["compressed_rank_upper"]
                    + reflected["compressed_rank_upper"]
                ),
            }
        )

    script_path = Path(__file__).resolve()
    return {
        "status": "PASS",
        "rigorous_scalar_interval_audit": True,
        "full_operator_certificate": False,
        "scope": (
            "logarithmic-shift rational residual factors for the finite "
            "adjacent Loewner bridges"
        ),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": _git_sha(),
        "script_sha256": _sha256(script_path),
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "precision_bits": precision,
        "flint_threads": threads,
        "start_mode": start_mode,
        "bridge_count": bridge_count,
        "same_sign_factor_count": same_factors,
        "reflected_factor_count": reflected_factors,
        "same_sign_residual_cap": str(same_cap),
        "reflected_residual_cap": str(reflected_cap),
        "combined_compressed_rank_upper": 2 * same_factors + 2 * reflected_factors,
        "proof_formula": (
            "Z <= tanh(log(alpha)/(4*k))^2 from the nearest logarithmic "
            "shift and unit bounds for all remaining factors"
        ),
        "rows": rows,
        "lean_targets": [
            "RiemannCvs.V23BoundaryWeylMainline.twoLoewnerCompression_posterior",
            "RiemannCvs.V23BoundaryWeylMainline.relativeCoupling_of_twoLoewnerCompression",
        ],
        "remaining_boundary": (
            "interval-certified small compressed Gram matrices, the first "
            "full-energy adjacent bridge, and the infinite form/operator passage"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start-mode", type=int, default=1920)
    parser.add_argument("--bridge-count", type=int, default=14)
    parser.add_argument("--same-factors", type=int, default=64)
    parser.add_argument("--reflected-factors", type=int, default=12)
    parser.add_argument("--same-cap", default="1/200")
    parser.add_argument("--reflected-cap", default="1/4000")
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    payload = certify(
        start_mode=args.start_mode,
        bridge_count=args.bridge_count,
        same_factors=args.same_factors,
        reflected_factors=args.reflected_factors,
        same_cap=Fraction(args.same_cap),
        reflected_cap=Fraction(args.reflected_cap),
        precision=args.prec,
        threads=args.threads,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        "adjacent Loewner compression-tail audit PASS: "
        f"bridges={payload['bridge_count']} rank<="
        f"{payload['combined_compressed_rank_upper']} precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
