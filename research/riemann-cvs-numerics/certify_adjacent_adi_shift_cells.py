#!/usr/bin/env python3
"""Certify concrete ADI root/pole noncollision cells at one adjacent bridge.

The generic Lean telescoping theorem is exact once no source or target grid
point meets an ADI root or pole.  For a bridge mode ``K`` most noncollision
facts follow from the coarse signs/ranges

    same-sign: root < 2 < pole,
    reflected: 0 < root and pole < 0.

Only the target-pole comparisons remain.  For every pole this script proves a
strict integer cell enclosure with Arb,

    m < K * pole < m+1                  (same-sign),
    m < K * (-pole) < m+1               (reflected).

The integer ``m`` is selected from a floating midpoint and is then discarded
as evidence: both strict inequalities are rechecked using the complete Arb
balls.  The production Mobius implementation is also replayed through a
separate inverse cross-ratio formula; every root/pole difference must contain
zero.  Thus the artifact audits both the grid cells and the shift construction,
while the corresponding ``K{mode}AdiShiftBinding`` module turns precisely
these inequalities into the noncollision premises of the exact ADI
factorization theorem.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import platform
import re
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
from certify_adjacent_compressed_gram import _roots_and_poles
from certify_preconditioned_relative_shell import _fraction_arb, _sha256
from flint import arb, ctx

DEFAULT_MODE = 1920
DEFAULT_SAME_FACTORS = 31
DEFAULT_REFLECTED_FACTORS = 12


def _progress(message: str) -> None:
    print(f"[adjacent-adi-shift-cells] {message}", flush=True)


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


def _script_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _interval(value: arb, digits: int = 40) -> dict[str, str]:
    return {
        "ball": value.str(digits, radius=True),
        "lower": value.lower().str(digits, radius=True),
        "upper": value.upper().str(digits, radius=True),
    }


def _strict_positive(value: arb, label: str) -> None:
    if not (arb(0) < value):
        raise RuntimeError(f"strict Arb inequality failed: {label}: {value}")


def _alternative_inverse(
    endpoints: tuple[Fraction, Fraction, Fraction, Fraction],
    alpha: arb,
    value: arb,
) -> arb:
    """Invert the endpoint map using a cross-ratio, not a linear solve.

    If ``y`` is the normalized coordinate and the endpoint map sends
    ``(a,b,c,d)`` to ``(-alpha,-1,1,alpha)``, then

        t = -2(y+alpha) / ((alpha-1)(y-1)),
        u = t(b-a)/(b-c),
        x = (u c-a)/(u-1).

    This gives an algebraically independent replay of the production inverse
    Mobius evaluation used by ``_roots_and_poles``.
    """

    a, b, c, _d = (_fraction_arb(endpoint) for endpoint in endpoints)
    denominator_t = (alpha - 1) * (value - 1)
    if denominator_t.contains(0):
        raise RuntimeError("alternative inverse t-denominator contains zero")
    t = -2 * (value + alpha) / denominator_t
    denominator_bc = b - c
    if denominator_bc.contains(0):
        raise RuntimeError("alternative inverse endpoint denominator contains zero")
    u = t * (b - a) / denominator_bc
    denominator_u = u - 1
    if denominator_u.contains(0):
        raise RuntimeError("alternative inverse u-denominator contains zero")
    return (u * c - a) / denominator_u


def _alternative_roots_and_poles(
    *,
    endpoints: tuple[Fraction, Fraction, Fraction, Fraction],
    factors: int,
    inverse: bool,
) -> tuple[list[arb], list[arb], dict[str, Any]]:
    a, b, c, d = endpoints
    gamma_q = ((c - a) * (d - b)) / ((c - b) * (d - a))
    gamma = _fraction_arb(gamma_q)
    alpha = -1 + 2 * gamma + 2 * (gamma * gamma - gamma).sqrt()
    roots: list[arb] = []
    poles: list[arb] = []
    for index in range(factors):
        exponent = Fraction(2 * index + 1, 2 * factors)
        shift = (alpha.log() * _fraction_arb(exponent)).exp()
        root = _alternative_inverse(endpoints, alpha, -shift)
        pole = _alternative_inverse(endpoints, alpha, shift)
        # The reflected rational function is the reciprocal of the direct one.
        if inverse:
            root, pole = pole, root
        roots.append(root)
        poles.append(pole)
    return roots, poles, {
        "cross_ratio": str(gamma_q),
        "alpha": _interval(alpha),
        "formula": (
            "t=-2*(y+alpha)/((alpha-1)*(y-1)); "
            "u=t*(b-a)/(b-c); x=(u*c-a)/(u-1)"
        ),
        "inverse_rational_function": inverse,
    }


def _candidate_cell(value: arb) -> int:
    midpoint = float(value.mid())
    if not math.isfinite(midpoint):
        raise RuntimeError("cell selector midpoint is not finite")
    return math.floor(midpoint)


def _certify_geometry(
    *,
    mode: int,
    label: str,
    endpoints: tuple[Fraction, Fraction, Fraction, Fraction],
    factors: int,
    inverse: bool,
    reflected: bool,
) -> dict[str, Any]:
    roots, poles, production_geometry = _roots_and_poles(
        endpoints=endpoints, factors=factors, inverse=inverse
    )
    alt_roots, alt_poles, alternative_geometry = _alternative_roots_and_poles(
        endpoints=endpoints, factors=factors, inverse=inverse
    )
    if len(roots) != factors or len(poles) != factors:
        raise RuntimeError(f"{label}: production factor count mismatch")

    entries: list[dict[str, Any]] = []
    cells: list[int] = []
    lower_margins: list[arb] = []
    upper_margins: list[arb] = []
    range_margins: list[arb] = []
    root_residuals: list[arb] = []
    pole_residuals: list[arb] = []

    for index, (production_root, production_pole, root, pole) in enumerate(
        zip(roots, poles, alt_roots, alt_poles, strict=True)
    ):
        # The alternative values are the literal closed formulas mirrored by
        # Lean.  All strict certificate checks below therefore apply directly
        # to the formal shift definitions.  The production values are retained
        # for the independent replay against the factor builder used by the
        # rank-86 Gram certificate.
        root_residual = production_root - root
        pole_residual = production_pole - pole
        if not root_residual.contains(0):
            raise RuntimeError(f"{label}[{index}]: independent root replay misses zero")
        if not pole_residual.contains(0):
            raise RuntimeError(f"{label}[{index}]: independent pole replay misses zero")

        if reflected:
            root_margin = root
            pole_sign_margin = -pole
            _strict_positive(root_margin, f"{label}[{index}] root > 0")
            _strict_positive(pole_sign_margin, f"{label}[{index}] pole < 0")
            scaled_pole = mode * (-pole)
            range_statement = "0 < root and pole < 0"
        else:
            root_margin = 2 - root
            pole_sign_margin = pole - 2
            _strict_positive(root_margin, f"{label}[{index}] root < 2")
            _strict_positive(pole_sign_margin, f"{label}[{index}] 2 < pole")
            scaled_pole = mode * pole
            range_statement = "root < 2 < pole"

        cell = _candidate_cell(scaled_pole)
        lower_margin = scaled_pole - cell
        upper_margin = cell + 1 - scaled_pole
        _strict_positive(lower_margin, f"{label}[{index}] cell lower margin")
        _strict_positive(upper_margin, f"{label}[{index}] cell upper margin")

        cells.append(cell)
        lower_margins.append(lower_margin)
        upper_margins.append(upper_margin)
        range_margins.extend((root_margin, pole_sign_margin))
        root_residuals.append(root_residual)
        pole_residuals.append(pole_residual)
        entries.append(
            {
                "index": index,
                "exponent": str(Fraction(2 * index + 1, 2 * factors)),
                "root": _interval(root),
                "pole": _interval(pole),
                "production_root": _interval(production_root),
                "production_pole": _interval(production_pole),
                "range_statement": range_statement,
                "root_range_margin": _interval(root_margin),
                "pole_sign_margin": _interval(pole_sign_margin),
                "scaled_absolute_pole": _interval(scaled_pole),
                "cell": cell,
                "strict_cell_lower_margin": _interval(lower_margin),
                "strict_cell_upper_margin": _interval(upper_margin),
                "production_minus_literal_root_residual": _interval(root_residual),
                "production_minus_literal_pole_residual": _interval(pole_residual),
            }
        )

    # These minima are selected only after every member has independently
    # passed its strict Arb comparison; they are diagnostic summaries.
    min_lower_index = min(range(factors), key=lambda i: float(lower_margins[i].mid()))
    min_upper_index = min(range(factors), key=lambda i: float(upper_margins[i].mid()))
    min_range_index = min(
        range(2 * factors), key=lambda i: float(range_margins[i].mid())
    )
    cell_bytes = json.dumps(cells, separators=(",", ":")).encode("ascii")
    return {
        "status": "PASS",
        "label": label,
        "endpoints": [str(endpoint) for endpoint in endpoints],
        "factor_count": factors,
        "production_geometry": production_geometry,
        "alternative_geometry": alternative_geometry,
        "production_literal_formula_root_residuals_contain_zero": sum(
            residual.contains(0) for residual in root_residuals
        ),
        "production_literal_formula_pole_residuals_contain_zero": sum(
            residual.contains(0) for residual in pole_residuals
        ),
        "strict_range_checks": 2 * factors,
        "strict_grid_cell_checks": 2 * factors,
        "cells": cells,
        "cells_sha256": hashlib.sha256(cell_bytes).hexdigest().upper(),
        "minimum_cell_lower_margin": {
            "index": min_lower_index,
            "interval": _interval(lower_margins[min_lower_index]),
        },
        "minimum_cell_upper_margin": {
            "index": min_upper_index,
            "interval": _interval(upper_margins[min_upper_index]),
        },
        "minimum_range_margin": {
            "entry_index": min_range_index,
            "factor_index": min_range_index // 2,
            "kind": "root" if min_range_index % 2 == 0 else "pole",
            "interval": _interval(range_margins[min_range_index]),
        },
        "entries": entries,
    }


def _reference_audit(reference_path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    reference = json.loads(reference_path.read_text(encoding="utf-8"))
    if reference.get("status") != "PASS":
        raise RuntimeError("reference artifact is not PASS")
    fields = ("mode", "same_sign_factor_count", "reflected_factor_count")
    for field in fields:
        if reference.get(field) != payload.get(field):
            raise RuntimeError(f"reference mismatch for {field}")
    for geometry in ("same_sign", "reflected"):
        if reference[geometry]["cells"] != payload[geometry]["cells"]:
            raise RuntimeError(f"reference cell transcript mismatch for {geometry}")
        if reference[geometry]["cells_sha256"] != payload[geometry]["cells_sha256"]:
            raise RuntimeError(f"reference cell hash mismatch for {geometry}")
    return {
        "status": "PASS",
        "path": str(reference_path.resolve()),
        "sha256": _sha256(reference_path.resolve()),
        "precision_bits": reference.get("precision_bits"),
        "cell_transcripts_identical": True,
    }


def _lean_literal_cell_audit(
    lean_path: Path, same_cells: list[int], reflected_cells: list[int]
) -> dict[str, Any]:
    """Parse and compare the two literal cell tables in the Lean source."""

    source = lean_path.read_text(encoding="utf-8")

    def extract(definition: str) -> list[int]:
        match = re.search(
            rf"def\s+{re.escape(definition)}\b.*?:=\s*\[(.*?)\]",
            source,
            flags=re.DOTALL,
        )
        if match is None:
            raise RuntimeError(f"Lean cell definition not found: {definition}")
        return [int(value) for value in re.findall(r"\d+", match.group(1))]

    lean_same = extract("samePoleCellList")
    lean_reflected = extract("reflectedPoleCellList")
    if lean_same != same_cells:
        raise RuntimeError("Lean same-sign cell transcript differs from Arb cells")
    if lean_reflected != reflected_cells:
        raise RuntimeError("Lean reflected cell transcript differs from Arb cells")
    return {
        "status": "PASS",
        "path": str(lean_path.resolve()),
        "sha256": _script_hash(lean_path.resolve()),
        "same_sign_entries": len(lean_same),
        "reflected_entries": len(lean_reflected),
        "both_transcripts_identical": True,
    }


def certify(
    *,
    mode: int,
    same_factors: int,
    reflected_factors: int,
    precision: int,
    threads: int,
    reference_json: Path | None,
    lean_path: Path | None,
) -> dict[str, Any]:
    if mode < 1:
        raise ValueError("mode must be positive")
    if same_factors < 1 or reflected_factors < 1:
        raise ValueError("factor counts must be positive")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if threads < 1:
        raise ValueError("thread count must be positive")
    ctx.prec = precision
    ctx.threads = threads

    same_endpoints = (
        Fraction(mode + 1, mode),
        Fraction(2),
        Fraction(2 * mode + 1, mode),
        Fraction(4),
    )
    reflected_endpoints = (
        Fraction(-4),
        Fraction(-(2 * mode + 1), mode),
        Fraction(mode + 1, mode),
        Fraction(2),
    )
    _progress(
        f"certifying K={mode} {same_factors} same-sign root/pole ranges "
        "and target-pole cells"
    )
    same = _certify_geometry(
        mode=mode,
        label="same_sign",
        endpoints=same_endpoints,
        factors=same_factors,
        inverse=False,
        reflected=False,
    )
    _progress(
        f"certifying K={mode} {reflected_factors} reflected root/pole ranges "
        "and target-pole cells"
    )
    reflected = _certify_geometry(
        mode=mode,
        label="reflected",
        endpoints=reflected_endpoints,
        factors=reflected_factors,
        inverse=True,
        reflected=True,
    )

    script_path = Path(__file__).resolve()
    if lean_path is None:
        lean_path = (
            script_path.parent.parent
            / "riemann-cvs-lean"
            / "RiemannCvs"
            / f"K{mode}AdiShiftBinding.lean"
        )
    lean_audit = _lean_literal_cell_audit(
        lean_path, same["cells"], reflected["cells"]
    )
    _progress("Lean literal cell transcripts match every Arb-selected cell")
    production_path = Path(
        __import__("certify_adjacent_compressed_gram").__file__
    ).resolve()
    fraction_path = Path(
        __import__("certify_preconditioned_relative_shell").__file__
    ).resolve()
    payload: dict[str, Any] = {
        "status": "PASS",
        "rigorous_interval_certificate": True,
        "scope": f"literal K={mode} ADI shift ranges and pole grid noncollision cells",
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": _git_sha(),
        "script_sha256": _script_hash(script_path),
        "dependency_sha256": {
            production_path.name: _script_hash(production_path),
            fraction_path.name: _script_hash(fraction_path),
        },
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "precision_bits": precision,
        "flint_threads": threads,
        "mode": mode,
        "same_sign_factor_count": same_factors,
        "reflected_factor_count": reflected_factors,
        "combined_factor_count": same_factors + reflected_factors,
        "combined_rank_upper": 2 * (same_factors + reflected_factors),
        "same_sign": same,
        "reflected": reflected,
        "lean_literal_cell_audit": lean_audit,
        "lean_target": f"RiemannCvs.K{mode}AdiShiftBinding",
        "proof_boundary": (
            "Arb proves the concrete transcendental range/cell inequalities; "
            "Lean proves that those certificate fields imply every generic ADI "
            "noncollision premise and hence the exact factorization identity"
        ),
    }
    if reference_json is not None:
        payload["reference_precision_audit"] = _reference_audit(reference_json, payload)
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", type=int, default=DEFAULT_MODE)
    parser.add_argument("--same-factors", type=int, default=DEFAULT_SAME_FACTORS)
    parser.add_argument(
        "--reflected-factors", type=int, default=DEFAULT_REFLECTED_FACTORS
    )
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--reference-json", type=Path)
    parser.add_argument("--lean-path", type=Path)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    payload = certify(
        mode=args.mode,
        same_factors=args.same_factors,
        reflected_factors=args.reflected_factors,
        precision=args.prec,
        threads=args.threads,
        reference_json=args.reference_json,
        lean_path=args.lean_path,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"K{payload['mode']} ADI shift-cell certificate PASS: "
        f"factors={payload['combined_factor_count']} "
        f"rank={payload['combined_rank_upper']} "
        f"precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
