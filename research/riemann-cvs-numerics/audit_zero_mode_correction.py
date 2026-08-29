#!/usr/bin/env python3
"""High-precision audit of the V22 cutoff-free zero-mode correction.

For ``L = log(c)`` and ``c_k = 2 k + 1/2``, the zero-frequency geometric
terms are

    G1 = sum exp(-c_k L) / c_k,
    G2 = sum exp(-c_k L) / c_k**2.

The corrected closed form is ``XC(0) = psi1(1/4)/4 - L*G1 - G2``.  The script
checks that this changes the cutoff-free zero entry by the negative rank-one
amount ``delta = 2*G1 + 2*G2/L`` and independently compares the closed form
with the defining CCM/CvS archimedean integral.  It also guards the source
structure that caused the original omission: ``g_x1`` and ``g_x2`` must be
accumulated outside the ``n != 0`` branch.

This is a high-precision identity/regression audit.  The interval inertia
certificate is produced separately by ``certify_parity_gap.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

import mpmath as mp


UPSTREAM_SOURCE = (
    "https://github.com/akivag613/connes-cvs-/blob/"
    "5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c/"
    "papers/2_guinand_weil_dictionary_tail_order/scripts/arb_ldlt_certify.py"
)


def source_structure_audit(source_path: Path) -> dict[str, object]:
    source = source_path.read_text(encoding="utf-8")
    lines = source.splitlines()

    def unique_line(fragment: str) -> tuple[int, str]:
        matches = [(i + 1, line) for i, line in enumerate(lines) if fragment in line]
        if len(matches) != 1:
            raise AssertionError(f"expected one source line containing {fragment!r}")
        return matches[0]

    if_line_no, if_line = unique_line("if n != 0:")
    gcc_line_no, gcc_line = unique_line("g_cc +=")
    gx1_line_no, gx1_line = unique_line("g_x1 +=")
    gx2_line_no, gx2_line = unique_line("g_x2 +=")

    indent = lambda line: len(line) - len(line.lstrip())
    if not indent(gcc_line) > indent(if_line):
        raise AssertionError("g_cc must remain conditional on n != 0")
    if indent(gx1_line) != indent(if_line) or indent(gx2_line) != indent(if_line):
        raise AssertionError("g_x1 and g_x2 must include the n = 0 terms")

    start = source.index("def pole_J")
    end = source.find("\ndef ", start + len("def pole_J"))
    pole_block = source[start:] if end < 0 else source[start:end]
    if pole_block.count("arb(2).log()") != 1:
        raise AssertionError("strict pole_J must contain exactly one log(2)")
    if "2 * arb(2).log()" in pole_block:
        raise AssertionError("strict pole_J contains an extra log(2)")

    return {
        "source_path": str(source_path),
        "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "if_n_nonzero_line": if_line_no,
        "g_cc_line": gcc_line_no,
        "g_x1_line": gx1_line_no,
        "g_x2_line": gx2_line_no,
        "zero_mode_terms_unconditional": True,
        "pole_J_log2_count": 1,
    }


def pole_J(L: mp.mpf) -> mp.mpf:
    U = mp.exp(L / 2)
    return (
        -2 * mp.log(U + 1)
        + mp.log(U * U + 1)
        + 2 * mp.atan(U)
        + mp.log(2)
        - mp.pi / 2
    )


def arch_kappa(L: mp.mpf) -> mp.mpf:
    eL = mp.exp(L)
    return mp.euler + mp.log(4 * mp.pi * (eL - 1) / (eL + 1))


def zero_mode_sums(L: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    half = mp.mpf("0.5")
    G1 = mp.nsum(
        lambda k: mp.exp(-(2 * k + half) * L) / (2 * k + half),
        [0, mp.inf],
    )
    G2 = mp.nsum(
        lambda k: mp.exp(-(2 * k + half) * L) / (2 * k + half) ** 2,
        [0, mp.inf],
    )
    return G1, G2


def direct_archimedean_zero_entry(L: mp.mpf) -> mp.mpf:
    def integrand(x: mp.mpf) -> mp.mpf:
        if x == 0:
            return mp.mpf("0.5") - 1 / L
        return (
            2 * mp.exp(x / 2) * (1 - x / L) - 2
        ) / (mp.exp(x) - mp.exp(-x))

    return arch_kappa(L) + mp.quad(integrand, [0, L])


def matrix_builder_crosscheck(c_text: str, N: int, prec: int) -> dict[str, object]:
    """Compare every exploratory float entry with the strict Arb midpoint."""
    import numpy as np

    source_dir = Path(__file__).resolve().parent
    if str(source_dir) not in sys.path:
        sys.path.insert(0, str(source_dir))
    from certify_parity_gap import build_cutoff_free_matrix
    from explore_smooth_cutoff_velocity import build_matrix

    c_float = float(mp.mpf(c_text))
    if not mp.mpf(c_text).ae(mp.floor(mp.mpf(c_text))):
        raise ValueError("matrix cross-check requires an integral c")
    c_int = int(mp.mpf(c_text))
    exploratory = build_matrix(c_float, N)
    strict = build_cutoff_free_matrix(c_int, N, prec)
    dim = 2 * N + 1
    strict_mid = np.array(
        [[float(strict[i, j].mid()) for j in range(dim)] for i in range(dim)]
    )
    difference = exploratory - strict_mid
    max_abs = float(np.max(np.abs(difference)))
    frobenius = float(np.linalg.norm(difference))
    if max_abs >= 2e-15:
        raise AssertionError("exploratory and strict matrix builders disagree")
    return {
        "N": N,
        "dimension": dim,
        "arb_prec_bits": prec,
        "max_abs_float_difference": max_abs,
        "frobenius_float_difference": frobenius,
        "tolerance": 2e-15,
    }


def audit(
    c_text: str,
    dps: int,
    source_path: Path,
    matrix_N: int,
    matrix_prec: int,
) -> dict[str, object]:
    if dps < 90:
        raise ValueError("dps must be at least 90")
    mp.mp.dps = dps
    c = mp.mpf(c_text)
    if not c > 1:
        raise ValueError("c must be greater than one")

    L = mp.log(c)
    G1, G2 = zero_mode_sums(L)
    base = mp.polygamma(1, mp.mpf(1) / 4) / 4
    corrected_xc = base - L * G1 - G2
    delta = 2 * G1 + 2 * G2 / L

    kappa = arch_kappa(L)
    J = pole_J(L)
    legacy_wr = kappa + J - 2 * base / L
    corrected_wr = kappa + J - 2 * corrected_xc / L
    direct_wr = direct_archimedean_zero_entry(L)
    wrong_two_log2_wr = corrected_wr + mp.log(2)

    closed_vs_direct = abs(corrected_wr - direct_wr)
    delta_identity_error = abs((corrected_wr - legacy_wr) - delta)
    wrong_log2_error = abs((wrong_two_log2_wr - direct_wr) - mp.log(2))
    tolerance = mp.power(10, -min(70, dps // 2))

    if not G1 > 0 or not G2 > 0 or not delta > 0:
        raise AssertionError("zero-mode correction sums must be strictly positive")
    if not closed_vs_direct < tolerance:
        raise AssertionError("closed form does not match the defining integral")
    if not delta_identity_error < tolerance:
        raise AssertionError("rank-one delta identity failed")
    if not wrong_log2_error < tolerance:
        raise AssertionError("two-log(2) normalization diagnostic failed")

    expected_delta_c13 = mp.mpf(
        "1.97596937071718375848858750178771622127604888263256"
    )
    expected_error: mp.mpf | None = None
    if c == 13:
        expected_error = abs(delta - expected_delta_c13)
        if not expected_error < mp.mpf("1e-49"):
            raise AssertionError("c=13 correction does not reproduce the V22 value")

    digits = min(100, dps - 10)

    def text(x: mp.mpf) -> str:
        return mp.nstr(x, digits)

    return {
        "status": "PASS",
        "scope": (
            "high-precision zero-mode identity and source-structure audit; "
            "finite spectral inertia is certified separately with Arb"
        ),
        "c": c_text,
        "dps": dps,
        "git_sha": os.environ.get("GITHUB_SHA"),
        "upstream_source": UPSTREAM_SOURCE,
        "source_structure": source_structure_audit(source_path),
        "matrix_builder_crosscheck": matrix_builder_crosscheck(
            c_text, matrix_N, matrix_prec
        ),
        "zero_mode": {
            "L": text(L),
            "G1": text(G1),
            "G2": text(G2),
            "trigamma_quarter_over_four": text(base),
            "corrected_XC0": text(corrected_xc),
            "delta": text(delta),
            "delta_positive": True,
            "expected_v22_delta_c13_abs_error": (
                text(expected_error) if expected_error is not None else None
            ),
        },
        "closed_form_checks": {
            "legacy_WR00": text(legacy_wr),
            "corrected_WR00": text(corrected_wr),
            "direct_integral_WR00": text(direct_wr),
            "closed_vs_direct_abs_error": text(closed_vs_direct),
            "corrected_minus_legacy_minus_delta_abs_error": text(
                delta_identity_error
            ),
            "two_log2_excess": text(wrong_two_log2_wr - direct_wr),
            "log2": text(mp.log(2)),
            "two_log2_excess_minus_log2_abs_error": text(wrong_log2_error),
            "tolerance": text(tolerance),
        },
        "audit_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", default="13")
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--matrix-N", type=int, default=4)
    parser.add_argument("--matrix-prec", type=int, default=400)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    if args.matrix_N < 0 or args.matrix_prec < 128:
        parser.error("require matrix-N >= 0 and matrix-prec >= 128")

    source_path = Path(__file__).with_name("certify_parity_gap.py")
    result = audit(
        args.c, args.dps, source_path, args.matrix_N, args.matrix_prec
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "status": result["status"],
                "c": result["c"],
                "corrected_XC0": result["zero_mode"]["corrected_XC0"],
                "delta": result["zero_mode"]["delta"],
                "matrix_builder_max_abs_difference": result[
                    "matrix_builder_crosscheck"
                ]["max_abs_float_difference"],
                "closed_vs_direct_abs_error": result["closed_form_checks"][
                    "closed_vs_direct_abs_error"
                ],
                "json_out": str(args.json_out),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
