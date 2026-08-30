#!/usr/bin/env python3
"""Certify explicit Archimedean CvS tail envelopes at ``c=13``.

For a positive Fourier mode ``n`` put

    L = log(c),  y = pi*n/L,  w = 2*y,  z = 1/4 + i*y.

The cutoff-free source formulas use

    S_n = Im(psi(z))/2 - w*g_s(n)

and

    -(W_R)_{nn}
      = Re(psi(z)) - psi(1/4) - kappa_L - J_L
        + Re(psi'(z))/(2L)
        - 2*g_cc(n) - 2*g_x1(n) - 2*g_x2(n)/L.

This script interval-checks a source-level proof that, for every ``n >= N0``,

    0 <= S_n <= 4/5,
    |S_n - pi/4| <= 1/(4*n),
    -(W_R)_{nn} >= log(n) - 19/20

when ``c=13`` and ``N0=960``.  The proof uses the following explicit bounds.

* DLMF 5.11.2, truncated before the Bernoulli sum, has remainder at most
  ``sec(arg(z)/2)^3/(12*|z|^2)``.  Since ``arg(z) <= pi/2``, this is at most
  ``sqrt(2)/(6*y^2)``.
* From ``psi'(z) = sum_(k>=0) 1/(k+z)^2``, every term with ``k+1/4 >= y``
  has nonnegative real part.  There are at most ``y+1`` earlier terms and each
  is at least ``-1/y^2``, hence
  ``Re(psi'(z)) >= -(1/y + 1/y^2)``.
* With ``d_k=2k+1/2`` and ``e_k=exp(-d_k L)``, set
  ``C=sum e_k`` and ``B=sum d_k e_k``.  Then
  ``g_cc <= 2C``, ``g_x1 <= B/w^2``, ``|g_x2| <= C/w^2``, and
  ``w*g_s <= C/w``.  Both ``B`` and ``C`` are evaluated by exact geometric
  closed forms.

Every omitted correction decreases in magnitude as ``n`` grows, while
``atan(4y)`` increases.  It is therefore sufficient to certify the displayed
constant inequalities at ``N0``.  Arb is used for every transcendental and
rational comparison.  The script also reconstructs the exact source formulas
at the endpoint as an independent wiring check.  Together with the exact
Hilbert-commutator identity and the contraction bound for the normalized
discrete Hilbert transform, the centered estimate gives the conditional
tail-to-tail operator bound ``||(W_R)_off|| <= 1/(2*N)`` on modes ``n>=N``.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import platform
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
from flint import acb, arb, ctx

from certify_parity_gap import arch_kappa, geom_sums, pole_J


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def _fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _git_sha() -> str | None:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            text=True,
            encoding="utf-8",
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def _ball_record(value: arb, digits: int = 50) -> dict[str, str]:
    return {
        "midpoint": value.mid().str(digits, radius=False),
        "radius": value.rad().str(16, radius=False),
        "lower": value.lower().str(digits, radius=True),
        "upper": value.upper().str(digits, radius=True),
    }


def certify(
    *,
    c: int,
    minimum_mode: int,
    diagonal_offset: Fraction,
    symbol_upper: Fraction,
    centered_decay: Fraction,
    precision: int,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if minimum_mode <= 0:
        raise ValueError("minimum_mode must be strictly positive")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    ctx.prec = precision

    L = arb(c).log()
    pi = arb.pi()
    a = arb(1) / 4
    n0 = arb(minimum_mode)
    y0 = pi * n0 / L
    w0 = 2 * y0
    sqrt_two = arb(2).sqrt()

    # e_k = exp(-(2k+1/2)L) = r*t^k.
    r = (-L / 2).exp()
    t = (-2 * L).exp()
    geometric_mass = r / (1 - t)
    geometric_first_moment = r * (
        (arb(1) / 2) / (1 - t) + 2 * t / (1 - t) ** 2
    )

    kappa = arch_kappa(L)
    pole_constant = pole_J(L)
    psi_quarter = a.digamma()

    digamma_real_error = (arb(1) / 8 + sqrt_two / 6) / y0**2
    trigamma_contribution_error = (
        1 / y0 + 1 / y0**2
    ) / (2 * L)
    gx1_contribution_error = 2 * geometric_first_moment / w0**2
    gx2_contribution_error = (2 / L) * geometric_mass / w0**2
    decreasing_diagonal_error = (
        digamma_real_error
        + trigamma_contribution_error
        + gx1_contribution_error
        + gx2_contribution_error
    )

    # g_cc <= sum e_k/d_k <= 2*sum e_k, hence -2*g_cc >= -4C.
    asymptotic_diagonal_constant = (
        (pi / L).log()
        - psi_quarter
        - kappa
        - pole_constant
        - 4 * geometric_mass
    )
    diagonal_constant_lower = (
        asymptotic_diagonal_constant - decreasing_diagonal_error
    )
    diagonal_target = -_fraction_arb(diagonal_offset)
    diagonal_pass = bool(diagonal_constant_lower > diagonal_target)

    digamma_half_remainder = sqrt_two / (12 * y0**2)
    symbol_lower = (
        (y0 / a).atan() / 2
        - digamma_half_remainder
        - geometric_mass / (2 * y0)
    )
    symbol_upper_bound = (
        pi / 4 + 1 / (4 * y0) + digamma_half_remainder
    )
    symbol_target = _fraction_arb(symbol_upper)
    symbol_lower_pass = bool(symbol_lower > 0)
    symbol_upper_pass = bool(symbol_upper_bound < symbol_target)

    # The same DLMF remainder gives a much sharper centered envelope.  Since
    # y = pi*n/L, multiplication by n turns the 1/y terms into constants and
    # the 1/y^2 remainder into a decreasing 1/n error.  On the lower side use
    # pi/2 - atan(4y) = atan(1/(4y)) <= 1/(4y).
    centered_target = _fraction_arb(centered_decay)
    centered_upper_scaled = n0 * (
        1 / (4 * y0) + digamma_half_remainder
    )
    centered_lower_scaled = n0 * (
        1 / (8 * y0)
        + digamma_half_remainder
        + geometric_mass / (2 * y0)
    )
    centered_upper_pass = bool(centered_upper_scaled < centered_target)
    centered_lower_pass = bool(centered_lower_scaled < centered_target)
    centered_commutator_coefficient = 2 * centered_target

    # Reconstruct the exact endpoint formulas used by the canonical matrix
    # builder.  This is not needed by the monotone envelope proof, but catches
    # a sign, scale, or geometric-correction wiring mismatch.
    z = acb(a, y0)
    psi = z.digamma()
    psi1 = z.polygamma(acb(1))
    g_s, g_cc, g_x1, g_x2 = geom_sums(minimum_mode, L, precision)
    source_symbol = arb(1) / 2 * psi.imag - w0 * g_s
    source_cc = -arb(1) / 2 * (psi.real - psi_quarter) + g_cc
    source_xc = arb(1) / 4 * psi1.real - L * g_x1 - g_x2
    source_negative_arch_diagonal = -(
        kappa + 2 * source_cc + pole_constant - (2 / L) * source_xc
    )
    source_diagonal_constant = source_negative_arch_diagonal - n0.log()
    source_endpoint_pass = bool(
        source_symbol > 0
        and source_symbol < symbol_target
        and source_diagonal_constant > diagonal_target
    )
    source_centered_pass = bool(
        abs(source_symbol - pi / 4) < centered_target / n0
    )

    if not (
        diagonal_pass
        and symbol_lower_pass
        and symbol_upper_pass
        and centered_upper_pass
        and centered_lower_pass
        and source_endpoint_pass
        and source_centered_pass
    ):
        raise RuntimeError("Archimedean tail envelope target failed")

    return {
        "status": "PASS",
        "rigorous_constant_certificate": True,
        "scope": (
            "Arb audit of the explicit DLMF/series/geometric inequalities "
            "that imply the all-mode Archimedean envelope"
        ),
        "analytic_reference": "https://dlmf.nist.gov/5.11",
        "c": c,
        "minimum_mode": minimum_mode,
        "precision_bits": precision,
        "proved_for_every_integer_mode": f"n >= {minimum_mode}",
        "proved_symbol_envelope": f"0 <= S_n <= {symbol_upper}",
        "proved_centered_symbol_envelope": (
            f"abs(S_n - pi/4) <= ({centered_decay})/n"
        ),
        "conditional_tail_commutator_norm_envelope": (
            "given the exact commutator identity and ||H||<=1, on modes "
            f"n>=N, ||[M_S,H]|| <= ({2 * centered_decay})/N"
        ),
        "proved_diagonal_envelope": (
            f"-(W_R)_nn >= log(n) - {diagonal_offset}"
        ),
        "analytic_inputs": [
            (
                "DLMF 5.11.2 first-neglected-term remainder with "
                "sec(arg(z)/2)^3 <= 2*sqrt(2)"
            ),
            (
                "Re psi'(1/4+iy) >= -(1/y+1/y^2) from its "
                "absolutely convergent series"
            ),
            (
                "g_cc <= 2C, g_x1 <= B/w^2, "
                "abs(g_x2) <= C/w^2, w*g_s <= C/w"
            ),
            (
                "all error majorants decrease for y>=y0 and "
                "atan(4y) increases"
            ),
            (
                "pi/2-atan(4y)=atan(1/(4y))<=1/(4y); after "
                "multiplication by n, both centered error majorants "
                "are maximal at n0"
            ),
            (
                "[M_S,H]=[M_(S-pi/4),H] and ||H||=1, so the "
                "centered symbol envelope gives the tail norm bound"
            ),
        ],
        "constants": {
            "L": _ball_record(L),
            "y0": _ball_record(y0),
            "geometric_mass_C": _ball_record(geometric_mass),
            "geometric_first_moment_B": _ball_record(
                geometric_first_moment
            ),
            "psi_one_quarter": _ball_record(psi_quarter),
            "kappa_L": _ball_record(kappa),
            "J_L": _ball_record(pole_constant),
        },
        "diagonal_audit": {
            "target_constant": str(-diagonal_offset),
            "asymptotic_constant_before_decreasing_errors": _ball_record(
                asymptotic_diagonal_constant
            ),
            "digamma_real_error_upper": _ball_record(
                digamma_real_error
            ),
            "trigamma_contribution_error_upper": _ball_record(
                trigamma_contribution_error
            ),
            "gx1_contribution_error_upper": _ball_record(
                gx1_contribution_error
            ),
            "gx2_contribution_error_upper": _ball_record(
                gx2_contribution_error
            ),
            "decreasing_error_sum_upper": _ball_record(
                decreasing_diagonal_error
            ),
            "proved_constant_lower": _ball_record(
                diagonal_constant_lower
            ),
            "strict_target_pass": diagonal_pass,
            "strict_target_slack": _ball_record(
                diagonal_constant_lower - diagonal_target
            ),
        },
        "symbol_audit": {
            "target_upper": str(symbol_upper),
            "proved_lower": _ball_record(symbol_lower),
            "proved_upper": _ball_record(symbol_upper_bound),
            "strict_lower_pass": symbol_lower_pass,
            "strict_upper_pass": symbol_upper_pass,
            "upper_target_slack": _ball_record(
                symbol_target - symbol_upper_bound
            ),
        },
        "centered_symbol_audit": {
            "target_decay_coefficient": str(centered_decay),
            "upper_scaled_error_at_n0": _ball_record(
                centered_upper_scaled
            ),
            "lower_scaled_error_at_n0": _ball_record(
                centered_lower_scaled
            ),
            "strict_upper_pass": centered_upper_pass,
            "strict_lower_pass": centered_lower_pass,
            "upper_slack": _ball_record(
                centered_target - centered_upper_scaled
            ),
            "lower_slack": _ball_record(
                centered_target - centered_lower_scaled
            ),
            "tail_commutator_norm_coefficient": _ball_record(
                centered_commutator_coefficient
            ),
            "operator_consequence": (
                "given the exact Hilbert-commutator adapter, for every "
                "N>=n0 the Archimedean off-diagonal compression to modes "
                f"n>=N has norm at most ({2 * centered_decay})/N"
            ),
        },
        "source_formula_endpoint_replay": {
            "mode": minimum_mode,
            "S_n": _ball_record(source_symbol),
            "negative_arch_diagonal": _ball_record(
                source_negative_arch_diagonal
            ),
            "negative_arch_diagonal_minus_log_n": _ball_record(
                source_diagonal_constant
            ),
            "strict_target_pass": source_endpoint_pass,
            "centered_error": _ball_record(
                abs(source_symbol - pi / 4)
            ),
            "centered_target_at_endpoint": _ball_record(
                centered_target / n0
            ),
            "strict_centered_pass": source_centered_pass,
        },
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "platform": platform.platform(),
        "git_sha": _git_sha(),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "script_sha256": _sha256(Path(__file__).resolve()),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--minimum-mode", type=int, default=960)
    parser.add_argument("--diagonal-offset", default="19/20")
    parser.add_argument("--symbol-upper", default="4/5")
    parser.add_argument("--centered-decay", default="1/4")
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    result = certify(
        c=args.c,
        minimum_mode=args.minimum_mode,
        diagonal_offset=_positive_fraction(
            args.diagonal_offset, "diagonal_offset"
        ),
        symbol_upper=_positive_fraction(args.symbol_upper, "symbol_upper"),
        centered_decay=_positive_fraction(
            args.centered_decay, "centered_decay"
        ),
        precision=args.prec,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "proved_for_every_integer_mode": result[
                    "proved_for_every_integer_mode"
                ],
                "proved_symbol_envelope": result[
                    "proved_symbol_envelope"
                ],
                "proved_centered_symbol_envelope": result[
                    "proved_centered_symbol_envelope"
                ],
                "conditional_tail_commutator_norm_envelope": result[
                    "conditional_tail_commutator_norm_envelope"
                ],
                "proved_diagonal_envelope": result[
                    "proved_diagonal_envelope"
                ],
                "diagonal_constant_lower": result["diagonal_audit"][
                    "proved_constant_lower"
                ],
                "symbol_enclosure": {
                    "lower": result["symbol_audit"]["proved_lower"],
                    "upper": result["symbol_audit"]["proved_upper"],
                },
                "artifact": str(args.json_out.resolve()),
                "sha256": _sha256(args.json_out.resolve()),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
