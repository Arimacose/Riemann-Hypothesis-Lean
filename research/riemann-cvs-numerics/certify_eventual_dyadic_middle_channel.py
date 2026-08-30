#!/usr/bin/env python3
"""Certify an eventual dyadic middle-channel relative-energy budget.

This script composes two independently replayable inputs for the cutoff-free
``c=13`` CvS operator:

* the finite path-power certificate ``||T_13|| < 10/3`` for the prime
  translation operator; and
* the all-mode Archimedean certificate
  ``|S_n-pi/4| <= 1/(4*n)`` together with its corrected parity decomposition.

For one parity sector, let the middle and new dyadic shells be
``[N,2N]`` and ``[2N,4N]``.  The input certificates and elementary compression
bounds give

    gap(N) = log(N) - d - P
             - A_internal(N) - Pole(N) + shift,

    epsilon(N) = P + A_cross(N) + Pole(N),

where ``d=19/20``, ``P=10/3``, and

    A_internal(N)
      = log(3/2)/2 + 1/(2N) + 1/(4*pi*(N-1)),

    A_cross(N)
      = sqrt(log(5/3)*log(4/3))/2
        + 1/(2N) + 1/(4*pi*(N-1)).

The pole block has the exact rank-two form

    32*L*sinh(L/4)^2 * (a*a^* - b*b^*),

with ``a_n^2+b_n^2 = 1/(L^2+16*pi^2*n^2)``.  On signed modes
``|n|>=N``, the integral comparison for ``sum 1/n^2`` therefore gives

    Pole(N) <= 32*L*sinh(L/4)^2 / (8*pi^2*(N-1)).

Compression to a parity block or to an internal/cross block does not increase
these norms.  Hence the rectangular coupling theorem yields the scalar
relative coefficient

    rho(N) = epsilon(N)^2 / (gap(N)*gap(2N)).

The error bound ``epsilon(N)`` decreases and both coercive floors increase.
Once ``rho(N) < 2/27``, the same strict inequality holds at every larger mode,
in particular at every later dyadic shell.  Arb is used for every
transcendental evaluation and strict comparison.  The resulting JSON is a
rigorous scalar-composition certificate conditional on the explicitly listed
operator identifications; it does not replace those Lean/source adapters or
the remaining finite bridge certificates.
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
from flint import arb, ctx


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


def _ball_record(value: arb, digits: int = 60) -> dict[str, str]:
    return {
        "midpoint": value.mid().str(digits, radius=False),
        "radius": value.rad().str(16, radius=False),
        "lower": value.lower().str(digits, radius=True),
        "upper": value.upper().str(digits, radius=True),
    }


def _load_json(path: Path, name: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read {name}: {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{name} must contain a JSON object")
    return payload


def _require_bool(payload: dict[str, Any], key: str, name: str) -> None:
    if payload.get(key) is not True:
        raise ValueError(f"{name} does not certify {key}=true")


def _validate_script_hash(
    payload: dict[str, Any], script: Path, name: str
) -> str:
    expected = str(payload.get("script_sha256", "")).upper()
    actual = _sha256(script)
    if expected != actual:
        raise ValueError(
            f"{name} script hash mismatch: artifact={expected}, current={actual}"
        )
    return actual


def _validate_input_certificates(
    *,
    c: int,
    prime_path: Path,
    arch_path: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    prime = _load_json(prime_path, "prime certificate")
    arch = _load_json(arch_path, "Archimedean certificate")

    if prime.get("status") != "PASS" or arch.get("status") != "PASS":
        raise ValueError("both input certificates must have status PASS")
    _require_bool(prime, "rigorous_certificate", "prime certificate")
    _require_bool(
        arch, "rigorous_constant_certificate", "Archimedean certificate"
    )
    if prime.get("c") != c or arch.get("c") != c:
        raise ValueError("input certificate cutoff does not match --c")
    _require_bool(
        prime,
        "all_power_row_sums_strictly_below_target_power",
        "prime certificate",
    )

    centered = arch.get("centered_symbol_audit")
    dyadic = arch.get("dyadic_parity_operator_audit")
    diagonal = arch.get("diagonal_audit")
    if not isinstance(centered, dict) or not isinstance(dyadic, dict):
        raise ValueError("Archimedean certificate lacks centered/dyadic audit")
    if not isinstance(diagonal, dict):
        raise ValueError("Archimedean certificate lacks diagonal audit")
    for key in ("strict_upper_pass", "strict_lower_pass"):
        _require_bool(centered, key, "Archimedean centered audit")
    _require_bool(diagonal, "strict_target_pass", "Archimedean diagonal audit")
    if dyadic.get("leading_hankel_kernel") != "1/(2*(k+l))":
        raise ValueError("unexpected Archimedean leading Hankel kernel")
    decomposition = str(arch.get("parity_archimedean_decomposition", ""))
    if "leading Hankel" not in decomposition:
        raise ValueError("Archimedean certificate lacks corrected parity split")

    script_dir = Path(__file__).resolve().parent
    prime_script = script_dir / "certify_prime_translation_power_bound.py"
    arch_script = script_dir / "certify_archimedean_tail_envelope.py"
    prime_script_hash = _validate_script_hash(
        prime, prime_script, "prime certificate"
    )
    arch_script_hash = _validate_script_hash(
        arch, arch_script, "Archimedean certificate"
    )

    prime_git = prime.get("git_sha")
    arch_git = arch.get("git_sha")
    if prime_git and arch_git and prime_git != arch_git:
        raise ValueError("input certificates were produced from different commits")
    current_git = _git_sha()
    if current_git and prime_git and current_git != prime_git:
        raise ValueError(
            "prime certificate commit does not match the current checkout"
        )
    if current_git and arch_git and current_git != arch_git:
        raise ValueError(
            "Archimedean certificate commit does not match the current checkout"
        )

    metadata = {
        "prime_certificate": {
            "path": str(prime_path.resolve()),
            "sha256": _sha256(prime_path.resolve()),
            "script_sha256": prime_script_hash,
            "git_sha": prime_git,
        },
        "archimedean_certificate": {
            "path": str(arch_path.resolve()),
            "sha256": _sha256(arch_path.resolve()),
            "script_sha256": arch_script_hash,
            "git_sha": arch_git,
        },
        "same_git_sha": bool(prime_git and prime_git == arch_git),
    }
    return prime, arch, metadata


def certify(
    *,
    c: int,
    prime_certificate: Path,
    archimedean_certificate: Path,
    start_mode: int,
    certified_matrix_frontier: int,
    shift_gain: Fraction,
    channel_target: Fraction,
    max_doublings: int,
    precision: int,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if start_mode < 2:
        raise ValueError("start_mode must be at least two")
    if start_mode % 2:
        raise ValueError("start_mode must be even")
    if certified_matrix_frontier != 2 * start_mode:
        raise ValueError(
            "certified_matrix_frontier must equal 2*start_mode: the existing "
            "matrix step has two-channel parameter K=start_mode/2, while "
            "start_mode is the first open adjacent-shell channel"
        )
    if max_doublings <= 0:
        raise ValueError("max_doublings must be strictly positive")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < channel_target < 1:
        raise ValueError("channel_target must lie strictly between zero and one")

    ctx.prec = precision
    prime, arch, input_metadata = _validate_input_certificates(
        c=c,
        prime_path=prime_certificate,
        arch_path=archimedean_certificate,
    )

    prime_norm = Fraction(str(prime["target_operator_norm"]))
    centered_audit = arch["centered_symbol_audit"]
    diagonal_audit = arch["diagonal_audit"]
    centered_decay = Fraction(str(centered_audit["target_decay_coefficient"]))
    diagonal_target = Fraction(str(diagonal_audit["target_constant"]))
    if diagonal_target >= 0:
        raise ValueError("expected a negative diagonal target constant")
    diagonal_offset = -diagonal_target
    minimum_mode = int(arch["minimum_mode"])
    induction_start = int(
        arch["dyadic_parity_operator_audit"]["induction_start_mode"]
    )
    if start_mode < minimum_mode or start_mode < induction_start:
        raise ValueError(
            "start_mode lies below the certified Archimedean induction range"
        )
    pi = arb.pi()
    L = arb(c).log()
    prime_bound = _fraction_arb(prime_norm)
    decay = _fraction_arb(centered_decay)
    shift = _fraction_arb(shift_gain)
    target = _fraction_arb(channel_target)
    offset = _fraction_arb(diagonal_offset)

    leading_internal = (arb(3) / 2).log() / 2
    leading_cross = (
        (arb(5) / 3).log() * (arb(4) / 3).log()
    ).sqrt() / 2
    pole_prefactor = 32 * L * (L / 4).sinh() ** 2

    def centered_remainder(mode: int) -> arb:
        n = arb(mode)
        return 2 * decay / n + decay / (pi * (n - 1))

    def pole_tail(mode: int) -> arb:
        n = arb(mode)
        return pole_prefactor / (8 * pi**2 * (n - 1))

    def internal_arch(mode: int) -> arb:
        return leading_internal + centered_remainder(mode)

    def cross_arch(mode: int) -> arb:
        return leading_cross + centered_remainder(mode)

    def gap(mode: int) -> arb:
        n = arb(mode)
        return (
            n.log()
            - offset
            - prime_bound
            - internal_arch(mode)
            - pole_tail(mode)
            + shift
        )

    def coupling(mode: int) -> arb:
        return prime_bound + cross_arch(mode) + pole_tail(mode)

    def row(mode: int, doubling_index: int) -> dict[str, Any]:
        low_gap = gap(mode)
        high_gap = gap(2 * mode)
        if not low_gap > 0 or not high_gap > 0:
            raise RuntimeError(
                f"coercive floor is not strictly positive at mode {mode}"
            )
        epsilon = coupling(mode)
        rho = epsilon**2 / (low_gap * high_gap)
        if rho < target:
            comparison = "strictly_below"
        elif rho > target:
            comparison = "strictly_above"
        else:
            raise RuntimeError(
                f"precision does not separate rho({mode}) from the target"
            )
        return {
            "doubling_index": doubling_index,
            "mode": mode,
            "middle_shell": f"[{mode},{2 * mode}]",
            "new_shell": f"[{2 * mode},{4 * mode}]",
            "centered_arch_remainder_upper": _ball_record(
                centered_remainder(mode)
            ),
            "internal_arch_norm_upper": _ball_record(internal_arch(mode)),
            "adjacent_cross_arch_norm_upper": _ball_record(cross_arch(mode)),
            "pole_tail_norm_upper": _ball_record(pole_tail(mode)),
            "low_coercive_floor": _ball_record(low_gap),
            "high_coercive_floor": _ball_record(high_gap),
            "cross_norm_upper": _ball_record(epsilon),
            "relative_coefficient_upper": _ball_record(rho),
            "comparison_to_channel_target": comparison,
            "strict_channel_pass": comparison == "strictly_below",
            "target_slack": _ball_record(target - rho),
        }

    checked: list[dict[str, Any]] = []
    threshold_row: dict[str, Any] | None = None
    for doubling_index in range(max_doublings + 1):
        mode = start_mode * (2**doubling_index)
        candidate = row(mode, doubling_index)
        checked.append(candidate)
        if candidate["strict_channel_pass"]:
            threshold_row = candidate
            break
    if threshold_row is None:
        raise RuntimeError("no strict eventual threshold found within max_doublings")

    first_passing_mode = int(threshold_row["mode"])
    if first_passing_mode < start_mode:
        raise RuntimeError("eventual threshold lies below the first open channel")
    before = checked[:-1]
    if not all(
        item["comparison_to_channel_target"] == "strictly_above"
        for item in before
    ):
        raise RuntimeError("a pre-threshold comparison is not strictly above")

    bridge_modes: list[int] = []
    mode = start_mode
    while mode < first_passing_mode:
        bridge_modes.append(mode)
        mode *= 2
    if mode != first_passing_mode:
        raise RuntimeError("eventual threshold is not dyadically aligned")

    previous_row = checked[-2] if len(checked) >= 2 else None
    result = {
        "status": "PASS",
        "rigorous_scalar_composition_certificate": True,
        "scope": (
            "Arb composition of certified global prime and all-mode "
            "Archimedean bounds with an elementary rank-two pole-tail bound"
        ),
        "c": c,
        "precision_bits": precision,
        "inputs": {
            "prime_operator_norm_upper": str(prime_norm),
            "archimedean_diagonal_offset": str(diagonal_offset),
            "centered_symbol_decay": str(centered_decay),
            "spectral_shift_gain": str(shift_gain),
            "per_channel_target": str(channel_target),
            "start_mode": start_mode,
            "certified_matrix_frontier": certified_matrix_frontier,
            "minimum_archimedean_mode": minimum_mode,
            "archimedean_induction_start": induction_start,
        },
        "input_certificates": input_metadata,
        "analytic_bounds": {
            "middle_shell": "[N,2N]",
            "new_shell": "[2N,4N]",
            "leading_internal_arch_norm_upper": _ball_record(
                leading_internal
            ),
            "leading_adjacent_cross_arch_norm_upper": _ball_record(
                leading_cross
            ),
            "centered_parity_remainder_formula": (
                f"2*({centered_decay})/N + "
                f"({centered_decay})/(pi*(N-1))"
            ),
            "internal_arch_formula": (
                "log(3/2)/2 + centered_parity_remainder(N)"
            ),
            "adjacent_cross_arch_formula": (
                "sqrt(log(5/3)*log(4/3))/2 + "
                "centered_parity_remainder(N)"
            ),
            "pole_prefactor": _ball_record(pole_prefactor),
            "pole_tail_formula": (
                "32*log(c)*sinh(log(c)/4)^2 / "
                "(8*pi^2*(N-1))"
            ),
            "pole_tail_derivation": (
                "rank-two norm <= prefactor*sum_{|n|>=N} "
                "1/(L^2+16*pi^2*n^2), followed by "
                "2*sum_{n>=N}1/n^2 < 2/(N-1)"
            ),
            "coercive_floor_formula": (
                "log(N)-diagonal_offset-prime_bound-"
                "internal_arch(N)-pole_tail(N)+shift_gain"
            ),
            "cross_norm_formula": (
                "prime_bound+adjacent_cross_arch(N)+pole_tail(N)"
            ),
            "relative_coefficient_formula": (
                "cross_norm(N)^2/(gap(N)*gap(2*N))"
            ),
        },
        "monotonicity_certificate": {
            "domain": f"every integer N >= {first_passing_mode}",
            "epsilon_nonincreasing": True,
            "low_and_high_gaps_strictly_increasing": True,
            "relative_coefficient_strictly_decreasing": True,
            "reason": (
                "log(N) increases, while 1/N, 1/(N-1), the "
                "Archimedean remainder, and the pole tail decrease"
            ),
            "consequence": (
                f"rho(N) < {channel_target} for every integer "
                f"N >= {first_passing_mode}"
            ),
        },
        "dyadic_threshold": {
            "first_passing_doubling_index": threshold_row["doubling_index"],
            "first_passing_mode": first_passing_mode,
            "first_passing_row": threshold_row,
            "previous_dyadic_row": previous_row,
            "all_earlier_checked_rows_strictly_above_target": True,
        },
        "checked_dyadic_rows": checked,
        "finite_reduction": {
            "already_certified_transition": (
                f"N={certified_matrix_frontier // 2} to "
                f"N={certified_matrix_frontier}"
            ),
            "last_certified_two_channel_mode": start_mode // 2,
            "first_open_middle_channel_mode": start_mode,
            "remaining_middle_channel_bridge_start_modes": bridge_modes,
            "remaining_middle_channel_bridge_count": len(bridge_modes),
            "eventual_middle_channel_range_start": first_passing_mode,
            "middle_channel_tail_reduced_to_finite_bridges": True,
            "previous_core_channel_still_requires_uniform_control": True,
        },
        "operator_consequence": (
            "conditional on the certified operator identifications, the "
            "middle/new adjacent-shell cross form has relative coefficient "
            f"strictly below {channel_target} for every N >= "
            f"{first_passing_mode}"
        ),
        "conditional_operator_inputs": [
            (
                "the path-power certificate represents the complete c=13 "
                "prime block as the self-adjoint translation operator T_13"
            ),
            (
                "the Archimedean parity block is the certified same-sign "
                "commutator plus the reflected leading Hankel kernel and "
                "centered remainder"
            ),
            (
                "orthogonal parity/internal/cross compression does not "
                "increase the global prime or pole operator norm"
            ),
            (
                "the diagonal envelope and x<=-shift_gain give the displayed "
                "coercive shell floors"
            ),
        ],
        "lean_adapters": [
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_coerciveNormBounds",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_twoChannelBudgets",
            "RiemannCvs.BoundaryWeylSchurTail.fourNinthsShell_of_twoChannelReference",
        ],
        "remaining_obligation": (
            "certify the listed finite dyadic bridges and the previous-core "
            "channel, then instantiate the concrete Hilbert/parity adapters"
        ),
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "platform": platform.platform(),
        "git_sha": _git_sha(),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "script_sha256": _sha256(Path(__file__).resolve()),
    }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--prime-certificate", type=Path, required=True)
    parser.add_argument("--archimedean-certificate", type=Path, required=True)
    parser.add_argument("--start-mode", type=int, default=1920)
    parser.add_argument(
        "--certified-matrix-frontier", type=int, default=3840
    )
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--channel-target", default="2/27")
    parser.add_argument("--max-doublings", type=int, default=32)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    result = certify(
        c=args.c,
        prime_certificate=args.prime_certificate.resolve(),
        archimedean_certificate=args.archimedean_certificate.resolve(),
        start_mode=args.start_mode,
        certified_matrix_frontier=args.certified_matrix_frontier,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        channel_target=_positive_fraction(
            args.channel_target, "channel_target"
        ),
        max_doublings=args.max_doublings,
        precision=args.prec,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    threshold = result["dyadic_threshold"]
    finite = result["finite_reduction"]
    previous = threshold["previous_dyadic_row"]
    print(
        json.dumps(
            {
                "status": result["status"],
                "first_passing_mode": threshold["first_passing_mode"],
                "relative_coefficient_upper": threshold[
                    "first_passing_row"
                ]["relative_coefficient_upper"],
                "previous_dyadic_relative_coefficient_upper": (
                    previous["relative_coefficient_upper"]
                    if previous is not None
                    else None
                ),
                "remaining_middle_channel_bridge_count": finite[
                    "remaining_middle_channel_bridge_count"
                ],
                "remaining_middle_channel_bridge_start_modes": finite[
                    "remaining_middle_channel_bridge_start_modes"
                ],
                "artifact": str(args.json_out.resolve()),
                "sha256": _sha256(args.json_out.resolve()),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
