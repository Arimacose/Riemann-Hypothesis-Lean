#!/usr/bin/env python3
"""Compose the combined-symbol L2 bound with coercive shell floors.

This is a rigorous Arb scalar composition.  Conditional on the recorded CvS
source and Hilbert-compression identifications, it bounds the
newest historical-band/new-shell Loewner channel.  For previous cutoff K, the
historical band is (K/2,K] and the new shell is (2K,4K].

The two dyadic L2 bounds and the exact 1/pi Fourier normalization give the
Frobenius-square budget 24/pi^2.  Dividing by the coercive floors at K/2 and
2K gives the relative coefficient tested against 1/30.
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


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _git_sha() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True, encoding="utf-8"
    ).strip()


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _ball_record(value: arb, digits: int = 70) -> dict[str, str]:
    return {
        "midpoint": value.mid().str(digits, radius=False),
        "radius": value.rad().str(18, radius=False),
        "lower": value.lower().str(digits, radius=False),
        "upper": value.upper().str(digits, radius=False),
    }


def _validate_script_record(record: dict[str, Any], script_path: Path) -> None:
    if record.get("script_sha256") != _sha256(script_path):
        raise ValueError(f"tracked script hash mismatch for {script_path}")


def certify(
    *,
    c: int,
    precision: int,
    start_previous_cutoff: int,
    first_open_previous_cutoff: int,
    max_doublings: int,
    target: Fraction,
    shift_gain: Fraction,
    combined_path: Path,
    prime_path: Path,
    arch_path: Path,
) -> dict[str, Any]:
    if c <= 1 or precision < 128:
        raise ValueError("require c>1 and precision>=128")
    if start_previous_cutoff <= 0 or start_previous_cutoff % 2:
        raise ValueError("start previous cutoff must be positive and even")
    if first_open_previous_cutoff <= 0:
        raise ValueError("first open previous cutoff must be positive")
    if not 0 < target < 1 or shift_gain < 0:
        raise ValueError("invalid target or shift gain")

    repo = Path(
        subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True, encoding="utf-8"
        ).strip()
    )
    numeric = repo / "research" / "riemann-cvs-numerics"
    combined_script = numeric / "certify_combined_symbol_dyadic_l2.py"
    prime_script = numeric / "certify_prime_translation_power_bound.py"
    arch_script = numeric / "certify_archimedean_tail_envelope.py"

    combined = _load(combined_path)
    prime = _load(prime_path)
    arch = _load(arch_path)
    head = _git_sha()

    if not (
        combined.get("status") == "PASS"
        and combined.get("rigorous_constant_certificate") is True
        and combined.get("strict_target_pass") is True
        and int(combined.get("c")) == c
        and Fraction(str(combined.get("target_scaled_upper"))) == 1
    ):
        raise ValueError(
            "combined-symbol certificate does not prove the unit L2 target"
        )
    if not (
        prime.get("status") == "PASS"
        and prime.get("rigorous_certificate") is True
        and int(prime.get("c")) == c
        and Fraction(str(prime.get("target_operator_norm"))) == Fraction(10, 3)
    ):
        raise ValueError("prime certificate does not prove the 10/3 target")
    if not (
        arch.get("status") == "PASS"
        and arch.get("rigorous_constant_certificate") is True
        and int(arch.get("c")) == c
        and arch["centered_symbol_audit"]["strict_upper_pass"] is True
        and arch["centered_symbol_audit"]["strict_lower_pass"] is True
    ):
        raise ValueError("Archimedean certificate is incomplete")
    for record in (combined, prime, arch):
        if record.get("git_sha") != head:
            raise ValueError("certificate/current checkout Git SHA mismatch")
    if (
        int(combined.get("precision_bits")) < precision
        or int(arch.get("precision_bits")) < precision
    ):
        raise ValueError("L2 or Archimedean precision is below the requested precision")
    if int(prime.get("precision_bits")) < 128:
        raise ValueError("prime certificate precision is below 128 bits")
    _validate_script_record(combined, combined_script)
    _validate_script_record(prime, prime_script)
    _validate_script_record(arch, arch_script)
    arch_dependency = combined["source_dependencies"]["archimedean_certificate"]
    if arch_dependency["sha256"] != _sha256(arch_path):
        raise ValueError(
            "combined-symbol certificate references another Archimedean input"
        )

    l2_start = int(combined["start_mode"])
    if start_previous_cutoff // 2 < l2_start:
        raise ValueError("historical half-shell lies below the certified L2 range")

    ctx.prec = precision
    pi = arb.pi()
    decay = _fraction_arb(
        Fraction(str(arch["centered_symbol_audit"]["target_decay_coefficient"]))
    )
    diagonal_target = Fraction(str(arch["diagonal_audit"]["target_constant"]))
    if diagonal_target >= 0:
        raise ValueError("expected a negative diagonal target")
    offset = _fraction_arb(-diagonal_target)
    prime_bound = _fraction_arb(Fraction(str(prime["target_operator_norm"])))
    shift = _fraction_arb(shift_gain)
    target_ball = _fraction_arb(target)
    length = arb(c).log()
    leading_internal = (arb(3) / 2).log() / 2
    pole_prefactor = 32 * length * (length / 4).sinh() ** 2

    def centered_remainder(mode: int) -> arb:
        n = arb(mode)
        return 2 * decay / n + decay / (pi * (n - 1))

    def pole_tail(mode: int) -> arb:
        n = arb(mode)
        return pole_prefactor / (8 * pi**2 * (n - 1))

    def gap(mode: int) -> arb:
        n = arb(mode)
        return (
            n.log()
            - offset
            - prime_bound
            - leading_internal
            - centered_remainder(mode)
            - pole_tail(mode)
            + shift
        )

    # rows=K/2, high L2 budget=1/(2K), old unweighted square sum<=2K,
    # and sum_(2K<q<=4K)1/q^2<=1/(4K): 32*(1/4+1/2)/pi^2.
    matrix_square_budget = arb(24) / pi**2
    checked: list[dict[str, Any]] = []
    threshold_row: dict[str, Any] | None = None
    previous_low_gap: arb | None = None
    previous_high_gap: arb | None = None
    for doubling_index in range(max_doublings + 1):
        cutoff = start_previous_cutoff * (2**doubling_index)
        low_mode = cutoff // 2
        high_mode = 2 * cutoff
        low_gap = gap(low_mode)
        high_gap = gap(high_mode)
        if not low_gap > 0 or not high_gap > 0:
            raise RuntimeError(f"nonpositive coercive floor at K={cutoff}")
        rho = matrix_square_budget / (low_gap * high_gap)
        if rho < target_ball:
            comparison = "strictly_below"
        elif rho > target_ball:
            comparison = "strictly_above"
        else:
            raise RuntimeError(f"precision does not separate K={cutoff} from target")
        low_growth = previous_low_gap is None or low_gap > previous_low_gap
        high_growth = previous_high_gap is None or high_gap > previous_high_gap
        row = {
            "doubling_index": doubling_index,
            "previous_cutoff_K": cutoff,
            "historical_band": [low_mode + 1, cutoff],
            "new_shell": [high_mode + 1, 2 * high_mode],
            "low_coercive_floor": _ball_record(low_gap),
            "high_coercive_floor": _ball_record(high_gap),
            "relative_coefficient_upper": _ball_record(rho),
            "comparison_to_one_thirtieth": comparison,
            "target_slack": _ball_record(target_ball - rho),
            "strict_leading_pass": comparison == "strictly_below",
            "coercive_floors_grew_from_previous_row": low_growth and high_growth,
        }
        checked.append(row)
        previous_low_gap = low_gap
        previous_high_gap = high_gap
        if row["strict_leading_pass"]:
            threshold_row = row
            break
    if threshold_row is None:
        raise RuntimeError("no strict threshold within max doublings")
    if not all(
        row["comparison_to_one_thirtieth"] == "strictly_above" for row in checked[:-1]
    ):
        raise RuntimeError("a pre-threshold row is not strictly above")
    if not all(row["coercive_floors_grew_from_previous_row"] for row in checked):
        raise RuntimeError("coercive floors did not grow across checked dyadic rows")

    threshold = int(threshold_row["previous_cutoff_K"])
    bridge_cutoffs: list[int] = []
    cutoff = first_open_previous_cutoff
    while cutoff < threshold:
        bridge_cutoffs.append(cutoff)
        cutoff *= 2
    if cutoff != threshold:
        raise RuntimeError("finite bridge range is not dyadically aligned")

    return {
        "status": "PASS",
        "rigorous_scalar_composition_certificate": True,
        "scope": (
            "Arb composition of the combined-symbol dyadic L2 bound and "
            "coercive shell floors; conditional on the listed source/operator identifications"
        ),
        "c": c,
        "precision_bits": precision,
        "source_dependencies": {
            "combined_symbol_l2": {
                "path": str(combined_path.resolve()),
                "sha256": _sha256(combined_path),
                "git_sha": combined["git_sha"],
            },
            "prime_translation_power": {
                "path": str(prime_path.resolve()),
                "sha256": _sha256(prime_path),
                "git_sha": prime["git_sha"],
            },
            "archimedean_envelope": {
                "path": str(arch_path.resolve()),
                "sha256": _sha256(arch_path),
                "git_sha": arch["git_sha"],
            },
        },
        "matrix_square_budget": {
            "formula": "32*(1/4+1/2)/pi^2 = 24/pi^2",
            "upper": _ball_record(matrix_square_budget),
            "derivation": [
                "K/2 rows times the high-shell weighted L2 budget 1/(2K) gives 1/4",
                "the old weighted L2 budget and p<=K give sum F(p)^2<=2K",
                "the new-shell reciprocal-square sum is at most 1/(4K), giving 1/2",
                "the concrete Fourier Loewner symbol is normalized by 1/pi",
            ],
        },
        "coercive_floor_formula": (
            "log(N)-19/20-10/3-log(3/2)/2-[1/(2N)+1/(4*pi*(N-1))]-poleTail(N)+1/1024"
        ),
        "relative_coefficient_formula": ("(24/pi^2)/(gap(K/2)*gap(2K))"),
        "target_leading_coefficient": str(target),
        "checked_dyadic_rows": checked,
        "threshold": {
            "first_passing_previous_cutoff": threshold,
            "first_passing_row": threshold_row,
            "all_earlier_checked_rows_strictly_above": True,
            "coercive_floors_strictly_increased": True,
        },
        "finite_reduction": {
            "first_open_previous_cutoff": first_open_previous_cutoff,
            "finite_newest_channel_bridge_cutoffs": bridge_cutoffs,
            "finite_newest_channel_bridge_count": len(bridge_cutoffs),
            "eventual_newest_channel_range_start": threshold,
        },
        "half_transport_consequence": (
            "for each fixed historical row band, the same matrix-square budget "
            "halves when the target shell length doubles; growing coercive floors "
            "therefore give the q_next<=q_previous/2 envelope"
        ),
        "lean_interfaces_prepared": [
            "RiemannCvs.CombinedSymbolDyadicL2.scaled_shifted_symbolSquareBudget",
            "RiemannCvs.CombinedSymbolDyadicL2.shifted_symbolSquare_sum_le_four_mul",
            "RiemannCvs.CombinedSymbolDyadicL2.rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul",
            "RiemannCvs.CombinedSymbolDyadicL2.rectangular_relativeCoupling_newestBand_of_shifted_symbolSquareRowBudgets",
            "RiemannCvs.CombinedSymbolDyadicL2.rectangularSymbolSquareBudget_two_mul",
            "RiemannCvs.CombinedSymbolDyadicL2.rectangularSymbolSquareBudget_halfTransport",
            "RiemannCvs.CombinedSymbolDyadicL2.rectangular_relativeCoupling_halfTransport_of_shifted_symbolSquareRowBudgets",
            "RiemannCvs.CombinedSymbolDyadicL2.summable_archimedeanGeometricSeries_terms",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicArchimedeanSymbol_odd",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicCutoffFreeKernel_archimedean_law",
            "RiemannCvs.CombinedSymbolDyadicL2.summable_archimedeanCosineGeometricSeries_terms",
            "RiemannCvs.CombinedSymbolDyadicL2.summable_archimedeanXOneGeometricSeries_terms",
            "RiemannCvs.CombinedSymbolDyadicL2.summable_archimedeanXTwoGeometricSeries_terms",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicArchimedeanDiagonal_neg",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicCutoffFreeKernel_actualArchimedean_law",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicCvSBuilderMatrix_eq_kernelRestriction",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicCvSBuilderEvenMatrix_eq_evenParityMatrix",
            "RiemannCvs.CombinedSymbolDyadicL2.logarithmicCvSBuilderOddMatrix_eq_oddParityMatrix",
        ],
        "conditional_operator_inputs": [
            "the parity shell forms dominate the displayed Euclidean coercive floors",
            "the separated mode bands are identified with the stated finite row and column sets",
            "the block-diagonal shell energies are identified with the recursive-core energy sum",
        ],
        "git_sha": head,
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "platform": platform.platform(),
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "script_sha256": _sha256(Path(__file__).resolve()),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--prec", type=int, default=384)
    parser.add_argument("--start-previous-cutoff", type=int, default=3840)
    parser.add_argument("--first-open-previous-cutoff", type=int, default=1920)
    parser.add_argument("--max-doublings", type=int, default=20)
    parser.add_argument("--target", type=Fraction, default=Fraction(1, 30))
    parser.add_argument("--shift-gain", type=Fraction, default=Fraction(1, 1024))
    parser.add_argument("--combined-certificate", type=Path, required=True)
    parser.add_argument("--prime-certificate", type=Path, required=True)
    parser.add_argument("--archimedean-certificate", type=Path, required=True)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    result = certify(
        c=args.c,
        precision=args.prec,
        start_previous_cutoff=args.start_previous_cutoff,
        first_open_previous_cutoff=args.first_open_previous_cutoff,
        max_doublings=args.max_doublings,
        target=args.target,
        shift_gain=args.shift_gain,
        combined_path=args.combined_certificate,
        prime_path=args.prime_certificate,
        arch_path=args.archimedean_certificate,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        "combined-symbol newest-energy PASS: K >= "
        f"{result['threshold']['first_passing_previous_cutoff']}, "
        f"finite bridges={result['finite_reduction']['finite_newest_channel_bridge_count']}"
    )
    print(f"artifact: {args.json_out.resolve()}")
    print(f"sha256: {_sha256(args.json_out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
