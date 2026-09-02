#!/usr/bin/env python3
"""Certify finite source moments and parity energy floors below mode 960.

The analytic V23 low-frontier transport starts uniformly at source base
``B = 960``.  For the three smaller standard source shells

    (120, 240], (240, 480], (480, 960],

the Lean bridge in ``FiniteMomentLowModeTransport.lean`` needs only:

* an upper bound for ``sum n^2 F(n)^2`` in the even sector;
* an upper bound for ``sum F(n)^2`` in the odd sector; and
* a lower eigenvalue bound for each unshifted parity shell matrix.

Here ``F`` is the complete c=13 builder Loewner symbol: rational pole minus
the Fourier-normalized Archimedean-plus-prime symbol.  This script evaluates
all symbol values and all matrix entries directly with Arb intervals.  Each
energy-floor claim is reduced to positive definiteness of ``H - gap I`` and
proved by a fixed exact-dyadic congruence followed by strict interval
Gershgorin margins.  Floating Cholesky selects the congruence only; its entries
are embedded as exact dyadic Arb values before any proof check.

The weaker interval ``(20,120]`` is additionally split at modes 30 and 60.
This coercivity-adapted, nonuniform partition produces three more source
certificates on ``(20,30]``, ``(30,60]``, and ``(60,120]``.  The resulting
JSON is a finite external certificate for all literal constants used by the
Lean specializations.  It does not certify the remote target shell: that side
is discharged analytically in Lean.
"""

from __future__ import annotations

import argparse
import datetime as dt
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
    _validate_direct_construction,
)
from certify_odd_fixed_base_channel import _certify_positive_matrix
from certify_preconditioned_relative_shell import _fraction_arb, _sha256
from flint import arb, arb_mat, ctx

Sector = Literal["even", "odd"]


SOURCE_SPECS: dict[int, dict[str, Fraction]] = {
    120: {
        "gap": Fraction(137, 100),
        "even_second_moment_upper": Fraction(735000),
        "odd_zero_moment_upper": Fraction(219, 10),
        "relative_budget": Fraction(1, 795),
    },
    240: {
        "gap": Fraction(177, 100),
        "even_second_moment_upper": Fraction(6274000),
        "odd_zero_moment_upper": Fraction(47),
        "relative_budget": Fraction(1, 500),
    },
    480: {
        "gap": Fraction(129, 50),
        "even_second_moment_upper": Fraction(49740000),
        "odd_zero_moment_upper": Fraction(92),
        "relative_budget": Fraction(1, 350),
    },
}

RESIDUAL_SOURCE_SPECS: tuple[dict[str, int | Fraction], ...] = (
    {
        "start": 60,
        "dimension": 60,
        "gap": Fraction(22, 25),
        "even_second_moment_upper": Fraction(107500),
        "odd_zero_moment_upper": Fraction(49, 4),
        "mode_second_moment": 509410,
        "relative_budget": Fraction(1, 900),
    },
    {
        "start": 30,
        "dimension": 30,
        "gap": Fraction(49, 100),
        "even_second_moment_upper": Fraction(12110),
        "odd_zero_moment_upper": Fraction(27, 5),
        "mode_second_moment": 64355,
        "relative_budget": Fraction(1, 900),
    },
    {
        "start": 20,
        "dimension": 10,
        "gap": Fraction(19, 100),
        "even_second_moment_upper": Fraction(1530),
        "odd_zero_moment_upper": Fraction(47, 20),
        "mode_second_moment": 6585,
        "relative_budget": Fraction(1, 900),
    },
)


def _progress(message: str) -> None:
    print(f"[finite-source] {message}", flush=True)


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


def _dependency_record(path: Path) -> dict[str, str]:
    return {"path": str(path.resolve()), "sha256": _sha256(path.resolve())}


def _ball_record(value: arb) -> dict[str, Any]:
    """A stable human-readable record of one rigorous Arb enclosure."""

    return {
        "arb": str(value),
        "midpoint": str(value.mid()),
        "radius": str(value.rad()),
    }


def _builder_symbol(kernel: DirectParityKernel, n: int) -> arb:
    """Evaluate the literal Lean ``c13HistoricalBuilderLoewnerSymbol``.

    ``kernel.S + kernel.prime_sine`` is the raw logarithmic combined symbol.
    The finite CvS matrix uses Fourier normalization by pi.  The rational pole
    symbol is ``-prefactor*n/(L^2 + 16*pi^2*n^2)``.
    """

    if not 0 <= n <= kernel.cutoff:
        raise IndexError("symbol mode outside the direct parity kernel")
    denominator = kernel.L * kernel.L + 16 * kernel.pi * kernel.pi * n * n
    pole = -(kernel.prefactor * n / denominator)
    combined = (kernel.S[n] + kernel.prime_sine[n]) / kernel.pi
    return pole - combined


def _source_interval_matrix(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    start: int,
    dimension: int,
    gap: Fraction,
) -> arb_mat:
    """Build ``H_sector[(start,start+dimension]] - gap I`` directly."""

    modes = list(range(start + 1, start + dimension + 1))
    matrix = arb_mat(dimension, dimension)
    gap_ball = _fraction_arb(gap)
    for i, k in enumerate(modes):
        for j in range(i, dimension):
            value = kernel.parity_entry(sector, k, modes[j])
            if i == j:
                value -= gap_ball
            matrix[i, j] = value
            matrix[j, i] = value
    return matrix


def _source_interval_moments(
    *, kernel: DirectParityKernel, start: int, dimension: int
) -> tuple[arb, arb, dict[str, Any]]:
    """Enclose the two builder-symbol moments on a finite interval."""

    started = time.time()
    even_second = arb(0)
    odd_zero = arb(0)
    for n in range(start + 1, start + dimension + 1):
        value = _builder_symbol(kernel, n)
        square = value * value
        even_second += n * n * square
        odd_zero += square
    return even_second, odd_zero, {
        "mode_range": [start + 1, start + dimension],
        "mode_count": dimension,
        "seconds": round(time.time() - started, 3),
        "formula": {
            "builder_symbol": (
                "-prefactor*n/(L^2+16*pi^2*n^2) "
                "- (S[n]+prime_sine[n])/pi"
            ),
            "even_second_moment": "sum n^2 * builder_symbol(n)^2",
            "odd_zero_moment": "sum builder_symbol(n)^2",
        },
    }


def _strict_upper_certificate(
    *, value: arb, upper: Fraction, label: str
) -> dict[str, Any]:
    upper_ball = _fraction_arb(upper)
    slack = upper_ball - value
    if not value <= upper_ball:
        raise RuntimeError(
            f"{label} is not rigorously bounded by {upper}: value={value}"
        )
    if not slack > 0:
        raise RuntimeError(f"{label} has no strictly positive interval slack")
    return {
        "status": "PASS",
        "label": label,
        "value_enclosure": _ball_record(value),
        "rational_upper": str(upper),
        "strict": True,
        "slack_enclosure": _ball_record(slack),
    }


def certify(
    *,
    c: int,
    precision: int,
    threads: int,
    bases: list[int],
    validate_cutoff: int | None,
    json_out: Path,
) -> dict[str, Any]:
    if c != 13:
        raise ValueError("the current Lean specializations are literal c=13")
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if threads < 1:
        raise ValueError("threads must be positive")
    if not bases:
        raise ValueError("at least one source base is required")
    unknown = sorted(set(bases) - set(SOURCE_SPECS))
    if unknown:
        raise ValueError(f"no literal Lean source specification for {unknown}")
    if len(set(bases)) != len(bases):
        raise ValueError("source bases must not be repeated")

    bases = sorted(bases)
    cutoff = 2 * max(bases)
    if validate_cutoff is not None and not 1 <= validate_cutoff <= cutoff:
        raise ValueError("validate_cutoff must lie between one and the cutoff")
    ctx.prec = precision
    ctx.threads = threads
    started = time.time()
    validation = (
        _validate_direct_construction(
            c=c,
            cutoff=validate_cutoff,
            precision=precision,
        )
        if validate_cutoff is not None
        else None
    )
    if validation is not None:
        _progress(
            "canonical direct-parity replay passed through "
            f"{validate_cutoff}"
        )
    kernel = DirectParityKernel.build(c=c, cutoff=cutoff, precision=precision)
    _progress(
        f"built direct c={c} parity kernel through {cutoff} in "
        f"{kernel.build_seconds:.3f}s"
    )

    stem = json_out.with_suffix("")
    source_certificates: dict[str, Any] = {}
    for base in bases:
        spec = SOURCE_SPECS[base]
        _progress(f"enclosing source-symbol moments for B={base}")
        even_second, odd_zero, moment_construction = _source_interval_moments(
            kernel=kernel, start=base, dimension=base
        )
        even_moment_certificate = _strict_upper_certificate(
            value=even_second,
            upper=spec["even_second_moment_upper"],
            label=f"B={base} even source second moment",
        )
        odd_moment_certificate = _strict_upper_certificate(
            value=odd_zero,
            upper=spec["odd_zero_moment_upper"],
            label=f"B={base} odd source zero moment",
        )

        parity_energy: dict[str, Any] = {}
        for sector in ("even", "odd"):
            _progress(
                f"proving B={base} {sector} shell floor "
                f">= {spec['gap']}"
            )
            matrix_started = time.time()
            matrix = _source_interval_matrix(
                kernel=kernel,
                sector=sector,
                start=base,
                dimension=base,
                gap=spec["gap"],
            )
            matrix_seconds = time.time() - matrix_started
            preconditioner_path = stem.with_name(
                f"{stem.name}_B{base}_{sector}_preconditioner.npy"
            )
            positive = _certify_positive_matrix(
                matrix=matrix,
                label=(
                    f"c=13 unshifted {sector} source shell "
                    f"({base},{2 * base}] minus {spec['gap']} I"
                ),
                preconditioner_path=preconditioner_path,
            )
            parity_energy[sector] = {
                "status": "PASS",
                "source_gap": str(spec["gap"]),
                "matrix_mode_range": [base + 1, 2 * base],
                "matrix_dimension": base,
                "matrix_construction_seconds": round(matrix_seconds, 3),
                "strict_positive_matrix": positive,
                "quadratic_form_consequence": (
                    f"{spec['gap']} * sum_i x_i^2 <="
                    f" H_{sector},B(x,x)"
                ),
            }

        source_certificates[str(base)] = {
            "status": "PASS",
            "base": base,
            "source_modes": [base + 1, 2 * base],
            "relative_budget_at_target_15360": str(spec["relative_budget"]),
            "moment_construction": moment_construction,
            "even_second_moment": even_moment_certificate,
            "odd_zero_moment": odd_moment_certificate,
            "energy_floors": parity_energy,
            "lean_certificate_types": {
                "even": (
                    "C13EvenFiniteSourceMomentCertificate "
                    f"{base} {spec['even_second_moment_upper']} {spec['gap']}"
                ),
                "odd": (
                    "C13OddFiniteSourceMomentCertificate "
                    f"{base} {spec['odd_zero_moment_upper']} {spec['gap']}"
                ),
            },
        }

    residual_source_certificates: dict[str, Any] = {}
    for residual in RESIDUAL_SOURCE_SPECS:
        residual_start = int(residual["start"])
        residual_dimension = int(residual["dimension"])
        residual_end = residual_start + residual_dimension
        residual_gap = Fraction(residual["gap"])
        residual_key = f"{residual_start + 1}-{residual_end}"
        _progress(
            "enclosing residual source-symbol moments on "
            f"({residual_start},{residual_end}]"
        )
        residual_even, residual_odd, residual_moment_construction = (
            _source_interval_moments(
                kernel=kernel,
                start=residual_start,
                dimension=residual_dimension,
            )
        )
        residual_even_certificate = _strict_upper_certificate(
            value=residual_even,
            upper=Fraction(residual["even_second_moment_upper"]),
            label=(
                f"({residual_start},{residual_end}] even source second moment"
            ),
        )
        residual_odd_certificate = _strict_upper_certificate(
            value=residual_odd,
            upper=Fraction(residual["odd_zero_moment_upper"]),
            label=f"({residual_start},{residual_end}] odd source zero moment",
        )
        residual_mode_second = sum(
            n * n for n in range(residual_start + 1, residual_end + 1)
        )
        if residual_mode_second != int(residual["mode_second_moment"]):
            raise RuntimeError("an exact residual source mode moment changed")

        residual_energy: dict[str, Any] = {}
        for sector in ("even", "odd"):
            _progress(
                f"proving residual {sector} floor on "
                f"({residual_start},{residual_end}] >= {residual_gap}"
            )
            matrix_started = time.time()
            matrix = _source_interval_matrix(
                kernel=kernel,
                sector=sector,
                start=residual_start,
                dimension=residual_dimension,
                gap=residual_gap,
            )
            matrix_seconds = time.time() - matrix_started
            preconditioner_path = stem.with_name(
                f"{stem.name}_B{residual_start}to{residual_end}_"
                f"{sector}_preconditioner.npy"
            )
            positive = _certify_positive_matrix(
                matrix=matrix,
                label=(
                    f"c=13 unshifted {sector} residual source interval "
                    f"({residual_start},{residual_end}] minus "
                    f"{residual_gap} I"
                ),
                preconditioner_path=preconditioner_path,
            )
            residual_energy[sector] = {
                "status": "PASS",
                "source_gap": str(residual_gap),
                "matrix_mode_range": [residual_start + 1, residual_end],
                "matrix_dimension": residual_dimension,
                "matrix_construction_seconds": round(matrix_seconds, 3),
                "strict_positive_matrix": positive,
                "quadratic_form_consequence": (
                    f"{residual_gap} * sum_i x_i^2 <= "
                    f"H_{sector},({residual_start},{residual_end}](x,x)"
                ),
            }

        residual_source_certificates[residual_key] = {
            "status": "PASS",
            "start": residual_start,
            "dimension": residual_dimension,
            "source_modes": [residual_start + 1, residual_end],
            "relative_budget_at_target_15360": str(
                residual["relative_budget"]
            ),
            "exact_mode_second_moment": residual_mode_second,
            "moment_construction": residual_moment_construction,
            "even_second_moment": residual_even_certificate,
            "odd_zero_moment": residual_odd_certificate,
            "energy_floors": residual_energy,
            "lean_certificate_types": {
                "even": (
                    "C13EvenFiniteIntervalSourceCertificate "
                    f"{residual_start} {residual_dimension} "
                    f"{residual['even_second_moment_upper']} {residual_gap}"
                ),
                "odd": (
                    "C13OddFiniteIntervalSourceCertificate "
                    f"{residual_start} {residual_dimension} "
                    f"{residual_mode_second} "
                    f"{residual['odd_zero_moment_upper']} {residual_gap}"
                ),
            },
        }

    script_path = Path(__file__).resolve()
    direct_script = script_path.with_name(
        "certify_direct_parity_relative_shell.py"
    )
    fixed_base_script = script_path.with_name(
        "certify_odd_fixed_base_channel.py"
    )
    preconditioned_script = script_path.with_name(
        "certify_preconditioned_relative_shell.py"
    )
    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "finite Arb source-symbol moments and unshifted parity energy "
            "floors for three standard below-frontier shells and the three "
            "coercivity-adapted residual intervals covering (20,120]"
        ),
        "c": c,
        "precision_bits": precision,
        "flint_threads": threads,
        "source_bases": bases,
        "target_base_used_by_lean": 15360,
        "direct_formula_validation": validation,
        "kernel": {
            "cutoff": cutoff,
            "precision_bits": precision,
            "prime_power_count": len(kernel.prime_powers),
            "prime_powers": [
                {"q": q, "base_prime": p} for q, p in kernel.prime_powers
            ],
            "one_dimensional_prime_aggregation": True,
            "build_seconds": round(kernel.build_seconds, 3),
        },
        "source_certificates": source_certificates,
        "residual_source_certificates": residual_source_certificates,
        "proof_chain": [
            "direct Arb formulas enclose the complete c=13 builder symbol",
            "Arb summation proves each rational source-moment upper bound",
            "direct Arb parity formulas enclose every source-shell entry",
            "the rational source gap is subtracted from the exact diagonal",
            "a floating Cholesky basis is embedded as exact dyadic Arb data",
            "strict interval Gershgorin margins prove H-gap*I positive",
            "the Lean bridge combines these finite sources with analytic target bounds",
        ],
        "source_dependencies": {
            "direct_parity": _dependency_record(direct_script),
            "positive_matrix_utility": _dependency_record(fixed_base_script),
            "exact_dyadic_utility": _dependency_record(preconditioned_script),
        },
        "lean_targets": [
            "RiemannCvs.V23BoundaryWeylMainline.C13EvenFiniteSourceMomentCertificate",
            "RiemannCvs.V23BoundaryWeylMainline.C13OddFiniteSourceMomentCertificate",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteEvenBuilder_480_15360_relative_oneOver350",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteOddBuilder_480_15360_relative_oneOver350",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteEvenBuilder_240_15360_relative_oneOver500",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteOddBuilder_240_15360_relative_oneOver500",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteEvenBuilder_120_15360_relative_oneOver795",
            "RiemannCvs.V23BoundaryWeylMainline.c13HistoricalRemoteOddBuilder_120_15360_relative_oneOver795",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteEvenBuilder_60_60_15360_relative_oneOver900",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteOddBuilder_60_60_15360_relative_oneOver900",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteEvenBuilder_30_30_15360_relative_oneOver900",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteOddBuilder_30_30_15360_relative_oneOver900",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteEvenBuilder_20_10_15360_relative_oneOver900",
            "RiemannCvs.V23BoundaryWeylMainline.c13FiniteIntervalRemoteOddBuilder_20_10_15360_relative_oneOver900",
        ],
        "timings_seconds": {
            "kernel": round(kernel.build_seconds, 3),
            "total": round(time.time() - started, 3),
        },
        "remaining_boundary": (
            "the structured fixed modes [1,20] and the closed "
            "infinite-dimensional boundary-Weyl operator passage remain "
            "separate obligations"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument(
        "--validate-cutoff",
        type=int,
        default=120,
        help="canonical full-matrix replay cutoff; use 0 to omit",
    )
    parser.add_argument(
        "--base",
        type=int,
        action="append",
        dest="bases",
        help="source base to certify; repeat for several (default: 120,240,480)",
    )
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = certify(
        c=args.c,
        precision=args.prec,
        threads=args.threads,
        bases=args.bases or [120, 240, 480],
        validate_cutoff=(args.validate_cutoff or None),
        json_out=args.json_out,
    )
    payload.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(
                timespec="seconds"
            ),
            "python_version": platform.python_version(),
            "numpy_version": np.__version__,
            "python_flint_version": flint.__version__,
            "platform": platform.platform(),
            "git_sha": _git_sha(),
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest().upper(),
        }
    )
    encoded = json.dumps(payload, indent=2, sort_keys=True, allow_nan=False)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")

    print(
        "finite source moment/floor certificate PASS: "
        f"bases={','.join(map(str, payload['source_bases']))}, "
        f"precision={payload['precision_bits']} bits"
    )
    for base in payload["source_bases"]:
        source = payload["source_certificates"][str(base)]
        even = source["energy_floors"]["even"]["strict_positive_matrix"]
        odd = source["energy_floors"]["odd"]["strict_positive_matrix"]
        print(
            f"  B={base}: even_moment<="
            f"{source['even_second_moment']['rational_upper']} "
            f"odd_moment<={source['odd_zero_moment']['rational_upper']} "
            f"gap={source['energy_floors']['even']['source_gap']}"
        )
        print(
            "    strict_gershgorin even="
            f"{even['gershgorin']['strictly_positive_rows']}/"
            f"{even['gershgorin']['dimension']} odd="
            f"{odd['gershgorin']['strictly_positive_rows']}/"
            f"{odd['gershgorin']['dimension']}"
        )
    for key, residual in payload["residual_source_certificates"].items():
        residual_even = residual["energy_floors"]["even"][
            "strict_positive_matrix"
        ]
        residual_odd = residual["energy_floors"]["odd"][
            "strict_positive_matrix"
        ]
        print(
            f"  residual {key}: even_moment<="
            f"{residual['even_second_moment']['rational_upper']} "
            f"odd_moment<={residual['odd_zero_moment']['rational_upper']} "
            f"gap={residual['energy_floors']['even']['source_gap']}"
        )
        print(
            "    strict_gershgorin even="
            f"{residual_even['gershgorin']['strictly_positive_rows']}/"
            f"{residual_even['gershgorin']['dimension']} odd="
            f"{residual_odd['gershgorin']['strictly_positive_rows']}/"
            f"{residual_odd['gershgorin']['dimension']}"
        )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
