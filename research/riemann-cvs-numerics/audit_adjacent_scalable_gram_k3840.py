#!/usr/bin/env python3
"""Cross-audit the scalable K3840 Grams against explicit Arb rows.

The scalable certifier replaces explicit K-by-rank factors by partial-fraction
moments.  This regression rebuilds the manageable K=3840 factors directly and
checks all seven centered Grams entrywise.  It also certifies strict positivity
of

    scalable Young majorant + relative_slack * dyadic_scale * I - exact Gram.

The scale is the next power of two above the midpoint spectral radius, so the
absolute identity slack remains an exact rational and the relative size is
explicit.  Young's inequality gives the unslacked semidefinite domination
algebraically; this numerical regression is only a strict cross-audit of the
slacked difference and is not presented as a proof of strict positivity for
the unslacked matrix.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gc
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import numpy as np
from flint import arb, arb_mat, ctx

from certify_adjacent_compressed_gram import (
    _adi_factors,
    _column_stack,
    _fraction_arb,
    _identity,
)
from certify_adjacent_compressed_gram_scalable import (
    assemble_left,
    assemble_right,
    build_family_data,
    build_moments,
    certify_positive_matrix,
    git_sha,
    gram_upper_majorant,
    partial_fraction_transform,
    principal,
    script_hash,
)
from certify_direct_parity_relative_shell import DirectParityKernel
from certify_preconditioned_relative_shell import (
    _midpoint_numpy,
    _sha256,
    _symmetrize_enclosure,
)


MODE = 3840
SAME_FACTORS = 64
REFLECTED_FACTORS = 12


def progress(message: str) -> None:
    print(f"[adjacent-scalable-k3840-audit] {message}", flush=True)


def positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be strictly positive")
    return value


def explicit_factors(
    *,
    mode: int,
    roots: list[arb],
    poles: list[arb],
    reflected: bool,
    symbol: list[arb],
) -> tuple[arb_mat, arb_mat]:
    row_modes = list(range(mode + 1, 2 * mode + 1))
    column_modes = list(range(2 * mode + 1, 4 * mode + 1))
    diagonal_left = [
        _fraction_arb(Fraction(value, mode)) for value in row_modes
    ]
    diagonal_right = [
        (-1 if reflected else 1) * _fraction_arb(Fraction(value, mode))
        for value in column_modes
    ]
    scale = arb(mode).sqrt()
    generator_left = [
        (-symbol[value] / scale, 1 / scale) for value in row_modes
    ]
    generator_right = [
        (
            1 / scale,
            (-1 if reflected else 1) * symbol[value] / scale,
        )
        for value in column_modes
    ]
    return _adi_factors(
        diagonal_left=diagonal_left,
        diagonal_right=diagonal_right,
        generator_left=generator_left,
        generator_right=generator_right,
        roots=roots,
        poles=poles,
    )


def explicit_gramians(
    left_same: arb_mat,
    right_same: arb_mat,
    left_reflected: arb_mat,
    right_reflected: arb_mat,
) -> dict[str, arb_mat]:
    combined_left = _column_stack(left_same, left_reflected)
    even_right = _column_stack(
        right_same, right_reflected, first_sign=-1, second_sign=-1
    )
    odd_right = _column_stack(
        right_same, right_reflected, first_sign=-1, second_sign=1
    )
    factors = {
        "same_left": left_same,
        "same_right": right_same,
        "reflected_left": left_reflected,
        "reflected_right": right_reflected,
        "combined_left": combined_left,
        "even_right": even_right,
        "odd_right": odd_right,
    }
    result: dict[str, arb_mat] = {}
    for label, factor in factors.items():
        gram = factor.transpose() * factor
        _symmetrize_enclosure(gram)
        result[label] = gram
    return result


def scalable_grams(
    *, mode: int, precision: int, eta: Fraction
) -> tuple[
    dict[str, arb_mat],
    dict[str, arb_mat],
    tuple[list[arb], list[arb], list[arb], list[arb]],
    dict[str, Any],
]:
    (
        same_roots,
        same_poles,
        reflected_roots,
        reflected_poles,
        geometry,
    ) = build_family_data(mode, SAME_FACTORS, REFLECTED_FACTORS)
    left_same_basis, left_same_transform = partial_fraction_transform(
        same_roots, same_poles, side="left"
    )
    left_reflected_basis, left_reflected_transform = partial_fraction_transform(
        reflected_roots, reflected_poles, side="left"
    )
    right_same_basis, right_same_transform = partial_fraction_transform(
        same_roots, same_poles, side="right"
    )
    right_reflected_basis, right_reflected_transform = partial_fraction_transform(
        reflected_roots,
        reflected_poles,
        side="right",
        argument_sign=-1,
    )
    left_h0, left_h1, left_h2, left_stats = build_moments(
        mode=mode,
        lo=mode + 1,
        hi=2 * mode,
        families=[
            (left_same_basis, left_same_transform),
            (left_reflected_basis, left_reflected_transform),
        ],
        c=13,
        precision=precision,
    )
    right_h0, right_h1, right_h2, right_stats = build_moments(
        mode=mode,
        lo=2 * mode + 1,
        hi=4 * mode,
        families=[
            (right_same_basis, right_same_transform),
            (right_reflected_basis, right_reflected_transform),
        ],
        c=13,
        precision=precision,
    )

    same_left_h0 = principal(left_h0, 0, SAME_FACTORS)
    reflected_left_h0 = principal(
        left_h0, SAME_FACTORS, REFLECTED_FACTORS
    )
    same_right_h0 = principal(right_h0, 0, SAME_FACTORS)
    reflected_right_h0 = principal(
        right_h0, SAME_FACTORS, REFLECTED_FACTORS
    )
    symbol_signs = [1] * SAME_FACTORS + [-1] * REFLECTED_FACTORS
    odd_column_signs = [-1] * SAME_FACTORS + [1] * REFLECTED_FACTORS
    centers = {
        "same_left": assemble_left(
            same_left_h0,
            principal(left_h1, 0, SAME_FACTORS),
            principal(left_h2, 0, SAME_FACTORS),
        ),
        "same_right": assemble_right(
            same_right_h0,
            principal(right_h1, 0, SAME_FACTORS),
            principal(right_h2, 0, SAME_FACTORS),
            [1] * SAME_FACTORS,
        ),
        "reflected_left": assemble_left(
            reflected_left_h0,
            principal(left_h1, SAME_FACTORS, REFLECTED_FACTORS),
            principal(left_h2, SAME_FACTORS, REFLECTED_FACTORS),
        ),
        "reflected_right": assemble_right(
            reflected_right_h0,
            principal(right_h1, SAME_FACTORS, REFLECTED_FACTORS),
            principal(right_h2, SAME_FACTORS, REFLECTED_FACTORS),
            [-1] * REFLECTED_FACTORS,
        ),
        "combined_left": assemble_left(left_h0, left_h1, left_h2),
        "even_right": assemble_right(
            right_h0, right_h1, right_h2, symbol_signs
        ),
        "odd_right": assemble_right(
            right_h0,
            right_h1,
            right_h2,
            symbol_signs,
            odd_column_signs,
        ),
    }
    majorants = {
        "same_left": gram_upper_majorant(
            center=centers["same_left"],
            h0=same_left_h0,
            minimum_mode=mode + 1,
            eta=eta,
            error_slot="first",
        ),
        "same_right": gram_upper_majorant(
            center=centers["same_right"],
            h0=same_right_h0,
            minimum_mode=2 * mode + 1,
            eta=eta,
            error_slot="second",
            signs=[1] * SAME_FACTORS,
        ),
        "reflected_left": gram_upper_majorant(
            center=centers["reflected_left"],
            h0=reflected_left_h0,
            minimum_mode=mode + 1,
            eta=eta,
            error_slot="first",
        ),
        "reflected_right": gram_upper_majorant(
            center=centers["reflected_right"],
            h0=reflected_right_h0,
            minimum_mode=2 * mode + 1,
            eta=eta,
            error_slot="second",
            signs=[-1] * REFLECTED_FACTORS,
        ),
        "combined_left": gram_upper_majorant(
            center=centers["combined_left"],
            h0=left_h0,
            minimum_mode=mode + 1,
            eta=eta,
            error_slot="first",
        ),
        "even_right": gram_upper_majorant(
            center=centers["even_right"],
            h0=right_h0,
            minimum_mode=2 * mode + 1,
            eta=eta,
            error_slot="second",
            signs=symbol_signs,
        ),
        "odd_right": gram_upper_majorant(
            center=centers["odd_right"],
            h0=right_h0,
            minimum_mode=2 * mode + 1,
            eta=eta,
            error_slot="second",
            signs=[-1] * (SAME_FACTORS + REFLECTED_FACTORS),
        ),
    }
    return (
        centers,
        majorants,
        (same_roots, same_poles, reflected_roots, reflected_poles),
        {
            "shift_geometry": geometry,
            "source_moments": left_stats,
            "target_moments": right_stats,
        },
    )


def compare_entrywise(
    left: arb_mat, right: arb_mat, *, label: str
) -> dict[str, float | int | str]:
    if left.nrows() != right.nrows() or left.ncols() != right.ncols():
        raise ValueError(f"{label} dimensions differ")
    count = left.nrows() * left.ncols()
    containing = 0
    max_midpoint = 0.0
    max_radius = 0.0
    for i in range(left.nrows()):
        for j in range(left.ncols()):
            difference = left[i, j] - right[i, j]
            if difference.contains(0):
                containing += 1
            max_midpoint = max(max_midpoint, abs(float(difference.mid())))
            max_radius = max(max_radius, float(difference.rad()))
    if containing != count:
        raise RuntimeError(
            f"{label} has only {containing}/{count} differences containing zero"
        )
    return {
        "label": label,
        "entries": count,
        "differences_containing_zero": containing,
        "max_midpoint_abs": max_midpoint,
        "max_radius": max_radius,
    }


def audit(
    *,
    precision: int,
    eta: Fraction,
    relative_identity_slack: Fraction,
    json_out: Path,
) -> dict[str, Any]:
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    ctx.prec = precision
    ctx.threads = 1
    started = time.time()

    progress("building scalable centered Grams and Young majorants")
    centers, majorants, roots_and_poles, scalable_metadata = scalable_grams(
        mode=MODE, precision=precision, eta=eta
    )
    same_roots, same_poles, reflected_roots, reflected_poles = roots_and_poles

    progress("building the explicit finite symbol rows")
    kernel = DirectParityKernel.build(c=13, cutoff=4 * MODE, precision=precision)
    exact_symbol = [
        (kernel.S[index] + kernel.prime_sine[index]) / kernel.pi
        for index in range(4 * MODE + 1)
    ]
    centered_symbol = [
        arb(1) / 4 + kernel.prime_sine[index] / kernel.pi
        for index in range(4 * MODE + 1)
    ]

    center_same = explicit_factors(
        mode=MODE,
        roots=same_roots,
        poles=same_poles,
        reflected=False,
        symbol=centered_symbol,
    )
    center_reflected = explicit_factors(
        mode=MODE,
        roots=reflected_roots,
        poles=reflected_poles,
        reflected=True,
        symbol=centered_symbol,
    )
    explicit_centers = explicit_gramians(
        center_same[0], center_same[1], center_reflected[0], center_reflected[1]
    )
    center_audits = []
    for label, scalable_center in centers.items():
        record = compare_entrywise(
            scalable_center, explicit_centers[label], label=label
        )
        center_audits.append(record)
        progress(f"center equality passed for {label}")
    del center_same, center_reflected, explicit_centers, centered_symbol
    gc.collect()

    exact_same = explicit_factors(
        mode=MODE,
        roots=same_roots,
        poles=same_poles,
        reflected=False,
        symbol=exact_symbol,
    )
    exact_reflected = explicit_factors(
        mode=MODE,
        roots=reflected_roots,
        poles=reflected_poles,
        reflected=True,
        symbol=exact_symbol,
    )
    exact_grams = explicit_gramians(
        exact_same[0], exact_same[1], exact_reflected[0], exact_reflected[1]
    )
    del exact_same, exact_reflected, exact_symbol, kernel
    gc.collect()

    stem = json_out.with_suffix("")
    majorant_audits = []
    for label, majorant in majorants.items():
        unslacked = majorant - exact_grams[label]
        _symmetrize_enclosure(unslacked)
        unslacked_eigenvalues = np.linalg.eigvalsh(_midpoint_numpy(unslacked))
        unslacked_midpoint_minimum = float(unslacked_eigenvalues[0])
        unslacked_midpoint_maximum = float(unslacked_eigenvalues[-1])
        spectral_radius = max(
            1.0,
            abs(unslacked_midpoint_minimum),
            abs(unslacked_midpoint_maximum),
        )
        scale_exponent = max(0, math.ceil(math.log2(spectral_radius)))
        dyadic_scale = 1 << scale_exponent
        absolute_identity_slack = relative_identity_slack * dyadic_scale
        slacked = unslacked + _identity(
            unslacked.nrows(), _fraction_arb(absolute_identity_slack)
        )
        _symmetrize_enclosure(slacked)
        slacked_midpoint_minimum = float(
            np.linalg.eigvalsh(_midpoint_numpy(slacked))[0]
        )
        if slacked_midpoint_minimum <= 0:
            raise RuntimeError(f"{label} slacked difference is not midpoint positive")
        progress(
            f"{label}: midpoint minima unslacked="
            f"{unslacked_midpoint_minimum:.6e}, slacked="
            f"{slacked_midpoint_minimum:.6e}; dyadic scale={dyadic_scale}"
        )
        certificate = certify_positive_matrix(
            matrix=slacked,
            label=f"{label} Young majorant plus identity slack minus exact Gram",
            preconditioner_path=stem.with_name(
                stem.name + f"_{label}_slacked_preconditioner.npy"
            ),
        )
        majorant_audits.append(
            {
                "label": label,
                "dimension": slacked.nrows(),
                "relative_identity_slack": str(relative_identity_slack),
                "dyadic_spectral_scale": dyadic_scale,
                "absolute_identity_slack": str(absolute_identity_slack),
                "unslacked_midpoint_minimum_eigenvalue_diagnostic": (
                    unslacked_midpoint_minimum
                ),
                "unslacked_midpoint_maximum_eigenvalue_diagnostic": (
                    unslacked_midpoint_maximum
                ),
                "slacked_midpoint_minimum_eigenvalue_diagnostic": (
                    slacked_midpoint_minimum
                ),
                "slacked_strict_positive_certificate": certificate,
                "proof_boundary": (
                    "the certificate proves strict positivity only after the "
                    "displayed identity slack; unslacked Young PSD domination "
                    "is the separate algebraic argument used by the certifier"
                ),
            }
        )
        progress(f"slacked majorant audit passed for {label}")
        del unslacked, slacked
        gc.collect()

    script_path = Path(__file__).resolve()
    dependency_paths = [
        script_path.parent / "certify_adjacent_compressed_gram.py",
        script_path.parent / "certify_adjacent_compressed_gram_scalable.py",
        script_path.parent / "certify_direct_parity_relative_shell.py",
        script_path.parent / "certify_preconditioned_relative_shell.py",
    ]
    return {
        "status": "PASS",
        "rigorous_interval_cross_audit": True,
        "scope": "K3840 scalable partial-fraction Gram regression",
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "git_sha": git_sha(),
        "script_sha256": script_hash(script_path),
        "dependency_sha256": {
            path.name: script_hash(path) for path in dependency_paths
        },
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "precision_bits": precision,
        "flint_threads": 1,
        "mode": MODE,
        "same_sign_factor_count": SAME_FACTORS,
        "reflected_factor_count": REFLECTED_FACTORS,
        "combined_rank_upper": 2 * (SAME_FACTORS + REFLECTED_FACTORS),
        "young_eta": str(eta),
        "relative_identity_slack": str(relative_identity_slack),
        "scalable_metadata": scalable_metadata,
        "center_entrywise_audits": center_audits,
        "slacked_majorant_audits": majorant_audits,
        "center_conclusion": (
            "all seven scalable centered Grams are entrywise Arb enclosures "
            "of the corresponding explicit-row Grams"
        ),
        "young_majorant_boundary": (
            "the production certifier relies on the algebraic Young PSD "
            "inequality; the strict numerical certificates here apply only "
            "to majorant + relative_identity_slack*dyadic_scale*I - exact Gram"
        ),
        "timings_seconds": {"total": round(time.time() - started, 3)},
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--young-eta", default="1/100000")
    parser.add_argument("--relative-identity-slack", default="1/1000000")
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    payload = audit(
        precision=args.prec,
        eta=positive_fraction(args.young_eta, "young-eta"),
        relative_identity_slack=positive_fraction(
            args.relative_identity_slack, "relative-identity-slack"
        ),
        json_out=args.json_out,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"K3840 scalable Gram regression PASS: precision={payload['precision_bits']}"
    )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
