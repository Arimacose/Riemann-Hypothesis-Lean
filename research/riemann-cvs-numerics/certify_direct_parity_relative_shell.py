#!/usr/bin/env python3
"""Certify a large relative-energy shell from direct Arb parity blocks.

The canonical finite certificate first constructs the full
``(2 * shell_cutoff + 1)`` matrix and only then compresses it into reflection
parity sectors.  That route duplicates reflection-related data and becomes the
dominant memory cost beyond cutoff 1920.  This script evaluates the exact even
and odd formulas directly and allocates only the three blocks required by the
Schur argument:

    rho R_q(core),       C_core,shell,       H_shell.

The prime-power contribution is aggregated into two one-dimensional Arb
sequences before any matrix entry is formed.  Thus the direct formulas retain
the cancellation in the full prime sum instead of bounding prime powers one at
a time.  Each sector is then certified by the same verified Arb solve, exact
dyadic congruence, and strict Gershgorin test used by
``certify_preconditioned_relative_shell.py``.

An optional small-cutoff replay compares every direct interval entry with the
canonical full-matrix construction and requires the difference interval to
contain zero.  This is a finite shell certificate; the all-cutoff analytic
estimate and the closed-tail operator passage remain separate obligations.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gc
import hashlib
import json
import os
import platform
import subprocess
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Literal

import flint
import numpy as np
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    arch_kappa,
    build_cutoff_free_matrix,
    closed_forms,
    parity_blocks,
    pole_J,
    prime_powers_up_to,
    reflection_symmetric_enclosure,
)
from certify_preconditioned_relative_shell import (
    _exact_upper_triangular,
    _fraction_arb,
    _gershgorin_certificate,
    _midpoint_numpy,
    _parity_dimension,
    _sha256,
    _symmetrize_enclosure,
    _validate_core_certificate as _validate_recursive_core_certificate,
    _verify_solve_residual,
)


Sector = Literal["even", "odd"]


def _progress(message: str) -> None:
    print(f"[direct-parity] {message}", flush=True)


def _positive_fraction(text: str, name: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    return value


def _repository_root() -> Path:
    completed = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return Path(completed.stdout.decode("utf-8").strip()).resolve()


def _verify_artifact_script_hash(
    payload: dict[str, Any], source_script: Path
) -> dict[str, Any]:
    """Match an artifact hash to the worktree or its recorded Git blob."""
    embedded = payload.get("script_sha256")
    if not isinstance(embedded, str) or len(embedded) != 64:
        raise ValueError("core certificate has no valid script_sha256")
    embedded = embedded.lower()
    current = hashlib.sha256(source_script.read_bytes()).hexdigest()
    if current == embedded:
        return {
            "sha256": embedded,
            "verification_mode": "current_worktree_file",
            "source_path": str(source_script.resolve()),
        }

    git_sha = payload.get("git_sha")
    if not isinstance(git_sha, str) or len(git_sha) != 40:
        raise ValueError(
            "core certificate script hash differs from the worktree and has "
            "no valid git_sha"
        )
    root = _repository_root()
    relative = source_script.resolve().relative_to(root).as_posix()
    completed = subprocess.run(
        ["git", "show", f"{git_sha}:{relative}"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    blob_hash = hashlib.sha256(completed.stdout).hexdigest()
    if blob_hash != embedded:
        raise ValueError(
            "core certificate script_sha256 matches neither the worktree nor "
            "the source blob at its recorded git_sha"
        )
    return {
        "sha256": embedded,
        "verification_mode": "recorded_git_blob",
        "git_sha": git_sha,
        "git_path": relative,
    }


def _validate_preconditioned_core_certificate(
    path: Path,
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shift_gain: Fraction,
    q_upper: Fraction,
) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    expected = {
        "status": "PASS",
        "rigorous_certificate": True,
        "c": c,
        "low_cutoff": low_cutoff,
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
    }
    for key, value in expected.items():
        if payload.get(key) != value:
            raise ValueError(
                f"preconditioned core field {key!r}: expected {value!r}, "
                f"got {payload.get(key)!r}"
            )

    certified_cutoff = payload.get("largest_cutoff")
    if not isinstance(certified_cutoff, int) or certified_cutoff < core_cutoff:
        raise ValueError(
            "preconditioned core certificate does not reach the requested cutoff"
        )
    prior_rho = Fraction(payload.get("rho_upper", "0"))
    if not 0 < prior_rho < 1:
        raise ValueError("preconditioned core certificate has invalid rho_upper")

    # A rigorous core can have been produced either by the first dense-parity
    # bridge or by this direct-parity continuation.  Older artifacts do not
    # carry an explicit generator tag, so identify the generator by the
    # embedded source hash rather than trusting a descriptive string.  This is
    # what lets the certified N=3840 direct shell become the core of the next
    # N=7680 shell without weakening source provenance.
    source_candidates = (
        Path(__file__),
        Path(__file__).with_name("certify_preconditioned_relative_shell.py"),
    )
    source_record = None
    source_errors: list[str] = []
    for source_script in source_candidates:
        try:
            source_record = _verify_artifact_script_hash(payload, source_script)
            break
        except ValueError as exc:
            source_errors.append(f"{source_script.name}: {exc}")
    if source_record is None:
        raise ValueError(
            "rigorous core certificate generator hash matches no supported "
            "source script; " + "; ".join(source_errors)
        )
    github_sha = os.environ.get("GITHUB_SHA")
    if github_sha is not None and payload.get("git_sha") != github_sha:
        raise ValueError("core certificate git_sha does not match GITHUB_SHA")

    sectors = {
        record.get("sector"): record for record in payload.get("sectors", [])
    }
    if set(sectors) != {"even", "odd"}:
        raise ValueError("preconditioned core must contain even and odd sectors")

    sector_records: list[dict[str, Any]] = []
    for sector_name in ("even", "odd"):
        sector = sectors[sector_name]
        expected_dimension = _parity_dimension(sector_name, certified_cutoff)
        if sector.get("status") != "PASS":
            raise ValueError(f"{sector_name} preconditioned sector did not pass")
        if sector.get("full_dimension") != expected_dimension:
            raise ValueError(f"{sector_name} preconditioned dimension is wrong")
        if sector.get("core_dimension", 0) + sector.get(
            "shell_dimension", 0
        ) != expected_dimension:
            raise ValueError(f"{sector_name} block dimensions do not add up")

        residual = sector.get("solve_residual", {})
        residual_total = residual.get("entry_count")
        if not isinstance(residual_total, int) or residual_total <= 0:
            raise ValueError(f"{sector_name} has no verified residual entries")
        if residual.get("entries_containing_zero") != residual_total:
            raise ValueError(f"{sector_name} verified residual is incomplete")

        preconditioner = sector.get("preconditioner", {})
        for field in (
            "upper_triangular",
            "all_dyadic_radii_zero",
            "all_diagonal_entries_positive",
        ):
            if preconditioner.get(field) is not True:
                raise ValueError(
                    f"{sector_name} preconditioner field {field!r} is not true"
                )
        recorded_preconditioner = Path(preconditioner.get("path", ""))
        local_preconditioner = path.with_name(recorded_preconditioner.name)
        if not local_preconditioner.is_file():
            raise ValueError(
                f"missing sibling {sector_name} preconditioner artifact: "
                f"{local_preconditioner}"
            )
        expected_hash = str(preconditioner.get("sha256", "")).upper()
        actual_hash = _sha256(local_preconditioner)
        if actual_hash != expected_hash:
            raise ValueError(
                f"{sector_name} preconditioner artifact hash does not match"
            )

        gershgorin = sector.get("gershgorin", {})
        shell_dimension = sector["shell_dimension"]
        if gershgorin.get("dimension") != shell_dimension:
            raise ValueError(f"{sector_name} Gershgorin dimension is wrong")
        if gershgorin.get("strictly_positive_rows") != shell_dimension:
            raise ValueError(
                f"{sector_name} Gershgorin transcript is not strictly positive"
            )

        sector_records.append(
            {
                "sector": sector_name,
                "final_dimension": expected_dimension,
                "solve_residual_entries": residual_total,
                "gershgorin_dimension": shell_dimension,
                "gershgorin_transcript_sha256": gershgorin.get(
                    "margin_transcript_sha256"
                ),
                "preconditioner_path": str(local_preconditioner.resolve()),
                "preconditioner_sha256": actual_hash,
            }
        )

    return {
        "certificate_kind": (
            "direct_parity_recursive_shell"
            if Path(source_record.get("source_path", source_record.get("git_path", ""))).name
            == Path(__file__).name
            else "preconditioned_recursive_shell"
        ),
        "path": str(path.resolve()),
        "sha256": _sha256(path),
        "git_sha": payload.get("git_sha"),
        "script": source_record,
        "precision_bits": payload.get("precision_bits"),
        "certified_through_cutoff": certified_cutoff,
        "requested_core_cutoff": core_cutoff,
        "prior_rho_upper": str(prior_rho),
        "principal_submatrix_consequence": (
            "the prior Schur certificate and rho<1 prove R_q positive through "
            "its largest cutoff; the requested leading section is positive"
        ),
        "sectors": sector_records,
    }


def _validate_any_core_certificate(
    path: Path,
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shift_gain: Fraction,
    q_upper: Fraction,
) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("rigorous_certificate") is True:
        return _validate_preconditioned_core_certificate(
            path,
            c=c,
            low_cutoff=low_cutoff,
            core_cutoff=core_cutoff,
            shift_gain=shift_gain,
            q_upper=q_upper,
        )
    recursive = _validate_recursive_core_certificate(
        path,
        c=c,
        low_cutoff=low_cutoff,
        core_cutoff=core_cutoff,
        shift_gain=shift_gain,
        q_upper=q_upper,
    )
    return {"certificate_kind": "recursive_interval_ldlt", **recursive}


@dataclass
class DirectParityKernel:
    cutoff: int
    precision: int
    L: arb
    pi: arb
    prefactor: arb
    sqrt_two: arb
    S: list[arb]
    pole_a: list[arb]
    pole_b: list[arb]
    diagonal_arch: list[arb]
    prime_sine: list[arb]
    prime_diagonal: list[arb]
    prime_powers: list[tuple[int, int]]
    build_seconds: float

    @classmethod
    def build(cls, *, c: int, cutoff: int, precision: int) -> DirectParityKernel:
        started = time.time()
        ctx.prec = precision
        S, CC, XC, L = closed_forms(cutoff, c, precision)
        pi = arb.pi()
        prefactor = 32 * L * (L / 4).sinh() ** 2
        sqrt_two = arb(2).sqrt()
        kappa = arch_kappa(L)
        pole_constant = pole_J(L)
        sixteen_pi_sq = 16 * pi * pi
        L_sq = L * L

        pole_a: list[arb] = []
        pole_b: list[arb] = []
        diagonal_arch: list[arb] = []
        for n in range(cutoff + 1):
            denominator = L_sq + sixteen_pi_sq * n * n
            pole_a.append(L / denominator)
            pole_b.append(4 * pi * n / denominator)
            diagonal_arch.append(
                kappa + 2 * CC[n] + pole_constant - (2 / L) * XC[n]
            )

        prime_data = prime_powers_up_to(c)
        prime_sine = [arb(0) for _ in range(cutoff + 1)]
        prime_diagonal = [arb(0) for _ in range(cutoff + 1)]
        for q, p in prime_data:
            weight = arb(p).log() * (arb(q) ** arb("-0.5"))
            y = arb(q).log()
            diagonal_scale = 2 * weight * (1 - y / L)
            for n in range(cutoff + 1):
                angle = 2 * pi * n * y / L
                prime_sine[n] += weight * angle.sin()
                prime_diagonal[n] += diagonal_scale * angle.cos()

        return cls(
            cutoff=cutoff,
            precision=precision,
            L=L,
            pi=pi,
            prefactor=prefactor,
            sqrt_two=sqrt_two,
            S=S,
            pole_a=pole_a,
            pole_b=pole_b,
            diagonal_arch=diagonal_arch,
            prime_sine=prime_sine,
            prime_diagonal=prime_diagonal,
            prime_powers=prime_data,
            build_seconds=time.time() - started,
        )

    def parity_entry(self, sector: Sector, k: int, ell: int) -> arb:
        if not 0 <= k <= self.cutoff or not 0 <= ell <= self.cutoff:
            raise IndexError("mode outside the direct parity kernel")
        if sector == "odd" and (k == 0 or ell == 0):
            raise ValueError("the odd sector has no zero mode")
        if k > ell:
            k, ell = ell, k

        if k == 0:
            if ell == 0:
                return (
                    self.prefactor * self.pole_a[0] * self.pole_a[0]
                    - self.diagonal_arch[0]
                    - self.prime_diagonal[0]
                )
            zero_positive = (
                self.prefactor * self.pole_a[0] * self.pole_a[ell]
                + (self.S[ell] + self.prime_sine[ell])
                / (self.pi * ell)
            )
            return self.sqrt_two * zero_positive

        if k == ell:
            arch_same = self.diagonal_arch[k]
            prime_same = self.prime_diagonal[k]
        else:
            denominator = self.pi * (k - ell)
            arch_same = (self.S[ell] - self.S[k]) / denominator
            prime_same = (
                self.prime_sine[ell] - self.prime_sine[k]
            ) / denominator

        reflected_denominator = self.pi * (k + ell)
        arch_reflected = (-self.S[ell] - self.S[k]) / reflected_denominator
        prime_reflected = (
            -self.prime_sine[ell] - self.prime_sine[k]
        ) / reflected_denominator

        if sector == "even":
            pole = (
                2
                * self.prefactor
                * self.pole_a[k]
                * self.pole_a[ell]
            )
            return (
                pole
                - arch_same
                - arch_reflected
                - prime_same
                - prime_reflected
            )

        pole = -2 * self.prefactor * self.pole_b[k] * self.pole_b[ell]
        return (
            pole
            - arch_same
            + arch_reflected
            - prime_same
            + prime_reflected
        )


def _sector_modes(sector: Sector, cutoff: int) -> range:
    return range(0, cutoff + 1) if sector == "even" else range(1, cutoff + 1)


def _build_unshifted_parity_block(
    kernel: DirectParityKernel, sector: Sector, cutoff: int
) -> arb_mat:
    modes = list(_sector_modes(sector, cutoff))
    block = arb_mat(len(modes), len(modes))
    for i, k in enumerate(modes):
        for j in range(i, len(modes)):
            value = kernel.parity_entry(sector, k, modes[j])
            block[i, j] = value
            block[j, i] = value
    return block


def _build_sector_blocks_direct(
    *,
    kernel: DirectParityKernel,
    sector: Sector,
    low_cutoff: int,
    core_cutoff: int,
    shell_cutoff: int,
    shift_gain: arb,
    q: arb,
    rho: arb,
) -> tuple[arb_mat, arb_mat, arb_mat, dict[str, Any]]:
    started = time.time()
    core_modes = list(_sector_modes(sector, core_cutoff))
    shell_modes = list(range(core_cutoff + 1, shell_cutoff + 1))
    core_dimension = len(core_modes)
    shell_dimension = len(shell_modes)
    core = arb_mat(core_dimension, core_dimension)
    coupling = arb_mat(core_dimension, shell_dimension)
    shell = arb_mat(shell_dimension, shell_dimension)

    for i, k in enumerate(core_modes):
        for j in range(i, core_dimension):
            ell = core_modes[j]
            value = kernel.parity_entry(sector, k, ell)
            if i == j:
                value += shift_gain
            if k <= low_cutoff and ell <= low_cutoff:
                value *= q
            value *= rho
            core[i, j] = value
            core[j, i] = value

    for i, k in enumerate(core_modes):
        for j, ell in enumerate(shell_modes):
            coupling[i, j] = kernel.parity_entry(sector, k, ell)

    for i, k in enumerate(shell_modes):
        for j in range(i, shell_dimension):
            value = kernel.parity_entry(sector, k, shell_modes[j])
            if i == j:
                value += shift_gain
            shell[i, j] = value
            shell[j, i] = value

    upper_core = core_dimension * (core_dimension + 1) // 2
    upper_shell = shell_dimension * (shell_dimension + 1) // 2
    return core, coupling, shell, {
        "sector": sector,
        "core_dimension": core_dimension,
        "shell_dimension": shell_dimension,
        "direct_entry_evaluations": (
            upper_core + core_dimension * shell_dimension + upper_shell
        ),
        "allocated_arb_entries": (
            core_dimension * core_dimension
            + core_dimension * shell_dimension
            + shell_dimension * shell_dimension
        ),
        "avoided_full_matrix_entries": (2 * shell_cutoff + 1) ** 2,
        "seconds": round(time.time() - started, 3),
        "formula": (
            "even[k,l]=A[k,l]+A[k,-l]; "
            "odd[k,l]=A[k,l]-A[k,-l]"
        ),
        "prime_aggregation": (
            "P_n=sum_{q<=c} Lambda(q)/sqrt(q) sin(2*pi*n*log(q)/L); "
            "D_n=sum_{q<=c} 2*Lambda(q)/sqrt(q)*(1-log(q)/L) "
            "cos(2*pi*n*log(q)/L)"
        ),
    }


def _validate_direct_construction(
    *, c: int, cutoff: int, precision: int
) -> dict[str, Any]:
    started = time.time()
    kernel = DirectParityKernel.build(c=c, cutoff=cutoff, precision=precision)
    raw = build_cutoff_free_matrix(c, cutoff, precision)
    symmetric = reflection_symmetric_enclosure(raw, cutoff)
    del raw
    canonical_even, canonical_odd = parity_blocks(symmetric, cutoff)
    del symmetric

    records: list[dict[str, Any]] = []
    for sector, canonical in (
        ("even", canonical_even),
        ("odd", canonical_odd),
    ):
        direct = _build_unshifted_parity_block(kernel, sector, cutoff)
        entry_count = direct.nrows() * direct.ncols()
        contains_zero = 0
        max_midpoint_delta = 0.0
        max_difference_radius = 0.0
        for i in range(direct.nrows()):
            for j in range(direct.ncols()):
                difference = direct[i, j] - canonical[i, j]
                if difference.contains(0):
                    contains_zero += 1
                max_midpoint_delta = max(
                    max_midpoint_delta, abs(float(difference.mid()))
                )
                max_difference_radius = max(
                    max_difference_radius, float(difference.rad())
                )
        if contains_zero != entry_count:
            raise RuntimeError(
                f"{sector} direct parity replay has an interval missing zero"
            )
        records.append(
            {
                "sector": sector,
                "dimension": direct.nrows(),
                "entry_count": entry_count,
                "difference_intervals_containing_zero": contains_zero,
                "max_abs_difference_midpoint": max_midpoint_delta,
                "max_difference_radius": max_difference_radius,
            }
        )
        del direct, canonical
        gc.collect()

    return {
        "status": "PASS",
        "cutoff": cutoff,
        "precision_bits": precision,
        "criterion": (
            "every direct-minus-canonical Arb interval contains exact zero"
        ),
        "kernel_build_seconds": round(kernel.build_seconds, 3),
        "sectors": records,
        "total_seconds": round(time.time() - started, 3),
    }


def _certify_sector_blocks(
    *,
    sector: Sector,
    core: arb_mat,
    coupling: arb_mat,
    shell: arb_mat,
    construction: dict[str, Any],
    preconditioner_path: Path,
    started_at: float,
) -> dict[str, Any]:
    core_dimension = core.nrows()
    shell_dimension = shell.nrows()
    if core.ncols() != core_dimension:
        raise ValueError("direct core block must be square")
    if coupling.nrows() != core_dimension or coupling.ncols() != shell_dimension:
        raise ValueError("direct coupling block has the wrong dimensions")
    if shell.ncols() != shell_dimension:
        raise ValueError("direct shell block must be square")

    _progress(
        f"{sector}: verified solve {core_dimension}x{core_dimension} by "
        f"{core_dimension}x{shell_dimension}"
    )
    solve_started = time.time()
    solution = core.solve(coupling, algorithm="precond")
    solve_seconds = time.time() - solve_started
    _progress(f"{sector}: verified solve finished in {solve_seconds:.3f}s")

    _progress(f"{sector}: checking every verified-solve residual entry")
    residual_started = time.time()
    residual_record = _verify_solve_residual(core, solution, coupling)
    residual_seconds = time.time() - residual_started
    _progress(f"{sector}: residual check finished in {residual_seconds:.3f}s")

    _progress(f"{sector}: enclosing the exact Schur complement")
    schur_started = time.time()
    schur = shell - coupling.transpose() * solution
    _symmetrize_enclosure(schur)
    schur_seconds = time.time() - schur_started
    del solution
    gc.collect()
    _progress(f"{sector}: Schur enclosure finished in {schur_seconds:.3f}s")

    _progress(f"{sector}: selecting the floating Cholesky basis")
    midpoint_started = time.time()
    schur_midpoint = _midpoint_numpy(schur)
    cholesky = np.linalg.cholesky(schur_midpoint)
    preconditioner_midpoint = np.triu(np.linalg.inv(cholesky.T))
    midpoint_seconds = time.time() - midpoint_started
    del schur_midpoint, cholesky

    preconditioner_path.parent.mkdir(parents=True, exist_ok=True)
    np.save(preconditioner_path, preconditioner_midpoint, allow_pickle=False)
    reloaded = np.load(preconditioner_path, allow_pickle=False)
    if not np.array_equal(reloaded, preconditioner_midpoint):
        raise RuntimeError("saved preconditioner does not replay byte-for-byte")
    del reloaded

    exact_started = time.time()
    preconditioner = _exact_upper_triangular(preconditioner_midpoint)
    diagonal_midpoints: list[float] = []
    for i in range(preconditioner.nrows()):
        diagonal = preconditioner[i, i]
        if diagonal.rad() != 0 or not diagonal > 0:
            raise RuntimeError(
                "exact dyadic preconditioner has a nonpositive diagonal"
            )
        diagonal_midpoints.append(float(diagonal.mid()))
    exact_seconds = time.time() - exact_started

    _progress(f"{sector}: enclosing the exact dyadic congruence")
    congruence_started = time.time()
    preconditioned = preconditioner.transpose() * (
        schur * preconditioner
    )
    congruence_seconds = time.time() - congruence_started
    _progress(f"{sector}: exact congruence finished in {congruence_seconds:.3f}s")

    _progress(f"{sector}: proving strict Gershgorin lower margins")
    gershgorin_started = time.time()
    gershgorin = _gershgorin_certificate(preconditioned)
    gershgorin_seconds = time.time() - gershgorin_started

    return {
        "sector": sector,
        "status": "PASS",
        "core_dimension": core_dimension,
        "shell_dimension": shell_dimension,
        "full_dimension": core_dimension + shell_dimension,
        "direct_construction": construction,
        "solve_algorithm": "arb_mat.solve(precond)",
        "solve_residual": residual_record,
        "preconditioner": {
            "path": str(preconditioner_path.resolve()),
            "sha256": _sha256(preconditioner_path),
            "dtype": str(preconditioner_midpoint.dtype),
            "shape": list(preconditioner_midpoint.shape),
            "storage": "NumPy .npy; every float is embedded as an exact dyadic",
            "upper_triangular": True,
            "all_dyadic_radii_zero": True,
            "all_diagonal_entries_positive": True,
            "min_diagonal_midpoint": min(diagonal_midpoints),
        },
        "gershgorin": gershgorin,
        "proof_consequence": (
            "the exact dyadic congruence is strictly positive definite; "
            "hence the Schur complement and enlarged recursive-shell matrix "
            "are positive definite"
        ),
        "timings_seconds": {
            "kernel_and_block_construction": construction["seconds"],
            "verified_solve": round(solve_seconds, 3),
            "residual_check": round(residual_seconds, 3),
            "schur_enclosure": round(schur_seconds, 3),
            "midpoint_preconditioner": round(midpoint_seconds, 3),
            "exact_dyadic_embedding": round(exact_seconds, 3),
            "arb_congruence": round(congruence_seconds, 3),
            "gershgorin": round(gershgorin_seconds, 3),
            "total_including_construction": round(time.time() - started_at, 3),
        },
    }


def certify(
    *,
    c: int,
    low_cutoff: int,
    core_cutoff: int,
    shell_cutoff: int,
    precision: int,
    shift_gain: Fraction,
    q_upper: Fraction,
    rho_upper: Fraction,
    core_certificate_path: Path,
    json_out: Path,
    validate_cutoff: int | None,
    threads: int,
) -> dict[str, Any]:
    if c <= 1:
        raise ValueError("c must exceed one")
    if not 1 <= low_cutoff < core_cutoff < shell_cutoff:
        raise ValueError(
            "require 1 <= low_cutoff < core_cutoff < shell_cutoff"
        )
    if precision < 128:
        raise ValueError("precision must be at least 128 bits")
    if not 0 < q_upper < 1:
        raise ValueError("q_upper must lie strictly between zero and one")
    if not 0 < rho_upper < 1:
        raise ValueError("rho_upper must lie strictly between zero and one")
    if validate_cutoff is not None and not 1 <= validate_cutoff <= core_cutoff:
        raise ValueError("validate_cutoff must lie between one and core_cutoff")
    if threads < 1:
        raise ValueError("threads must be positive")

    ctx.threads = threads
    core_certificate = _validate_any_core_certificate(
        core_certificate_path,
        c=c,
        low_cutoff=low_cutoff,
        core_cutoff=core_cutoff,
        shift_gain=shift_gain,
        q_upper=q_upper,
    )
    _progress(
        "validated the prior core through cutoff "
        f"{core_certificate['certified_through_cutoff']}"
    )
    validation = (
        _validate_direct_construction(
            c=c, cutoff=validate_cutoff, precision=precision
        )
        if validate_cutoff is not None
        else None
    )
    if validation is not None:
        _progress(
            f"canonical replay passed through cutoff {validation['cutoff']}"
        )

    started = time.time()
    ctx.prec = precision
    shift_ball = _fraction_arb(shift_gain)
    q_ball = _fraction_arb(q_upper)
    rho_ball = _fraction_arb(rho_upper)
    kernel = DirectParityKernel.build(
        c=c, cutoff=shell_cutoff, precision=precision
    )
    _progress(
        f"built one-dimensional Arb kernel through {shell_cutoff} in "
        f"{kernel.build_seconds:.3f}s"
    )

    stem = json_out.with_suffix("")
    sector_records: list[dict[str, Any]] = []
    for sector in ("even", "odd"):
        sector_started = time.time()
        _progress(f"{sector}: constructing direct core/coupling/shell blocks")
        core, coupling, shell, construction = _build_sector_blocks_direct(
            kernel=kernel,
            sector=sector,
            low_cutoff=low_cutoff,
            core_cutoff=core_cutoff,
            shell_cutoff=shell_cutoff,
            shift_gain=shift_ball,
            q=q_ball,
            rho=rho_ball,
        )
        _progress(
            f"{sector}: constructed {construction['direct_entry_evaluations']} "
            f"exact-form entries in {construction['seconds']:.3f}s"
        )
        preconditioner_path = stem.with_name(
            stem.name + f"_{sector}_preconditioner.npy"
        )
        sector_records.append(
            _certify_sector_blocks(
                sector=sector,
                core=core,
                coupling=coupling,
                shell=shell,
                construction=construction,
                preconditioner_path=preconditioner_path,
                started_at=sector_started,
            )
        )
        del core, coupling, shell
        gc.collect()

    return {
        "status": "PASS",
        "rigorous_certificate": True,
        "scope": (
            "rigorous finite direct-parity preconditioned-Schur interval "
            "certificate for one recursive relative-energy shell"
        ),
        "c": c,
        "low_cutoff": low_cutoff,
        "core_cutoff": core_cutoff,
        "shell_cutoff": shell_cutoff,
        "largest_cutoff": shell_cutoff,
        "precision_bits": precision,
        "flint_threads": threads,
        "shift_gain": str(shift_gain),
        "q_upper": str(q_upper),
        "rho_upper": str(rho_upper),
        "core_certificate": core_certificate,
        "direct_formula_validation": validation,
        "kernel": {
            "cutoff": shell_cutoff,
            "precision_bits": precision,
            "prime_powers": [
                {"q": q, "base_prime": p} for q, p in kernel.prime_powers
            ],
            "prime_power_count": len(kernel.prime_powers),
            "one_dimensional_prime_aggregation": True,
            "build_seconds": round(kernel.build_seconds, 3),
        },
        "matrix_condition": (
            "[[rho*R_q(core),C],[C^T,H_shell]] is positive definite"
        ),
        "discriminant_consequence": (
            "C(s,t)^2 < rho*R_q(core)(s,s)*H_shell(t,t)"
        ),
        "gluing_consequence": (
            "rho<1 glues the shell to the certified positive core and "
            "preserves the same q relative-energy coefficient"
        ),
        "proof_chain": [
            "the prior artifact certifies R_q(core) positive definite",
            "direct Arb formulas enclose the exact reflection parity blocks",
            "the full prime sum is retained in aggregated interval sequences",
            "Arb verified solve encloses (rho*R_q(core))^-1*C",
            "Arb arithmetic encloses the symmetric Schur complement",
            "the fixed exact dyadic upper-triangular basis is invertible",
            "all preconditioned Gershgorin lower margins are strictly positive",
            "Schur complement and enlarged relative-energy form are positive",
        ],
        "sectors": sector_records,
        "total_seconds": round(time.time() - started, 3),
        "lean_targets": [
            "RiemannCvs.BoundaryWeylSchurTail.twoBlockEnergy_nonnegative",
            "RiemannCvs.BoundaryWeylSchurTail.relativeCoupling_of_recursiveShell",
            "RiemannCvs.BoundaryWeylSchurTail.fourNinthsShell_oneThirdReserve",
        ],
        "remaining_boundary": (
            "this finite certificate does not replace the uniform dyadic "
            "two-channel estimate or the closed-tail operator limit"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--low-cutoff", type=int, default=20)
    parser.add_argument("--core-cutoff", type=int, required=True)
    parser.add_argument("--shell-cutoff", type=int, required=True)
    parser.add_argument("--prec", type=int, default=256)
    parser.add_argument("--shift-gain", default="1/1024")
    parser.add_argument("--q-upper", default="249/250")
    parser.add_argument("--rho-upper", default="4/9")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--core-certificate", type=Path, required=True)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument(
        "--validate-cutoff",
        type=int,
        default=12,
        help="small canonical replay cutoff; use 0 to omit",
    )
    args = parser.parse_args()

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = certify(
        c=args.c,
        low_cutoff=args.low_cutoff,
        core_cutoff=args.core_cutoff,
        shell_cutoff=args.shell_cutoff,
        precision=args.prec,
        shift_gain=_positive_fraction(args.shift_gain, "shift_gain"),
        q_upper=_positive_fraction(args.q_upper, "q_upper"),
        rho_upper=_positive_fraction(args.rho_upper, "rho_upper"),
        core_certificate_path=args.core_certificate,
        json_out=args.json_out,
        validate_cutoff=(args.validate_cutoff or None),
        threads=args.threads,
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
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    args.json_out.write_text(encoded + "\n", encoding="utf-8")

    print(
        "direct-parity recursive-shell certificate PASS: "
        f"c={args.c}, core={args.core_cutoff}, shell={args.shell_cutoff}, "
        f"q<{payload['q_upper']}, rho<{payload['rho_upper']}, "
        f"x<=-{payload['shift_gain']}"
    )
    for sector in payload["sectors"]:
        gershgorin = sector["gershgorin"]
        print(
            f"  {sector['sector']}: core={sector['core_dimension']} "
            f"shell={sector['shell_dimension']} "
            f"strict_gershgorin={gershgorin['strictly_positive_rows']}/"
            f"{gershgorin['dimension']} "
            f"transcript={gershgorin['margin_transcript_sha256']}"
        )
    print(f"artifact={args.json_out.resolve()}")
    print(f"sha256={_sha256(args.json_out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
