#!/usr/bin/env python3
"""Exploratory fixed-Hermite boundary-layer Weil-form calculation.

This script evaluates the two explicit normalized Hermite radical vectors,
forms their exact inversion-parity exterior tails in logarithmic coordinates,
and numerically decomposes the Weil quadratic form into:

* the archimedean multiplier ``m(s) = 2 theta'(s)``;
* the pole term;
* a finite prime-power translation sum.

The calculation is a floating-point pressure test.  It is NOT an interval
certificate and does not prove the analytic estimates in
``FIXED_HERMITE_WEIL_BOUNDARY_LAYER.md``.  In particular, the prime sum is
truncated explicitly and the FFT discretization is controlled only by
resolution sweeps and a Parseval diagnostic.

The main quantities to inspect are

    lambda^4 * ||t_plus||^2 / ||t_minus||^2

and

    lambda^4 * QW(t_plus) / QW(t_minus).

The predicted mass constant is ``195 / (88*pi^2)``.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Iterable

import numpy as np
from scipy.special import digamma


PI = math.pi
A_PLUS = 2 * 2 ** (3 / 4) * math.sqrt(3) * PI / 3
A_MINUS = 2 * 2 ** (1 / 4) * math.sqrt(5) * PI / 15
NORMALIZE_PLUS = math.sqrt(8 / 11)
NORMALIZE_MINUS = math.sqrt(8 / 13)
PREDICTED_MASS_CONSTANT = 195 / (88 * PI * PI)


def next_power_of_two(value: int) -> int:
    if value < 1:
        raise ValueError("value must be positive")
    return 1 << (value - 1).bit_length()


def normalized_hermite_radical(u: np.ndarray, parity: str) -> np.ndarray:
    u = np.asarray(u, dtype=float)
    gaussian = np.exp(-PI * u * u)
    if parity == "plus":
        return (
            NORMALIZE_PLUS
            * A_PLUS
            * u**2
            * (2 * PI * u**2 - 3)
            * gaussian
        )
    if parity == "minus":
        return (
            -NORMALIZE_MINUS
            * A_MINUS
            * u**2
            * (8 * PI**2 * u**4 - 30 * PI * u**2 + 15)
            * gaussian
        )
    raise ValueError(f"unknown parity {parity!r}")


def e_transform(u: np.ndarray, parity: str, dilation_terms: int) -> np.ndarray:
    """Truncated positive-integer dilation sum defining the map E."""
    total = np.zeros_like(np.asarray(u, dtype=float))
    for multiplier in range(1, dilation_terms + 1):
        total += normalized_hermite_radical(multiplier * u, parity)
    return np.sqrt(u) * total


def prime_powers_up_to(limit: int) -> list[tuple[int, float]]:
    """Return ``(p^k, log p)`` for all prime powers at most ``limit``."""
    if limit < 2:
        return []
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[p]:
            is_prime[p * p : limit + 1 : p] = False

    weights: dict[int, float] = {}
    for p in np.flatnonzero(is_prime):
        q = int(p)
        while q <= limit:
            weights[q] = math.log(int(p))
            if q > limit // int(p):
                break
            q *= int(p)
    return sorted(weights.items())


def archimedean_multiplier(frequency: np.ndarray) -> np.ndarray:
    """Return ``2*theta'(s)`` in the standard Mellin convention."""
    z = 0.25 + 0.5j * frequency
    return -math.log(PI) + np.real(digamma(z))


def build_tail(
    lam: float,
    parity: str,
    oversample: int,
    y_max: float,
    dilation_terms: int,
) -> tuple[np.ndarray, np.ndarray, float]:
    if lam < 2:
        raise ValueError("the fixed-Hermite sign bounds require lambda >= 2")
    if oversample < 8 or y_max <= 0 or dilation_terms < 1:
        raise ValueError("invalid discretization parameters")

    log_lam = math.log(lam)
    boundary_width = lam ** -2
    dx = boundary_width / oversample
    x_max = log_lam + y_max * boundary_width
    size = next_power_of_two(math.ceil(2 * x_max / dx) + 1)
    x0 = -size * dx / 2
    x = x0 + np.arange(size) * dx

    tail = np.zeros(size, dtype=float)
    upper = x >= log_lam
    tail[upper] = e_transform(np.exp(x[upper]), parity, dilation_terms)

    epsilon = 1.0 if parity == "plus" else -1.0
    lower = x <= -log_lam
    tail[lower] = epsilon * e_transform(
        np.exp(-x[lower]), parity, dilation_terms
    )
    return x, tail, dx


def correlation_at_shift(
    x: np.ndarray,
    tail: np.ndarray,
    dx: float,
    shift: float,
) -> float:
    translated = np.interp(x + shift, x, tail, left=0.0, right=0.0)
    return float(np.sum(tail * translated) * dx)


def evaluate_case(
    lam: float,
    parity: str,
    oversample: int,
    y_max: float,
    dilation_terms: int,
    prime_extra: int,
) -> dict[str, object]:
    x, tail, dx = build_tail(
        lam, parity, oversample, y_max, dilation_terms
    )
    norm_sq = float(np.sum(tail * tail) * dx)
    if not math.isfinite(norm_sq) or norm_sq <= 0:
        raise RuntimeError(f"nonpositive tail norm for lambda={lam}, {parity}")

    transform = dx * np.fft.fft(tail)
    frequency = 2 * PI * np.fft.fftfreq(len(tail), d=dx)
    ds = 2 * PI / (len(tail) * dx)

    parseval_norm = float(np.sum(np.abs(transform) ** 2) * ds / (2 * PI))
    parseval_relative_error = abs(parseval_norm / norm_sq - 1)

    multiplier = archimedean_multiplier(frequency)
    archimedean = float(
        np.sum(np.abs(transform) ** 2 * multiplier) * ds / (2 * PI)
    )

    mellin_plus_half = float(np.sum(tail * np.exp(x / 2)) * dx)
    mellin_minus_half = float(np.sum(tail * np.exp(-x / 2)) * dx)
    pole = 2 * mellin_plus_half * mellin_minus_half

    prime_limit = max(2, math.ceil(lam * lam) + prime_extra)
    prime = 0.0
    for prime_power, von_mangoldt in prime_powers_up_to(prime_limit):
        correlation = correlation_at_shift(
            x, tail, dx, math.log(prime_power)
        )
        prime += (
            2
            * von_mangoldt
            / math.sqrt(prime_power)
            * correlation
        )

    quadratic = archimedean + pole - prime
    return {
        "lambda": lam,
        "parity": parity,
        "grid_size": len(tail),
        "dx": dx,
        "log_outer_endpoint": float(max(abs(x[0]), abs(x[-1]))),
        "dilation_terms": dilation_terms,
        "prime_power_cutoff": prime_limit,
        "prime_tail_decay_indicator": math.exp(-2 * PI * prime_extra),
        "norm_sq": norm_sq,
        "parseval_norm_sq": parseval_norm,
        "parseval_relative_error": parseval_relative_error,
        "archimedean": archimedean,
        "pole": pole,
        "prime_truncated": prime,
        "quadratic_truncated": quadratic,
        "archimedean_per_norm": archimedean / norm_sq,
        "pole_per_norm": pole / norm_sq,
        "prime_per_norm": prime / norm_sq,
        "quadratic_per_norm": quadratic / norm_sq,
        "two_log_lambda": 2 * math.log(lam),
    }


def parse_lambda_list(text: str) -> list[float]:
    values = [float(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise argparse.ArgumentTypeError("at least one lambda is required")
    if any(not math.isfinite(value) or value < 2 for value in values):
        raise argparse.ArgumentTypeError("all lambda values must be finite and >= 2")
    return values


def paired_summary(cases: Iterable[dict[str, object]]) -> list[dict[str, object]]:
    by_lambda: dict[float, dict[str, dict[str, object]]] = {}
    for case in cases:
        lam = float(case["lambda"])
        by_lambda.setdefault(lam, {})[str(case["parity"])] = case

    rows: list[dict[str, object]] = []
    for lam in sorted(by_lambda):
        pair = by_lambda[lam]
        if set(pair) != {"plus", "minus"}:
            raise RuntimeError(f"missing parity partner at lambda={lam}")
        plus = pair["plus"]
        minus = pair["minus"]
        mass_ratio = float(plus["norm_sq"]) / float(minus["norm_sq"])
        quadratic_ratio = float(plus["quadratic_truncated"]) / float(
            minus["quadratic_truncated"]
        )
        rows.append(
            {
                "lambda": lam,
                "lambda4_mass_ratio": lam**4 * mass_ratio,
                "predicted_mass_constant": PREDICTED_MASS_CONSTANT,
                "lambda4_truncated_quadratic_ratio": lam**4 * quadratic_ratio,
                "common_scale_ratio": float(plus["quadratic_per_norm"])
                / float(minus["quadratic_per_norm"]),
                "plus_quadratic_per_norm": plus["quadratic_per_norm"],
                "minus_quadratic_per_norm": minus["quadratic_per_norm"],
                "max_parseval_relative_error": max(
                    float(plus["parseval_relative_error"]),
                    float(minus["parseval_relative_error"]),
                ),
            }
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lambdas", type=parse_lambda_list, default="3,4,5,6,8")
    parser.add_argument("--oversample", type=int, default=48)
    parser.add_argument("--y-max", type=float, default=24.0)
    parser.add_argument("--dilation-terms", type=int, default=4)
    parser.add_argument("--prime-extra", type=int, default=24)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    cases = [
        evaluate_case(
            lam,
            parity,
            args.oversample,
            args.y_max,
            args.dilation_terms,
            args.prime_extra,
        )
        for lam in args.lambdas
        for parity in ("plus", "minus")
    ]
    pairs = paired_summary(cases)

    max_parseval = max(float(row["max_parseval_relative_error"]) for row in pairs)
    if max_parseval > 1e-8:
        raise RuntimeError(f"Parseval regression failed: {max_parseval}")
    if any(
        not math.isfinite(float(case["quadratic_truncated"]))
        for case in cases
    ):
        raise RuntimeError("nonfinite quadratic value")

    result = {
        "status": "PASS",
        "proof_status": "none; floating-point exploratory pressure test only",
        "statement": (
            "fixed-Hermite exterior masses and a truncated numerical Weil-form "
            "decomposition exhibit the predicted quartic parity scaling"
        ),
        "limitations": [
            "FFT and quadrature are double precision, not interval arithmetic",
            "the prime-power sum is truncated at the reported cutoff",
            "no tail remainder is rigorously enclosed",
            "no ground-state, simple-even, or RH conclusion follows",
        ],
        "parameters": {
            "lambdas": args.lambdas,
            "oversample": args.oversample,
            "y_max": args.y_max,
            "dilation_terms": args.dilation_terms,
            "prime_extra": args.prime_extra,
        },
        "predicted_mass_constant": PREDICTED_MASS_CONSTANT,
        "cases": cases,
        "paired_summary": pairs,
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }

    output = Path(args.json_out)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "paired_summary": pairs}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
