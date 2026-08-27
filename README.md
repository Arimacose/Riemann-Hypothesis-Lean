# Riemann Hypothesis research in Lean

This repository collects Lean 4 formalizations, proof-audited finite-dimensional
reductions, research notes, and rigorous numerical certificates developed in a
Riemann-hypothesis research program based on Connes–van Suijlekom / related CvS
approximations to the Weil quadratic form.

## Repository layout

- [`research/riemann-cvs-lean`](research/riemann-cvs-lean): the pinned Lean 4
  package and its axiom-audit entry points.
- [`research/riemann-cvs-notes`](research/riemann-cvs-notes): analytic research
  notes supporting the formalized reductions.
- [`research/riemann-cvs-numerics`](research/riemann-cvs-numerics): rigorous
  interval and parity-certificate scripts.
- [`.github/workflows`](.github/workflows): independent Lean, axiom, and
  numerical-certificate checks.

## Verified scope

The current formal package certifies specific finite-dimensional algebraic,
order-theoretic, parity, projection, tail-bound, and no-crossing results used by
the research program. It does not state that the Riemann Hypothesis has been
formalized or proved. See the [package README](research/riemann-cvs-lean/README.md)
and [status report](research/riemann-cvs-lean/STATUS.md) for the exact boundary.

## Reproduce the Lean checks

```bash
cd research/riemann-cvs-lean
lake exe cache get
lake build
lake env lean RiemannCvs/PrintAxioms.lean
```

The toolchain and Mathlib revisions are pinned in the package files.
