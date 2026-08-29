# V23 boundary-Weyl cumulative-residue reduction

## 1. Status and version boundary

V22 repaired the omitted zero-frequency archimedean contribution and proved
that it is a negative rank-one update in the central Fourier coordinate.  V23
does not replace that calculation.  It adds the finite boundary-Weyl
no-crossing reduction that was described after the historical V17 repository
surface but had not yet been committed as a replayable Lean module.

The checked umbrella is now

```text
RiemannCvs.V23BoundaryWeylMainline
```

and imports the complete V22 surface.  Historical umbrellas remain in place
so that each already-published proof boundary can still be reproduced.

## 2. The cumulative-residue object

Let

```text
lambda_0 < lambda_1 < ... < lambda_N
G_N(x) = sum_{j=0}^N r_j / (lambda_j - x),   x < lambda_0,
R_j = sum_{k=0}^j r_k.
```

The reciprocal weights

```text
a_j(x) = 1 / (lambda_j - x)
```

are positive and decreasing in `j`.  Finite Abel summation gives the exact
identity

```text
sum_{j=0}^N r_j a_j
  = R_N a_N + sum_{j=0}^{N-1} R_j (a_j - a_{j+1}).
```

Consequently

```text
R_j >= 0 for j < N,   R_N > 0
```

implies `G_N(x) > 0` for every `x < lambda_0`.  This is stronger and more
flexible than requiring every residue to be positive: an individual residue
may be negative while every cumulative residue remains nonnegative.

`BoundaryWeylCumulative.lean` now proves:

* the finite Abel identity by induction;
* nonnegative and strict-positive weighted-sum variants;
* positivity and nonvanishing of `G_N` before the first pole;
* exclusion of a factorized characteristic numerator root there;
* positivity of `1 + Delta G_N` when `Delta > 0`;
* positivity of `G_N / (1 + Delta G_N)`.

The last two statements are the scalar sign component needed after a concrete
Sherman--Morrison identity has identified the V22 zero-mode update with that
ratio.

## 3. Repaired boundary-gap layer

`BoundaryGapNoCrossing.lean` previously declared its elementary first theorem
for a linear map on an otherwise unconstrained type.  A clean dependency
replay therefore requested additive and module instances that the theorem did
not use.  The argument only evaluates a boundary function and tests whether
its value is zero, so V23 gives it the exact abstraction

```text
boundary : E -> Real.
```

Linear functionals in the Sylvester specialization coerce to this function
type.  The module now builds independently, and its theorem again composes
with the existing rank-one Sylvester obstruction.

## 4. What this closes

The finite logical chain is now explicit:

```text
cumulative residues
  -> boundary-Weyl positivity before the first even pole
  -> no zero of the factorized odd characteristic numerator
  -> no finite lowest-parity crossing on that parameter slice.
```

Separately, the repository already proves that continuous branches preserve
their strict order when equality is excluded, and that negative rank-one prime
events lower the even branch while leaving the odd branch fixed.  The V23
umbrella imports those continuation and event-gluing theorems so the remaining
inputs are visible at one proof boundary rather than scattered across notes.

## 5. What remains open

The following are still explicit proof obligations:

1. derive the concrete rectangular displacement relation for the corrected
   CvS even and odd blocks;
2. derive its determinant/resolvent factorization with the same sign and
   normalization used by `finiteBoundaryWeyl`;
3. certify the cumulative residues rigorously, and then obtain estimates
   uniform in the Galerkin cutoff and along the continuous cutoff parameter;
4. keep the V22 central-mode functional distinct from the Sylvester boundary
   functional until a source-level identification is proved;
5. construct the limiting self-adjoint branches and transfer finite
   no-crossing through the compactness/resolvent limit;
6. close the source-specific PSWF-to-Bessel exterior remainder used by the
   stationary-phase route.

Earlier high-precision finite experiments support positive cumulative
residues at several sample pairs `(c,N)`, but those midpoint calculations are
not promoted here to interval certificates.  V23 formalizes the exact theorem
that a future Arb certificate must feed.

## 6. Local replay

From `research/riemann-cvs-lean`:

```powershell
lake build RiemannCvs.BoundaryGapNoCrossing
lake env lean RiemannCvs/BoundaryGapNoCrossing.lean
lake build RiemannCvs.BoundaryWeylCumulative
lake env lean RiemannCvs/BoundaryWeylCumulative.lean
lake build RiemannCvs.V23BoundaryWeylMainline
lake env lean RiemannCvs/V23BoundaryWeylMainline.lean
```

The V23 workflow additionally rejects proof placeholders and user-declared
axioms/constants, prints the axiom dependencies of every new terminal theorem,
and replays the corrected V22 finite Arb parity certificate as a regression
gate.
