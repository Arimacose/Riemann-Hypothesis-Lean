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

## 4. Concrete displacement and determinant bridges

`CvSParityDisplacement.lean` now proves the source entry identity

```text
(p-q) A(p,q) + (p+q) A(p,-q) = 2p A(p,0)
```

separately for every odd-symbol Loewner difference quotient and for the
rational pole kernel.  The law is closed under addition and scalar
multiplication, so it applies term-by-term to the finite CvS kernel.

With the zero mode represented by `none`, positive frequencies by `some j`,
and

```text
D[i,none]   = 0,
D[i,some j] = frequency_i delta_ij,
eta         = (1, sqrt(2), ..., sqrt(2)),
beta_i      = sqrt(2) frequency_i A(frequency_i,0),
```

Lean derives both the matrix identity

```text
D E - O D = beta etaᵀ
```

and its vector/linear-map form consumed directly by `SylvesterNoCrossing`.
It also proves that `ker D` is exactly the central cosine line and that `D`
annihilates the central-central rank-one matrix.  Hence the repaired V22
zero-mode term preserves this displacement relation exactly.

`ObliqueWeylDeterminant.lean` proves the finite Lagrange identity

```text
P(x) / product_i (x-lambda_i)
  = sum_i r_i / (x-lambda_i),
r_i = P(lambda_i) / product_(j != i) (lambda_i-lambda_j).
```

For a monic degree-`N` odd characteristic product over a monic degree-`N+1`
even product, it additionally proves `sum_i r_i = 1`, the global sign change
for denominators `lambda_i-x`, and the actual matrix determinant-ratio form
after identifying the two block characteristic polynomials with the enumerated
spectral products.  Thus the sign and normalization consumed by
`finiteBoundaryWeyl` are no longer note-only assumptions: the multiplicative
form has exactly `scale = -1` in the factorization theorem used by the
no-zero layer.

## 5. Quantitative cutoff-to-limit interface

`BoundaryWeylCumulative.lean` now retains quantitative information from the
Abel decomposition instead of only proving a strict sign.  It proves both

```text
R_N / (lambda_N-x) <= G_N(x)
```

and, for every `k < N`,

```text
R_k * (1/(lambda_k-x) - 1/(lambda_(k+1)-x)) <= G_N(x).
```

The second bound matters because the last pole may escape to infinity with the
Galerkin cutoff, making the first bound decay even when `R_N = 1`.  A fixed
early cumulative mass and reciprocal-weight drop can instead retain a positive
margin.

`BoundaryWeylUniformLimit.lean` then proves two exact transfer interfaces:

1. an eventual common lower margin survives pointwise convergence of the
   Galerkin Weyl functions;
2. one finite certificate of size `2 * margin`, combined with a rigorous
   finite-to-limit error at most `margin`, leaves the limiting Weyl value
   strictly positive.

Both final-term and early-prefix variants are available.  The early-prefix
theorems expose the next source-level target precisely: bound one `R_k` and its
adjacent pole weight drop from below while bounding the truncation/resolvent
tail from above.  For a whole compact `x`-domain the same constants must be
uniform on that domain.  The unbounded far-left region still needs its separate
normalized asymptotic argument; `sum r_i = 1` identifies its expected leading
sign but is not used as a hidden limit theorem.

The strengthened finite certificate now instantiates this interface at
`(c,N) = (13,20)`.  Using prefix `k = 11`, interval arithmetic proves on the
entire compact window `-100 <= x <= 0` that

```text
R_11 > 0.61960373407854799386476356739527323,
1/(lambda_11+100) - 1/(lambda_12+100)
  > 7.06521281852709305850381039692401889e-5,
G_20(x) > 4.37763224441900953233735639238815229e-5.
```

The last inequality combines the Arb endpoint enclosure with the Lean theorem
that reciprocal pole drops increase as `x` moves right before the first pole.
It is a rigorous single-cutoff compact margin, not yet a cutoff-uniform or
continuum estimate.

The compact error-budget theorem turns this number into a concrete logical
threshold: a rigorous bound

```text
sup_{-100 <= x <= 0} |G_20(x) - G_limit(x)|
  <= 2.1888161222095047e-5
```

would already imply `G_limit(x) > 0` throughout that window.  Establishing
that estimate on the closed window including `x = 0`, however, is not the
correct analytic route for this family.  A cross-cutoff replay of the certified
spectral data gives

```text
G_12(0) ≈ 7.0357e14,
G_16(0) ≈ 3.6507e17,
G_20(0) ≈ 8.9014e19,
G_24(0) ≈ 6.8204e21.
```

The corresponding lowest even poles decrease from about `2.14e-29` to
`3.07e-43`.  Thus `x = 0` is a moving threshold singularity, not a point at
which these finite real-valued Weyl functions exhibit uniform convergence.
The finite Abel certificate remains valid there, but the continuum transfer
must use compact windows `xLeft <= x <= xRight < 0` and then exhaust the open
negative half-line.  At `x = -100`, by contrast, the same certified midpoint
data give `|G_20-G_24| ≈ 6.27e-6`; this is a convergence diagnostic, not a
replacement for a rigorous tail bound.

The same rigorous computation was replayed at a small cutoff grid with the
same `k = 11` and window:

```text
N = 12: G_N(x) > 4.4793581103556951106685107384168e-5,
N = 16: G_N(x) > 1.4338277822912240388133563893400e-5,
N = 20: G_N(x) > 4.3776322444190095323373563923881e-5,
N = 24: G_N(x) > 4.2031636096344469926356667765480e-5.
```

This finite grid shows that the selected early prefix is not an isolated
`N = 20` accident, while still leaving the all-cutoff lower theorem as an
explicit obligation.

## 6. Variational Schur tail and far-left normalization

`BoundaryWeylSchurTail.lean` now supplies the missing quantitative shape of
the compact resolvent estimate.  For a low/high decomposition, let `u0` solve
the finite low-block variational resolvent equation, and let `(u,v)` solve the
full block system.  Assume uniform bounds

```text
lowForm(w,w)   >= a * ‖w‖²,
highForm(z,z)  >= gamma * ‖z‖²,
|coupling(w,z)| <= epsilon * ‖w‖ * ‖z‖,
epsilon² < a * gamma.
```

Lean proves first

```text
‖u-u0‖ <= epsilon²/(a*gamma-epsilon²) * ‖u0‖,
‖u0‖   <= ‖eta‖/a,
```

and then the boundary-response estimate

```text
|<eta,u>-<eta,u0>|
  <= ‖eta‖² epsilon² / (a * (a*gamma-epsilon²)).
```

The division-free acceptance form used by interval arithmetic is

```text
‖eta‖² epsilon²
  <= margin * a * (a*gamma-epsilon²).
```

A domain-uniform theorem composes this inequality directly with the finite
`2 * margin` Abel certificate.  This is stronger than the previous generic
`|G_N-G_limit| <= margin` slot: the remaining source work now has named and
separately measurable inputs `a`, `gamma`, and `epsilon`.

`BoundaryWeylFarLeft.lean` closes the algebraic part of the exterior
normalization.  If all finite poles are nonnegative, the total residue is one,
and

```text
sum_j |r_j| lambda_j <= moment,
```

then for every `t > 0`

```text
|G_N(-t) - 1/t| <= moment/t²,
G_N(-t) >= 1/t - moment/t².
```

Consequently, an eventual cutoff-uniform moment budget with `moment < t`
passes through pointwise convergence and proves positivity at `x = -t`.
The companion gluing theorem combines those exterior points with positivity
on one compact window `[-moment,-delta]`, yielding positivity on the entire
open tail `x < -delta`.
What remains here is source-specific: bound that absolute spectral moment
uniformly.  The normalized leading sign and the exact amount of exterior
room are now kernel-checked Lean conclusions.

The same Arb boxes already give a rigorous finite-grid probe for this new
quantity.  The certificate now forms `sum_j |r_j| lambda_j` directly in Arb
and requires it to lie strictly below the replay threshold `2`.  Midpoint
values (for scale only; the JSON records full enclosures) are

```text
N = 12: 1.0723849534170354
N = 16: 1.2564966113971965
N = 20: 1.5163173229304040
N = 24: 1.4105625250409555
```

This is finite-grid evidence, not the all-cutoff theorem.  It does show that
the new far-left interface is numerically relevant rather than vacuous: a
uniform moment bound near `2` would cover `x < -2`, leaving only a bounded
negative interval for the compact Schur argument.

## 7. What this closes

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

## 8. Rigorous finite Arb certificate

`certify_boundary_weyl_cumulative.py` now constructs the corrected CvS matrix
as Arb balls, takes its exact reflection-symmetric even and odd blocks, and
certifies the cumulative-residue hypothesis at `(c,N) = (13,20)`.

The midpoint eigensolver is used only to propose search brackets.  For every
ordered eigenvalue, the accepted lower endpoint has exactly `j` negative
pivots in `A-tI`, while the upper endpoint has exactly `j+1`; both counts come
from interval LDL factorizations.  Therefore the resulting 21 even and 20 odd
boxes are rigorous eigenvalue enclosures.  Interval products then evaluate

```text
r_j = product_k (lambda_j - mu_k)
      / product_{i != j} (lambda_j - lambda_i).
```

The local replay certified:

```text
lambda_even,0 < lambda_odd,0 < lambda_even,1,
R_j > 0 for every 0 <= j <= 20,
R_0 > 1.3930283937174343958004986706459e-19,
R_20 contains 1 exactly within its Arb enclosure.
```

Residues `14,15,16,18,20` are strictly negative.  Their cumulative sums remain
strictly positive, so this case genuinely uses the Abel/cumulative theorem
rather than the stronger but false claim that every residue is positive.

Replay from the repository root with the pinned dependencies:

```powershell
python research/riemann-cvs-numerics/certify_boundary_weyl_cumulative.py `
  --c 13 --N 20 --prec 900 --dps 180 --iterations 120 `
  --margin-left=-100 --margin-right=0 --margin-prefix-index 11 `
  --moment-upper 2 `
  --json-out work/v23_c13_N20_boundary_weyl_cumulative.json
```

The JSON artifact records both endpoint inertias and their pivot-transcript
hashes, every eigenvalue enclosure, every residue enclosure, and every
cumulative enclosure.  A run exits successfully only when all prefixes are
strictly positive.

## 9. What remains open

The following are still explicit proof obligations:

1. instantiate the characteristic-polynomial identification for the concrete
   self-adjoint CvS blocks from a Lean-side ordered eigenvalue enumeration;
2. instantiate the new Schur inputs `a`, `gamma`, and `epsilon`, prove their
   product budget on each compact domain with right endpoint `< 0`, and make
   the constants uniform in the Galerkin cutoff and continuous cutoff
   parameter;
3. prove a cutoff-uniform upper bound for the absolute first spectral moment
   consumed by the new far-left theorem;
4. keep the V22 central-mode functional distinct from the Sylvester boundary
   functional until a source-level identification is proved;
5. construct the limiting self-adjoint branches and supply the concrete
   compactness/resolvent convergence consumed by the new transfer interface;
6. close the source-specific PSWF-to-Bessel exterior remainder used by the
   stationary-phase route.

The new certificate closes the finite `(13,20)` numerical hypothesis consumed
by the Lean theorem.  The exact finite displacement, characteristic-product,
residue-normalization, determinant-ratio, quantitative Abel, and logical
finite-to-limit adapters are now formalized.  The source-specific uniform
margin and convergence estimates listed above remain the dominant proof
boundary.

## 10. Local Lean replay

From `research/riemann-cvs-lean`:

```powershell
lake build RiemannCvs.BoundaryGapNoCrossing
lake env lean RiemannCvs/BoundaryGapNoCrossing.lean
lake build RiemannCvs.CvSParityDisplacement
lake env lean RiemannCvs/CvSParityDisplacement.lean
lake build RiemannCvs.ObliqueWeylDeterminant
lake env lean RiemannCvs/ObliqueWeylDeterminant.lean
lake build RiemannCvs.BoundaryWeylCumulative
lake env lean RiemannCvs/BoundaryWeylCumulative.lean
lake build RiemannCvs.BoundaryWeylUniformLimit
lake env lean RiemannCvs/BoundaryWeylUniformLimit.lean
lake build RiemannCvs.BoundaryWeylSchurTail
lake env lean RiemannCvs/BoundaryWeylSchurTail.lean
lake build RiemannCvs.BoundaryWeylFarLeft
lake env lean RiemannCvs/BoundaryWeylFarLeft.lean
lake build RiemannCvs.V23BoundaryWeylMainline
lake env lean RiemannCvs/V23BoundaryWeylMainline.lean
```

The V23 workflow additionally rejects proof placeholders and user-declared
axioms/constants, prints the axiom dependencies of every new terminal theorem,
replays the corrected V22 finite Arb parity certificate, and emits the new
cumulative-residue interval certificate as a downloadable regression artifact.
