import RiemannCvs.V22ZeroModeMainline
import RiemannCvs.CvSParityDisplacement
import RiemannCvs.ObliqueWeylDeterminant
import RiemannCvs.BoundaryWeylCumulative
import RiemannCvs.BoundaryWeylUniformLimit
import RiemannCvs.BoundaryWeylSchurTail
import RiemannCvs.BoundaryWeylFarLeft
import RiemannCvs.BoundaryGapNoCrossing
import RiemannCvs.ParityOrderContinuation
import RiemannCvs.PiecewiseParityContinuation

/-!
# V23 boundary-Weyl no-crossing mainline

This umbrella extends the checked V22 zero-mode surface with the finite
boundary-Weyl layer recovered from the subsequent research argument.

The new kernel-checked chain contains:

1. the exact source-kernel identity for odd Loewner quotients and the rational
   pole term;
2. its cosine/sine compression to the concrete rectangular relation
   `D E - O D = beta etaᵀ`, including preservation under the V22 central-mode
   correction and a typed linear-map adapter for `SylvesterNoCrossing`;
3. the Lagrange characteristic-product expansion, total-residue normalization
   `sum r_i = 1`, and its signed matrix-determinant ratio form;
4. finite Abel summation together with quantitative lower bounds from either
   the final cumulative term or any earlier cumulative weight drop;
5. strict positivity from nonnegative proper cumulative residues and a
   strictly positive final cumulative residue;
6. positivity and nonvanishing of the boundary-Weyl function everywhere
   before its first pole;
7. exclusion of a factorized numerator root in that region;
8. preservation of the scalar sign through the V22 negative rank-one
   correction denominator;
9. explicit finite-to-limit interfaces: an eventual cutoff-uniform positive
   margin, or one finite `2 * margin` certificate plus a tail error of at most
   `margin`;
10. a variational low/high block theorem that turns low coercivity `a`, high
    coercivity `gamma`, coupling `epsilon`, and the product budget
    `‖eta‖² epsilon² <= margin * a * (a gamma - epsilon²)` into that required
    boundary-Weyl tail error; the concrete CvS origin-evaluation vector is now
    identified with the Euclidean Riesz vector, with
    `‖eta‖² = 2 * card ι + 1` and the current `N = 20` value exactly `41`;
    the same module now also exposes a weighted-boundary replacement whose
    numerator is `observationWeight * sourceWeight * epsilon²`, where the
    observation norm is required only on the actual Schur-error subspace;
11. a stronger energy-normalized Schur route: if
    `coupling(w,z)² <= q * lowForm(w,w) * highForm(z,z)` with `q < 1`, the weak
    block equations and low-form symmetry imply
    `<eta,u0> <= <eta,u>` directly, so finite positivity transfers without any
    Euclidean boundary-mass or additive tail-margin loss; a recursive
    three-block theorem now preserves the same `q` when a new shell couples to
    the already scaled core with coefficient `rho <= 1`; a stricter reference
    coefficient `q₀ < q` also leaves the balanced core reserve
    `((q-q₀)/(2q)) * (q*low+high)`, and a new adapter reduces future shells to
    a coupling budget against that simpler reference energy;
12. a normalized far-left estimate
    `|G_N(-t) - 1/t| <= moment/t²`, derived from total residue one and a first
    absolute spectral-moment budget;
13. the repaired boundary-gap obstruction, continuous no-crossing propagation,
   and order preservation across rank-one prime events.

The companion Arb audit certifies the cumulative-residue hypotheses for the
corrected finite `(c,N) = (13,20)` parity blocks, including several negative
individual residues whose prefixes nevertheless stay strictly positive.  It
also certifies a `k = 11` Abel-prefix lower margin on `-100 ≤ x ≤ 0`.  The
relative-energy companion certificate proves, by 2000-bit interval LDL, that
the concrete nested split `N = 20` inside `N = 120` satisfies `q < 999/1000`
in both parity sectors at `x = -1/1024`.  A second 900-bit recursive
certificate attaches the shells `120 -> 240` with `rho < 1/3` and
`240 -> 480` with `rho < 1/5`; every resulting even and odd LDL pivot is
strictly positive.  A third 900-bit certificate tightens the coefficient to
`q₀ = 249/250` through `N = 480` and attaches `480 -> 960` with
`rho < 1/7`, again with every even and odd pivot strictly positive.  Comparing
this certificate with the final `q = 999/1000` form leaves the exact balanced
reference-energy reserve coefficient `1/666`.  Positive diagonal growth
extends all four finite stages to every `x ≤ -1/1024`.  This is evidence for,
and a scalable inductive interface toward, the all-cutoff target rather than
a replacement for its operator proof.  The
finite certificate is valid at the endpoint, but the real-valued
finite-to-limit resolvent comparison must be applied on compact subintervals
whose right endpoint is strictly negative: the certified lowest even pole
approaches zero and the finite Weyl values at `x = 0` grow rather than converge
uniformly.

This is a finite reduction layer, not a hidden continuum estimate.  The
concrete displacement, signed determinant/residue identities, quantitative
Abel bounds, and the logical finite-to-limit transfer are now checked.
Applying them to the full CvS family still requires source-specific constants
for the low/high coercivities, coupling, absolute spectral moment, and
continuous-parameter uniformity, plus the concrete spectral enumeration,
compactness, and remaining exterior remainder estimate.  The two new modules
now expose the exact inequalities those constants must satisfy instead of
leaving “resolvent tail” and “far-left asymptotic” as opaque hypotheses.
The concrete identity `‖eta_M‖² = 2M+1` also exposes a structural obstruction:
a dimension-independent coupling bound together with only logarithmic
high-gap growth does not satisfy the synchronized Weyl Schur budget.  The next
source estimate may instead prove the dimensionless relative-energy inequality
with some `q < 1`: this removes the boundary vector entirely and is now the
preferred target.  The finite recursive chain through `N = 480` preserves
the concrete `q = 999/1000` benchmark, while the stricter `q₀ = 249/250`
certificate reaches `N = 960` and exposes a `1/666` reference-energy reserve
for that benchmark.  The remaining proof obligation is now the more concrete
uniform estimate `kappa_K ≤ rho/666` with one `rho < 1` for every later dyadic
shell, followed by passage from finite-support vectors to the closed tail
operator.
-/
