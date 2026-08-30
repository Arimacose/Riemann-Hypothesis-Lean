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
    a coupling budget against that simpler reference energy; scalar shell
    energies now have an explicit natural-number induction theorem, and if
    those finite-support energies converge, their nonnegativity passes to the
    closed-form limit; a uniform `rhoStar <= 1` specialization exposes the
    exact remaining dyadic-shell input; a two-channel budget theorem also
    recombines the fixed-low/shell and high-core/shell estimates while exposing
    the exact factor-two allocation required by `(a+b)^2 <= 2a^2+2b^2`; the
    rigorous `rho = 1/12` bridge keeps `2/3` of its block-diagonal reference.
    For the steady tail, the balanced choice `rhoStar = 4/9` is now proved to
    keep `1/3`, and it maximizes the reusable budget
    `rhoStar * reserve = 4/27`.  A packaged theorem therefore reduces every
    later shell to two separate channel coefficients of at most `2/27`;
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
reference-energy reserve coefficient `1/666`.  A midpoint diagnostic at
`960 -> 1920` selects the direct coefficient `rho = 1/12`; a fourth rigorous
certificate then validates that shell at 256 bits by an Arb verified solve,
an exact Schur enclosure, a fixed invertible dyadic congruence, and `960/960`
strictly positive preconditioned Gershgorin rows in each parity sector.  A fifth
direct-parity certificate avoids the full signed-mode matrix and validates
`1920 -> 3840` with the optimized `rhoStar = 4/9`: both 256-bit and 384-bit
replays have `1920/1920` strict rows in each sector, and both precisions select
the same byte-for-byte exact-dyadic preconditioners.  Positive diagonal growth
extends all six finite stages through `N = 3840` to every `x ≤ -1/1024`.  This
is evidence for, and a scalable inductive interface toward, the all-cutoff
target rather than a replacement for its operator proof.
The same diagnostic finds reference coefficients about `0.04327` and
`0.05486`, far above `1/666`; thus the balanced reserve is an eventual-tail
interface rather than the immediate `960 -> 1920` bound.  A direct-parity
midpoint probe, cross-checked entrywise against the canonical Arb construction
at `N = 120`, selected the next two shells.  Its `1920 -> 3840` direct
coefficient is now replaced by the rigorous `4/9` certificate above.  The
remaining `3840 -> 7680` direct `q₀` coefficients are about `0.01982` and
`0.03208`; those two values, and the component-wise channel splits below,
remain midpoint scaling data rather than interval certificates.
Optimizing the balanced recursive coefficient changes the preferred uniform
target to `rhoStar = 4/9`: it leaves reserve `1/3` and the maximal reusable
reference budget `4/27`.  The two-channel theorem assigns `2/27` to each
source block.  At `1920 -> 3840`, the measured previous/middle channel
coefficients are about `0.00635/0.03440` in the even sector and
`0.02855/0.03454` in the odd sector.  At `3840 -> 7680` they are about
`0.00474/0.01727` and `0.01734/0.01744`.  All eight values are below `2/27`,
with the tightest observed slack still about `0.03953`.  The combined
recursive-reference coefficients are about `0.03544/0.04768` and
`0.02016/0.03068`, all far below `4/27`.  This identifies the repeatable
steady induction shape `2/27 + 2/27 -> 4/27 -> 4/9 -> 1/3`.  Two rigorous
analytic-constant audits now sharpen the source side of this target.  Exact
rational path geometry and Arb weights for all `415642` admissible sixth-power
paths prove the prime translation norm `‖T_13‖ < 10/3`.  The digamma remainder,
trigamma series, and geometric corrections prove, for every `n >= 960`,
`0 <= S_n <= 4/5` and
`-(W_R)_(n,n) >= log n - 19/20`.  These replace the old global prime and
Archimedean constants; the remaining step is their sharp block-relative use,
not another finite-cutoff extrapolation.  The
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
certificate now reaches `N = 3840` and exposes a `1/666` reference-energy
reserve for that benchmark.  Beyond this finite bridge, the preferred
analytic obligation is now the component-wise dyadic estimate: for every
dyadic `K >= 1920`, both the old-core/new-shell and middle-shell/new-shell
relative coefficients are at most `2/27`.  The packaged `rhoStar = 4/9`
theorem then supplies the direct recursive shell bound and renews a `1/3`
reserve automatically.  This is followed by convergence of the finite-support
energies to the closed tail form.  The scalar induction and order-limit
passage are kernel-checked; the source-specific form convergence and uniform
two-channel matrix estimate remain open.
-/
