import RiemannCvs.V22ZeroModeMainline
import RiemannCvs.CvSParityDisplacement
import RiemannCvs.CombinedSymbolDyadicL2
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
    exact remaining dyadic-shell input; a variable-coefficient refinement now
    turns an actual coefficient `u_n^2` into reserve `1-u_n` and propagates the
    finite reserve product `prod_{i<n}(1-u_i)`, so the analytic layer may prove
    one positive product floor without paying a fixed reserve at every scale;
    this lower bound, and strict positivity when the base energy is positive,
    now pass directly to any convergent closed-form limit; a multichannel
    weighted-Cauchy adapter also combines an arbitrary finite family of earlier
    dyadic shells with aggregate coefficient `sum q_i`, and a `q_i <= q_0/2^i`
    envelope costs at most `2*q_0`, independently of the number of shells;
    a two-channel budget theorem also
    recombines the fixed-low/shell and high-core/shell estimates while exposing
    the exact factor-two allocation required by `(a+b)^2 <= 2a^2+2b^2`; the
    rigorous `rho = 1/12` bridge keeps `2/3` of its block-diagonal reference.
    For the steady tail, the balanced choice `rhoStar = 4/9` is also proved to
    keep `1/3`, and it maximizes the reusable fixed-coefficient budget
    `rhoStar * reserve = 4/27`.  A packaged theorem therefore reduces every
    later shell to two separate channel coefficients of at most `2/27`;
12. a normalized far-left estimate
    `|G_N(-t) - 1/t| <= moment/t²`, derived from total residue one and a first
    absolute spectral-moment budget;
13. the repaired boundary-gap obstruction, continuous no-crossing propagation,
   and order preservation across rank-one prime events;
14. combined-symbol dyadic `L²` adapters: the exact parity Loewner numerators
    imply factor-two-separated entry bounds and direct square bounds by
    `32 * (F(q)^2/q^2 + F(p)^2/q^2)`; rectangular Cauchy then aggregates
    column-square budgets.  Finite Abel summation plus Mathlib's reciprocal-
    square tail estimate turns an affine prefix bound into a strict `1/N`
    shell bound.  The companion endpoint expression is proved antitone for
    positive natural modes, matching the new Arb start-mode certificate.

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
`|S_n - π/4| <= 1/(4*n)`, as well as
`-(W_R)_(n,n) >= log n - 19/20`.  Since constants disappear from a
commutator, the positive-positive Loewner remainder is at most `1/(2*N)`.
The reflected parity block is different: `S_(-n)=-S_n` leaves the explicit
leading Hankel kernel `±1/(2*(k+l))`.  Integral Schur bounds put its norm below
`log(3/2)/2` on one dyadic block and below
`sqrt(log(5/3)*log(4/3))/2` between adjacent dyadic blocks.  Adding the
centered reflected remainder gives, at `N=1920`, respective rigorous source
bounds about `0.203035` and `0.191976`.  The generic same-sign operator-norm
step and its exact `1/(4*N) -> 1/(2*N)` specialization are proved in
`BoundaryWeylSchurTail`; the Hankel Schur estimates remain explicit
source-level inputs.  Thus the old global Archimedean amplitude is replaced by
a small structured dyadic term.  The prime previous/middle crossblocks and
their block-relative normalization are now the tight source terms, rather
than another finite-cutoff extrapolation.  The
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
reserve for that benchmark.  Beyond this finite bridge, the
middle-shell/new-shell estimate is certified for every integer
`K >= 31,457,280`, leaving fourteen finite middle-channel bridges from
`K=1920` through `K=15,728,640`.  The old-core/new-shell channel remains open
at every dyadic scale.  The fixed `2/27 + 2/27 -> 4/9` package is still a
sufficient route, but the new variable-reserve theorem also permits the
actual relative coefficient `u_K^2` at each scale and retains the finite
product of `1-u_K`; proving a positive uniform floor for those products
avoids the artificial exponential loss of repeatedly substituting the
worst-case `1/3` reserve.  Independently, the new finite-channel theorem
reduces the previous-core source estimate to dyadic shell budgets whose sum is
  at most `2/27`; a squared-norm envelope `q_i <= (1/27)/2^i` is sufficient for
  that channel at every depth, while the selected odd-exception split uses the
  stricter regular leading value `1/30`.  A tracked midpoint decomposition of the already
certified `1920 -> 3840` transition gives aggregate previous-core coefficients
about `0.00760` and `0.01171` in the even and odd sectors, both well below
  `2/27`; under the selected `1/30` envelope only the odd fixed base `[1,20]`
  misses, by about `0.000373`, so the source split keeps that base as a finite
channel and applies the geometric target to the dyadic tail.  The Lean theorem
`relativeCoupling_of_finiteException_and_dyadicChannelBudgets` implements this
split without a factor-two loss: a certified exceptional coefficient plus
twice the leading dyadic coefficient need only fit below `2/27`.  The
multichannel table remains route-selection data, but the singled-out odd base
is now an interval certificate: direct Arb parity formulas and exact-dyadic
congruences prove its coefficient is below `1/384`, with `20/20` positive base
rows, `38400/38400` verified-solve residual intervals containing zero, and
`1920/1920` positive Schur rows.  Choosing regular leading coefficient `1/30`
then gives exact allocation `133/1920` and positive slack `83/17280` below
`2/27`; `relativeCoupling_of_v23OddFixedBaseAndDyadicBudgets` is the matching
Lean adapter.  At the first `1920 -> 3840` transition, direct Arb formulas,
two common reverse-Schur solves, and exact-dyadic congruences now also certify
all nine regular source bands: five even bands with budget sum `31/480`, and
four odd bands with sum `1/16`.  Their exact finite slacks inside `2/27` are
`41/4320` in the even sector and, after adding the odd `1/384` exception,
`31/3456` in the odd sector.  The scalar normalization is now stronger than
the initial-block estimate: the same finite reserve product controls the
initial energy plus the sum of every historical shell energy, and a direct
adapter converts a source estimate against that full block-diagonal sum into
one relative to the recursively glued core.  The all-scale regular envelope is
now also reduced to two local source estimates: every newest coefficient is at
most `1/30`, and transporting an existing band one dyadic scale outward reduces
its coefficient by at least one half.  Four new Lean theorems propagate those
inputs through the full triangular channel array, provide the finite-range
shape consumed by the Cauchy adapter, and preserve the odd `1/384` exception.
  A two-scale midpoint regression from `K=960` to `K=1920` observes all ten
  repeated-band ratios strictly below `1/2`, but remains route-selection evidence.
  The same probe now reconstructs every crossblock as prime, Archimedean, and
  rank-two pole pieces against the same full energies.  Prime and pole separately
  decay below one half, while the two newest Archimedean ratios exceed one half;
  consequently a three-independent-component proof is too coarse.  Retaining
  the combined Archimedean/prime Loewner symbol gives all ten ratios below one
  half, and adding the pole by the two-piece amplitude triangle stays below one
  half for all nine regular channels.  The same two-piece bound puts both newest
  parity channels below `1/30`; the odd `[1,20]` block remains the certified fixed
  exception.  Two additional Lean theorems formalize exactly this amplitude
  triangle and its half-transport specialization.  Two source-level parity
  identities now also rewrite every off-diagonal Loewner crossblock entry into
  the exact weighted numerators `q*F(q)-p*F(p)` in the even sector and
  `p*F(q)-q*F(p)` in the odd sector, both over `p^2-q^2`.  Thus the remaining
  source estimate targets the combined odd symbol directly and retains the
  observed prime/Archimedean cancellation.  Eight initial source-algebra theorems now
  define the finite prime sine polynomial, prove its oddness, combine it with
  any odd Archimedean symbol, commute addition and scalar multiplication with
  the complete diagonal-aware Loewner kernel, preserve the concrete `1/pi`
  normalization, and prove the omitted endpoint phase `sin(2*pi*n)=0` on every
  natural Fourier mode.  Four more entrywise theorems expose the actual prime
  diagonal, identify the literal per-event assembly loop with its finite sum,
  delete the cutoff event on and off the diagonal, and prove that the complete
  piecewise prime entry is exactly the normalized Loewner kernel.  A combined
  actual-diagonal adapter then leaves only the Archimedean source formula.
  Hence the prime algebra, entrywise identification, and normalization are
  checked.  Five further full-source theorems expose the literal normalized
  Archimedean diagonal/off-diagonal entry, instantiate the rational pole with
  scale `32*log(c)*sinh(log(c)/4)^2` and denominators `log(c)^2+16*pi^2*n^2`,
  assemble `T=W_02-W_R-W_p`, and prove its complete displacement law.  The
  concrete Archimedean symbol is now defined by its literal digamma-imaginary
  part and exponentially convergent geometric correction.  Lean proves the
  correction series summable for every `c>1`, proves the symbol odd by complex
  conjugation, and instantiates the full cutoff-free displacement law with it.
  The concrete diagonal is now defined from the real digamma and
  derivative-of-digamma terms, all three Arb geometric corrections, and the
  exact `kappa` and `J` cutoff constants.  Lean proves every diagonal series
  summable for `c>1`, proves all correction terms and the assembled diagonal
  reflection-even, and instantiates the full kernel with no free Archimedean
  source argument.  Lean now also defines the literal centered signed-integer
  CvS builder, removes its signed-symbol and absolute-diagonal branches using
  the proved reflection laws, and identifies every finite matrix entry with
  the exact cutoff-free kernel restriction.  Its literal finite cosine and sine
  matrices are now proved equal to the existing orthonormal even and odd parity
  compressions.  The remaining operator bridge is the shell coordinate map,
  coercive-floor domination, and recursive shell-energy identification.
  The combined-symbol certificate
  now also rests on a Lean proof of the finite nonresonant geometric-sum bound,
  including arbitrary starting indices and its sine/cosine projections; Arb
  retains the composite doubled/difference/sum phase checks.  Nine further
  Lean theorems now instantiate the prime polynomial with the exact
  `log(p)/sqrt(q)` weights and `2*pi*log(q)/log(c)` phases, package its complete
  normalized combined Loewner kernel, prove exact cutoff-event deletion, and
  prove strict-interior single-phase nonresonance from `1<q<c`.  Thirteen more
  Lean theorems isolate the sole pair-sum resonance `q*r=c`, enumerate the
  tracked cutoff-13 locations `2,3,4,5,7,8,9,11`, and prove all single,
  doubled, pair-difference, and pair-sum denominators symbolically nonzero.
  Arb now supplies their rigorous magnitudes rather than the nonresonance
  fact.  The analytic CvS digamma/geometric value and diagonal, the finite
  prime and rational-pole branches, the full sign assembly, and the finite
  parity compression are now source-identified.  The certificate
  now proves the scalar weighted square budget `<1/N` for every `N>=1920`.
  Fourteen further Lean adapters preserve the concrete `1/pi` Fourier scale,
  turn the old-band weighted budget into an ordinary square sum, close the
  newest-band matrix constant at `24/pi^2`, pass it through two coercive energy
  floors, and prove exact one-half transport when the target shell doubles.
  The corresponding 256-bit and 384-bit Arb compositions agree: the newest
  regular coefficient is strictly below `1/30` for every dyadic previous
  cutoff `K>=491520`; the first passing upper midpoint is
  `0.0329380152768082444...`, with strict slack
  `0.0003953180565250889...`.  Hence this analytic route reduces the newest
  channel below that threshold to the eight finite cutoffs
  `1920,3840,7680,15360,30720,61440,122880,245760`.  This conclusion remains
  conditional on the listed concrete Loewner-symbol, parity-compression, and
  coercive-floor identifications.  The source-specific proof of the
  joint Loewner/pole amplitude bounds, the identification of separated band
  energies with the scalar shell decomposition, and a uniform coefficient
  partial-sum bound strictly below one remain analytic inputs.  The scalar
  product lemmas turn the last bound into the explicit positive floor `1-total`.
  This is followed by convergence of the finite-support energies to the closed
  tail form.
  The triangular transport induction, two-source amplitude adapter, full
  block-sum normalization, finite-product floor adapter, and strict order-limit
  passage are kernel-checked; the source-specific Loewner/pole transport bound
  and shell-energy identification, the fourteen finite middle bridges, the
  summable coefficient bound, and source-specific form convergence remain open.
-/
