import RiemannCvs.V22ZeroModeMainline
import RiemannCvs.CvSParityDisplacement
import RiemannCvs.CombinedSymbolDyadicL2
import RiemannCvs.C13ArchimedeanEndpoint
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
  compressions.  With `B=K/2`, `Fin B` and `Fin (4B)` are now proved to exhaust
  exactly the historical `(B,2B]` rows and newest `(4B,8B]` columns, and both
  rectangular builder restrictions are identified with the corresponding
  parity submatrices.  A finite-component coercivity theorem now derives the
  displayed Euclidean floor from one diagonal lower bound and absolute bounds
  for all perturbation forms.  The remaining operator bridge is the concrete
  CvS component bounds.  On the
  recursive side, `recursiveBlockEnergy` now gives the canonical `E+2*C+T`
  recursion, its finite-sum formula is proved, and the reserve-product plus
  next-shell adapters no longer ask for a separate recursion hypothesis.
  The finite matrix quadratic form is now split exactly as `base+2*cross+tail`
  on a sum-type index, with the two oriented crossblocks averaged so no hidden
  symmetry hypothesis is needed.  The actual even and odd CvS matrices are
  pulled back to the proved historical/newest indices, their rectangular
  blocks are identified with the earlier band matrices, and both concrete
  quadratic forms feed the recursive successor theorem directly.  Symmetry and
  simultaneous-reflection invariance of the pole and Loewner branches are now
  proved through the concrete builder and both parity compressions; hence the
  averaged cross coordinate simplifies exactly to the single rectangular
  historical/newest bilinear form consumed by the certificate.  A generic
  finite-matrix tower theorem now proves that exact reindexings
  `I(n+1) ≃ I(n) ⊕ S(n)`, vector concatenation, and preservation of the old
  matrix block force the entire concrete energy sequence to equal
  `recursiveBlockEnergy`.  The odd `Fin` tower and the even `Option Fin` tower
  now have explicit dyadic split equivalences; Lean proves their vector
  concatenation and old-core matrix preservation identities and instantiates
  the generic theorem for both concrete parity energies.  Thus the all-scale
  shell-tower compatibility is closed without another scalar recursion
  hypothesis.  For any finite positive-mode family, both concrete parity
  matrices are now split exactly into the negative Archimedean main diagonal
  and three error matrices (pole, Archimedean remainder, and prime).  The
  generic coercive-floor adapters reduce the operator input to one pointwise
  diagonal lower bound and three absolute quadratic-form bounds.
  The pulled-back right-right block of each actual tower is now identified with
  exactly that positive-mode matrix, including the `4B -> 8B` newest-shell mode
  map, so the same adapters give the coercive floor directly for
  `finiteMatrixTowerTailEnergy`; neither shell identification, matrix
  decomposition, nor its parity signs remain implicit.  The pole error is now
  factored further: the even and odd parity pole blocks are explicit rank-one
  forms, so their absolute quadratic-form bounds follow from finite scalar
  sums of squared rational weights by Cauchy--Schwarz.  Pointwise reciprocal-
  square estimates and an exact consecutive-shell reindexing now bound both
  sums by the recorded `scale/(8*pi^2*old)` pole tail; cutoff `13` has direct
  assumption-free specializations.  New cutoff-13 consumers insert that bound
  automatically for both standalone shells and the actual odd/even matrix
  towers.  Thus only the Archimedean remainder and prime error forms remain
  alongside the diagonal bound.  The diagonal self-entry is also rewritten to
  the literal Archimedean diagonal used by the interval certificate, while
  `CombinedSymbolDyadicL2` now closes all geometric corrections, derives the
  real digamma floor from a DLMF-form complex norm remainder, reduces the
  trigamma real floor to decay of the shifted digamma derivative through a
  differentiated shift equation and finite telescoping, proves the remaining
  error antitone, and reduces the cutoff-13 all-mode floor to one scalar
  endpoint comparison at mode `960`.  `C13ArchimedeanEndpoint` now proves that
  comparison from explicit rational bounds for `log`, `arctan`, `π`, and square
  roots, so the diagonal route retains only the global quadratic digamma
  remainder as an analytic premise.
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
  prime and rational-pole branches, the full sign assembly, the finite parity
  compression, and the newest separated mode bands are now source-identified.
  The certificate
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
  `1920,3840,7680,15360,30720,61440,122880,245760`.  This conclusion now
  retains only the concrete Archimedean diagonal/remainder and prime-form
  bounds.  The source-specific previous-core proof of the joint Loewner/pole
  amplitude bounds and a uniform coefficient partial-sum bound strictly below
  one remain analytic inputs.  The scalar
  product lemmas turn the last bound into the explicit positive floor `1-total`.
  This is followed by convergence of the finite-support energies to the closed
  tail form.
  The triangular transport induction, two-source amplitude adapter, full
  block-sum normalization, finite-product floor adapter, and strict order-limit
  passage are kernel-checked; the source-specific Loewner/pole transport bound
  and shell-energy identification, the fourteen finite middle bridges, the
  summable coefficient bound, and source-specific form convergence remain open.
-/

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail
open Filter
open scoped Topology

/-!
## Concrete historical/newest block forms

The separated historical rows and newest columns already have exact finite
indices in `CombinedSymbolDyadicL2`.  Pulling the full parity matrices back to
their sum type supplies a literal two-block matrix, so the generic recursive
energy coordinates apply without an informal reindexing step.
-/

/-- Even-parity builder restricted to the historical and newest positive-mode
bands, with the two bands represented by the two summands of the index. -/
noncomputable def logarithmicCvSBuilderEvenHistoricalNewestBlock
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    Matrix (Fin B ⊕ Fin (4 * B)) (Fin B ⊕ Fin (4 * B)) ℝ :=
  fun i j =>
    logarithmicCvSBuilderEvenMatrix c location base (8 * B)
      (Sum.elim
        (fun k => some (historicalBandIndex B k))
        (fun k => some (newestShellIndex B k)) i)
      (Sum.elim
        (fun k => some (historicalBandIndex B k))
        (fun k => some (newestShellIndex B k)) j)

/-- Odd-parity counterpart of
`logarithmicCvSBuilderEvenHistoricalNewestBlock`. -/
noncomputable def logarithmicCvSBuilderOddHistoricalNewestBlock
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    Matrix (Fin B ⊕ Fin (4 * B)) (Fin B ⊕ Fin (4 * B)) ℝ :=
  fun i j =>
    logarithmicCvSBuilderOddMatrix c location base (8 * B)
      (Sum.elim (historicalBandIndex B) (newestShellIndex B) i)
      (Sum.elim (historicalBandIndex B) (newestShellIndex B) j)

/-- The left-right block is exactly the previously identified even newest-band
restriction. -/
@[simp] theorem logarithmicCvSBuilderEvenHistoricalNewestBlock_inl_inr
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (i : Fin B) (j : Fin (4 * B)) :
    logarithmicCvSBuilderEvenHistoricalNewestBlock c location base B
        (Sum.inl i) (Sum.inr j) =
      logarithmicCvSBuilderEvenNewestBand c location base B i j := by
  rfl

/-- The left-right block is exactly the previously identified odd newest-band
restriction. -/
@[simp] theorem logarithmicCvSBuilderOddHistoricalNewestBlock_inl_inr
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (i : Fin B) (j : Fin (4 * B)) :
    logarithmicCvSBuilderOddHistoricalNewestBlock c location base B
        (Sum.inl i) (Sum.inr j) =
      logarithmicCvSBuilderOddNewestBand c location base B i j := by
  rfl

/-- The pulled-back even historical/newest matrix remains symmetric. -/
theorem logarithmicCvSBuilderEvenHistoricalNewestBlock_symm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (i j : Fin B ⊕ Fin (4 * B)) :
    logarithmicCvSBuilderEvenHistoricalNewestBlock c location base B i j =
      logarithmicCvSBuilderEvenHistoricalNewestBlock
        c location base B j i := by
  unfold logarithmicCvSBuilderEvenHistoricalNewestBlock
  exact logarithmicCvSBuilderEvenMatrix_symm _ _ _ _ _ _

/-- The pulled-back odd historical/newest matrix remains symmetric. -/
theorem logarithmicCvSBuilderOddHistoricalNewestBlock_symm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (i j : Fin B ⊕ Fin (4 * B)) :
    logarithmicCvSBuilderOddHistoricalNewestBlock c location base B i j =
      logarithmicCvSBuilderOddHistoricalNewestBlock
        c location base B j i := by
  unfold logarithmicCvSBuilderOddHistoricalNewestBlock
  exact logarithmicCvSBuilderOddMatrix_symm _ _ _ _ _ _

/-- The even recursive cross coordinate is exactly the rectangular
historical/newest bilinear form used by the scalar certificate. -/
theorem logarithmicCvSBuilderEvenHistoricalNewestBlock_crossEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location base B) x y =
      ∑ i, ∑ j,
        x i * logarithmicCvSBuilderEvenNewestBand
          c location base B i j * y j := by
  calc
    finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location base B) x y =
      ∑ i, ∑ j, x i *
        logarithmicCvSBuilderEvenHistoricalNewestBlock c location base B
          (Sum.inl i) (Sum.inr j) * y j :=
      finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm _ x y
        (logarithmicCvSBuilderEvenHistoricalNewestBlock_symm
          c location base B)
    _ = _ := by rfl

/-- The odd recursive cross coordinate is exactly the corresponding
rectangular historical/newest bilinear form. -/
theorem logarithmicCvSBuilderOddHistoricalNewestBlock_crossEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location base B) x y =
      ∑ i, ∑ j,
        x i * logarithmicCvSBuilderOddNewestBand
          c location base B i j * y j := by
  calc
    finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location base B) x y =
      ∑ i, ∑ j, x i *
        logarithmicCvSBuilderOddHistoricalNewestBlock c location base B
          (Sum.inl i) (Sum.inr j) * y j :=
      finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm _ x y
        (logarithmicCvSBuilderOddHistoricalNewestBlock_symm
          c location base B)
    _ = _ := by rfl

/-- Exact `base + 2*cross + tail` decomposition of the concrete even parity
historical/newest form. -/
theorem logarithmicCvSBuilderEvenHistoricalNewestBlock_energy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location base B)
        (finiteMatrixBlockVector x y) =
      finiteMatrixBlockBaseEnergy
          (logarithmicCvSBuilderEvenHistoricalNewestBlock
            c location base B) x +
        2 * finiteMatrixBlockCrossEnergy
          (logarithmicCvSBuilderEvenHistoricalNewestBlock
            c location base B) x y +
        finiteMatrixBlockTailEnergy
          (logarithmicCvSBuilderEvenHistoricalNewestBlock
            c location base B) y := by
  exact finiteMatrixQuadraticEnergy_blockVector
    (logarithmicCvSBuilderEvenHistoricalNewestBlock c location base B) x y

/-- Exact `base + 2*cross + tail` decomposition of the concrete odd parity
historical/newest form. -/
theorem logarithmicCvSBuilderOddHistoricalNewestBlock_energy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location base B)
        (finiteMatrixBlockVector x y) =
      finiteMatrixBlockBaseEnergy
          (logarithmicCvSBuilderOddHistoricalNewestBlock
            c location base B) x +
        2 * finiteMatrixBlockCrossEnergy
          (logarithmicCvSBuilderOddHistoricalNewestBlock
            c location base B) x y +
        finiteMatrixBlockTailEnergy
          (logarithmicCvSBuilderOddHistoricalNewestBlock
            c location base B) y := by
  exact finiteMatrixQuadraticEnergy_blockVector
    (logarithmicCvSBuilderOddHistoricalNewestBlock c location base B) x y

/-- Once the three displayed concrete even coordinates are assigned to one
recursive step, the successor energy is definitionally the full pulled-back
CvS quadratic form. -/
theorem recursiveBlockEnergy_succ_eq_evenHistoricalNewestForm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location eventBase : ι → ℝ) (B : ℕ)
    (base : ℝ) (tail cross : ℕ → ℝ) (n : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ)
    (hBase :
      recursiveBlockEnergy base tail cross n =
        finiteMatrixBlockBaseEnergy
          (logarithmicCvSBuilderEvenHistoricalNewestBlock
            c location eventBase B) x)
    (hTail :
      tail n = finiteMatrixBlockTailEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location eventBase B) y)
    (hCross :
      cross n = finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location eventBase B) x y) :
    recursiveBlockEnergy base tail cross (n + 1) =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenHistoricalNewestBlock
          c location eventBase B)
        (finiteMatrixBlockVector x y) := by
  exact recursiveBlockEnergy_succ_eq_finiteMatrixQuadraticEnergy
    base tail cross n
    (logarithmicCvSBuilderEvenHistoricalNewestBlock
      c location eventBase B) x y hBase hTail hCross

/-- Odd-parity specialization of the exact recursive finite-form adapter. -/
theorem recursiveBlockEnergy_succ_eq_oddHistoricalNewestForm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location eventBase : ι → ℝ) (B : ℕ)
    (base : ℝ) (tail cross : ℕ → ℝ) (n : ℕ)
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ)
    (hBase :
      recursiveBlockEnergy base tail cross n =
        finiteMatrixBlockBaseEnergy
          (logarithmicCvSBuilderOddHistoricalNewestBlock
            c location eventBase B) x)
    (hTail :
      tail n = finiteMatrixBlockTailEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location eventBase B) y)
    (hCross :
      cross n = finiteMatrixBlockCrossEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location eventBase B) x y) :
    recursiveBlockEnergy base tail cross (n + 1) =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddHistoricalNewestBlock
          c location eventBase B)
        (finiteMatrixBlockVector x y) := by
  exact recursiveBlockEnergy_succ_eq_finiteMatrixQuadraticEnergy
    base tail cross n
    (logarithmicCvSBuilderOddHistoricalNewestBlock
      c location eventBase B) x y hBase hTail hCross

/-!
## Exact all-scale parity towers

The positive modes of the finite CvS matrices are initial segments of one
fixed sequence.  Splitting `Fin next` at `old` therefore gives the concrete
index equivalence required by the generic matrix-tower theorem.  Fixed global
coordinate sequences automatically concatenate across the split, and the
literal builder formulas automatically preserve the old matrix block.
-/

/-- Split a finite initial segment into its old prefix and new shell. -/
noncomputable def finBlockSplitEquiv
    {old shell next : ℕ} (h : next = old + shell) :
    Fin next ≃ Fin old ⊕ Fin shell :=
  (Fin.castOrderIso h).toEquiv.trans finSumFinEquiv.symm

/-- Restriction of one global positive-mode coordinate sequence. -/
noncomputable def finGlobalVector
    (z : ℕ → ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => z i

/-- Consecutive shell extracted from the same global coordinate sequence. -/
noncomputable def finGlobalShellVector
    (z : ℕ → ℝ) (old shell : ℕ) : Fin shell → ℝ :=
  fun j => z (old + j)

/-- A global positive-mode vector pulls back to the old prefix concatenated
with its consecutive shell. -/
theorem finGlobalVector_pullback_split
    (z : ℕ → ℝ) {old shell next : ℕ}
    (h : next = old + shell) :
    finiteVectorPullback (finBlockSplitEquiv h) (finGlobalVector z next) =
      finiteMatrixBlockVector
        (finGlobalVector z old) (finGlobalShellVector z old shell) := by
  funext i
  rcases i with i | j
  · simp [finiteVectorPullback, finiteMatrixBlockVector,
      finGlobalVector, finBlockSplitEquiv]
  · simp [finiteVectorPullback, finiteMatrixBlockVector,
      finGlobalVector, finGlobalShellVector, finBlockSplitEquiv]

/-- Under the initial-segment split, the old-old block of the literal odd
builder is exactly the previous odd builder matrix. -/
theorem logarithmicCvSBuilderOddMatrix_pullback_inl_inl
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    {old shell next : ℕ} (h : next = old + shell)
    (i j : Fin old) :
    finiteMatrixPullback (finBlockSplitEquiv h)
        (logarithmicCvSBuilderOddMatrix c location base next)
        (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderOddMatrix c location base old i j := by
  simp [finiteMatrixPullback, finBlockSplitEquiv,
    logarithmicCvSBuilderOddMatrix, positiveIntegerMode]

noncomputable def logarithmicCvSBuilderOddTowerMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (size : ℕ → ℕ)
    (n : ℕ) : Matrix (Fin (size n)) (Fin (size n)) ℝ :=
  logarithmicCvSBuilderOddMatrix c location base (size n)

noncomputable def logarithmicCvSBuilderOddTowerVector
    (z : ℕ → ℝ) (size : ℕ → ℕ)
    (n : ℕ) : Fin (size n) → ℝ :=
  finGlobalVector z (size n)

noncomputable def logarithmicCvSBuilderOddTowerShellVector
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (n : ℕ) : Fin (shell n) → ℝ :=
  finGlobalShellVector z (size n) (shell n)

noncomputable def logarithmicCvSBuilderOddTowerSplit
    (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) : Fin (size (n + 1)) ≃ Fin (size n) ⊕ Fin (shell n) :=
  finBlockSplitEquiv (hSize n)

/-- Every nested odd-parity finite CvS energy is exactly the canonical
recursive block energy, for any additive shell schedule and fixed global
positive-mode coordinate sequence. -/
theorem logarithmicCvSBuilderOddTowerEnergy_eq_recursiveBlockEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n) :
    ∀ n,
      finiteMatrixTowerEnergy
          (logarithmicCvSBuilderOddTowerMatrix c location base size)
          (logarithmicCvSBuilderOddTowerVector z size) n =
        recursiveBlockEnergy
          (finiteMatrixTowerEnergy
            (logarithmicCvSBuilderOddTowerMatrix c location base size)
            (logarithmicCvSBuilderOddTowerVector z size) 0)
          (finiteMatrixTowerTailEnergy
            (logarithmicCvSBuilderOddTowerMatrix c location base size)
            (logarithmicCvSBuilderOddTowerShellVector z size shell)
            (logarithmicCvSBuilderOddTowerSplit size shell hSize))
          (finiteMatrixTowerCrossEnergy
            (logarithmicCvSBuilderOddTowerMatrix c location base size)
            (logarithmicCvSBuilderOddTowerVector z size)
            (logarithmicCvSBuilderOddTowerShellVector z size shell)
            (logarithmicCvSBuilderOddTowerSplit size shell hSize)) n := by
  apply finiteMatrixTowerEnergy_eq_recursiveBlockEnergy
    (logarithmicCvSBuilderOddTowerMatrix c location base size)
    (logarithmicCvSBuilderOddTowerVector z size)
    (logarithmicCvSBuilderOddTowerShellVector z size shell)
    (logarithmicCvSBuilderOddTowerSplit size shell hSize)
  · intro n
    exact finGlobalVector_pullback_split z (hSize n)
  · intro n i j
    exact logarithmicCvSBuilderOddMatrix_pullback_inl_inl
      c location base (hSize n) i j

/-- Reassociate an optional coordinate over a binary sum so that the central
coordinate stays with the old even block. -/
noncomputable def optionSumEquiv (α β : Type*) :
    Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv x := by rcases x with _ | (_ | _) <;> rfl
  right_inv x := by rcases x with (_ | _) | _ <;> rfl

/-- Even-sector split: the central coordinate and old positive modes form the
left block, while only the newly added positive modes form the shell. -/
noncomputable def optionFinBlockSplitEquiv
    {old shell next : ℕ} (h : next = old + shell) :
    Option (Fin next) ≃ Option (Fin old) ⊕ Fin shell where
  toFun
    | none => Sum.inl none
    | some i =>
      match finBlockSplitEquiv h i with
      | Sum.inl j => Sum.inl (some j)
      | Sum.inr j => Sum.inr j
  invFun
    | Sum.inl none => none
    | Sum.inl (some i) => some ((finBlockSplitEquiv h).symm (Sum.inl i))
    | Sum.inr j => some ((finBlockSplitEquiv h).symm (Sum.inr j))
  left_inv
    | none => rfl
    | some i => by
      cases hi : finBlockSplitEquiv h i with
      | inl j =>
          simp only [hi]
          congr 1
          simpa [hi] using (finBlockSplitEquiv h).symm_apply_apply i
      | inr j =>
          simp only [hi]
          congr 1
          simpa [hi] using (finBlockSplitEquiv h).symm_apply_apply i
  right_inv
    | Sum.inl none => rfl
    | Sum.inl (some i) => by
        simp only
        rw [(finBlockSplitEquiv h).apply_symm_apply (Sum.inl i)]
    | Sum.inr j => by
        simp only
        rw [(finBlockSplitEquiv h).apply_symm_apply (Sum.inr j)]

/-- Restriction of one global even-sector vector, with a fixed central
coordinate and a global positive-mode sequence. -/
noncomputable def optionFinGlobalVector
    (z0 : ℝ) (z : ℕ → ℝ) (N : ℕ) : Option (Fin N) → ℝ
  | none => z0
  | some i => z i

theorem optionFinGlobalVector_pullback_split
    (z0 : ℝ) (z : ℕ → ℝ)
    {old shell next : ℕ} (h : next = old + shell) :
    finiteVectorPullback (optionFinBlockSplitEquiv h)
        (optionFinGlobalVector z0 z next) =
      finiteMatrixBlockVector
        (optionFinGlobalVector z0 z old)
        (finGlobalShellVector z old shell) := by
  funext i
  rcases i with (_ | i) | j
  · rfl
  · simp [finiteVectorPullback, finiteMatrixBlockVector,
      optionFinGlobalVector, optionFinBlockSplitEquiv,
      finBlockSplitEquiv]
  · simp [finiteVectorPullback, finiteMatrixBlockVector,
      optionFinGlobalVector, finGlobalShellVector,
      optionFinBlockSplitEquiv, finBlockSplitEquiv]

/-- Under the even-sector split, the old-old block is exactly the previous
even builder matrix, including the unchanged central coordinate. -/
theorem logarithmicCvSBuilderEvenMatrix_pullback_inl_inl
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    {old shell next : ℕ} (h : next = old + shell)
    (i j : Option (Fin old)) :
    finiteMatrixPullback (optionFinBlockSplitEquiv h)
        (logarithmicCvSBuilderEvenMatrix c location base next)
        (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderEvenMatrix c location base old i j := by
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · simp [finiteMatrixPullback, optionFinBlockSplitEquiv,
      finBlockSplitEquiv, logarithmicCvSBuilderEvenMatrix,
      positiveIntegerMode]
  · simp [finiteMatrixPullback, optionFinBlockSplitEquiv,
      finBlockSplitEquiv, logarithmicCvSBuilderEvenMatrix,
      positiveIntegerMode]
  · simp [finiteMatrixPullback, optionFinBlockSplitEquiv,
      finBlockSplitEquiv, logarithmicCvSBuilderEvenMatrix,
      positiveIntegerMode]

noncomputable def logarithmicCvSBuilderEvenTowerMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (size : ℕ → ℕ)
    (n : ℕ) : Matrix (Option (Fin (size n))) (Option (Fin (size n))) ℝ :=
  logarithmicCvSBuilderEvenMatrix c location base (size n)

noncomputable def logarithmicCvSBuilderEvenTowerVector
    (z0 : ℝ) (z : ℕ → ℝ) (size : ℕ → ℕ)
    (n : ℕ) : Option (Fin (size n)) → ℝ :=
  optionFinGlobalVector z0 z (size n)

noncomputable def logarithmicCvSBuilderEvenTowerShellVector
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (n : ℕ) : Fin (shell n) → ℝ :=
  finGlobalShellVector z (size n) (shell n)

noncomputable def logarithmicCvSBuilderEvenTowerSplit
    (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) :
    Option (Fin (size (n + 1))) ≃
      Option (Fin (size n)) ⊕ Fin (shell n) :=
  optionFinBlockSplitEquiv (hSize n)

/-- Every nested even-parity finite CvS energy, including the central mode,
is exactly the canonical recursive block energy. -/
theorem logarithmicCvSBuilderEvenTowerEnergy_eq_recursiveBlockEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z0 : ℝ) (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n) :
    ∀ n,
      finiteMatrixTowerEnergy
          (logarithmicCvSBuilderEvenTowerMatrix c location base size)
          (logarithmicCvSBuilderEvenTowerVector z0 z size) n =
        recursiveBlockEnergy
          (finiteMatrixTowerEnergy
            (logarithmicCvSBuilderEvenTowerMatrix c location base size)
            (logarithmicCvSBuilderEvenTowerVector z0 z size) 0)
          (finiteMatrixTowerTailEnergy
            (logarithmicCvSBuilderEvenTowerMatrix c location base size)
            (logarithmicCvSBuilderEvenTowerShellVector z size shell)
            (logarithmicCvSBuilderEvenTowerSplit size shell hSize))
          (finiteMatrixTowerCrossEnergy
            (logarithmicCvSBuilderEvenTowerMatrix c location base size)
            (logarithmicCvSBuilderEvenTowerVector z0 z size)
            (logarithmicCvSBuilderEvenTowerShellVector z size shell)
            (logarithmicCvSBuilderEvenTowerSplit size shell hSize)) n := by
  apply finiteMatrixTowerEnergy_eq_recursiveBlockEnergy
    (logarithmicCvSBuilderEvenTowerMatrix c location base size)
    (logarithmicCvSBuilderEvenTowerVector z0 z size)
    (logarithmicCvSBuilderEvenTowerShellVector z size shell)
    (logarithmicCvSBuilderEvenTowerSplit size shell hSize)
  · intro n
    exact optionFinGlobalVector_pullback_split z0 z (hSize n)
  · intro n i j
    exact logarithmicCvSBuilderEvenMatrix_pullback_inl_inl
      c location base (hSize n) i j

/-!
## Concrete positive-mode coercive decomposition

For any finite family of signed positive-mode labels, the concrete even and odd
CvS matrices split exactly into the negative Archimedean main diagonal and
three error matrices, ordered as rational pole, Archimedean remainder, and
finite-prime contribution.  The final adapters reduce the recorded coercive
floor to one pointwise diagonal lower bound and three absolute quadratic-form
bounds; no matrix decomposition remains implicit.
-/

open Finset
open scoped BigOperators
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def finiteVectorEuclideanNormSq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, x i ^ 2

@[simp] theorem finiteVectorEuclideanNormSq_nonneg
    {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ finiteVectorEuclideanNormSq x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finiteMatrixQuadraticEnergy_add
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteMatrixQuadraticEnergy (A + B) x =
      finiteMatrixQuadraticEnergy A x + finiteMatrixQuadraticEnergy B x := by
  simp [finiteMatrixQuadraticEnergy, mul_add, add_mul, Finset.sum_add_distrib]

theorem finiteMatrixQuadraticEnergy_sum_finset
    {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (E : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteMatrixQuadraticEnergy (∑ k ∈ s, E k) x =
      ∑ k ∈ s, finiteMatrixQuadraticEnergy (E k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteMatrixQuadraticEnergy]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [finiteMatrixQuadraticEnergy_add, ih]

theorem finiteMatrixQuadraticEnergy_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteMatrixQuadraticEnergy (∑ k, E k) x =
      ∑ k, finiteMatrixQuadraticEnergy (E k) x := by
  simpa using finiteMatrixQuadraticEnergy_sum_finset (Finset.univ : Finset κ) E x

theorem finiteMatrixQuadraticEnergy_componentFloor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A diagonal : Matrix ι ι ℝ)
    (errorMatrix : κ → Matrix ι ι ℝ)
    (x : ι → ℝ)
    (diagonalFloor shift floor : ℝ)
    (errorBound : κ → ℝ)
    (hDecomp : A = diagonal + ∑ k, errorMatrix k)
    (hDiagonal :
      diagonalFloor * finiteVectorEuclideanNormSq x ≤
        finiteMatrixQuadraticEnergy diagonal x)
    (hError : ∀ k,
      |finiteMatrixQuadraticEnergy (errorMatrix k) x| ≤
        errorBound k * finiteVectorEuclideanNormSq x)
    (hFloor :
      floor ≤ diagonalFloor - (∑ k, errorBound k) + shift) :
    floor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy A x +
        shift * finiteVectorEuclideanNormSq x := by
  apply coerciveFloor_of_componentBounds
    (finiteMatrixQuadraticEnergy A x + shift * finiteVectorEuclideanNormSq x)
    (finiteMatrixQuadraticEnergy diagonal x)
    (finiteVectorEuclideanNormSq x)
    diagonalFloor shift floor
    (fun k => finiteMatrixQuadraticEnergy (errorMatrix k) x)
    errorBound
  · exact finiteVectorEuclideanNormSq_nonneg x
  · rw [hDecomp, finiteMatrixQuadraticEnergy_add,
      finiteMatrixQuadraticEnergy_sum]
  · exact hDiagonal
  · exact hError
  · exact hFloor

open Finset
open scoped BigOperators
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def logarithmicCvSBuilderEvenPositiveModeMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    logarithmicCvSBuilderEntry c location base (mode i) (mode j) +
      logarithmicCvSBuilderEntry c location base (mode i) (-mode j)

noncomputable def logarithmicCvSBuilderOddPositiveModeMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    logarithmicCvSBuilderEntry c location base (mode i) (mode j) -
      logarithmicCvSBuilderEntry c location base (mode i) (-mode j)

noncomputable def logarithmicCvSArchimedeanPositiveModeDiagonalMatrix
    {κ : Type*} [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) : Matrix κ κ ℝ :=
  fun i j =>
    if i = j then
      -logarithmicCvSArchimedeanEntry c (mode i) (mode i)
    else 0

noncomputable def logarithmicCvSPoleEvenPositiveModeMatrix
    {κ : Type*} (c : ℝ) (mode : κ → ℤ) : Matrix κ κ ℝ :=
  fun i j =>
    logarithmicCvSPoleEntry c (mode i) (mode j) +
      logarithmicCvSPoleEntry c (mode i) (-mode j)

noncomputable def logarithmicCvSPoleOddPositiveModeMatrix
    {κ : Type*} (c : ℝ) (mode : κ → ℤ) : Matrix κ κ ℝ :=
  fun i j =>
    logarithmicCvSPoleEntry c (mode i) (mode j) -
      logarithmicCvSPoleEntry c (mode i) (-mode j)

noncomputable def logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
    {κ : Type*} [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) : Matrix κ κ ℝ :=
  fun i j =>
    -(if i = j then 0 else
        logarithmicCvSArchimedeanEntry c (mode i) (mode j)) -
      logarithmicCvSArchimedeanEntry c (mode i) (-mode j)

noncomputable def logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
    {κ : Type*} [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) : Matrix κ κ ℝ :=
  fun i j =>
    -(if i = j then 0 else
        logarithmicCvSArchimedeanEntry c (mode i) (mode j)) +
      logarithmicCvSArchimedeanEntry c (mode i) (-mode j)

noncomputable def finiteLogarithmicPrimeEvenPositiveModeErrorMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    -(finiteLogarithmicPrimeEntry c location base (mode i : ℝ) (mode j : ℝ) +
      finiteLogarithmicPrimeEntry c location base (mode i : ℝ) (-mode j : ℝ))

noncomputable def finiteLogarithmicPrimeOddPositiveModeErrorMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    -(finiteLogarithmicPrimeEntry c location base (mode i : ℝ) (mode j : ℝ) -
      finiteLogarithmicPrimeEntry c location base (mode i : ℝ) (-mode j : ℝ))

noncomputable def logarithmicCvSBuilderEvenPositiveModeErrorMatrix
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Fin 3 → Matrix κ κ ℝ :=
  ![logarithmicCvSPoleEvenPositiveModeMatrix c mode,
    logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c mode,
    finiteLogarithmicPrimeEvenPositiveModeErrorMatrix c location base mode]

noncomputable def logarithmicCvSBuilderOddPositiveModeErrorMatrix
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Fin 3 → Matrix κ κ ℝ :=
  ![logarithmicCvSPoleOddPositiveModeMatrix c mode,
    logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c mode,
    finiteLogarithmicPrimeOddPositiveModeErrorMatrix c location base mode]

theorem logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    logarithmicCvSBuilderEvenPositiveModeMatrix c location base mode =
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode +
        ∑ k, logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          c location base mode k := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Fin.sum_univ_three,
      logarithmicCvSBuilderEvenPositiveModeMatrix,
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
      logarithmicCvSBuilderEvenPositiveModeErrorMatrix,
      logarithmicCvSPoleEvenPositiveModeMatrix,
      logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
      finiteLogarithmicPrimeEvenPositiveModeErrorMatrix,
      logarithmicCvSBuilderEntry]
    ring
  · simp [Fin.sum_univ_three,
      logarithmicCvSBuilderEvenPositiveModeMatrix,
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
      logarithmicCvSBuilderEvenPositiveModeErrorMatrix,
      logarithmicCvSPoleEvenPositiveModeMatrix,
      logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
      finiteLogarithmicPrimeEvenPositiveModeErrorMatrix,
      logarithmicCvSBuilderEntry, hij]
    ring

theorem logarithmicCvSBuilderOddPositiveModeMatrix_decomposition
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    logarithmicCvSBuilderOddPositiveModeMatrix c location base mode =
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode +
        ∑ k, logarithmicCvSBuilderOddPositiveModeErrorMatrix
          c location base mode k := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Fin.sum_univ_three,
      logarithmicCvSBuilderOddPositiveModeMatrix,
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
      logarithmicCvSBuilderOddPositiveModeErrorMatrix,
      logarithmicCvSPoleOddPositiveModeMatrix,
      logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
      finiteLogarithmicPrimeOddPositiveModeErrorMatrix,
      logarithmicCvSBuilderEntry]
    ring
  · simp [Fin.sum_univ_three,
      logarithmicCvSBuilderOddPositiveModeMatrix,
      logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
      logarithmicCvSBuilderOddPositiveModeErrorMatrix,
      logarithmicCvSPoleOddPositiveModeMatrix,
      logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
      finiteLogarithmicPrimeOddPositiveModeErrorMatrix,
      logarithmicCvSBuilderEntry, hij]
    ring

theorem logarithmicCvSBuilderEvenMatrix_some_eq_positiveModeMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    (fun i j : Fin N =>
      logarithmicCvSBuilderEvenMatrix c location base N (some i) (some j)) =
      logarithmicCvSBuilderEvenPositiveModeMatrix
        c location base (fun i : Fin N => positiveIntegerMode i) := by
  rfl

theorem logarithmicCvSBuilderOddMatrix_eq_positiveModeMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    logarithmicCvSBuilderOddMatrix c location base N =
      logarithmicCvSBuilderOddPositiveModeMatrix
        c location base (fun i : Fin N => positiveIntegerMode i) := by
  rfl

theorem logarithmicCvSArchimedeanPositiveModeDiagonalMatrix_energy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode) x =
      ∑ i, (-logarithmicCvSArchimedeanEntry c (mode i) (mode i)) * x i ^ 2 := by
  unfold finiteMatrixQuadraticEnergy
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix
  apply Finset.sum_congr rfl
  intro i _hi
  simp
  ring

theorem logarithmicCvSArchimedeanPositiveModeDiagonalMatrix_ge
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) (diagonalFloor : ℝ)
    (hDiagonal : ∀ i : κ,
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry c (mode i) (mode i)) :
    diagonalFloor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode) x := by
  rw [logarithmicCvSArchimedeanPositiveModeDiagonalMatrix_energy]
  unfold finiteVectorEuclideanNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_mul_of_nonneg_right (hDiagonal i) (sq_nonneg (x i))

theorem logarithmicCvSBuilderEvenPositiveModeMatrix_coerciveFloor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ)
    (diagonalFloor shift floor : ℝ) (errorBound : Fin 3 → ℝ)
    (hDiagonal : ∀ i : κ,
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry c (mode i) (mode i))
    (hError : ∀ k,
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            c location base mode k) x| ≤
        errorBound k * finiteVectorEuclideanNormSq x)
    (hFloor : floor ≤ diagonalFloor - (∑ k, errorBound k) + shift) :
    floor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            c location base mode) x +
        shift * finiteVectorEuclideanNormSq x := by
  apply finiteMatrixQuadraticEnergy_componentFloor
    (logarithmicCvSBuilderEvenPositiveModeMatrix c location base mode)
    (logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode)
    (logarithmicCvSBuilderEvenPositiveModeErrorMatrix c location base mode)
    x diagonalFloor shift floor errorBound
  · exact logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition
      c location base mode
  · exact logarithmicCvSArchimedeanPositiveModeDiagonalMatrix_ge
      c mode x diagonalFloor hDiagonal
  · exact hError
  · exact hFloor

theorem logarithmicCvSBuilderOddPositiveModeMatrix_coerciveFloor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ)
    (diagonalFloor shift floor : ℝ) (errorBound : Fin 3 → ℝ)
    (hDiagonal : ∀ i : κ,
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry c (mode i) (mode i))
    (hError : ∀ k,
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            c location base mode k) x| ≤
        errorBound k * finiteVectorEuclideanNormSq x)
    (hFloor : floor ≤ diagonalFloor - (∑ k, errorBound k) + shift) :
    floor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            c location base mode) x +
        shift * finiteVectorEuclideanNormSq x := by
  apply finiteMatrixQuadraticEnergy_componentFloor
    (logarithmicCvSBuilderOddPositiveModeMatrix c location base mode)
    (logarithmicCvSArchimedeanPositiveModeDiagonalMatrix c mode)
    (logarithmicCvSBuilderOddPositiveModeErrorMatrix c location base mode)
    x diagonalFloor shift floor errorBound
  · exact logarithmicCvSBuilderOddPositiveModeMatrix_decomposition
      c location base mode
  · exact logarithmicCvSArchimedeanPositiveModeDiagonalMatrix_ge
      c mode x diagonalFloor hDiagonal
  · exact hError
  · exact hFloor

/-!
## Concrete tower-shell coercivity

The right-right block of each pulled-back parity tower is the arbitrary
positive-mode matrix above for the consecutive shell modes.  Consequently the
component coercivity adapters apply directly to `finiteMatrixTowerTailEnergy`,
without a separate shell-matrix identification hypothesis.
-/

/-- Signed positive modes carried by the consecutive shell after an old
initial segment. -/
noncomputable def finGlobalShellPositiveMode
    (old shell : ℕ) (j : Fin shell) : ℤ :=
  (old + 1 + (j : ℕ) : ℕ)

/-- The right-right block of the pulled-back odd builder is exactly the odd
positive-mode matrix on the consecutive shell. -/
theorem logarithmicCvSBuilderOddMatrix_pullback_inr_inr
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    {old shell next : ℕ} (h : next = old + shell)
    (i j : Fin shell) :
    finiteMatrixPullback (finBlockSplitEquiv h)
        (logarithmicCvSBuilderOddMatrix c location base next)
        (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderOddPositiveModeMatrix c location base
        (finGlobalShellPositiveMode old shell) i j := by
  simp [finiteMatrixPullback, finBlockSplitEquiv,
    logarithmicCvSBuilderOddMatrix,
    logarithmicCvSBuilderOddPositiveModeMatrix,
    positiveIntegerMode, finGlobalShellPositiveMode]
  congr 1 <;> ring_nf

/-- The right-right block of the pulled-back even builder is exactly the even
positive-mode matrix on the consecutive shell; the central mode remains in
the old block. -/
theorem logarithmicCvSBuilderEvenMatrix_pullback_inr_inr
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    {old shell next : ℕ} (h : next = old + shell)
    (i j : Fin shell) :
    finiteMatrixPullback (optionFinBlockSplitEquiv h)
        (logarithmicCvSBuilderEvenMatrix c location base next)
        (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderEvenPositiveModeMatrix c location base
        (finGlobalShellPositiveMode old shell) i j := by
  simp [finiteMatrixPullback, optionFinBlockSplitEquiv,
    finBlockSplitEquiv, logarithmicCvSBuilderEvenMatrix,
    logarithmicCvSBuilderEvenPositiveModeMatrix,
    positiveIntegerMode, finGlobalShellPositiveMode]
  congr 1 <;> ring_nf

/-- The actual odd tower-tail coordinate is the positive-mode quadratic
energy of its consecutive shell. -/
theorem logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) :
    finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderOddTowerMatrix c location base size)
        (logarithmicCvSBuilderOddTowerShellVector z size shell)
        (logarithmicCvSBuilderOddTowerSplit size shell hSize) n =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix c location base
          (finGlobalShellPositiveMode (size n) (shell n)))
        (finGlobalShellVector z (size n) (shell n)) := by
  unfold finiteMatrixTowerTailEnergy finiteMatrixBlockTailEnergy
    finiteMatrixQuadraticEnergy
  simp only [logarithmicCvSBuilderOddTowerMatrix,
    logarithmicCvSBuilderOddTowerShellVector,
    logarithmicCvSBuilderOddTowerSplit]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [logarithmicCvSBuilderOddMatrix_pullback_inr_inr
    c location base (hSize n) i j]

/-- The actual even tower-tail coordinate is the positive-mode quadratic
energy of its consecutive shell. -/
theorem logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) :
    finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderEvenTowerMatrix c location base size)
        (logarithmicCvSBuilderEvenTowerShellVector z size shell)
        (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix c location base
          (finGlobalShellPositiveMode (size n) (shell n)))
        (finGlobalShellVector z (size n) (shell n)) := by
  unfold finiteMatrixTowerTailEnergy finiteMatrixBlockTailEnergy
    finiteMatrixQuadraticEnergy
  simp only [logarithmicCvSBuilderEvenTowerMatrix,
    logarithmicCvSBuilderEvenTowerShellVector,
    logarithmicCvSBuilderEvenTowerSplit]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [logarithmicCvSBuilderEvenMatrix_pullback_inr_inr
    c location base (hSize n) i j]

/-- At the dyadic `4B -> 8B` transition, the generic consecutive-shell mode
map is definitionally the recorded newest-shell mode map. -/
theorem finGlobalShellPositiveMode_four_mul_eq_newestShellMode
    (B : ℕ) :
    finGlobalShellPositiveMode (4 * B) (4 * B) =
      fun j : Fin (4 * B) => (newestShellMode B j : ℤ) := by
  funext j
  rfl

/-- The positive-mode component bounds give the requested coercive floor
directly for an actual odd tower shell. -/
theorem logarithmicCvSBuilderOddTowerTailEnergy_coerciveFloor
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (diagonalFloor shift floor : ℝ)
    (errorBound : Fin 3 → ℝ)
    (hDiagonal : ∀ i : Fin (shell n),
      diagonalFloor ≤
        -logarithmicCvSArchimedeanEntry c
          (finGlobalShellPositiveMode (size n) (shell n) i)
          (finGlobalShellPositiveMode (size n) (shell n) i))
    (hError : ∀ k,
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            c location base
            (finGlobalShellPositiveMode (size n) (shell n)) k)
          (finGlobalShellVector z (size n) (shell n))| ≤
        errorBound k * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hFloor : floor ≤ diagonalFloor - (∑ k, errorBound k) + shift) :
    floor * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderOddTowerMatrix c location base size)
          (logarithmicCvSBuilderOddTowerShellVector z size shell)
          (logarithmicCvSBuilderOddTowerSplit size shell hSize) n +
        shift * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)) := by
  rw [logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    c location base z size shell hSize n]
  exact logarithmicCvSBuilderOddPositiveModeMatrix_coerciveFloor
    c location base
    (finGlobalShellPositiveMode (size n) (shell n))
    (finGlobalShellVector z (size n) (shell n))
    diagonalFloor shift floor errorBound hDiagonal hError hFloor

/-- The positive-mode component bounds give the requested coercive floor
directly for an actual even tower shell. -/
theorem logarithmicCvSBuilderEvenTowerTailEnergy_coerciveFloor
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (diagonalFloor shift floor : ℝ)
    (errorBound : Fin 3 → ℝ)
    (hDiagonal : ∀ i : Fin (shell n),
      diagonalFloor ≤
        -logarithmicCvSArchimedeanEntry c
          (finGlobalShellPositiveMode (size n) (shell n) i)
          (finGlobalShellPositiveMode (size n) (shell n) i))
    (hError : ∀ k,
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            c location base
            (finGlobalShellPositiveMode (size n) (shell n)) k)
          (finGlobalShellVector z (size n) (shell n))| ≤
        errorBound k * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hFloor : floor ≤ diagonalFloor - (∑ k, errorBound k) + shift) :
    floor * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderEvenTowerMatrix c location base size)
          (logarithmicCvSBuilderEvenTowerShellVector z size shell)
          (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n +
        shift * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)) := by
  rw [logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    c location base z size shell hSize n]
  exact logarithmicCvSBuilderEvenPositiveModeMatrix_coerciveFloor
    c location base
    (finGlobalShellPositiveMode (size n) (shell n))
    (finGlobalShellVector z (size n) (shell n))
    diagonalFloor shift floor errorBound hDiagonal hError hFloor

/-!
## Explicit pole-component bound

The rational pole parity blocks factor into one rank-one form each.  Their
quadratic energies and absolute Cauchy bounds therefore reduce exactly to
finite sums of explicit scalar weights.  The Archimedean diagonal self-entry
is also rewritten to the literal diagonal function used by the interval
certificate.
-/
noncomputable def logarithmicCvSPoleScale (c : ℝ) : ℝ :=
  32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2

noncomputable def logarithmicCvSPoleDenominator (c : ℝ) (n : ℤ) : ℝ :=
  Real.log c ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2

noncomputable def logarithmicCvSPoleEvenWeight (c : ℝ) (n : ℤ) : ℝ :=
  Real.log c / logarithmicCvSPoleDenominator c n

noncomputable def logarithmicCvSPoleOddWeight (c : ℝ) (n : ℤ) : ℝ :=
  4 * Real.pi * (n : ℝ) / logarithmicCvSPoleDenominator c n

@[simp] theorem logarithmicCvSArchimedeanEntry_self (c : ℝ) (n : ℤ) :
    logarithmicCvSArchimedeanEntry c n n =
      logarithmicArchimedeanDiagonal c |(n : ℝ)| := by
  simp [logarithmicCvSArchimedeanEntry]

theorem finGlobalShellPositiveMode_pos (old shell : ℕ) (j : Fin shell) :
    0 < finGlobalShellPositiveMode old shell j := by
  unfold finGlobalShellPositiveMode
  omega

theorem logarithmicCvSArchimedeanEntry_shell_self
    (c : ℝ) (old shell : ℕ) (j : Fin shell) :
    logarithmicCvSArchimedeanEntry c
        (finGlobalShellPositiveMode old shell j)
        (finGlobalShellPositiveMode old shell j) =
      logarithmicArchimedeanDiagonal c
        (finGlobalShellPositiveMode old shell j : ℝ) := by
  rw [logarithmicCvSArchimedeanEntry_self, abs_of_pos]
  exact_mod_cast finGlobalShellPositiveMode_pos old shell j

theorem logarithmicCvSArchimedeanShellDiagonal_ge
    (c : ℝ) (old shell : ℕ) (diagonalFloor : ℝ)
    (hDiagonal : ∀ j : Fin shell,
      diagonalFloor ≤
        -logarithmicArchimedeanDiagonal c
          (finGlobalShellPositiveMode old shell j : ℝ)) :
    ∀ j : Fin shell,
      diagonalFloor ≤
        -logarithmicCvSArchimedeanEntry c
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  intro j
  rw [logarithmicCvSArchimedeanEntry_shell_self]
  exact hDiagonal j

/-!
The cutoff-13 asymptotic envelope now feeds the literal shell diagonal.  For
an old cutoff at least `960`, the diagonal floor is `log old - 19/20`.  The
legacy adapters expose separate pointwise digamma, trigamma-series, and
shifted-derivative premises; the narrowest adapter below derives all of them
from one global DLMF-form quadratic remainder bound and one scalar endpoint
comparison at `960`.
-/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hDigammaRemainder : ∀ j : Fin shell,
      ‖Complex.digamma
            (archimedeanArgument 13
              (finGlobalShellPositiveMode old shell j : ℝ)) -
          (Complex.log
              (archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)) -
            1 / (2 *
              archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13
            (finGlobalShellPositiveMode old shell j : ℝ) ^ 2))
    (hTrigamma : ∀ j : Fin shell,
      archimedeanTrigammaSeriesFloor 13
          (finGlobalShellPositiveMode old shell j : ℝ) ≤
        (deriv Complex.digamma
          (archimedeanArgument 13
            (finGlobalShellPositiveMode old shell j : ℝ))).re)
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  apply logarithmicCvSArchimedeanShellDiagonal_ge
  intro j
  let n := finGlobalShellPositiveMode old shell j
  have hModeNat : 960 ≤ old + 1 + (j : ℕ) := by omega
  have hMode : (960 : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast hModeNat
  have hOldPos : 0 < (old : ℝ) := by
    exact_mod_cast (show 0 < old by omega)
  have hOldMode : (old : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast (show old ≤ old + 1 + (j : ℕ) by omega)
  have hLog : Real.log (old : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hOldPos hOldMode
  have hDiagonal :=
    c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth
      (n : ℝ) hMode (by simpa [n] using hDigammaRemainder j)
        (by simpa [n] using hTrigamma j) hEndpoint
  linarith

/-- The literal cutoff-13 shell route with the trigamma premise expressed as
the canonical complex `HasSum` identity on every shell mode.  The elementary
real-part estimate is discharged by
`archimedeanTrigammaSeriesFloor_le_of_hasSum`. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hDigammaRemainder : ∀ j : Fin shell,
      ‖Complex.digamma
            (archimedeanArgument 13
              (finGlobalShellPositiveMode old shell j : ℝ)) -
          (Complex.log
              (archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)) -
            1 / (2 *
              archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13
            (finGlobalShellPositiveMode old shell j : ℝ) ^ 2))
    (hTrigammaSeries : ∀ j : Fin shell,
      HasSum
        (archimedeanTrigammaSeriesTerm 13
          (finGlobalShellPositiveMode old shell j : ℝ))
        (deriv Complex.digamma
          (archimedeanArgument 13
            (finGlobalShellPositiveMode old shell j : ℝ))))
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  apply c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth
    old shell hOld hDigammaRemainder
  · intro j
    have hModeNat : 0 < old + 1 + (j : ℕ) := by omega
    have hModeInt :
        (0 : ℤ) < finGlobalShellPositiveMode old shell j := by
      dsimp [finGlobalShellPositiveMode]
      exact_mod_cast hModeNat
    have hModePos :
        0 < (finGlobalShellPositiveMode old shell j : ℝ) := by
      exact_mod_cast hModeInt
    exact archimedeanTrigammaSeriesFloor_le_of_hasSum
      13 (finGlobalShellPositiveMode old shell j : ℝ)
        (by norm_num) hModePos (hTrigammaSeries j)
  · exact hEndpoint

/-- The literal cutoff-13 shell route with the canonical trigamma series
discharged by decay of the shifted digamma derivative at every shell mode. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaTail
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hDigammaRemainder : ∀ j : Fin shell,
      ‖Complex.digamma
            (archimedeanArgument 13
              (finGlobalShellPositiveMode old shell j : ℝ)) -
          (Complex.log
              (archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)) -
            1 / (2 *
              archimedeanArgument 13
                (finGlobalShellPositiveMode old shell j : ℝ)))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13
            (finGlobalShellPositiveMode old shell j : ℝ) ^ 2))
    (hTrigammaTail : ∀ j : Fin shell,
      Tendsto (fun N : ℕ =>
        deriv Complex.digamma
          (archimedeanArgument 13
            (finGlobalShellPositiveMode old shell j : ℝ) + (N : ℂ)))
        atTop (𝓝 0))
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  exact
    c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries
      old shell hOld hDigammaRemainder
        (fun j =>
          archimedeanTrigammaSeries_hasSum_of_tendsto_deriv_digamma
            13 (finGlobalShellPositiveMode old shell j : ℝ)
              (hTrigammaTail j))
        hEndpoint

/-- Every cutoff-13 shell diagonal has the certified floor once a single
global quadratic digamma-remainder bound and the cutoff-960 endpoint hold. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2)
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  apply logarithmicCvSArchimedeanShellDiagonal_ge
  intro j
  let n := finGlobalShellPositiveMode old shell j
  have hModeNat : 960 ≤ old + 1 + (j : ℕ) := by omega
  have hMode : (960 : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast hModeNat
  have hOldPos : 0 < (old : ℝ) := by
    exact_mod_cast (show 0 < old by omega)
  have hOldMode : (old : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast (show old ≤ old + 1 + (j : ℕ) by omega)
  have hLog : Real.log (old : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hOldPos hOldMode
  have hDiagonal :=
    c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound
      (n : ℝ) hMode hRemainder hEndpoint
  linarith

/-- The literal cutoff-13 shell diagonal with its mode-960 scalar endpoint
closed by `C13ArchimedeanEndpoint`; only the global quadratic digamma remainder
remains as a premise. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound_closed_endpoint
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  exact
    c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound
      old shell hOld hRemainder
        RiemannCvs.C13ArchimedeanEndpoint.c13_archimedeanEndpoint_bound

/-- The shell-diagonal route with both the scalar endpoint and the
right-half-plane sector factor closed.  The remaining premise is exactly the
DLMF first-neglected-term estimate. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_first_neglected_term
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hFirst : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  exact
    c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound_closed_endpoint
      old shell hOld
        (RiemannCvs.DigammaQuadraticRemainder.quadratic_remainder_bound_of_first_neglected_term
          hFirst)

/-- The V23 shell-diagonal route reduced to the literal Euler--Maclaurin
tent-kernel representation and its positive-real scalar mass estimate. -/
theorem c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_eulerMaclaurin_tent
    (old shell : ℕ) (hOld : 960 ≤ old)
    (hRepresentation : ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Set.Ioi 0,
          (RiemannCvs.DigammaEulerMaclaurin.periodicTentWeight t : ℂ) *
            (w + (t : ℂ))⁻¹ ^ 3))
    (hRealMass : ∀ r : ℝ, 0 < r →
      ∫ t : ℝ in Set.Ioi 0,
          RiemannCvs.DigammaEulerMaclaurin.periodicTentWeight t *
            (1 / (r + t) ^ 3) ≤
        1 / (12 * r ^ 2)) :
    ∀ j : Fin shell,
      Real.log (old : ℝ) - 19 / 20 ≤
        -logarithmicCvSArchimedeanEntry 13
          (finGlobalShellPositiveMode old shell j)
          (finGlobalShellPositiveMode old shell j) := by
  exact
    c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound_closed_endpoint
      old shell hOld
        (RiemannCvs.DigammaEulerMaclaurin.quadratic_remainder_bound_of_eulerMaclaurin_tent
          hRepresentation hRealMass)

theorem logarithmicCvSPoleEntry_even_factorization (c : ℝ) (n m : ℤ) :
    logarithmicCvSPoleEntry c n m + logarithmicCvSPoleEntry c n (-m) =
      2 * logarithmicCvSPoleScale c *
        logarithmicCvSPoleEvenWeight c n *
          logarithmicCvSPoleEvenWeight c m := by
  simp [logarithmicCvSPoleEntry, logarithmicCvSPoleScale,
    logarithmicCvSPoleDenominator, logarithmicCvSPoleEvenWeight,
    div_eq_mul_inv]
  ring

theorem logarithmicCvSPoleEntry_odd_factorization (c : ℝ) (n m : ℤ) :
    logarithmicCvSPoleEntry c n m - logarithmicCvSPoleEntry c n (-m) =
      -(2 * logarithmicCvSPoleScale c) *
        logarithmicCvSPoleOddWeight c n *
          logarithmicCvSPoleOddWeight c m := by
  simp [logarithmicCvSPoleEntry, logarithmicCvSPoleScale,
    logarithmicCvSPoleDenominator, logarithmicCvSPoleOddWeight,
    div_eq_mul_inv]
  ring

theorem logarithmicCvSPoleEvenPositiveModeMatrix_eq_rankOne
    {κ : Type*}
    (c : ℝ) (mode : κ → ℤ) :
    logarithmicCvSPoleEvenPositiveModeMatrix c mode =
      fun i j =>
        (2 * logarithmicCvSPoleScale c) *
          logarithmicCvSPoleEvenWeight c (mode i) *
            logarithmicCvSPoleEvenWeight c (mode j) := by
  ext i j
  exact logarithmicCvSPoleEntry_even_factorization c (mode i) (mode j)

theorem logarithmicCvSPoleOddPositiveModeMatrix_eq_rankOne
    {κ : Type*}
    (c : ℝ) (mode : κ → ℤ) :
    logarithmicCvSPoleOddPositiveModeMatrix c mode =
      fun i j =>
        (-(2 * logarithmicCvSPoleScale c)) *
          logarithmicCvSPoleOddWeight c (mode i) *
            logarithmicCvSPoleOddWeight c (mode j) := by
  ext i j
  exact logarithmicCvSPoleEntry_odd_factorization c (mode i) (mode j)

theorem finiteMatrixQuadraticEnergy_rankOne
    {κ : Type*} [Fintype κ]
    (a : ℝ) (u x : κ → ℝ) :
    finiteMatrixQuadraticEnergy (fun i j => a * u i * u j) x =
      a * (∑ i, u i * x i) ^ 2 := by
  unfold finiteMatrixQuadraticEnergy
  have hInner (i : κ) :
      (∑ j, x i * (a * u i * u j) * x j) =
        (x i * a * u i) * ∑ j, u j * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [show (∑ i, ∑ j, x i * (a * u i * u j) * x j) =
      ∑ i, (x i * a * u i) * ∑ j, u j * x j by
    apply Finset.sum_congr rfl
    intro i _hi
    exact hInner i]
  rw [← Finset.sum_mul]
  have hLeft : (∑ i, x i * a * u i) = a * ∑ i, u i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hLeft, pow_two]
  ring

theorem finiteMatrixQuadraticEnergy_rankOne_abs_le
    {κ : Type*} [Fintype κ]
    (a : ℝ) (u x : κ → ℝ) :
    |finiteMatrixQuadraticEnergy (fun i j => a * u i * u j) x| ≤
      |a| * (∑ i, u i ^ 2) * finiteVectorEuclideanNormSq x := by
  rw [finiteMatrixQuadraticEnergy_rankOne]
  let S := ∑ i, u i * x i
  change |a * S ^ 2| ≤ _
  rw [abs_mul, abs_of_nonneg (sq_nonneg S)]
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset κ) u x
  have hScaled := mul_le_mul_of_nonneg_left hCauchy (abs_nonneg a)
  simpa [finiteVectorEuclideanNormSq, mul_assoc] using hScaled

theorem logarithmicCvSPoleEvenPositiveModeMatrix_energy
    {κ : Type*} [Fintype κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (logarithmicCvSPoleEvenPositiveModeMatrix c mode) x =
      2 * logarithmicCvSPoleScale c *
        (∑ i, logarithmicCvSPoleEvenWeight c (mode i) * x i) ^ 2 := by
  rw [logarithmicCvSPoleEvenPositiveModeMatrix_eq_rankOne]
  exact finiteMatrixQuadraticEnergy_rankOne
    (2 * logarithmicCvSPoleScale c)
    (fun i => logarithmicCvSPoleEvenWeight c (mode i)) x

theorem logarithmicCvSPoleOddPositiveModeMatrix_energy
    {κ : Type*} [Fintype κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (logarithmicCvSPoleOddPositiveModeMatrix c mode) x =
      -(2 * logarithmicCvSPoleScale c) *
        (∑ i, logarithmicCvSPoleOddWeight c (mode i) * x i) ^ 2 := by
  rw [logarithmicCvSPoleOddPositiveModeMatrix_eq_rankOne]
  exact finiteMatrixQuadraticEnergy_rankOne
    (-(2 * logarithmicCvSPoleScale c))
    (fun i => logarithmicCvSPoleOddWeight c (mode i)) x

theorem logarithmicCvSPoleEvenPositiveModeMatrix_abs_energy_le
    {κ : Type*} [Fintype κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSPoleEvenPositiveModeMatrix c mode) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i, logarithmicCvSPoleEvenWeight c (mode i) ^ 2) *
          finiteVectorEuclideanNormSq x := by
  rw [logarithmicCvSPoleEvenPositiveModeMatrix_eq_rankOne]
  exact finiteMatrixQuadraticEnergy_rankOne_abs_le
    (2 * logarithmicCvSPoleScale c)
    (fun i => logarithmicCvSPoleEvenWeight c (mode i)) x

theorem logarithmicCvSPoleOddPositiveModeMatrix_abs_energy_le
    {κ : Type*} [Fintype κ]
    (c : ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSPoleOddPositiveModeMatrix c mode) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i, logarithmicCvSPoleOddWeight c (mode i) ^ 2) *
          finiteVectorEuclideanNormSq x := by
  rw [logarithmicCvSPoleOddPositiveModeMatrix_eq_rankOne]
  simpa only [abs_neg] using
    finiteMatrixQuadraticEnergy_rankOne_abs_le
      (-(2 * logarithmicCvSPoleScale c))
      (fun i => logarithmicCvSPoleOddWeight c (mode i)) x

theorem logarithmicCvSBuilderEvenPositiveModePoleError_abs_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ)
    (mode : κ → ℤ) (x : κ → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          c location base mode 0) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i, logarithmicCvSPoleEvenWeight c (mode i) ^ 2) *
          finiteVectorEuclideanNormSq x := by
  simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using
    logarithmicCvSPoleEvenPositiveModeMatrix_abs_energy_le c mode x

theorem logarithmicCvSBuilderOddPositiveModePoleError_abs_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ℝ) (location base : ι → ℝ)
    (mode : κ → ℤ) (x : κ → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeErrorMatrix
          c location base mode 0) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i, logarithmicCvSPoleOddWeight c (mode i) ^ 2) *
          finiteVectorEuclideanNormSq x := by
  simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using
    logarithmicCvSPoleOddPositiveModeMatrix_abs_energy_le c mode x
/-!
### Consecutive-shell `poleTail` closure

The two rational weights satisfy pointwise reciprocal-square bounds.  Reindexing
any consecutive finite shell as `Ioc old (old + shell)` and applying Mathlib's
reciprocal-square tail estimate closes both parity pole forms by the exact
`scale / (8 * pi^2 * old)` quantity used by the cutoff-13 Arb composition.
-/
private theorem sq_second_div_sq_add_sq_le_inv_sq
    (a b : ℝ) (hb : 0 < b) :
    (b / (a ^ 2 + b ^ 2)) ^ 2 ≤ 1 / b ^ 2 := by
  have hDen : 0 < a ^ 2 + b ^ 2 := by positivity
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hDen) (sq_pos_of_pos hb)]
  nlinarith [sq_nonneg a, sq_nonneg (a ^ 2),
    mul_nonneg (sq_nonneg a) (sq_nonneg b)]

private theorem sq_first_div_sq_add_sq_le_quarter_inv_sq
    (a b : ℝ) (hb : 0 < b) :
    (a / (a ^ 2 + b ^ 2)) ^ 2 ≤ 1 / (4 * b ^ 2) := by
  have hDen : 0 < a ^ 2 + b ^ 2 := by positivity
  have hFour : 0 < 4 * b ^ 2 := by positivity
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hDen) hFour]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]



theorem logarithmicCvSPoleOddWeight_sq_le
    (c : ℝ) (n : ℤ) (hn : 0 < n) :
    logarithmicCvSPoleOddWeight c n ^ 2 ≤
      1 / (16 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < 4 * Real.pi * (n : ℝ) := by positivity
  have h := sq_second_div_sq_add_sq_le_inv_sq
    (Real.log c) (4 * Real.pi * (n : ℝ)) hb
  unfold logarithmicCvSPoleOddWeight logarithmicCvSPoleDenominator
  convert h using 1 <;> ring

theorem logarithmicCvSPoleEvenWeight_sq_le
    (c : ℝ) (n : ℤ) (hn : 0 < n) :
    logarithmicCvSPoleEvenWeight c n ^ 2 ≤
      1 / (64 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < 4 * Real.pi * (n : ℝ) := by positivity
  have h := sq_first_div_sq_add_sq_le_quarter_inv_sq
    (Real.log c) (4 * Real.pi * (n : ℝ)) hb
  unfold logarithmicCvSPoleEvenWeight logarithmicCvSPoleDenominator
  convert h using 1 <;> ring



private theorem finGlobalShell_inv_sq_sum_eq_Ioc
    (old shell : ℕ) :
    (∑ j : Fin shell,
      (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹) =
      ∑ n ∈ Finset.Ioc old (old + shell), (((n : ℝ) ^ 2)⁻¹) := by
  have hIoc : Finset.Ioc old (old + shell) =
      Finset.Ico (old + 1) (old + shell + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : old + shell + 1 - (old + 1) = shell := by omega
  rw [hLength]
  simpa [finGlobalShellPositiveMode] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ((((old + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) shell)



theorem finGlobalShell_inv_sq_sum_le
    (old shell : ℕ) (hOld : old ≠ 0) :
    (∑ j : Fin shell,
      (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹) ≤
      1 / (old : ℝ) := by
  rw [finGlobalShell_inv_sq_sum_eq_Ioc]
  have hBase := sum_Ioc_inv_sq_le_sub (α := ℝ) hOld
    (Nat.le_add_right old shell)
  calc
    (∑ n ∈ Finset.Ioc old (old + shell), (((n : ℝ) ^ 2)⁻¹)) ≤
        (old : ℝ)⁻¹ - ((old + shell : ℕ) : ℝ)⁻¹ := hBase
    _ ≤ 1 / (old : ℝ) := by
      have hTail : 0 ≤ ((old + shell : ℕ) : ℝ)⁻¹ := by positivity
      simpa only [one_div] using sub_le_self (old : ℝ)⁻¹ hTail



theorem logarithmicCvSPoleOddWeight_shell_sum_le
    (c : ℝ) (old shell : ℕ) (hOld : old ≠ 0) :
    (∑ j : Fin shell,
      logarithmicCvSPoleOddWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
      1 / (16 * Real.pi ^ 2 * (old : ℝ)) := by
  have hPointwise : ∀ j : Fin shell,
      logarithmicCvSPoleOddWeight c
          (finGlobalShellPositiveMode old shell j) ^ 2 ≤
        (16 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
    intro j
    have hMode := finGlobalShellPositiveMode_pos old shell j
    have hModeReal : 0 <
        ((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) := by
      exact_mod_cast hMode
    have h := logarithmicCvSPoleOddWeight_sq_le c
      (finGlobalShellPositiveMode old shell j) hMode
    calc
      logarithmicCvSPoleOddWeight c
          (finGlobalShellPositiveMode old shell j) ^ 2 ≤
          1 / (16 * Real.pi ^ 2 *
            ((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2) := h
      _ = (16 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
        field_simp [Real.pi_ne_zero, ne_of_gt hModeReal]
  calc
    (∑ j : Fin shell,
      logarithmicCvSPoleOddWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
        ∑ j : Fin shell, (16 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum fun j _hj => hPointwise j
    _ = (16 * Real.pi ^ 2)⁻¹ *
        ∑ j : Fin shell,
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (16 * Real.pi ^ 2)⁻¹ * (1 / (old : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (finGlobalShell_inv_sq_sum_le old shell hOld) (by positivity)
    _ = 1 / (16 * Real.pi ^ 2 * (old : ℝ)) := by
      have hOldReal : (old : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hOld
      field_simp [Real.pi_ne_zero, hOldReal]



theorem logarithmicCvSPoleEvenWeight_shell_sum_le_strong
    (c : ℝ) (old shell : ℕ) (hOld : old ≠ 0) :
    (∑ j : Fin shell,
      logarithmicCvSPoleEvenWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
      1 / (64 * Real.pi ^ 2 * (old : ℝ)) := by
  have hPointwise : ∀ j : Fin shell,
      logarithmicCvSPoleEvenWeight c
          (finGlobalShellPositiveMode old shell j) ^ 2 ≤
        (64 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
    intro j
    have hMode := finGlobalShellPositiveMode_pos old shell j
    have hModeReal : 0 <
        ((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) := by
      exact_mod_cast hMode
    have h := logarithmicCvSPoleEvenWeight_sq_le c
      (finGlobalShellPositiveMode old shell j) hMode
    calc
      logarithmicCvSPoleEvenWeight c
          (finGlobalShellPositiveMode old shell j) ^ 2 ≤
          1 / (64 * Real.pi ^ 2 *
            ((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2) := h
      _ = (64 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
        field_simp [Real.pi_ne_zero, ne_of_gt hModeReal]
  calc
    (∑ j : Fin shell,
      logarithmicCvSPoleEvenWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
        ∑ j : Fin shell, (64 * Real.pi ^ 2)⁻¹ *
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum fun j _hj => hPointwise j
    _ = (64 * Real.pi ^ 2)⁻¹ *
        ∑ j : Fin shell,
          (((finGlobalShellPositiveMode old shell j : ℤ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (64 * Real.pi ^ 2)⁻¹ * (1 / (old : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (finGlobalShell_inv_sq_sum_le old shell hOld) (by positivity)
    _ = 1 / (64 * Real.pi ^ 2 * (old : ℝ)) := by
      have hOldReal : (old : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hOld
      field_simp [Real.pi_ne_zero, hOldReal]

theorem logarithmicCvSPoleEvenWeight_shell_sum_le
    (c : ℝ) (old shell : ℕ) (hOld : old ≠ 0) :
    (∑ j : Fin shell,
      logarithmicCvSPoleEvenWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
      1 / (16 * Real.pi ^ 2 * (old : ℝ)) := by
  calc
    (∑ j : Fin shell,
      logarithmicCvSPoleEvenWeight c
        (finGlobalShellPositiveMode old shell j) ^ 2) ≤
        1 / (64 * Real.pi ^ 2 * (old : ℝ)) :=
      logarithmicCvSPoleEvenWeight_shell_sum_le_strong c old shell hOld
    _ ≤ 1 / (16 * Real.pi ^ 2 * (old : ℝ)) := by
      have hOldReal : 0 < (old : ℝ) := by positivity
      have h16 : 0 < 16 * Real.pi ^ 2 * (old : ℝ) := by positivity
      have h64 : 0 < 64 * Real.pi ^ 2 * (old : ℝ) := by positivity
      rw [div_le_div_iff₀ h64 h16]
      nlinarith [sq_pos_of_pos Real.pi_pos]



theorem logarithmicCvSPoleScale_nonneg
    (c : ℝ) (hc : 1 ≤ c) :
    0 ≤ logarithmicCvSPoleScale c := by
  have hLog : 0 ≤ Real.log c := Real.log_nonneg hc
  unfold logarithmicCvSPoleScale
  positivity

theorem logarithmicCvSBuilderOddShellPoleError_abs_le
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      |logarithmicCvSPoleScale c| /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  have hRaw := logarithmicCvSBuilderOddPositiveModePoleError_abs_le
    c location base (finGlobalShellPositiveMode old shell) x
  have hWeights := logarithmicCvSPoleOddWeight_shell_sum_le
    c old shell hOld
  calc
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i : Fin shell,
          logarithmicCvSPoleOddWeight c
            (finGlobalShellPositiveMode old shell i) ^ 2) *
          finiteVectorEuclideanNormSq x := hRaw
    _ ≤ |2 * logarithmicCvSPoleScale c| *
        (1 / (16 * Real.pi ^ 2 * (old : ℝ))) *
          finiteVectorEuclideanNormSq x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWeights (abs_nonneg _))
        (finiteVectorEuclideanNormSq_nonneg x)
    _ = |logarithmicCvSPoleScale c| /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
      have hOldReal : (old : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hOld
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      field_simp [Real.pi_ne_zero, hOldReal]
      ring

theorem logarithmicCvSBuilderEvenShellPoleError_abs_le
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      |logarithmicCvSPoleScale c| /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  have hRaw := logarithmicCvSBuilderEvenPositiveModePoleError_abs_le
    c location base (finGlobalShellPositiveMode old shell) x
  have hWeights := logarithmicCvSPoleEvenWeight_shell_sum_le
    c old shell hOld
  calc
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      |2 * logarithmicCvSPoleScale c| *
        (∑ i : Fin shell,
          logarithmicCvSPoleEvenWeight c
            (finGlobalShellPositiveMode old shell i) ^ 2) *
          finiteVectorEuclideanNormSq x := hRaw
    _ ≤ |2 * logarithmicCvSPoleScale c| *
        (1 / (16 * Real.pi ^ 2 * (old : ℝ))) *
          finiteVectorEuclideanNormSq x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWeights (abs_nonneg _))
        (finiteVectorEuclideanNormSq_nonneg x)
    _ = |logarithmicCvSPoleScale c| /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
      have hOldReal : (old : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hOld
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      field_simp [Real.pi_ne_zero, hOldReal]
      ring



theorem logarithmicCvSBuilderOddShellPoleError_le_poleTail
    {ι : Type*} [Fintype ι]
    (c : ℝ) (hc : 1 ≤ c) (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      logarithmicCvSPoleScale c /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  simpa [abs_of_nonneg (logarithmicCvSPoleScale_nonneg c hc)] using
    logarithmicCvSBuilderOddShellPoleError_abs_le
      c location base old shell hOld x

theorem logarithmicCvSBuilderEvenShellPoleError_le_poleTail
    {ι : Type*} [Fintype ι]
    (c : ℝ) (hc : 1 ≤ c) (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          c location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      logarithmicCvSPoleScale c /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  simpa [abs_of_nonneg (logarithmicCvSPoleScale_nonneg c hc)] using
    logarithmicCvSBuilderEvenShellPoleError_abs_le
      c location base old shell hOld x



theorem c13_logarithmicCvSBuilderOddShellPoleError_le_poleTail
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeErrorMatrix
          13 location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  exact logarithmicCvSBuilderOddShellPoleError_le_poleTail
    13 (by norm_num) location base old shell hOld x

theorem c13_logarithmicCvSBuilderEvenShellPoleError_le_poleTail
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
          13 location base (finGlobalShellPositiveMode old shell) 0) x| ≤
      logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) *
        finiteVectorEuclideanNormSq x := by
  exact logarithmicCvSBuilderEvenShellPoleError_le_poleTail
    13 (by norm_num) location base old shell hOld x
/-!
### Pole-closed cutoff-13 coercivity consumers

These four adapters fill error component zero with the proved cutoff-13
`poleTail` theorem.  Both a standalone consecutive shell and the actual
odd/even matrix-tower tail now require only the Archimedean diagonal,
Archimedean-remainder form, prime form, and final scalar floor comparison.
-/
theorem c13_logarithmicCvSBuilderEvenShell_coerciveFloor
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ)
    (diagonalFloor shift floor archRemainderBound primeBound : ℝ)
    (hDiagonal : ∀ i : Fin shell,
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry 13
        (finGlobalShellPositiveMode old shell i)
        (finGlobalShellPositiveMode old shell i))
    (hArchRemainder :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
            13 (finGlobalShellPositiveMode old shell)) x| ≤
        archRemainderBound * finiteVectorEuclideanNormSq x)
    (hPrime :
      |finiteMatrixQuadraticEnergy
          (finiteLogarithmicPrimeEvenPositiveModeErrorMatrix
            13 location base (finGlobalShellPositiveMode old shell)) x| ≤
        primeBound * finiteVectorEuclideanNormSq x)
    (hFloor : floor ≤ diagonalFloor -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) +
        archRemainderBound + primeBound) + shift) :
    floor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            13 location base (finGlobalShellPositiveMode old shell)) x +
        shift * finiteVectorEuclideanNormSq x := by
  apply logarithmicCvSBuilderEvenPositiveModeMatrix_coerciveFloor
    13 location base (finGlobalShellPositiveMode old shell) x
    diagonalFloor shift floor
    ![logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (old : ℝ)),
      archRemainderBound, primeBound]
  · exact hDiagonal
  · intro k
    fin_cases k
    · simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using
        c13_logarithmicCvSBuilderEvenShellPoleError_le_poleTail
          location base old shell hOld x
    · simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using
        hArchRemainder
    · simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using hPrime
  · simpa [Fin.sum_univ_three] using hFloor

theorem c13_logarithmicCvSBuilderOddShell_coerciveFloor
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (old shell : ℕ) (hOld : old ≠ 0) (x : Fin shell → ℝ)
    (diagonalFloor shift floor archRemainderBound primeBound : ℝ)
    (hDiagonal : ∀ i : Fin shell,
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry 13
        (finGlobalShellPositiveMode old shell i)
        (finGlobalShellPositiveMode old shell i))
    (hArchRemainder :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
            13 (finGlobalShellPositiveMode old shell)) x| ≤
        archRemainderBound * finiteVectorEuclideanNormSq x)
    (hPrime :
      |finiteMatrixQuadraticEnergy
          (finiteLogarithmicPrimeOddPositiveModeErrorMatrix
            13 location base (finGlobalShellPositiveMode old shell)) x| ≤
        primeBound * finiteVectorEuclideanNormSq x)
    (hFloor : floor ≤ diagonalFloor -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) +
        archRemainderBound + primeBound) + shift) :
    floor * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            13 location base (finGlobalShellPositiveMode old shell)) x +
        shift * finiteVectorEuclideanNormSq x := by
  apply logarithmicCvSBuilderOddPositiveModeMatrix_coerciveFloor
    13 location base (finGlobalShellPositiveMode old shell) x
    diagonalFloor shift floor
    ![logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (old : ℝ)),
      archRemainderBound, primeBound]
  · exact hDiagonal
  · intro k
    fin_cases k
    · simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using
        c13_logarithmicCvSBuilderOddShellPoleError_le_poleTail
          location base old shell hOld x
    · simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using
        hArchRemainder
    · simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using hPrime
  · simpa [Fin.sum_univ_three] using hFloor

theorem c13_logarithmicCvSBuilderEvenTowerTailEnergy_coerciveFloor
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : size n ≠ 0)
    (diagonalFloor shift floor archRemainderBound primeBound : ℝ)
    (hDiagonal : ∀ i : Fin (shell n),
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry 13
        (finGlobalShellPositiveMode (size n) (shell n) i)
        (finGlobalShellPositiveMode (size n) (shell n) i))
    (hArchRemainder :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
            13 (finGlobalShellPositiveMode (size n) (shell n)))
          (finGlobalShellVector z (size n) (shell n))| ≤
        archRemainderBound * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hPrime :
      |finiteMatrixQuadraticEnergy
          (finiteLogarithmicPrimeEvenPositiveModeErrorMatrix
            13 location base
            (finGlobalShellPositiveMode (size n) (shell n)))
          (finGlobalShellVector z (size n) (shell n))| ≤
        primeBound * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hFloor : floor ≤ diagonalFloor -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (size n : ℝ)) +
        archRemainderBound + primeBound) + shift) :
    floor * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderEvenTowerMatrix 13 location base size)
          (logarithmicCvSBuilderEvenTowerShellVector z size shell)
          (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n +
        shift * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)) := by
  rw [logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    13 location base z size shell hSize n]
  exact c13_logarithmicCvSBuilderEvenShell_coerciveFloor
    location base (size n) (shell n) hOld
    (finGlobalShellVector z (size n) (shell n))
    diagonalFloor shift floor archRemainderBound primeBound
    hDiagonal hArchRemainder hPrime hFloor

theorem c13_logarithmicCvSBuilderOddTowerTailEnergy_coerciveFloor
    {ι : Type*} [Fintype ι]
    (location base : ι → ℝ)
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : size n ≠ 0)
    (diagonalFloor shift floor archRemainderBound primeBound : ℝ)
    (hDiagonal : ∀ i : Fin (shell n),
      diagonalFloor ≤ -logarithmicCvSArchimedeanEntry 13
        (finGlobalShellPositiveMode (size n) (shell n) i)
        (finGlobalShellPositiveMode (size n) (shell n) i))
    (hArchRemainder :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
            13 (finGlobalShellPositiveMode (size n) (shell n)))
          (finGlobalShellVector z (size n) (shell n))| ≤
        archRemainderBound * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hPrime :
      |finiteMatrixQuadraticEnergy
          (finiteLogarithmicPrimeOddPositiveModeErrorMatrix
            13 location base
            (finGlobalShellPositiveMode (size n) (shell n)))
          (finGlobalShellVector z (size n) (shell n))| ≤
        primeBound * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)))
    (hFloor : floor ≤ diagonalFloor -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (size n : ℝ)) +
        archRemainderBound + primeBound) + shift) :
    floor * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderOddTowerMatrix 13 location base size)
          (logarithmicCvSBuilderOddTowerShellVector z size shell)
          (logarithmicCvSBuilderOddTowerSplit size shell hSize) n +
        shift * finiteVectorEuclideanNormSq
          (finGlobalShellVector z (size n) (shell n)) := by
  rw [logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    13 location base z size shell hSize n]
  exact c13_logarithmicCvSBuilderOddShell_coerciveFloor
    location base (size n) (shell n) hOld
    (finGlobalShellVector z (size n) (shell n))
    diagonalFloor shift floor archRemainderBound primeBound
    hDiagonal hArchRemainder hPrime hFloor
end RiemannCvs.V23BoundaryWeylMainline
