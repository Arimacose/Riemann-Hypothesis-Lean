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

The same module now also solves this inequality for the high-gap side.  Given
an upper certificate `etaNormSq >= ‖eta‖²`, it is enough to verify

```text
epsilon² * (etaNormSq + margin*a)
  <= margin * a² * gamma.
```

This is the form consumed by the current constant audit: all quantities are
nonnegative products, and `gamma` appears only once on the right.

A domain-uniform theorem composes this inequality directly with the finite
`2 * margin` Abel certificate.  This is stronger than the previous generic
`|G_N-G_limit| <= margin` slot: the remaining source work now has named and
separately measurable inputs `a`, `gamma`, and `epsilon`.

`CvSParityDisplacement.lean` now closes the concrete Riesz adapter for the
remaining factor `‖eta‖²`.  The coefficient function

```text
eta = (1, sqrt(2), ..., sqrt(2))
```

is lifted to `EuclideanSpace Real (Option ι)`, and Lean proves

```text
<eta,x> = boundaryFunctional(x),
‖eta‖² = 2 * card(ι) + 1.
```

For the current `N = 20` finite block this specializes exactly to
`‖eta‖² = 41`.  Thus the compact Schur budget has only the three analytic
constants `a`, `gamma`, and `epsilon` left to instantiate.

An exact-dyadic Arb replay on the window

```text
[-2,-1/1024]
```

gives the finite prefix margin

```text
G_20(x) >= 0.03510510619558287875916412165205673...
```

and therefore the rigorous half-margin target

```text
margin = 0.0175525530977914393795820608.
```

The existing elementary log-tail audit at `c = 13` gives

```text
D_L = 8.133016113590798598418726830596668...
B_L = 20.728969460745556111615320051159706...
```

At the actual retained cutoff `M = 20`, the conservative shifted high floor is

```text
log(21)-D_L-B_L+1/1024
  = -25.8164865741129317...,
```

so it does not supply high-block coercivity for a direct `G_20`-to-limit
Schur comparison.

It is also inconsistent to keep `etaNormSq = 41` while sending the retained
cutoff `M` to a huge value: the concrete boundary norm changes with that same
cutoff according to

```text
etaNormSq(M) = 2M+1.
```

The repository now proves a structural no-go theorem for this synchronized
regime.  Put

```text
scale = margin * a²
      = 1.6739419076720657e-8,
epsilon² = B_L²
         = 429.6901749045219... .
```

Since the logarithmic high floor is bounded above by `M+1/1024`, while the
left side of the Schur budget contains `B_L²(2M+1)`, the two certified
coefficient margins are

```text
2*B_L²-scale
  = 859.3803497923044... > 0,
B_L²-scale/1024
  = 429.6901749045055... > 0.
```

Therefore no synchronized retained cutoff can satisfy the current Weyl Schur
budget with the dimension-independent choice `epsilon = B_L`; logarithmic
high-gap growth loses to the linear growth of the boundary-vector mass.  This
is stronger than merely observing an impractically large cutoff.

The next analytic target is selected by this obstruction: obtain either a
cutoff-decaying low/high coupling or a weighted boundary estimate that removes
the `2M+1` loss.  The sharper prolate/PSWF tail expected at order `lambda^-7`
is one existing source route, but it still needs a concrete adapter to the
actual CvS/Weil boundary resolvent.  The workflow records this audit in
`v23_c13_log_tail_schur_budget.json` so future constants can be compared
against the same Lean acceptance inequality.

`BoundaryWeylSchurTail.lean` now contains that weighted-boundary target as an
actual source-level API rather than a prose escape hatch.  For each compact
spectral domain, the adapter may choose an `errorSpace x` containing the
coupling-generated error `u(x)-u0(x)` and prove only

```text
||u0(x)|| <= sourceWeight,
|<eta,w>| <= observationWeight ||w||  for w in errorSpace(x).
```

The resulting checked estimate is

```text
|<eta,u(x)>-<eta,u0(x)>|
  <= observationWeight * sourceWeight * epsilon²
     / (lowGap*highGap-epsilon²),
```

with the division-free acceptance budget

```text
observationWeight * sourceWeight * epsilon²
  <= margin * (lowGap*highGap-epsilon²).
```

Thus the new numerator need not contain the global Euclidean mass
`||eta_M||²=2M+1`.  The theorem
`weightedSchurBudget_of_upperBounds` also accepts separate interval-certified
upper bounds for `observationWeight*sourceWeight` and `epsilon²`, while the
uniform positivity wrapper feeds the estimate directly into the already
formalized compact finite-margin transfer.  The remaining analytic obligation
is now precise: identify the actual CvS Schur-error range and derive a
cutoff-uniform restricted boundary norm (or enough cutoff decay in its product
with the finite-source norm).  The pure prolate `O(lambda^-7)` estimate becomes
relevant only after proving that range identification.

There is now a stronger route that removes the boundary functional from the
tail budget altogether.  Write the shifted low/high form as

```text
L(w,w) + 2 B(w,z) + H(z,z)
```

and suppose its dimensionless coupling satisfies

```text
B(w,z)² <= q * L(w,w) * H(z,z),    0 <= q < 1.
```

For the finite low solution `u0`, full low component `u`, high component `v`,
and `d=u-u0`, the weak equations give

```text
L(d,d) + B(d,v) = 0,
H(v,v) + B(u,v) = 0.
```

The relative bound applied to `(d,v)` yields

```text
L(d,d) <= q * H(v,v) < H(v,v).
```

Low-form symmetry and the finite source equation then identify the boundary
response difference exactly:

```text
<eta,u>-<eta,u0>
  = -B(u0,v)
  = H(v,v)-L(d,d)
  >= 0.
```

Lean now proves both this monotonicity and the quantitative companion

```text
(1-q) * |<eta,u>-<eta,u0>| <= q * <eta,u0>.
```

Consequently, finite boundary-Weyl positivity transfers directly to the full
block response under a relative-energy certificate with `q<1`; neither
`||eta_M||²`, `sourceWeight`, nor an additive finite-to-tail margin appears in
the positivity conclusion.  The theorem
`relativeCoupling_of_formGrowth` propagates a certificate when both diagonal
forms grow, matching the fact that moving left from `x=-delta` adds a positive
shift to both CvS blocks.

The new script `certify_relative_energy_coupling.py` gives the first rigorous
finite instance.  At

```text
c = 13,
retained cutoff = 20,
full cutoff = 120,
x = -1/1024,
q = 999/1000,
precision = 2000 bits,
```

it assembles the exact Arb enclosure of

```text
[[q L, B], [B^T, H]]
```

and certifies every unpivoted interval-LDL pivot strictly positive:

```text
even: 121 / 121 positive pivots,
      transcript 15adbfc971c8828991b06f87a5e3803d2eae829ad191460c2de73febf96a7e45,
odd:  120 / 120 positive pivots,
      transcript 4b8fb0e5fb931844e2a7282fb51f77c1f783044b2f1288db2c81fd1c77e5fe94.
```

Positive diagonal growth extends this finite certificate to every
`x <= -1/1024`.  It is still a nested finite-cutoff theorem: the next analytic
target is to prove the same relative form inequality for the closed complement
beyond every retained cutoff, or to give an all-cutoff tail majorant whose
limit stays strictly below one.  The finite result is materially stronger than
the earlier raw `B_L` probe because it succeeds at `N=120` with a rigorous
dimensionless constant while the Euclidean budget was structurally excluded.

The finite certificate is now organized as a genuinely recursive shell chain.
Let

```text
R_q(K) = [[q L, B_K], [B_K^T, H_K]]
```

be the scaled relative-energy form through cutoff `K`.  When a new shell is
attached, write

```text
R_q(K') = [[R_q(K), C], [C^T, H_shell]].
```

`BoundaryWeylSchurTail.lean` now proves the exact gluing rule used by the
certificate.  Positivity of

```text
[[rho * R_q(K), C], [C^T, H_shell]],    rho <= 1,
```

gives by the quadratic discriminant

```text
C(s,t)^2 <= rho * R_q(K)(s,s) * H_shell(t,t),
```

so the new shell preserves nonnegativity of the scaled form.  Applying the
converse discriminant in the original low variable recovers the *same* `q`
between the retained `N=20` block and the enlarged high block.  The checked
Lean chain is

```text
twoBlockEnergy_nonnegative
  -> relativeCoupling_of_scaledFormNonnegative
  -> relativeCoupling_of_recursiveShell.
```

The tracked script `certify_recursive_relative_energy_shells.py` rigorously
certifies two successive shells at 900 bits:

```text
base:       N = 20 -> 120, q = 999/1000,
shell 1:    N = 120 -> 240, rho = 1/3,
shell 2:    N = 240 -> 480, rho = 1/5.
```

Every interval-LDL pivot is strictly positive.  The local tracked replay gives

```text
even base:       121 / 121,
  transcript 70fb7678981df48b29dc58d1e936715bf8564f6c823a960fd90cff7db35b4beb,
even 120 -> 240: 241 / 241,
  transcript d50a98b49b7b0cd209592b6e9c8d4eba5e6d7411cc29ccefe47ee89b95b8d2e4,
even 240 -> 480: 481 / 481,
  transcript afb671e55b48425ea672f695737ce7dc3bdf4ecfb7a9ef4c50e512e951d2e080,

odd base:        120 / 120,
  transcript e3461b61ab25a3e9b7b42950254d58610cc42ebd4f1e9d5b595a0fe8bdf6b8f1,
odd 120 -> 240:  240 / 240,
  transcript 622a213c72f30ef187a51256e0c3db318b5c0db3fae66173ed53b5e17c2ead34,
odd 240 -> 480:  480 / 480,
  transcript c29e397377a86cc6d1017b4bb8d405e44795354d60e0e7c6bc8fd8edcd8df359.
```

The JSON artifact SHA-256 is
`A1A63FB1217E3A89F582B2D81A62E7B0212BED4F94C23BA001B4EC77C11B80AF`.
Positive diagonal growth again propagates all stages from the endpoint
`x=-1/1024` to every more negative parameter.  This does not yet quantify
every later shell, but it moves the rigorous finite frontier from `N=120` to
`N=480` and replaces the undifferentiated all-cutoff request by a precise
uniform target: prove one coefficient `rho_*<1` for every later dyadic shell,
then pass the finite-support inequality to the closed form domain.

The next certificate deliberately spends a smaller coefficient before trying
to estimate all future shells.  At 900 bits it proves

```text
reference coefficient q_0 = 249/250,
base:       N = 20 -> 480,
shell:      N = 480 -> 960, rho = 1/7,
x = -1/1024.
```

Every interval-LDL pivot is again strictly positive:

```text
even base:       481 / 481,
  transcript 2f7622c5c069b9e3ca5a1c17d1fe663eb7c1c59c94b7d83a30862d9315cc2813,
even 480 -> 960: 961 / 961,
  transcript d8ccfdb2e1fc8d9e4761c1b3838ebfc811f4842981f7c54c90c332c74fe3ab34,

odd base:        480 / 480,
  transcript 9c7ff1683830d053dc70e0fa1376a07f85094908920fbe0316777052fe32d63e,
odd 480 -> 960:  960 / 960,
  transcript b6e13bf080ecd0d49eca975cb7929dba9a1c0681d44b8b6398ce5778619712ef.
```

The JSON artifact SHA-256 is
`7DDC919A3644F04C3B33E09AA29139856493D40F9A685DDC91300324E5EF4050`.
This moves the strict finite `q_0` frontier to
`N=960`.  More importantly, evaluating the enlarged core with the final
coefficient `q=999/1000` leaves the exact gap

```text
q - q_0 = 3/1000,
(q - q_0) / (2q) = 1/666.
```

`relativeCouplingSlack_balancedReserve` proves this reserve without a square
root, and `relativeCouplingSlack_v23BalancedLowerBound` kernel-checks its exact
V23 specialization:

```text
(q-q_0) * (q*L + H) <= 2*q*R_q,
(1/666) * (q*L + H) <= R_q
  when q_0 = 249/250 and q = 999/1000.
```

The theorem `relativeShell_of_referenceReserve` then converts a shell estimate
against the simpler reference energy into the core-relative hypothesis used by
the recursive gluing theorem.  It supplies the following explicit sufficient
condition whenever the reference coupling has become small enough:

```text
C_K(s,t)^2 <= kappa_K * (q*L + H_K)(s,s) * H_shell(t,t),
kappa_K <= rho/666
```

with `rho<1`.  This is a useful eventual-tail interface, but the `1/666`
worst-case reserve should not be assumed to pay for the very next shell.

The tracked midpoint-only diagnostic `probe_relative_shell_budget.py` tests
that distinction before launching another expensive interval-LDL run.  For
`N=960 -> 1920` at 160-bit Arb construction precision it reports

```powershell
python research/riemann-cvs-numerics/probe_relative_shell_budget.py `
  --c 13 --low-cutoff 20 --core-cutoff 960 --shell-cutoff 1920 `
  --prec 160 --shift-gain 1/1024 --reference-q 999/1000 `
  --direct-q 999/1000 --direct-q 249/250 `
  --reserve 1/666 --candidate-rho 1/12 --json-out <artifact.json>
```

The resulting midpoint ratios are

```text
                              even                 odd
reference kappa, q=999/1000   0.04326543019694135   0.05485286505445342
kappa / (1/666)              28.81477651116294      36.53200812626598
direct rho, q=999/1000        0.043129289872473      0.06607458242245198
direct rho, q_0=249/250       0.04317011018121593   0.07807620268908923
```

The JSON explicitly records `MIDPOINT_DIAGNOSTIC_ONLY` and
`rigorous_certificate = false`; its SHA-256 is
`A2F775129E3B9C7811B309AC335D3B95DEF4355EC418575EB2B6BCC59C55A6BD`.
Thus the immediate `1/666` reference route is quantitatively the wrong bound
for this shell, while the direct `q_0` shell ratio remains below the rational
candidate `rho=1/12`.  The next rigorous finite target is therefore

```text
N = 960 -> 1920, q_0 = 249/250, rho = 1/12,
```

followed by either a uniform direct core-relative estimate below one or an
eventual cutoff beyond which the reference coefficient finally fits inside
the `1/666` reserve.  This separates a verified algebraic reserve from the
additional quantitative decay needed to use it.

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
2. convert the midpoint candidate for `N=960 -> 1920` into a rigorous
   `q_0=249/250`, `rho=1/12` interval certificate, then prove either one
   uniform direct core-relative coefficient below one on every remaining
   dyadic shell or an eventual reference-energy estimate
   `kappa_K <= rho/666`; pass the resulting `q=999/1000` finite-support
   inequality to the closed high complement uniformly on compact domains with
   right endpoint `< 0`.  The exact `1/666` reserve is already formalized, but
   the midpoint diagnostic shows that it is not the immediate `960 -> 1920`
   bound.  The older `a/gamma/epsilon` and restricted `errorSpace` budgets
   remain fallback interfaces, and the relative form inequality is the
   preferred route;
3. prove a cutoff-uniform upper bound for the absolute first spectral moment
   consumed by the new far-left theorem;
4. keep the V22 central-mode functional distinct from the Sylvester boundary
   functional until a source-level identification is proved;
5. construct the limiting self-adjoint branches and supply the concrete
   compactness/resolvent convergence consumed by the new transfer interface;
6. close the source-specific PSWF-to-Bessel exterior remainder used by the
   stationary-phase route.

The cumulative certificate closes the finite `(13,20)` numerical hypothesis,
and the recursive relative-energy certificates extend the checked Schur
comparison through `20 -> 120 -> 240 -> 480 -> 960` throughout
`x <= -1/1024`; the last stage uses `q_0=249/250` and leaves the exact `1/666`
reference-energy reserve for `q=999/1000`.  The exact
finite displacement, characteristic-product, residue-normalization,
determinant-ratio, quantitative Abel, energy-normalized monotonicity, and
recursive shell and reference-reserve adapters are now formalized.  The
midpoint-only `960 -> 1920` probe selects `rho=1/12` for the next direct
certificate and rules out immediate use of the conservative `1/666` reserve.
That next interval certificate, the uniform later-shell bound,
closed-form passage, uniform moment bound, and limiting resolvent construction
remain the dominant proof boundary.

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
