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
candidate `rho=1/12`.

That candidate is now discharged by the tracked rigorous certifier
`certify_preconditioned_relative_shell.py`:

```powershell
python research/riemann-cvs-numerics/certify_preconditioned_relative_shell.py `
  --c 13 --low-cutoff 20 --core-cutoff 960 --shell-cutoff 1920 `
  --prec 256 --shift-gain 1/1024 --q-upper 249/250 --rho-upper 1/12 `
  --core-certificate <N960-certificate.json> `
  --json-out <N1920-certificate.json>
```

The script first validates and hashes the earlier positive-core artifact.  It
then uses Arb's verified preconditioned solve to enclose

```text
X = ((1/12) * R_(249/250)(960))^-1 C
```

and the exact Schur complement `S = H_shell - C^T X`.  A floating Cholesky
factor selects a basis only; every selected float is embedded as an exact
dyadic number with zero Arb radius.  The resulting fixed upper-triangular
matrix `P` has a strictly positive diagonal, so it is invertible.  Arb then
encloses the exact congruence `P^T S P`, and every Gershgorin lower margin is
proved strictly positive.  Thus `S`, and hence the full recursive-shell
matrix, is positive definite without a Python-level LDL on the 1920-dimensional
matrix.

At 256 bits the strict result is

```text
even: Schur dimension 960, strict Gershgorin rows 960 / 960,
  transcript dc1b6b9545fbe484c2751b9a8760494bca0f00044120f6f1251e765587720a3a,
  maximum margin radius 1.4422482957167404e-66,
  preconditioner 985150B4B2831153AE83AF308F6233D09129A9C00B18F10B9C2D09DFE4BDA452,

odd:  Schur dimension 960, strict Gershgorin rows 960 / 960,
  transcript 6dd72042444dca9f628634f00ace414be83f971c1d29830456f014366c5632c6,
  maximum margin radius 2.1709399961456847e-64,
  preconditioner A6CA29BFE2D8236BA0E8AF779C51B98925B8F9ED1596A83383DC457948AF8494.
```

Every one of the `961 * 960` even and `960 * 960` odd verified-solve residual
entries contains zero.  The JSON artifact SHA-256 is
`427529EC13BD33695546C948E0AC29CC88594EB9E6948C8C6F69A61AFFFD2C45`.
This first established the strict finite `q_0=249/250` frontier at `N=1920`,
and positive diagonal growth propagates the result from `x=-1/1024` to every
more negative parameter.  The direct-parity interval certificate below now
advances that frontier once more, to `N=3840`.

### Post-`N=1920` dyadic scaling and the closed-form adapter

The tracked diagnostic `probe_dyadic_shell_scaling.py` removes a scalability
bottleneck from the exploratory step.  Instead of constructing the full
`(2*N+1)`-dimensional Arb matrix and only then compressing parity, it evaluates
the exact reflection formulas at Arb midpoints:

```text
A_even[k,l] = A[k,l] + A[k,-l],
A_odd [k,l] = A[k,l] - A[k,-l].
```

Only the two parity blocks are retained.  A mandatory small-cutoff replay
compares every optimized entry with the canonical full Arb construction.  At
`N=120`, 160-bit closed-form precision, the maximum absolute midpoint errors
are

```text
even  7.549516567451064e-14,
odd   7.549516567451064e-14,
```

against a validation tolerance of approximately `5.98e-10`.  Replaying the
known `960 -> 1920` shell recovers the previous direct and reference ratios to
about `1e-15`, providing an independent check on the direct-parity formulas.
All dense factorization and singular-value calculations still discard Arb
radii, so every output is explicitly marked `MIDPOINT_DIAGNOSTIC_ONLY` and
`rigorous_certificate = false`.

The measured dyadic sequence is

```text
core K   reference even   reference odd   direct q0 even   direct q0 odd
120      0.1382792604     0.2356840325    0.1762065127     0.2802822985
240      0.1495856749     0.1415268586    0.1481195772     0.1707009640
480      0.05654910850    0.07360485824   0.05518331660    0.1181968752
960      0.04326543020    0.05485286505   0.04317011018    0.07807620269
1920     0.03560377115    0.03841029645   0.03546731664    0.04974799255
3840     0.02008164012    0.02422753707   0.01981884246    0.03207483716
```

Thus every measured direct `q0=249/250` coefficient from `K=960` onward lies
below the already certified rational candidate `rho=1/12`.  That coefficient
is an excellent finite bridge, but it is not the best repeatable steady
coefficient.  Write a balanced shell coefficient as `rho=u^2`.  The glued
energy retains a `(1-u)` fraction of its block-diagonal reference, so the
budget available for the next shell is

```text
u^2 * (1-u) <= 4/27,
```

with equality at `u=2/3`.  The optimal rational steady choice is therefore

```text
rhoStar = 4/9,  retained reserve = 1/3,
combined next-shell budget = 4/27.
```

`balancedShellBudget_le_fourTwentySevenths` proves the scalar optimization in
Lean.  `fourNinthsShell_oneThirdReserve` proves that a `4/9` relative shell
retains the `1/3` reserve, and
`fourNinthsShell_of_twoChannelReference` packages the repeatable step.  Its
two channel hypotheses each use only `2/27`; the generic two-channel theorem
combines them to the `4/27` reference budget, converts this to the direct
`4/9` coefficient, and renews the same `1/3` reserve.

The rigorously certified `960 -> 1920` coefficient `1/12` retains `2/3` of its
reference, hence in particular supplies the weaker `1/3` reserve needed to
enter this optimized steady recursion.  The two post-frontier probes were
replayed with the new target as follows:

```powershell
python research/riemann-cvs-numerics/probe_dyadic_shell_scaling.py `
  --c 13 --low-cutoff 20 --previous-cutoff 960 `
  --core-cutoff 1920 --shell-cutoff 3840 `
  --prec 160 --shift-gain 1/1024 --reference-q 999/1000 `
  --dyadic-reference-q 249/250 --dyadic-reserve 1/3 `
  --direct-q 249/250 --reserve 1/666 --candidate-rho 4/9 `
  --validate-cutoff 120 --json-out <N1920-to-N3840.json>

python research/riemann-cvs-numerics/probe_dyadic_shell_scaling.py `
  --c 13 --low-cutoff 20 --previous-cutoff 1920 `
  --core-cutoff 3840 --shell-cutoff 7680 `
  --prec 160 --shift-gain 1/1024 --reference-q 999/1000 `
  --dyadic-reference-q 249/250 --dyadic-reserve 1/3 `
  --direct-q 249/250 --reserve 1/666 --candidate-rho 4/9 `
  --validate-cutoff 120 --json-out <N3840-to-N7680.json>
```

Their local JSON SHA-256 values are respectively
`9031C77C7FCE637AE0669A69F9D28A8B20B0C1A133CB7B78269C998679AF1495`
and
`F1A695E4029376669C1C81D978F6853FE708252EFD2148C528A8EB0C2CD4ED2A`.
The tracked probe script SHA-256 for both artifacts is
`A62DDEAA0A9404B13BB0D03340C3F910FE993781A60F1D0D7FB4D926CB4B8E01`.

The component-wise midpoint measurements are:

```text
new shell       sector  previous-core channel  middle-shell channel  combined
1920 -> 3840    even    0.00634837851          0.03440346842         0.03543241333
1920 -> 3840    odd     0.02854236720          0.03453827359         0.04767400009
3840 -> 7680    even    0.00473830225          0.01726922679         0.02015208633
3840 -> 7680    odd     0.01733024036          0.01743311006         0.03067107119
per-channel sufficient upper bound                           2/27 = 0.07407407407
combined available budget                                   4/27 = 0.14814814815
```

Every measured channel has substantial slack, including the first odd sector.
These outputs remain midpoint diagnostics rather than interval certificates;
their role is to select a rational theorem target with room for analytic
majorants.

### Direct-parity interval certificate through `N=3840`

The tracked certifier `certify_direct_parity_relative_shell.py` now turns the
first post-`N=1920` probe into a rigorous interval certificate without
allocating the full `7681` by `7681` signed-mode matrix.  It constructs only
the exact Arb core, coupling, and shell blocks in one parity sector at a time.
Before forming any matrix entry it preserves the cancellation of the complete
prime-power sum in the one-dimensional sequences

```text
P_n = sum_(q<=13) Lambda(q)/sqrt(q) * sin(2*pi*n*log(q)/log(13)),
D_n = sum_(q<=13) 2*Lambda(q)/sqrt(q)*(1-log(q)/log(13))
      * cos(2*pi*n*log(q)/log(13)).
```

The exact parity formulas then use `P_n` off the diagonal and `D_n` on the
diagonal.  This avoids both the full reflection duplication and a
component-wise triangle inequality over the prime powers.  A canonical replay
at cutoff `120` compares direct-minus-canonical Arb balls entry by entry.  All
`14641` even and `14400` odd difference intervals contain exact zero at both
256 and 384 bits.

The production command is

```powershell
python research/riemann-cvs-numerics/certify_direct_parity_relative_shell.py `
  --c 13 --low-cutoff 20 --core-cutoff 1920 --shell-cutoff 3840 `
  --prec 256 --shift-gain 1/1024 --q-upper 249/250 `
  --rho-upper 4/9 --threads 16 `
  --core-certificate <N1920-certificate.json> `
  --validate-cutoff 120 --json-out <N3840-certificate.json>
```

The input validator checks the `N=1920` JSON, its source-script hash, both
sibling exact-dyadic preconditioners, all verified residual counts, and both
strict Gershgorin transcripts.  The new 256-bit run then proves

```text
sector  core dimension  shell dimension  residuals containing zero  strict rows
even    1921            1920             3688320 / 3688320          1920 / 1920
odd     1920            1920             3686400 / 3686400          1920 / 1920
```

The minimum preconditioned Gershgorin margin midpoints are respectively
`0.9999999999999988` and `0.9999999999999990`; their maximum radii are
`5.755702846280617e-67` and `9.362788957387741e-66`.  A separate 384-bit replay
uses the same byte-for-byte preconditioners and reduces those maximum radii to
`2.162832078123934e-105` and `3.438515796253990e-104`.  The common
preconditioner SHA-256 values are

```text
even  92D229EEF58648E410FCCDB7858F1B44D8268F6F74A6A475853C960596A6ACBD
odd   4407803835A7563DAC93008DA5A3555273E2D4249BA3930B5BC1B72BBDFFC461
```

The local 256-bit and 384-bit JSON SHA-256 values are respectively
`399087C684EFEDACFD3488D0F6A6A60F0C4E270EE42AC373F5AD8162959EB26F`
and
`163FE89519364EA1521E954E854EF070CE2D76BDDB72C9D8DF649EA525E1191A`;
the tracked script SHA-256 is
`257040825FF61DE8E985F8446B8640CB34456F35368C0EC8C63CCD18A6C56C8D`.

Consequently the strict finite `q0=249/250` frontier is now `N=3840` for
`x<=-1/1024`.  The coefficient `rhoStar=4/9` also enters exactly through the
Lean theorem `fourNinthsShell_oneThirdReserve`, so this finite step renews the
`1/3` reference reserve.  It does not supply an all-cutoff estimate.  The next
uniform two-channel obligation can, however, start at dyadic `K=1920` rather
than `K=960`; the already certified direct step covers the `K=960` instance.

### Prime-translation power certificate

The tracked script `certify_prime_translation_power_bound.py` improves the
prime-operator constant used in those analytic majorants.  For

```text
T_13 = sum_(q<13) Lambda(q)/sqrt(q) * (U_log(q) + U_log(q)^*),
```

it enumerates every length-six multiplicative path.  A path is active exactly
when the maximum of its exact rational partial products is less than thirteen
times the minimum.  Thus all interval endpoints are sorted as rational
numbers, while only the positive logarithmic weights require Arb enclosures.
The canonical 256-bit replay checks

```text
admissible paths at depths 0..6: 1, 16, 148, 1168, 8612, 60716, 415642
balanced start/end events:       415642 / 415642
open rational intervals:         2471
largest row-sum interval starts:  log(441/440)
largest sixth-power row sum:      1321.765395642150687267590536885896...
target (10/3)^6:                  1371.742112482853223593964334705075...
```

The largest row-sum enclosure has radius below `1.74e-71`.  The symmetric
Schur test for the positive kernel of `T_13^6`, followed by self-adjoint
spectral calculus, therefore gives the strict operator consequence

```text
||T_13|| < 10/3.
```

A separate 384-bit replay found the same path counts, same maximizing rational
interval, and same first 50 midpoint digits, with radius below `5.09e-110`.
The tracked script SHA-256 is
`7ADA5E51136814E35EE8811F286971BBD9EBC519941FC8E335420C81DDE49307`;
the 256-bit and 384-bit JSON SHA-256 values are respectively
`CF6ED73D830E703F8644239C75B8315ED119ADDF4D74ECDC0C5BF30CE0393FC6`
and
`E22E5E44A833B841977259A0CE28E953519592CB6B30E1EBCDF13E98F824F003`.
This replaces the earlier triangle bound near `9.94` by a strict bound below
`3.334`.  The finite path certificate is rigorous; using it in the full CvS
tail still requires the stated translation representation and Schur/spectral
adapter, which remain explicit source-level inputs rather than hidden numeric
assumptions.

### Archimedean all-mode tail envelope

The tracked `certify_archimedean_tail_envelope.py` removes two more coarse
constants from the post-`N=1920` analysis.  For

```text
y = pi*n/log(13),  z = 1/4 + i*y,
S_n = Im(psi(z))/2 - 2*y*g_s(n),
```

the source proof truncates the digamma expansion before its Bernoulli sum.
[DLMF 5.11.2 and its complex remainder bound](https://dlmf.nist.gov/5.11)
give an error at most `sqrt(2)/(6*y^2)` in this sector.  The absolutely
convergent trigamma series gives

```text
Re(psi'(1/4+i*y)) >= -(1/y + 1/y^2).
```

Finally, if `e_k=exp(-(2k+1/2)L)`, the exact geometric sums
`C=sum e_k` and `B=sum (2k+1/2)e_k` imply

```text
g_cc <= 2*C,
g_x1 <= B/(2*y)^2,
|g_x2| <= C/(2*y)^2,
2*y*g_s <= C/(2*y).
```

All error majorants decrease after `n=960`, while `atan(4*y)` increases.  The
256-bit Arb audit at the endpoint proves the uniform constants

```text
for every integer n >= 960:
  0 <= S_n <= 4/5,
  |S_n - pi/4| <= 1/(4*n),
  -(W_R)_nn >= log(n) - 19/20.

proved diagonal constant: -0.9473913542475865348897965532052193...
target constant:          -0.95
strict slack:               0.0026086457524134651102034467947807...

proved S lower:             0.7851731290996126271701508678397670...
proved S upper:             0.7856108654974296661809649367091011...
upper slack below 4/5:      0.0143891345025703338190350632908989...

n0 * upper centered error:  0.2041940159821023026919272536563560...
n0 * lower centered error:  0.2160329274601019150386356674652970...
centered target:             0.25
```

The centered estimate is substantially stronger than the coarse amplitude
bound.  On the upper side it uses
`S_n-pi/4 <= 1/(4*y)+sqrt(2)/(12*y^2)`.  On the lower side,
`pi/2-atan(4*y)=atan(1/(4*y)) <= 1/(4*y)` gives

```text
pi/4-S_n <= 1/(8*y) + sqrt(2)/(12*y^2) + C/(2*y).
```

After multiplication by `n`, both right sides are maximal at `n=960`; the
displayed Arb enclosures are strictly below `1/4`.  Therefore the conclusion
holds for every larger integer mode, rather than just at the replay endpoint.
The canonical source endpoint has centered error
`1.2332188514957847568e-5`, compared with the certified endpoint allowance
`1/3840 = 0.00026041666...`.

For the positive-positive Loewner block, constants disappear from the
commutator:

```text
[M_S,H] = [M_(S-pi/4),H].
```

On positive modes beginning at `N`, the centered multiplier norm is at most
`1/(4*N)` and the compressed normalized discrete Hilbert transform has norm
at most one.  Hence the same-sign centered part satisfies

```text
||same-sign centered Loewner block|| <= 1/(2*N).
```

Lean theorem
`commutator_norm_le_two_mul_of_norm_bounds` proves the general contraction
commutator bound, while `commutator_norm_le_one_div_two_mul` checks the exact
`1/(4*N) -> 1/(2*N)` specialization.

The reflection term must be retained.  The canonical source uses
`S_signed(-n)=-S_n`, so for positive `k,l` the centered parity decomposition is

```text
reflected leading term:   +/- 1/(2*(k+l)),
same-sign remainder:      norm <= 1/(2*N),
reflected remainder:      entry <= 1/(4*pi*k*l).
```

Thus the old global `8/5` estimate is not replaced by `1/(2*N)` for the whole
parity block.  Instead, it is replaced by one explicit scale-invariant Hankel
kernel plus a genuinely decaying remainder.  Decreasing-sum integral bounds
and the rectangular Schur test give

```text
leading norm on [N,2N]:
  < log(3/2)/2
  = 0.2027325540540821909890065577321746...

leading norm from [N,2N] to [2N,4N]:
  < sqrt(log(5/3)*log(4/3))/2
  = 0.1916737945745804846575712563836145...
```

The reflected centered remainder is rank-one dominated.  Combining it with
the same-sign commutator gives, for `N>=960`,

```text
centered parity remainder norm
  <= 1/(2*N) + 1/(4*pi*(N-1)).
```

At the uniform-induction start `N=1920`, the remainder is below
`0.0003018848644498598234589761412296...`; consequently the total internal
and adjacent-cross Archimedean bounds are respectively
`0.2030344389185320508124655338734042...` and
`0.1919756794390303444810302325248441...`.  This corrected decomposition is
the quantity to combine with the prime block.  The remaining concrete adapter
is the identification of the CvS parity compression with the same-sign
commutator and reflected Hankel pieces.

The script also reconstructs the canonical source formula at `n=960`; it
finds `S_960 = 0.7853858312089333...` and
`-(W_R)_(960,960)-log(960) = -0.9419387381934217...`, both strictly inside
the analytic envelope.  A 384-bit replay reproduces the displayed midpoint
digits while reducing the diagonal-constant radius from below `7.04e-76` to
below `2.09e-114`.

The tracked script SHA-256 is
`7E407A0BA4745B1FB70821E91465D260539211F69F71FB7FB3E89911E3F428EB`;
the 256-bit and 384-bit JSON SHA-256 values are respectively
`3511F196BB074E95AF6A5E589F31D1FD4151C64A1C9947A15076404765102E85`
and
`462545FA0FC71C840718B54BB761F8197025AB97AB6B1CB1DFC254A2564EDEC1`.
This all-mode envelope is a source-level analytic lemma with interval-audited
constants.  Its centered variation replaces the coarse Archimedean amplitude
by the explicit dyadic Hankel constants near `0.2031/0.1920` plus a decaying
remainder; the remaining use is to combine this structured term with a
cancellation-sensitive prime translation estimate in the two relative `2/27`
channels.  The
new Lean theorem `relativeCoupling_of_coerciveNormBounds` is the exact adapter:
ordinary low/high coercive floors, a rectangular operator-norm bound, and the
scalar budget `epsilon^2 <= q*lowGap*highGap` imply the required relative
energy inequality without another informal division step.

### Eventual global bound for the middle/new dyadic channel

The tracked `certify_eventual_dyadic_middle_channel.py` composes the strict
prime power certificate with the corrected Archimedean parity envelope.  Its
scope is one of the two recursive channels: the adjacent crossblock from the
middle shell `[N,2N]` to the new shell `[2N,4N]`.

The remaining pole term is handled directly from the exact rank-two
factorization.  With

```text
L = log(13),
polePrefactor = 32*L*sinh(L/4)^2,
a_n^2+b_n^2 = 1/(L^2+16*pi^2*n^2),
```

the signed tail and the integral comparison for `sum 1/n^2` give

```text
Pole(N) <= polePrefactor/(8*pi^2*(N-1)).
```

Orthogonal compression to a parity block, an internal shell, or a rectangular
crossblock preserves this upper bound.  The two certified Archimedean bounds
and the prime norm then give

```text
A_internal(N)
  = log(3/2)/2 + 1/(2*N) + 1/(4*pi*(N-1)),

A_cross(N)
  = sqrt(log(5/3)*log(4/3))/2
    + 1/(2*N) + 1/(4*pi*(N-1)),

gap(N)
  = log(N) - 19/20 - 10/3 - A_internal(N) - Pole(N) + 1/1024,

epsilon(N)
  = 10/3 + A_cross(N) + Pole(N),

rho(N)
  = epsilon(N)^2/(gap(N)*gap(2*N)).
```

Here the positive `1/1024` is the worst-case gain on `x<=-1/1024`.  The
rectangular coercive-norm adapter turns `rho(N)<2/27` into exactly the required
middle-channel relative-energy inequality.  Since `epsilon(N)` decreases and
both gaps increase, one successful threshold check covers every larger integer
mode, not only later powers of two.

The 256-bit Arb replay finds the first successful dyadic point based at
`N=1920` to be

```text
N:                     31,457,280 = 1920*2^14
gap(N):                12.7790516339938208758751165531000...
gap(2N):               13.4721988315436789108012415049796...
epsilon(N):             3.52500716188773898155132726632185...
rho(N):                 0.072174352883450058836996111895104...
2/27-rho(N):            0.0018997211906240152370779621789703...
```

The immediately preceding dyadic point `N=15,728,640` has
`rho(N)=0.080452998599332754813300470594574...`, strictly above `2/27` by
`0.006378924525258680739226396520500...`.  Thus this is the first dyadic
threshold for the stated coarse global bounds.  An independent 384-bit replay
reproduces the first 60 midpoint digits; the threshold-radius drops from below
`1.89e-77` to below `5.54e-116`.

The already certified `1920 -> 3840` matrix transition is the `K=960`
two-channel instance.  The first open adjacent-shell channel is therefore
`K=1920`, and the eventual bound reduces the remaining middle-channel tail to
the following fourteen finite start modes:

```text
1920, 3840, 7680, 15360, 30720, 61440, 122880, 245760,
491520, 983040, 1966080, 3932160, 7864320, 15728640.
```

The tracked script SHA-256 is
`34ADF5285523722DC3B46E02A7D0AB0C87ECC0D6BE69802D53A7D54865FB52E4`.
It verifies that both input JSON files have `PASS` status, match the current
prime/Archimedean script hashes, and were generated from the same current Git
commit before composing them.  This result is deliberately channel-specific:
the previous-core channel, the fourteen finite middle-channel bridges, and the
concrete Hilbert/parity compression adapters remain separate obligations.

The same measurements make the route choice sharper.  At `K=3840`, the
reference coefficients remain about `13.37` and `16.14` times the exact
`1/666` reserve.  The elementary log-tail constants are also too conservative
at this scale: equations (8) and (10) of `EXPLICIT_LOG_TAIL_THEOREM.md` give

```text
D_L + B_L = 28.8619855743363547...
```

for `c=13`, so their raw high-floor lower bound turns positive only beyond a
cutoff of order `3.42e12`.  The centered estimate bypasses that coarse
Archimedean loss.  The global prime norm, however, discards the cancellation
visible in each previous/middle crossblock and remains too large at the current
finite frontier; it closes the middle channel only at the eventual threshold
above and does not control the previous-core reference geometry.  The preferred
next theorem is therefore the remaining recursive dyadic-reference estimate

```text
|C_previous(s,t)|^2
  <= (2/27) * R_q0(K)(s,s) * H_[2K,4K](t,t),
|C_middle(s,t)|^2
  <= (2/27) * H_[K,2K](s,s) * H_[2K,4K](t,t)
for the previous channel at every dyadic K >= 1920 and for the middle channel
at the fourteen finite bridge modes below 31,457,280.
```

Combined with `fourNinthsShell_of_twoChannelReference`, these estimates produce
the uniform direct `rhoStar=4/9` step and renew the `1/3` reserve.  This avoids
extrapolating the coarse bounded-perturbation constant and avoids waiting for
the independent reference coefficient to cross `1/666`.

### Variable reserve products instead of repeated worst-case loss

The fixed `rhoStar=4/9` theorem remains a convenient sufficient package, but
iterating only its `1/3` reserve would introduce an artificial exponential
loss.  The scalar shell algebra now retains the actual scale-dependent
coefficient.  If the `n`-th gluing step satisfies

```text
cross_n^2 <= u_n^2 * E_n * T_n,       0 <= u_n <= 1,
E_(n+1) = E_n + 2*cross_n + T_n,
```

then the new theorem `sqShell_oneSubReserve` gives the one-step estimate

```text
(1-u_n) * (E_n+T_n) <= E_(n+1).
```

Consequently `recursiveShellEnergy_ge_reserveProduct` proves, for every finite
shell count `n`,

```text
[product_(i<n) (1-u_i)] * E_0 <= E_n.
```

The stronger theorem
`recursiveShellEnergy_ge_reserveProduct_mul_blockSum` now keeps every diagonal
shell energy in the reference:

```text
[product_(i<n) (1-u_i)] * [E_0 + sum_(i<n) T_i] <= E_n.
```

The induction does not pay an extra reserve at every historical block.  The
old block sum uses the preceding inequality, while the new tail uses only
`0 <= product_(i<n)(1-u_i) <= 1`.  Therefore
`recursiveShellEnergy_ge_reserveFloor_mul_blockSum` turns a uniform product
floor into

```text
reserveFloor * [E_0 + sum_(i<n) T_i] <= E_n.
```

Finally, `relativeShell_of_recursiveBlockSumReserve` composes this exact
normalization with `relativeShell_of_referenceReserve`: a next-shell source
estimate against the full block-diagonal reference, with
`budget <= rho * reserveFloor`, is immediately a coefficient-`rho` estimate
against the actual recursively glued core.  Thus no additional scalar
energy-normalization lemma is left between the dyadic channel sum and the
recursive core; the remaining inputs are the source-specific identification
of the channel energies and a positive analytic product floor.

The product floor itself is also reduced to a source-level summability target.
The theorem `reserveProduct_ge_one_sub_partialSum` proves the finite inequality

```text
1 - sum_(i<n) u_i <= product_(i<n) (1-u_i).
```

Hence `reserveProduct_ge_one_sub_of_partialSumBound` turns any uniform estimate

```text
sum_(i<n) u_i <= total
```

into the explicit floor `1-total`, and
`reserveProduct_pos_of_partialSum_lt_one` proves that floor is strictly positive
when `total<1`.  The analytic obligation is therefore the concrete uniform
partial-sum bound for the source-derived `u_i`, rather than another abstract
infinite-product argument.

Finally, `recursiveShellEnergy_ge_of_reserveProductLowerBound` consumes any
uniform scalar floor

```text
reserveFloor <= product_(i<n) (1-u_i)
```

immediately yields `reserveFloor * E_0 <= E_n` at every finite stage.  Thus the
theorems `recursiveShellEnergy_limit_ge_of_reserveProductLowerBound` and
`recursiveShellEnergy_limit_pos_of_reserveProductLowerBound` pass that lower
bound to a convergent closed-form energy and make it strictly positive whenever
`reserveFloor>0` and `E_0>0`.  The next separated-band estimate may therefore
use the measured scale-dependent previous-core coefficients instead of
replacing each one by `4/9`.  The remaining concrete analytic target is now a
summable upper envelope whose total is strictly below one; the three product
lemmas derive the positive floor internally.

### Multiscale Cauchy summation for the previous-core channel

Treating all modes below `K` as one previous-core block hides the geometric
separation between old dyadic shells and the new shell `[2K,4K]`.  The new Lean
theorem `relativeCoupling_of_finsetChannelBudgets` exposes that structure.  For
a finite shell family, suppose

```text
C_previous = sum_i C_i,
C_i^2 <= q_i * E_i * T,
q_i >= 0, E_i >= 0, T >= 0.
```

Weighted Cauchy--Schwarz now gives the sharp aggregate form

```text
C_previous^2 <= [sum_i q_i] * [sum_i E_i] * T.
```

Thus the number of earlier shells causes no extra factor.  The companion
theorem `dyadicChannelBudget_sum_le_two` proves

```text
q_i <= q_0 * 2^(-i)  for i<n
    ==> sum_(i<n) q_i <= 2*q_0,
```

and `relativeCoupling_of_dyadicChannelBudgets` packages both steps.  To fit the
existing previous-channel allocation `2/27`, it is therefore sufficient to
prove a shell-distance envelope with leading squared coefficient at most
`1/27`.  The selected odd-exception split below uses the stricter leading value
`1/30`.  The scalar comparison between the complete block-diagonal shell sum
and the recursive core is now formalized by the reserve-product block-sum
theorem.  The source layer must still identify its separated energies with
those scalar blocks and establish the `2^(-i)` coefficient envelope for the
structured total crossblock (or an explicit allocation among the prime,
Archimedean, and pole pieces).  The finite summation, budget conversion, and
recursive-core scalar normalization are kernel-checked.

The tracked `probe_previous_core_dyadic_channels.py` exercises this interface
at the already certified `1920 -> 3840` transition, which is the generic
two-channel instance with `K=960`.  It splits the previous core through `960`
into

```text
[0,20], [21,120], [121,240], [241,480], [481,960]
```

and measures each coupling to the new shell `[1921,3840]` against its own
block-diagonal energy and the new-shell energy.  Ordered from the most recent
historical shell (distance zero) back to the fixed base, the midpoint squared
coefficients are

```text
even: 0.002790073, 0.001504689, 0.000895220, 0.001176739, 0.001227540
odd:  0.003046025, 0.001732819, 0.000986091, 0.003482023, 0.002456279
sum:  0.007594261 (even), 0.011703238 (odd).
```

Both sums are far below the selected regular aggregate budget
`2*(1/30)=1/15`, with midpoint slacks about `0.05907` and `0.05496`.  The
stricter `q_i <= (1/30)*2^(-i)` envelope holds for every listed channel except
the odd fixed base `[1,20]`: at distance four it exceeds the regular candidate
by about `0.000372945`.  The route decision is therefore explicit:
keep that fixed base as a separately certified finite channel and use the
geometric envelope on the dyadic tail.  This entire table remains float64
linear algebra after Arb midpoint assembly; it selects the next interval and
analytic estimates and does not upgrade them to a proof.

The same tracked probe now runs a second consecutive scale in CI.  It extends
the historical cutoffs by `1920`, uses middle cutoff `3840` and new cutoff
`7680`, and compares every repeated band with the first diagnostic.  With the
selected `1/30` leading budget it records

```text
newest coefficient: 0.00220868125 (even), 0.00236664910 (odd) < 1/30;
ten repeated ratios: 0.415949472 .. 0.457977514 < 1/2;
odd fixed base:       0.00111164734 < 1/384.
```

The optional `--require-half-transport` flag makes those three midpoint facts
a workflow regression gate while the JSON retains
`MIDPOINT_DIAGNOSTIC_ONLY` and `rigorous_certificate=false`.

The source route is now diagnosed one level deeper.  With
`--source-component-diagnostic`, the probe rebuilds every historical/new-shell
crossblock as the sum of its prime, Archimedean, and rank-two pole matrices,
then whitens every piece against the same full shifted historical and new-shell
energies used for the total coefficient.  All ten first-scale and all twelve
second-scale crossblocks reconstruct within `6.51e-19` and `4.34e-19`,
respectively.  Across the ten repeated bands the individual squared-norm ratios
are

```text
prime:         0.389818987 .. 0.450288442 < 1/2;
pole:          0.112974742 .. 0.450298994 < 1/2;
Archimedean:   0.448724879 .. 0.566870868, with the newest bands above 1/2.
```

Thus a proof that allocates all three source components independently is too
coarse.  The full three-piece triangle coefficient divided by the preceding
total coefficient is about `0.64 .. 0.88` on the regular channels.  The kernel
formula itself provides the sharper grouping: the prime and Archimedean
difference quotients share one combined Loewner symbol, while the pole is a
separate rank-two block.  Keeping that Archimedean/prime Loewner block intact
gives all ten transport ratios in

```text
0.415949472 .. 0.457950001 < 1/2.
```

After adding the pole by the two-piece amplitude triangle, the nine regular
channels give coefficients relative to the preceding total in

```text
0.415949472 .. 0.459420916 < 1/2.
```

The same two-piece bound also proves the diagnostic newest-channel target with
substantial room:

```text
first scale:  0.002790073 (even), 0.003048788 (odd) < 1/30;
second scale: 0.002208681 (even), 0.002367718 (odd) < 1/30.
```

The only failure is the already separated odd `[1,20]` exception; its two-piece
triangle deliberately discards the strong cancellation captured by the direct
interval certificate.  The workflow flag
`--require-regular-loewner-pole-half-transport` now gates exactly the selected
route: nine regular two-piece inequalities pass, one declared fixed exception
is excluded, and the total crossblock regression still passes independently.

Four Lean theorems now encode the exact discrete consequence selected by this
diagnostic.  `channelBudgetEnvelope_of_newest_and_transport` handles a general
nonnegative decay factor;
`dyadicChannelBudgetEnvelope_of_newest_and_halfTransport` specializes to
`1/2`; `dyadicChannelBudgetEnvelope_on_range_of_newest_and_halfTransport`
produces the finite-range hypothesis consumed by the Cauchy adapter; and
`fixedExceptionBudget_of_halfTransport` preserves the odd fixed budget.  Thus
the full triangular envelope follows once the concrete CvS source layer proves

```text
q_(scale,0) <= 1/30,
q_(scale+1,distance+1) <= q_(scale,distance)/2.
```

Two further Lean theorems encode the newly selected source combination.
`relativeCoupling_of_twoSourceAmplitudeBounds` proves, against common
nonnegative energies `E` and `T`,

```text
C_L^2 <= a^2*E*T,
C_P^2 <= b^2*E*T
  ==> (C_L+C_P)^2 <= (a+b)^2*E*T.
```

Here `C_L` is the combined Archimedean/prime Loewner form and `C_P` is the pole
form.  `halfTransportRelativeCoupling_of_twoSourceAmplitudeBounds` immediately
specializes this when

```text
(a+b)^2 <= previousCoefficient/2,
```

producing the exact total half-transport hypothesis consumed by the triangular
induction.  This removes the fixed factor-two loss of the older generic
two-channel square inequality while preserving the source cancellation that the
component diagnostic shows is essential.

The combined Loewner source now has an exact off-diagonal Lean entry formula as
well.  For an odd symbol `F`, write

```text
K_F(p,q) = (F(q)-F(p))/(p-q),
```

away from the diagonal.  Theorems
`oddDifferenceKernel_evenParity_offDiagonal` and
`oddDifferenceKernel_oddParity_offDiagonal` prove, whenever `p != q` and
`p != -q`,

```text
K_F(p,q) + K_F(p,-q)
  = 2*(q*F(q)-p*F(p))/(p^2-q^2),

K_F(p,q) - K_F(p,-q)
  = 2*(p*F(q)-q*F(p))/(p^2-q^2).
```

The previous-core/new-shell blocks are disjoint, so these are precisely their
even and odd crossblock entries and the arbitrary diagonal branch disappears.
For the selected source grouping, `F` is the combined Archimedean/prime odd
symbol.  Consequently the next uniform estimate is no longer an unspecified
matrix-norm bound: it is a weighted divided-difference estimate for the two
displayed numerators, followed by the separate elementary pole amplitude and
the already formalized two-source triangle.

That selected split now has an exact Lean interface rather than an informal
recombination step.  The theorem
`relativeCoupling_of_exception_and_finsetChannelBudgets` inserts one separately
certified channel into the same weighted Cauchy family, so it does not incur the
factor-two loss from `(a+b)^2 <= 2*a^2+2*b^2`.  Its dyadic specialization
`relativeCoupling_of_finiteException_and_dyadicChannelBudgets` closes the final
coefficient `rho` whenever

```text
q_exception + 2*q_leading <= rho.
```

Thus the odd `[1,20]` block may consume its separately certified finite budget,
while the remaining analytic proof targets the unchanged
`q_i <= q_leading*2^(-i)` envelope.  What remains at source level is the
structured newest-band estimate, joint Archimedean/prime Loewner amplitude
transport, the separate rank-two pole amplitude, and the concrete shell-energy
identification; the Lean source-amplitude combination, triangular induction,
summation, normalization, and recombination are complete.

The tracked `certify_odd_fixed_base_channel.py` now closes that finite exception
at the first certified transition.  It evaluates the direct odd-parity Arb
formula for base modes `[1,20]`, their crossblock to `[1921,3840]`, and the
shifted new-shell block.  At 256-bit precision it proves

```text
C_[1,20](s,t)^2
  < (1/384) * [(249/250) H_[1,20](s,s)] * H_[1921,3840](t,t).
```

The certificate independently proves the `20 x 20` scaled base positive,
checks all `38,400/38,400` Arb verified-solve residual entries contain zero,
and proves all `1,920/1,920` rows of the exact-dyadic preconditioned Schur
complement have strictly positive Gershgorin margins.  A canonical cutoff-12
replay additionally requires every direct-minus-canonical interval entry to
contain exact zero.  Floating Cholesky selects the two bases only; both stored
NumPy bases are embedded as exact dyadic Arb matrices before positivity is
checked.

The selected conditional regular leading coefficient is now `1/30`, not the
saturated generic value `1/27`.  The exact allocation is

```text
1/384 + 2*(1/30) = 133/1920,
2/27 - 133/1920 = 83/17280 > 0.
```

Lean records the equality in `v23OddFixedBaseBudget_allocation` and packages the
result as `relativeCoupling_of_v23OddFixedBaseAndDyadicBudgets`.

The tracked `certify_regular_previous_core_channels.py` now closes every
remaining source crossblock at the same `1920 -> 3840` transition.  From newest
to oldest, it certifies the regular bands `[481,960]`, `[241,480]`,
`[121,240]`, and `[21,120]` in both parity sectors, plus the even fixed base
`[0,20]`.  The assigned coefficients are respectively

```text
1/30, 1/60, 1/120, 1/240, 1/480,
```

with the last coefficient used only by the even fixed base.  That base energy
also retains the reference factor `249/250`; the odd fixed base remains the
separate `1/384` exception above.

The certifier proves each common shifted `1920 x 1920` new-shell block positive,
solves against all source crossblocks at once per parity, checks all
`1,845,120/1,845,120` even and `1,804,800/1,804,800` odd residual intervals
contain zero, then proves nine smaller reverse Schur complements positive by
exact-dyadic congruences.  The resulting finite budget arithmetic is

```text
even regular sum = 31/480,
2/27 - 31/480 = 41/4320 > 0;

odd regular sum = 1/16,
odd regular sum + 1/384 = 25/384,
2/27 - 25/384 = 31/3456 > 0.
```

Lean records these equalities in `v23EvenFiniteRegularBudget_allocation` and
`v23OddFiniteRegularBudget_allocation`.  Thus the complete first-transition
source decomposition now has interval proof evidence.  The next source-level
obligations are to prove `q_i <= (1/30)*2^(-i)` uniformly at every later scale
through the newest-band and half-transport estimates, and to identify the sum
of concrete separated shell energies with the block sum consumed by the
recursive-core theorem.  The scalar comparison with the recursive core is now
formalized; the finite certificate alone does not supply those source
identifications.

The finite-support-to-closed-value order passage is now explicit in Lean.
`recursiveShellEnergy_nonnegative_nat` propagates nonnegativity through every
finite shell chain.  `recursiveShellEnergy_limit_nonnegative` passes this
order to any real limit of the finite-support form values, and
`recursiveShellEnergy_limit_nonnegative_of_uniformRho` specializes the result
to one uniform coefficient `rhoStar <= 1`.  Consequently the remaining
operator input is sharply separated into two source facts: the uniform
per-channel `2/27` estimates above and convergence of the
finite-support energies to the closed CvS tail form.  The new theorem
`relativeCoupling_of_twoChannelBudgets` further splits the first source fact:
the fixed-low/shell and high-core/shell cross terms may be bounded separately,
provided each consumes at most half of the available `4/27` reference budget.
This is the concrete component-wise route to improve on the coarse global
`B_L` norm.

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
2. after the rigorously checked chain
   `N=20 -> 120 -> 240 -> 480 -> 960 -> 1920 -> 3840`, propagate the now
   certified first-transition previous-core source estimates uniformly to all
   later scales, prove their recursive-core energy normalization, and certify
   the fourteen remaining finite middle-channel
   bridges through `K=15,728,640`; the new scalar-composition certificate gives
   the middle-channel coefficient `2/27` for every integer
   `K>=31,457,280`.  Then pass the resulting `q=999/1000` finite-support
   inequality to the closed high complement uniformly on compact domains with
   right endpoint `< 0`.  The exact `1/666` reserve, the optimized
   `4/9 -> 1/3 -> 4/27` steady recursion, and its two-channel Lean adapter are
   formalized.  The variable route `u_n^2 -> (1-u_n)` and the finite reserve-
   product induction and its strict closed-limit passage are also formalized;
   the analytic layer must now prove a uniform partial-sum bound below one for
   the source-derived `u_n`; the new finite-product lemmas then yield the
   positive floor `1-total`.  The finite- and
   dyadic-channel Cauchy adapters further reduce the previous-core coefficient
   `2/27` to a shell-distance envelope.  The generic route permits leading
   coefficient `1/27`; after assigning the certified odd fixed base `1/384`,
   the selected split uses leading coefficient `1/30`, has exact budget slack
   `83/17280`, and retains squared decay `2^(-i)`.  The new triangular Lean
   induction reduces that decay to a newest-band `1/30` bound and a one-half
   cross-scale transport inequality.  The two-scale midpoint regression checks
   those targets at `K=960 -> 1920`, with all ten repeated ratios below `1/2`,
   while keeping its diagnostic status explicit.  Its source split rejects the
   three-independent-component route, retains the combined
   Archimedean/prime Loewner symbol, and verifies that the Loewner-plus-pole
   amplitude triangle remains below one half on all nine regular bands.  The
   two corresponding amplitude lemmas are kernel-checked.  The preconditioned-Schur
   certificates supply the
   `960 -> 1920` and `1920 -> 3840` bridges, while the strict
   `||T_13||<10/3` power certificate and centered Archimedean envelope close the
   eventual middle-channel scalar budget.  The remaining analytic work is
   concentrated in a uniform previous-core Loewner-symbol amplitude estimate
   that preserves the prime/Archimedean cancellation, the separate elementary
   pole amplitude, the finite middle bridges, their relative channel
   normalization, and the concrete
   Hilbert-compression adapter.  The scalar comparison between the full
   block-diagonal shell sum and the recursively glued core is now formalized by
   the reserve-product block-sum theorem and its direct next-shell adapter;
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
comparison through `20 -> 120 -> 240 -> 480 -> 960 -> 1920 -> 3840` throughout
`x <= -1/1024`; the last two stages use `q_0=249/250`, while comparison with
`q=999/1000` leaves the exact `1/666` reference-energy reserve.  The exact
finite displacement, characteristic-product, residue-normalization,
determinant-ratio, quantitative Abel, energy-normalized monotonicity, and
recursive shell and reference-reserve adapters are now formalized.  The
preconditioned-Schur interval certificates close `960 -> 1920` at
`rho=1/12` and `1920 -> 3840` at `rhoStar=4/9`; the optimized steady recursion
uses reserve `1/3` and per-channel budget `2/27`, while the variable-reserve
theorems retain `product_(i<n)(1-u_i)` when sharper scale-dependent
coefficients are available.  The remaining
`3840 -> 7680` midpoint shell clears that target,
and the exact-rational/Arb sixth-power certificate proves the sharper prime
operator bound `||T_13||<10/3`.  The new Arb composition closes the
middle-channel budget for all `K>=31,457,280`, leaving fourteen finite
middle-channel bridges plus the all-scale previous-core channel.  That channel,
the closed-form passage, the uniform moment bound, and the limiting resolvent
construction remain the dominant proof boundary.

## 10. Local Lean replay

From `research/riemann-cvs-lean`:

```powershell
lake build RiemannCvs.BoundaryGapNoCrossing
lake env lean RiemannCvs/BoundaryGapNoCrossing.lean
lake build RiemannCvs.CvSParityDisplacement
lake env lean RiemannCvs/CvSParityDisplacement.lean
lake build RiemannCvs.CombinedSymbolDyadicL2
lake env lean RiemannCvs/CombinedSymbolDyadicL2.lean
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
replays the corrected V22 finite Arb parity certificate, certifies the direct
parity shell through `N=3840`, verifies the odd fixed-base exception and all
nine regular first-transition source channels, runs the consecutive
`N=3840/7680` previous-core transport diagnostics, reconstructs their
prime/Archimedean/pole source pieces, and gates the selected regular
Loewner-plus-pole two-amplitude route.  It emits those JSON records and
exact-dyadic preconditioners together with the cumulative-residue interval
certificate as downloadable regression artifacts.

## 11. Combined-symbol dyadic L2 certificate

The source diagnostics show that separating the Archimedean and prime pieces
before taking norms loses the observed cancellation: two newest
Archimedean-only transport ratios exceed one half, whereas every combined
Archimedean/prime Loewner ratio remains below one half.  The analytic route
therefore keeps the odd symbol

```text
F_n = S_n + P_n,
P_n = sum_(q<13) Lambda(q)/sqrt(q)
        * sin(2*pi*n*log(q)/log(13)).
```

The `q=13` event is removed exactly because its phase is `2*pi*n` and its sine
vanishes at every integer mode.  The tracked Archimedean certificate supplies

```text
abs(S_n-pi/4) <= 1/(4*n)  for every n>=960.
```

Expanding `(pi/4+P_n)^2`, and applying the finite geometric-sum bound to every
single, doubled, difference, and sum phase, gives for `1<=r<=N`

```text
sum_(n=N+1)^(N+r) F_n^2
  <= r * (main + linearDecay/N + quadraticDecay/N^2)
       + geometricError.
```

At `c=13` the Arb constants are

```text
main =
  1.886116580218509533713810564865291376175739019504099688831444...

geometricError =
  49.001298440261990885245030196417120623592790715793902569502416...
```

Finite Abel summation and the exact Mathlib tail bound

```text
sum_(N<n<=2N) 1/n^2 <= 1/(2*N)
```

then yield

```text
N * sum_(N<n<=2N) F_n^2/n^2
  <= prefixSlope(N)/2 + geometricError*N/(N+1)^2.
```

The right side decreases for positive integer `N`.  The new 256-bit and
384-bit replays both certify at `N=1920`

```text
scaled weighted upper =
  0.969210261436421258996629167478848133228926023272532415858561...

strict slack below 1 =
  0.030789738563578741003370832521151866771073976727467584141438...
```

Consequently, after formalizing the geometric-sum inequality in Lean and
interval-certifying nonresonance of every concrete phase, conditional on the
concrete source identification,

```text
sum_(N<n<=2N) F_n^2/n^2 < 1/N  for every integer N>=1920.
```

`CombinedSymbolDyadicL2.lean` now kernel-checks the reusable part of this
argument.  It includes:

* the factor-two-separated even and odd parity Loewner entry bounds;
* direct symbol-square entry estimates of the form
  `entry^2 <= 32*(F(q)^2/q^2+F(p)^2/q^2)`, followed by rectangular finite
  Cauchy--Schwarz adapters;
* the exact dyadic reciprocal-square estimate and its shifted form;
* an Abel upper theorem for affine prefix bounds;
* `dyadic_weighted_sum_lt_one_div_of_prefix_le_affine`, which turns the strict
  scaled endpoint inequality into the target `1/N` bound;
* `dyadicEndpointScaledUpper_antitone` and
  `dyadicEndpointScaledUpper_lt_one_of_start`, which formalize propagation
  from the certified start mode to every later natural mode;
* `dyadic_weighted_sum_lt_one_div_of_start_endpoint`, which packages the
  certified start endpoint, the all-mode source-prefix input, and the final
  strict weighted-shell conclusion in one theorem.

The certifier consumes the workflow-produced Archimedean JSON instead of
restating its result.  It verifies the input status, precision,
centered-decay coefficient, tracked script hash, and Git SHA before composing
the new constants.  The workflow replays both precisions and publishes both
JSON records.

This closes the uniform scalar `L2` source constant, not the complete
previous-core coefficient.  The next analytic step is to identify the
separated-band energy with the recursively glued core energy and send the
weighted symbol square sum through the full Cholesky/energy normalization.
That step must preserve the combined prime/Archimedean cancellation and the
strict `0.030789...` endpoint reserve rather than reverting to a
component-wise triangle estimate.

## 12. Combined-symbol matrix and newest-band energy bridge

The weighted square estimate now passes through the first matrix and energy
normalization layer without splitting the prime and Archimedean pieces.  For a
previous cutoff `K`, write the newest historical band as `(K/2,K]` and the new
shell as `(2K,4K]`.  The concrete off-diagonal CvS Loewner symbol is `F/pi`, so
its square budget retains the exact Fourier factor `1/pi^2`.

Two applications of the dyadic estimate give

```text
sum_(K/2<p<=K) F(p)^2/p^2 <= 2/K,
sum_(2K<q<=4K) F(q)^2/q^2 <= 1/(2K).
```

Since `p<=K`, the first inequality implies

```text
sum_(K/2<p<=K) F(p)^2 <= 2K.
```

The parity entry-square estimate, the `K/2` historical rows, and

```text
sum_(2K<q<=4K) 1/q^2 <= 1/(4K)
```

therefore produce the cutoff-independent Frobenius-square bound

```text
32/pi^2 * (1/4 + 1/2) = 24/pi^2.
```

`CombinedSymbolDyadicL2.lean` now kernel-checks this chain and its energy
normalization.  The principal new interfaces are:

* `scaled_shifted_symbolSquareBudget`, preserving `1/pi^2` exactly;
* `shifted_symbolSquare_sum_le_four_mul`, converting weighted to ordinary
  square sums on `(N,2N]`;
* `rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul`, proving the
  matrix constant `24*C`;
* `rectangular_relativeCoupling_newestBand_of_shifted_symbolSquareRowBudgets`,
  reducing the newest relative coefficient to
  `24*C <= q*lowGap*highGap`;
* `rectangularSymbolSquareBudget_two_mul` and
  `rectangularSymbolSquareBudget_halfTransport`, proving that a fixed
  historical band spends exactly half its preceding matrix budget when the
  target shell doubles and no more than half its relative coefficient when the
  coercive floors grow;
* `rectangular_relativeCoupling_halfTransport_of_shifted_symbolSquareRowBudgets`,
  packaging that half transport directly at the bilinear-energy level.

The new certifier `certify_combined_symbol_newest_energy.py` consumes the
tracked combined-symbol, prime-translation, and Archimedean certificates and
uses the same coercive shell floor as the eventual middle-channel proof.  Its
rigorous scalar formula is

```text
rho_newest(K)
  <= (24/pi^2) / (gap(K/2)*gap(2K)).
```

Independent 256-bit and 384-bit replays agree.  The first dyadic cutoff at
which this bound is strictly below `1/30` is

```text
K = 491520,
rho_newest(K) upper midpoint
  = 0.0329380152768082444332150801486928732...,
1/30-rho_newest(K) lower midpoint
  = 0.0003953180565250889001182531846404601....
```

At `K=245760` the interval is still strictly above `1/30`, so the threshold is
genuinely the first passing dyadic row in this route.  The newest-band analytic
tail is consequently reduced to eight finite bridge cutoffs:

```text
1920, 3840, 7680, 15360,
30720, 61440, 122880, 245760.
```

This scalar composition was introduced with four concrete operator inputs.
The current JSON has collapsed them to one analytic condition: the real
digamma and trigamma terms must satisfy their pointwise lower bounds, and the
Archimedean-remainder and prime parity forms must satisfy their displayed
absolute quadratic-form bounds.  All geometric corrections inside the
Archimedean diagonal and the even/odd `poleTail` component are now Lean
theorems; the cutoff-13 coercivity consumers insert the latter automatically
for both a standalone consecutive shell and the actual odd/even matrix towers.
The crossblock, parity compression, block-diagonal recursion, and concrete
shell-energy identification are kernel-checked below.  The eight finite bridges
remain.  The certificate still
replaces the formerly open all-scale newest-band estimate by a finite list plus
an explicit all-cutoff theorem and supplies the exact half-transport algebra
once a historical band has entered its analytic range.

## 13. Exact source algebra for the combined Loewner symbol

The first of the four newest-band operator inputs has now been split into an
algebraic part and an analytic source-formula part.  The algebraic part no
longer remains implicit.  `CombinedSymbolDyadicL2.lean` defines

```text
finiteSineSymbol(weight,phase)(x)
  = sum_i weight_i * sin(phase_i*x),
combinedSineSymbol(x)
  = arch(x) + finiteSineSymbol(x),
fourierNormalizedSymbol(x)
  = (1/pi) * combinedSineSymbol(x).
```

Lean proves that every finite sine polynomial is odd, that adding it to an odd
Archimedean symbol preserves oddness, and that the exact `1/pi` normalization
preserves oddness.  The complete `oddDifferenceKernel`, including its supplied
diagonal data, now satisfies exact addition and scalar-multiplication laws.
Consequently

```text
Loewner((arch + primeSine)/pi)
  = (1/pi) * (Loewner(arch) + Loewner(primeSine))
```

as a kernel identity rather than only away from the diagonal.  The theorem
`oddDifferenceKernel_fourierNormalized_combined` packages this equality in the
form consumed by the parity and energy layers.  The endpoint event omitted by
the Arb square-sum certificate is also checked symbolically:

```text
sin(2*pi*n) = 0  for every natural Fourier mode n.
```

The new public theorem surface is:

* `finiteSineSymbol_odd`;
* `combinedSineSymbol_odd`;
* `fourierNormalizedSymbol_odd`;
* `oddDifferenceKernel_add`;
* `oddDifferenceKernel_smul`;
* `oddDifferenceKernel_fourierNormalized`;
* `oddDifferenceKernel_fourierNormalized_combined`;
* `sin_two_pi_nat`.

All eight initial theorems compile with only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.  This closes the exact finite-sum,
prime/Archimedean combination, Fourier-normalization, and endpoint-deletion
algebra.  The entrywise prime adapter described below now closes the finite
prime matrix formula itself.  What still remains in this operator input is
source-specific and analytic: identify the concrete CvS Archimedean entries
and their diagonal values with the packaged Archimedean symbol, then identify
the combined cosine/sine restrictions with the finite historical-band/new-shell
matrices used by the relative-energy theorem.  The coercive-floor, recursive
block-sum, and eight finite newest-band bridges remain separate obligations.

The formerly recorded finite geometric-sum lemma is now also kernel-checked.
For every real `phase` with `sin (phase/2) != 0`, Lean proves

```text
norm (sum_(j=0)^(count-1) exp(i*(start+j)*phase))
  <= 1 / abs(sin(phase/2)),
```

and derives the same bound for the real sine and cosine sums.  The six public
interfaces are `norm_geometric_sum_le_inv_abs_sin_half`,
`norm_shifted_geometric_sum_le_inv_abs_sin_half`,
`exp_nat_mul_real_phase`, `norm_shifted_exp_sum_le_inv_abs_sin_half`,
`abs_shifted_sine_sum_le_inv_abs_sin_half`, and
`abs_shifted_cosine_sum_le_inv_abs_sin_half`.  Arb still certifies that each
actual single, doubled, pair-difference, and pair-sum phase denominator is
strictly positive; the universal inequality itself is no longer an external
mathematical input.

The prime source is now concrete at the Lean level rather than represented by
arbitrary `weight` and `phase` functions.  The definitions are

```text
logarithmicPrimeWeight(q,p) = log(p)/sqrt(q),
logarithmicPrimePhase(c,q) = 2*pi*log(q)/log(c),
finiteLogarithmicPrimeSymbol(c)(x)
  = sum_i logarithmicPrimeWeight(q_i,p_i)
      * sin(logarithmicPrimePhase(c,q_i)*x).
```

Lean proves this finite symbol is odd, combines it with the Archimedean odd
symbol, and establishes the complete diagonal-aware identity for its exact
`1/pi` normalized Loewner kernel.  For every `c>1`, the endpoint phase is
exactly `2*pi`, so the entire weighted cutoff event vanishes at natural modes.
For every strict interior event `1<q<c`, monotonicity of the real logarithm
puts the half phase strictly between `0` and `pi`; hence its sine is positive
and the single-phase sine/cosine geometric bounds apply without a numerical
nonresonance premise.  The nine theorem interfaces are:

* `finiteLogarithmicPrimeSymbol_odd`;
* `logarithmicCombinedSymbol_odd`;
* `oddDifferenceKernel_fourierNormalized_logarithmicCombined`;
* `logarithmicPrimePhase_self`;
* `logarithmicPrimeEndpoint_sine_zero`;
* `logarithmicPrimeEndpoint_term_zero`;
* `logarithmicPrimePhase_half_sin_pos`;
* `abs_shifted_logarithmicPrime_sine_sum_le`;
* `abs_shifted_logarithmicPrime_cosine_sum_le`.

The finite prime matrix formula is now connected to this symbol literally.
`finiteLogarithmicPrimeDiagonal` is the cosine diagonal used by the Arb matrix
builder, `logarithmicPrimeEventEntry` is one iteration of its prime-power loop,
and `finiteLogarithmicPrimeEntry` is the corresponding piecewise finite sum.
Lean proves

```text
finiteLogarithmicPrimeEntry
  = sum_i logarithmicPrimeEventEntry_i
  = oddDifferenceKernel(finiteLogarithmicPrimeSymbol/pi,
      finiteLogarithmicPrimeDiagonal).
```

The cutoff event is zero as a complete entry on integer Fourier modes: off the
diagonal both sine values vanish, while on the diagonal the exact factor
`1-log(c)/log(c)` vanishes.  Finally,
`oddDifferenceKernel_logarithmicCombined_actualDiagonal` combines this literal
prime entry with an Archimedean normalized Loewner entry while keeping their
actual, already normalized matrix diagonals.  The four new public theorem
interfaces are:

* `finiteLogarithmicPrimeEntry_eq_sum_eventEntries`;
* `logarithmicPrimeEndpointEventEntry_nat_zero`;
* `finiteLogarithmicPrimeEntry_eq_oddDifferenceKernel`;
* `oddDifferenceKernel_logarithmicCombined_actualDiagonal`.

The genuinely open source step is therefore narrower again: prove that the
concrete CvS Archimedean off-diagonal formula and its digamma/trigamma diagonal
equal the packaged Archimedean kernel, then restrict the already combined
kernel to the finite parity shell bands.

The full cutoff-free sign and pole assembly is now exact as well.
`normalizedLoewnerSourceEntry` records the literal Archimedean branch used by
the matrix builder: its diagonal is supplied directly, while its off-diagonal
entry is `(S(q)-S(p))/(pi*(p-q))`.  Lean identifies it with
`oddDifferenceKernel(S/pi, diagonal)`.  The regular block
`logarithmicArchPrimeEntry` is this entry plus the finite prime entry above.

The rational source is instantiated without a symbolic placeholder:

```text
logarithmicPoleKernel(c,p,q)
  = poleKernel(
      32*log(c)*sinh(log(c)/4)^2,
      log(c)^2,
      16*pi^2,
      p,q).
```

For `c>1`, its two denominator parameters satisfy the positivity hypotheses,
so the pole displacement law follows.  The exact source sign convention is
then defined by

```text
logarithmicCutoffFreeKernel = W_02 - (W_R + W_p).
```

Lean proves this is the rational pole minus the normalized combined odd
Loewner kernel and, whenever the Archimedean symbol is odd, proves the full
cutoff-free displacement law.  The five new theorem interfaces are:

* `normalizedLoewnerSourceEntry_eq_oddDifferenceKernel`;
* `logarithmicArchPrimeEntry_eq_oddDifferenceKernel`;
* `logarithmicPoleKernel_law`;
* `logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel`;
* `logarithmicCutoffFreeKernel_law`.

The Archimedean symbol itself is now concrete as well.  With

```text
omega(c,x) = 2*pi*x/log(c),
a_k = 2*k + 1/2,
G(c,x) = sum_(k>=0) exp(-a_k*log(c))/(a_k^2+omega(c,x)^2),
S(c,x) = (1/2)*Im digamma(1/4+i*pi*x/log(c)) - omega(c,x)*G(c,x),
```

Lean proves that the series defining `G` is summable for every `c>1` by
comparison with an explicit geometric series.  Complex conjugation of Gamma,
its derivative, and digamma then gives oddness of the imaginary digamma term;
the squared-frequency denominator makes `G` even, so `S(c,-x)=-S(c,x)`.
Consequently the complete kernel with this concrete symbol satisfies the
cutoff-free displacement law directly, rather than through an abstract
odd-symbol hypothesis.  The eight public theorem interfaces are:

* `deriv_gamma_conj`;
* `digamma_conj`;
* `summable_archimedeanGeometricSeries_terms`;
* `archimedeanFrequency_neg`;
* `archimedeanGeometricSeries_neg`;
* `archimedeanDigammaImaginary_neg`;
* `logarithmicArchimedeanSymbol_odd`;
* `logarithmicCutoffFreeKernel_archimedean_law`.

The actual diagonal is now concrete too.  Lean defines the three series used
by the Arb builder,

```text
G_CC(c,x) = sum exp(-a_k*L)*omega^2/(a_k*(a_k^2+omega^2)),
G_X1(c,x) = sum exp(-a_k*L)*a_k/(a_k^2+omega^2),
G_X2(c,x) = sum exp(-a_k*L)*(a_k^2-omega^2)/(a_k^2+omega^2)^2,
```

then records the real digamma correction `CC`, the real derivative-of-digamma
correction `XC`, the exact cutoff constants `kappa` and `J`, and

```text
logarithmicArchimedeanDiagonal(c,x)
  = kappa(c) + 2*CC(c,x) + J(c) - (2/log(c))*XC(c,x).
```

All three series are proved summable for `c>1` by comparison with the same
exponential geometric majorant.  The Gamma/digamma conjugation argument is
differentiated once more, proving the real derivative term even; termwise
reflection proves every geometric diagonal correction even, hence the complete
diagonal is even.  The full kernel is finally instantiated with both the
concrete symbol and this concrete diagonal.  The fourteen new theorem
interfaces are:

* `archimedeanArgument_neg`;
* `archimedeanDigammaImaginary_eq_argument`;
* `deriv_digamma_conj`;
* `summable_archimedeanExponential_terms`;
* `summable_archimedeanCosineGeometricSeries_terms`;
* `summable_archimedeanXOneGeometricSeries_terms`;
* `summable_archimedeanXTwoGeometricSeries_terms`;
* `archimedeanCosineGeometricSeries_neg`;
* `archimedeanXOneGeometricSeries_neg`;
* `archimedeanXTwoGeometricSeries_neg`;
* `archimedeanCosineCorrection_neg`;
* `archimedeanCrossCorrection_neg`;
* `logarithmicArchimedeanDiagonal_neg`;
* `logarithmicCutoffFreeKernel_actualArchimedean_law`.

The elementary analytic part of that diagonal is now closed as well.  Put

```text
r = exp(-2*log(c)),
C(c) = exp(-log(c)/2)/(1-r),
B(c) = exp(-log(c)/2)*((1/2)/(1-r) + 2*r/(1-r)^2).
```

Lean proves that `C` and `B` are exactly the total exponential mass and first
half-integer moment.  Termwise positive comparison and `norm_tsum` then give,
for every nonzero frequency `w`,

```text
|w*G(c,x)| <= C(c)/|w|,
0 <= G_CC(c,x) <= 2*C(c),
0 <= G_X1(c,x) <= B(c)/w^2,
|G_X2(c,x)| <= C(c)/w^2.
```

These inequalities are combined inside Lean with arbitrary lower bounds for
`Re psi(1/4+i*pi*x/log(c))` and its real derivative.  The resulting theorem
produces the lower bound for `-logarithmicArchimedeanDiagonal(c,x)` with every
geometric correction, sign, and `2/log(c)` factor already discharged.  The
remaining diagonal work is therefore precisely the digamma/trigamma
asymptotic inequality and the cutoff-13 scalar constant comparison.  The
seventeen public interfaces of this layer are:

* `archimedeanGeometricMass`;
* `archimedeanGeometricFirstMoment`;
* `tsum_archimedeanExponential_eq_geometricMass`;
* `tsum_archimedeanExponentialMoment_eq_geometricFirstMoment`;
* `summable_archimedeanExponentialMoment_terms`;
* `archimedeanGeometricMass_nonneg`;
* `archimedeanGeometricSeries_nonneg`;
* `archimedeanGeometricSeries_le_mass`;
* `abs_archimedeanFrequency_mul_geometricSeries_le_mass`;
* `archimedeanCosineGeometricSeries_nonneg`;
* `archimedeanCosineGeometricSeries_le_mass`;
* `archimedeanXOneGeometricSeries_nonneg`;
* `archimedeanXOneGeometricSeries_le_firstMoment`;
* `abs_archimedeanXTwoGeometricSeries_le_mass`;
* `neg_two_mul_archimedeanCosineCorrection_ge`;
* `archimedeanCrossCorrection_ge`;
* `neg_logarithmicArchimedeanDiagonal_ge_of_digamma`.

### Digamma/trigamma asymptotic bridge

The next kernel-checked layer now matches the analytic decomposition used by
`certify_archimedean_tail_envelope.py`.  Put

```text
y(c,x) = pi*x/log(c),
D_floor(c,x) = log(y) - (1/8 + sqrt(2)/6)/y^2,
T_floor(c,x) = -(1/y + 1/y^2).
```

A complex norm premise for the first digamma asymptotic term,

```text
||psi(1/4+i*y) - (log(1/4+i*y) - 1/(2*(1/4+i*y)))||
  <= sqrt(2)/(6*y^2),
```

now implies `D_floor <= Re psi` inside Lean.  The proof uses
`Re(log z)=log||z||`, `y<=||z||`, the exact real part of `1/(2z)`, and
`|Re r|<=||r||`; the formerly informal `1/8` and remainder coefficients are
therefore wired to the literal complex argument.  Combining this with
`T_floor <= Re psi'` gives

```text
-logarithmicArchimedeanDiagonal(c,x)
  >= log(x) + asymptoticConstant(c) - asymptoticError(c,x).
```

Lean proves the displayed error antitone for positive modes.  Consequently the
cutoff-13 target

```text
-logarithmicArchimedeanDiagonal(13,x) >= log(x) - 19/20
```

for every `x>=960` follows from the two analytic inputs at `x` and one scalar
comparison at the single endpoint `x=960`.  A shell adapter sends
this directly to the literal CvS diagonal floor `log(old)-19/20` whenever
`old>=960`.  Thus the all-mode scalar monotonicity and every geometric term are
closed.  The elementary trigamma floor inequality is now closed as well: if

```text
sum_{n>=0} 1/(n + 1/4 + i*y)^2 = psi'(1/4+i*y),
```

then terms with `n<ceil(y)` are each at least `-1/y^2`, while all later real
parts are nonnegative.  Since `ceil(y)<=y+1`, Lean derives
`T_floor<=Re psi'`.  Lean now also derives the canonical trigamma `HasSum`
identity from the single shifted-derivative limit

```text
psi'(z+N) -> 0  as N -> infinity,    Re(z)>0.
```

Indeed, analyticity and nonvanishing of `Gamma` on the right half-plane make
`digamma=Gamma'/Gamma` analytic there.  Differentiating
`psi(z+1)=psi(z)+1/z` and telescoping gives the exact finite identity

```text
sum_{n<N} 1/(z+n)^2 = psi'(z)-psi'(z+N).
```

Lean separately proves absolute summability by comparison with the shifted
real p-series.  Thus the former canonical-series premise is discharged by the
displayed tail limit.  What remains in this diagonal branch is the DLMF
norm-remainder theorem, that shifted digamma-derivative decay, and the one
certified endpoint inequality.

The twenty public interfaces are:

* `archimedeanAsymptoticHeight`;
* `archimedeanArgument_re`;
* `archimedeanArgument_im`;
* `archimedeanAsymptoticHeight_pos`;
* `archimedeanFrequency_eq_two_mul_height`;
* `archimedeanFrequency_ne_zero_of_pos`;
* `archimedeanDigammaAsymptoticFloor`;
* `archimedeanTrigammaSeriesFloor`;
* `archimedeanArgument_log_re_ge_log_height`;
* `archimedeanArgument_halfInv_re_le`;
* `digamma_real_ge_asymptoticFloor_of_norm_remainder`;
* `archimedeanGeometricFirstMoment_nonneg`;
* `archimedeanDiagonalAsymptoticConstant`;
* `archimedeanDiagonalAsymptoticError`;
* `archimedeanDiagonalAsymptoticError_antitone`;
* `archimedeanDiagonalAsymptoticLower`;
* `neg_logarithmicArchimedeanDiagonal_ge_of_asymptotic_bounds`;
* `neg_logarithmicArchimedeanDiagonal_ge_log_sub_of_asymptotic_bounds`;
* `c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth`;
* `c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth`.

The elementary trigamma-series reduction adds five public interfaces:

* `archimedeanTrigammaSeriesTerm`;
* `archimedeanTrigammaSeriesTerm_re`;
* `archimedeanTrigammaSeriesFloor_le_of_hasSum`;
* `c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries`;
* `c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries`.

The derivative-shift and tail-limit reduction adds nine more public
interfaces:

* `digamma_analyticAt_of_re_pos`;
* `digamma_differentiableAt_of_re_pos`;
* `deriv_digamma_add_one`;
* `sum_range_one_div_add_sq_eq_deriv_digamma_sub`;
* `summable_one_div_complex_add_sq`;
* `hasSum_one_div_complex_add_sq_of_tendsto_deriv_digamma`;
* `archimedeanTrigammaSeries_hasSum_of_tendsto_deriv_digamma`;
* `c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaTail`;
* `c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaTail`.

The signed-integer finite builder bridge is now exact as well.  Lean defines
the implementation's signed Archimedean extension, absolute-mode diagonal,
literal rational pole entry, diagonal/off-diagonal Archimedean branch, complete
`W_02-W_R-W_p` entry, centered mode `i-N`, and the resulting
`(2*N+1) x (2*N+1)` matrix.  Oddness of the symbol and evenness of the diagonal
remove the sign/absolute-value implementation branches, after which every
entry is definitionally the corresponding restriction of
`logarithmicCutoffFreeKernel`.  The six theorem interfaces are:

* `signedLogarithmicArchimedeanSymbol_eq`;
* `logarithmicArchimedeanDiagonal_abs`;
* `logarithmicCvSPoleEntry_eq_kernel`;
* `logarithmicCvSArchimedeanEntry_eq_source`;
* `logarithmicCvSBuilderEntry_eq_cutoffFreeKernel`;
* `logarithmicCvSBuilderMatrix_eq_kernelRestriction`.

The orthonormal parity compression is now exact as well.  Lean defines the
positive-mode indexing together with the literal cosine and sine matrices used
by the finite builder, and proves entrywise that they are the existing even and
odd parity matrices of the cutoff-free kernel.  The two new theorem interfaces
are:

* `logarithmicCvSBuilderEvenMatrix_eq_evenParityMatrix`;
* `logarithmicCvSBuilderOddMatrix_eq_oddParityMatrix`.

The separated newest channel is now exact.  Writing `B=K/2`, Lean proves that
`Fin B` enumerates exactly `(B,2B]` and `Fin (4B)` enumerates exactly
`(4B,8B]`, embeds both into the positive modes of the `8B` parity matrix, and
identifies the resulting even and odd rectangular builder restrictions.  The
six new theorem interfaces are:

* `exists_historicalBandMode_iff`;
* `exists_newestShellMode_iff`;
* `positiveIntegerMode_historicalBandIndex`;
* `positiveIntegerMode_newestShellIndex`;
* `logarithmicCvSBuilderEvenNewestBand_eq_evenParityRestriction`;
* `logarithmicCvSBuilderOddNewestBand_eq_oddParityRestriction`.

Thus the remaining operator bridge starts after the full centered matrix, its
parity compression, and the certified finite row/column coordinates.  The
finite two-block coordinates are now coherent across the full dyadic tower as
recorded below; the remaining source task is the concrete diagonal and
perturbation component bounds.  The
universal coercive algebra is now formalized by
`coerciveFloor_of_componentBounds`: a diagonal form lower bound and finitely
many absolute perturbation bounds imply exactly the displayed Euclidean floor
after adding the shift.  The recursive scalar energy is now canonical as well:
`recursiveBlockEnergy` adjoins each shell by `E+2*C+T`, its closed finite-sum
formula is proved by `recursiveBlockEnergy_eq_base_add_sum`, and the reserve
and next-shell adapters
`recursiveBlockEnergy_ge_reserveProduct_mul_blockSum` and
`relativeShell_of_recursiveBlockEnergyReserve` consume that recursion without
an extra step hypothesis.

The finite block-coordinate algebra is now exact too.  Lean defines the full
finite matrix quadratic energy and its left-left `base`, right-right `tail`,
and averaged two-orientation `cross` coordinates on a sum-type index.  It proves

```text
Q(blockVector x y) = base(x) + 2*cross(x,y) + tail(y)
```

without assuming matrix symmetry, then proves that any identified scalar
recursion step is exactly this full quadratic form.  The concrete even and odd
CvS parity matrices are pulled back to `Fin B ⊕ Fin (4B)` through the already
proved historical/newest indices; their left-right blocks reduce definitionally
to the certified rectangular newest-band matrices, and both full forms satisfy
the exact block-energy identity.  The eight theorem interfaces are:

* `finiteMatrixQuadraticEnergy_blockVector`;
* `recursiveBlockEnergy_succ_eq_finiteMatrixQuadraticEnergy`;
* `logarithmicCvSBuilderEvenHistoricalNewestBlock_inl_inr`;
* `logarithmicCvSBuilderOddHistoricalNewestBlock_inl_inr`;
* `logarithmicCvSBuilderEvenHistoricalNewestBlock_energy`;
* `logarithmicCvSBuilderOddHistoricalNewestBlock_energy`;
* `recursiveBlockEnergy_succ_eq_evenHistoricalNewestForm`;
* `recursiveBlockEnergy_succ_eq_oddHistoricalNewestForm`.

The averaged cross is now identified with the certificate's single oriented
rectangular form.  At the kernel layer, Lean proves symmetry of every
diagonal-aware odd divided difference and of the rational pole kernel, together
with simultaneous-reflection invariance under an odd symbol and even diagonal.
The finite prime diagonal is even, so these facts propagate through the full
concrete cutoff-free kernel, the signed-integer builder, and both orthonormal
parity matrices.  The pulled-back historical/newest matrices are therefore
symmetric.  Applying
`finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm` removes the average and
gives exactly

```text
cross_even(x,y) = sum_i sum_j x_i * evenNewestBand(i,j) * y_j,
cross_odd (x,y) = sum_i sum_j x_i * oddNewestBand (i,j) * y_j.
```

The end-to-end interfaces are
`oddDifferenceKernel_symm`, `oddDifferenceKernel_neg_neg`,
`poleKernel_symm`, `poleKernel_neg_neg`,
`finiteLogarithmicPrimeDiagonal_even`,
`logarithmicCutoffFreeKernel_symm`,
`logarithmicCutoffFreeKernel_actual_neg_neg`,
`logarithmicCvSBuilderEntry_symm`,
`logarithmicCvSBuilderEntry_neg_neg`,
`logarithmicCvSBuilderEvenMatrix_symm`,
`logarithmicCvSBuilderOddMatrix_symm`,
`finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm`, and the concrete
`logarithmicCvSBuilderEvenHistoricalNewestBlock_crossEnergy` /
`logarithmicCvSBuilderOddHistoricalNewestBlock_crossEnergy` theorems.

The all-scale scalar recursion is now derived from a finite matrix tower rather
than postulated.  For arbitrary finite index families `I n` and shell families
`S n`, Lean pulls matrices and vectors back through exact equivalences
`I(n+1) ≃ I(n) ⊕ S(n)`, proves quadratic energy invariant under that reindexing,
and defines the concrete tower tail and cross energies.  If the pulled-back
next vector is `blockVector (x n) (y n)` and its left-left block is exactly the
previous matrix, `finiteMatrixTowerEnergy_succ` proves the concrete
`E+2*C+T` step.  Induction then gives

```text
finiteMatrixTowerEnergy A x n
  = recursiveBlockEnergy
      (finiteMatrixTowerEnergy A x 0)
      finiteMatrixTowerTailEnergy
      finiteMatrixTowerCrossEnergy n.
```

The interfaces are `finiteMatrixQuadraticEnergy_pullback`,
`finiteMatrixTowerEnergy_succ`, and
`finiteMatrixTowerEnergy_eq_recursiveBlockEnergy`.

The concrete dyadic instantiation is now closed as well.  `Fin` initial
segments split into old prefix plus shell, and a manually kernel-checked
`Option Fin` equivalence carries the zero mode through the even tower.  Lean
proves vector concatenation and old-core matrix preservation for both towers,
then instantiates `finiteMatrixTowerEnergy_eq_recursiveBlockEnergy` for the
actual odd and even CvS matrices.  No separate scalar shell recursion or tower
compatibility hypothesis remains.

The positive-mode coercive decomposition is now explicit for an arbitrary
finite mode map `mode : kappa -> Int`, so it applies to initial segments,
historical bands, and new shells.  Each concrete even/odd builder matrix is
proved equal to the negative Archimedean main diagonal plus exactly three error
matrices, in the fixed order pole, Archimedean remainder, prime.  The main
diagonal energy is reduced to a coordinate sum, and the two specialized
coercive-floor theorems consume only:

1. the pointwise lower bound for `-logarithmicCvSArchimedeanEntry(c,n,n)`;
2. absolute quadratic-form bounds for the Archimedean-remainder and prime
   matrices; and
3. the final scalar floor comparison.

Thus matrix splitting, parity/reflection signs, summation of the three errors,
and passage from pointwise diagonal control to a form lower bound are no longer
part of the analytic obligation.

The final shell identification is now exact as well.  The right-right block of
the pulled-back odd `Fin` tower and even `Option Fin` tower equals the arbitrary
positive-mode matrix on the consecutive shell modes.  The generic shell mode
specializes definitionally to `newestShellMode B` at the `4B -> 8B`
transition.  Therefore both actual `finiteMatrixTowerTailEnergy` coordinates
are equal to the corresponding positive-mode quadratic energies, and the two
new tower-tail coercive-floor theorems consume the same pointwise diagonal and
three error-form bounds directly.  No extra shell-energy identification input
remains.

The rational pole component is no longer an opaque form estimate.  Lean now
defines its common scale, denominator, and even/odd scalar weights and proves
that the even pole matrix is `2*scale*u*u^T`, while the odd pole matrix is
`-2*scale*v*v^T`.  Their quadratic energies are therefore exactly
`2*scale*(sum u_i*x_i)^2` and `-2*scale*(sum v_i*x_i)^2`.  Finite
Cauchy--Schwarz yields the absolute bounds consumed by error component zero:

```text
|Q_pole,even(x)| <= |2*scale| * (sum u_i^2) * ||x||_2^2,
|Q_pole,odd (x)| <= |2*scale| * (sum v_i^2) * ||x||_2^2.
```

Those scalar estimates are now closed.  Lean proves, for every positive
integer mode `n`,

```text
oddWeight(c,n)^2  <= 1/(16*pi^2*n^2),
evenWeight(c,n)^2 <= 1/(64*pi^2*n^2).
```

It reindexes the consecutive shell modes `old+1,...,old+shell` as
`Ioc old (old+shell)` and applies Mathlib's reciprocal-square tail estimate to
obtain `sum 1/n^2 <= 1/old`.  Consequently both parity pole errors obey

```text
|Q_pole,shell(x)|
  <= |scale(c)|/(8*pi^2*old) * ||x||_2^2.
```

For `c>=1`, `scale(c)>=0`, and the cutoff-13 specializations therefore match
the certificate's literal `poleTail(N)=scale(13)/(8*pi^2*(N-1))` with
`old=N-1`.  Two standalone-shell and two matrix-tower coercivity theorems fill
error component zero with this result and expose only the diagonal,
Archimedean-remainder, prime, and final scalar-floor premises.  The pole
component of the shell coercive floor is no longer an analytic hypothesis.
The Archimedean self-entry is simultaneously identified with
`logarithmicArchimedeanDiagonal(c,mode)`.  Its exponential-series mass and
first moment, together with the `G`, `G_CC`, `G_X1`, and `G_X2` bounds, are now
kernel-checked.  The remaining diagonal inequality is reduced to the real
digamma/trigamma estimates on exactly the argument enclosed by the Arb
certificate.

The local `base`, `tail`, and literal rectangular `cross` algebra is no longer
an open step.  The
finite prime loop, Archimedean symbol and diagonal formulas,
signed-integer restriction, parity compression, band restriction, endpoint
deletion, rational pole parameters, subtraction signs, convergence,
reflection, and displacement algebra no longer belong to those open steps.

The composite phase conditions are also symbolic now.  For two strict
interior locations, Lean proves the pair-difference half phase lies in
`(-pi,0)`.  For a pair sum, the sine is positive when `q*r<c`, negative when
`c<q*r<c^2`, so its sole possible resonance is `q*r=c`; the doubled phase is
the specialization `q^2=c`.  The tracked cutoff-13 data are represented by

```text
locations = [2,3,4,5,7,8,9,11],
bases     = [2,3,2,5,7,2,3,11].
```

Finite `Fin 8` case proofs establish `1<q<13`, injectivity of the location
list, and `q_i*q_j != 13` for all 64 pairs.  The aggregate theorem
`c13PrimePhase_all_nonresonant` therefore proves every denominator class used
by the square expansion nonzero: single, doubled, pair-difference, and
pair-sum.  Arb continues to enclose their absolute magnitudes to obtain the
explicit constant `geometricError`; it no longer carries the logical burden
of proving phase nonresonance.

## The trigamma tail now follows from the same global DLMF remainder

The separate shifted-digamma-derivative premise has now been eliminated from
the narrowest cutoff-13 route.  On the right half-plane Lean considers

```text
R(w) = digamma(w) - (log(w) - 1/(2*w)).
```

For a fixed `z` with positive real part and any radius `0<r<Re(z)`, every
closed ball centered at `z+N` stays in the right half-plane.  The Gamma-based
analyticity theorem for `digamma`, the slit-plane derivative of `log`, and the
elementary inverse derivative make `R` differentiable on each such ball.
Cauchy's first-derivative estimate therefore proves

```text
sup_{|w-(z+N)|=r} ||R(w)|| <= epsilon(N),  epsilon(N) -> 0
  ==> ||R'(z+N)|| <= epsilon(N)/r
  ==> R'(z+N) -> 0.
```

Lean separately computes the derivative of the asymptotic model as

```text
(log(w) - 1/(2*w))' = 1/w + 1/(2*w^2)
```

and proves that this expression tends to zero along `z+N`.  Adding the two
limits yields `digamma'(z+N) -> 0`, which feeds the already checked finite
telescoping theorem and produces the canonical reciprocal-square `HasSum`.

A global quadratic remainder bound

```text
0 < Re(w) ==> ||R(w)|| <= C / ||w||^2
```

automatically supplies the shrinking circle envelope: on the radius-`r`
circle, `||w||` is at least `N+Re(z)-r`, so one may take
`epsilon(N)=C/(N+Re(z)-r)^2`.  For the literal Archimedean argument,
`height=Im(z)<=||z||`; the same global bound also gives the exact pointwise
`C/height^2` estimate used by the diagonal floor.  Consequently the choice
`C=sqrt(2)/6` discharges both the digamma floor and the trigamma series from
one analytic hypothesis.

This Cauchy/global-remainder layer adds nine public theorem interfaces:

* `tendsto_deriv_digamma_natTranslate_of_uniform_asymptotic`;
* `tendsto_deriv_digamma_natTranslate_of_quadratic_remainder_bound`;
* `hasSum_one_div_complex_add_sq_of_uniform_asymptotic`;
* `hasSum_one_div_complex_add_sq_of_quadratic_remainder_bound`;
* `archimedeanTrigammaSeries_hasSum_of_uniform_asymptotic`;
* `archimedeanTrigammaSeries_hasSum_of_quadratic_remainder_bound`;
* `archimedean_digamma_remainder_le_of_quadratic_remainder_bound`;
* `c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound`;
* `c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound`.

Thus the narrowest Archimedean diagonal boundary now consists of one global
right-half-plane DLMF-form quadratic remainder theorem and the single scalar
endpoint comparison at mode `960`.  The remaining operator boundary after
that diagonal is the Archimedean-remainder and prime parity quadratic-form
control recorded by the certificate.

## Exact digamma closure and the prime-translation Fourier bridge

The preceding paragraph is now historical.  The global quadratic digamma
remainder and the cutoff-13 scalar comparison have both been proved in Lean.
The exact tent-kernel Euler--Maclaurin representation gives the first-neglected
term and quadratic remainder bounds without an analytic premise, and the
cutoff-13 endpoint arithmetic closes the Archimedean diagonal theorem.  The
public zero-premise consumers are

```text
DigammaEulerMaclaurin.digamma_eulerMaclaurin_tent_representation
DigammaEulerMaclaurin.digamma_first_neglected_term_bound
DigammaEulerMaclaurin.digamma_quadratic_remainder_bound
C13ArchimedeanEndpoint.c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_closed
V23BoundaryWeylMainline.c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
```

Thus the Archimedean main diagonal is no longer part of the conditional
operator boundary.

The finite prime matrix has also acquired an exact operator source adapter.
Write `L=log(c)`, `y=log(q)`, and let `U_y` denote translation by `y` truncated
to the overlap interval `[0,L-y]`.  For integer Fourier modes `n,m`, Lean now
defines twice the real normalized coefficient

```text
(2/L) * integral_{0}^{L-y}
  cos(2*pi*((m-n)*x + m*y)/L) dx.
```

It proves the diagonal formula

```text
2*(1-y/L)*cos(2*pi*n*y/L)
```

and, for `n != m`, the off-diagonal formula

```text
(sin(2*pi*m*y/L)-sin(2*pi*n*y/L))/(pi*(n-m)).
```

After multiplication by `log(p)/sqrt(q)`, these are exactly the two branches
of `logarithmicPrimeEventEntry`.  Summing eventwise proves

```text
finiteLogarithmicPrimeEntry
  = finitePrimeTranslationFourierEntry
```

on every integer-mode pair.  The identity is then lifted to arbitrary finite
mode families, the full signed lattice, and the normalized even/odd parity
compressions.  A single full signed-space quadratic-form estimate therefore
supplies both V23 prime-form premises with the same constant; at cutoff 13 the
consumer exposes the certificate's literal `10/3` constant.

The separate sixth-power functional-analytic step is now checked as well.  In
any C-star algebra, Lean proves for self-adjoint `T`

```text
||T^3|| = ||T||^3,
||T^6|| = ||T||^6,
||T^6|| < (10/3)^6  ==>  ||T|| < 10/3.
```

Accordingly, the prime route no longer lacks matrix-entry identification,
parity transfer, or sixth-root spectral extraction.  Its remaining boundary
is narrower and explicit: construct the weighted truncated-translation
operator on the chosen `L2[0,log 13]` realization, prove the positive
length-six path-kernel expansion and symmetric Schur row-sum implication, and
replay the finite exact-rational/Arb path certificate inside that interface.
The other major operator input still open is the Archimedean off-diagonal
remainder form.  Cross-scale diagnostics continue to favor keeping the
Archimedean and prime Loewner pieces coupled where possible, because the
combined block exhibits half-transport even when the isolated Archimedean
component does not.

## A direct positive supersolution replaces the six-step prime path as the preferred route

The length-six certificate remains valid, but it is no longer the shortest
known route to the cutoff-13 prime bound.  In multiplicative physical
coordinates `t=exp(x)` on `[1,13]`, the positive prime translation is

```text
(T h)(t) = sum_{q=p^a<13} log(p)/sqrt(q) *
  (1_{t*q<=13} h(t*q) + 1_{q<=t} h(t/q)).
```

A numerical Perron probe placed the true positive spectral scale near `3.099`,
well below `10/3`, and revealed that a very small rational step function is
already a strict supersolution.  The chosen function is symmetric under
`t -> 13/t`.  Its multiplicative boundary thresholds and successive heights
are

```text
thresholds = [6/5, 3/2, 5/3, 15/8],
heights    = [1, 5/6, 10/13, 5/7, 9/13].
```

The eight true weights, in location order `[2,3,4,5,7,8,9,11]`, are bounded
in Lean by

```text
[491,635,347,720,736,246,367,724] / 1000.
```

These are not imported decimal assertions.  `PrimeTranslationSupersolution`
proves rational upper bounds for `log 2`, `log 3`, `log 5`, `log 7`, and
`log 11` using the finite `log_div` series, proves the needed square-root
lower bounds algebraically, and derives all eight strict
`log(p)/sqrt(q)` inequalities.  Weight monotonicity then proves that the true
row is below the rational-envelope row at every rational test point.

All support and layer changes occur at 62 rational breakpoints.  The 61 open
cells and all 62 endpoints give the exact rational maximum

```text
max (T_upper h)/h = 33223/10000,
10/3 - 33223/10000 = 331/30000 > 0.
```

The worst open cell is `(39/25,13/8)`, sampled exactly at `637/400`.
The independent 256-bit Arb replay gives the true ratio there as

```text
3.3183648737458053186903603272898534948691120282671
```

with radius below `3.34e-76`.  The new script
`certify_prime_translation_supersolution.py` verifies exact breakpoint
geometry, constancy of every open-cell signature, all exact rational rows,
all true Arb rows, and the stated exact margin.  Its local PASS artifact is
`c13_prime_translation_supersolution.json`.

The algebraic Schur core is also formal now.  For every finite nonnegative
symmetric real kernel `A`, positive vector `h`, and row supersolution
`A*h <= B*h`, `WeightedSchurSupersolution.weightedSchur_quadratic` proves

```text
|sum_{i,j} A(i,j) x(i) x(j)| <= B * sum_i x(i)^2.
```

It uses the exact weighted square inequality

```text
2*a*b <= (h_j/h_i)*a^2 + (h_i/h_j)*b^2
```

and symmetry to identify the two oriented sums.  Thus the direct route has
already replaced 415642 admissible length-six paths by 61 atomic cells at the
certificate level, while retaining the sixth-power route as an independent
fallback.

Two analytic connections remain before this becomes the literal V23 prime
premise.  First, Lean must promote the representative/end-point table to an
all-point (almost-everywhere) cell-coverage theorem; the Python certificate
already checks the exact signature constancy.  Second, the finite weighted
Schur skeleton must be lifted to the bounded partial-translation operator on
`L2[0,log 13]` and composed with the proved Fourier-compression identity.
This is now a one-step positive-supersolution interface rather than a
six-fold path-kernel expansion.

## The 61-cell certificate now covers every real physical point

The first of those two connections is now closed, and in a stronger form than
the representative-point statement.  The deterministic generator
`generate_prime_translation_continuous_supersolution.py` emits
`PrimeTranslationContinuousSupersolution.lean` and verifies the checked-in
module byte-for-byte in `--check` mode.  The generated proof defines the same
step height directly on `Real`, partitions `[1,13]` at the exact 62 rational
breakpoints, proves the upper-weight row inequality on every open cell and
every endpoint, and then exhausts the ordered interval.

The resulting theorem is genuinely continuous-domain rather than a density
claim about rational samples:

```text
c13ContinuousSupersolution_all_upper_rows_le
  (t : Real) (1 <= t) (t <= 13) :
  T_upper h(t) <= (33223/10000) * h(t).
```

The eight already-proved strict logarithmic weight inequalities and
nonnegativity of every row factor then give the final pointwise statement

```text
c13ContinuousActualPrimeTranslationRow_lt_tenThird
  (t : Real) (1 <= t) (t <= 13) :
  T_actual h(t) < (10/3) * h(t).
```

Thus neither interpolation nor an unformalized assertion that the row
signature is constant remains in the prime supersolution certificate.  The
remaining prime-side analytic boundary is now only the operator passage:
formalize the partial translations on `L2[0,log 13]`, integrate the weighted
AM-GM inequality under translation, and compose the resulting norm bound with
the existing Fourier-compression/parity bridge.  No sixth-power path
enumeration is needed on this preferred route.

## The continuous weighted-Schur operator passage is formal

The weighted AM--GM integration step is now a proved Lean theorem rather than
an operator-level plan.  `PrimeTranslationContinuousSchur` defines, for a
finite family of shifts `a_i` and nonnegative weights `w_i`, the literal
partial-translation form

```text
sum_i 2*w_i * integral_0^(L-a_i) f(x)*f(x+a_i) dx.
```

For one shift, `oneShift_abs_integral_le` applies the positive-weight square
inequality pointwise on the open overlap, integrates it, and uses the exact
interval-translation identity to turn the second Schur half into an integral
over `[a_i,L]`.  The finite theorem then sums these estimates.  Two truncation
lemmas prove that the weak upper test `x <= L-a_i` and strict lower test
`a_i < x` reconstruct the full interval integral without double-counting the
shared endpoint.  Consequently

```text
finiteTranslationIntegratedRows
  = integral_0^L finiteTranslationNormalizedRow(x) * f(x)^2 dx,
```

and `finiteTranslationSchur` proves the continuous analogue of the finite
matrix Schur test with exactly the same row constant `B`.

The cutoff-13 specialization is also closed at the pointwise-coordinate
level.  It pulls the generated height back by `t=exp(x)`, sets
`a_i=log(q_i)`, proves all eight shifts lie in `[0,log 13]`, and verifies the
exponential identities for both translated neighbors.  The strict lower
overlap convention can omit only the equality point `q_i=exp(x)`, so its row
is bounded by the already-certified closed-support multiplicative row.  Lean
therefore proves

```text
c13_finiteTranslationNormalizedRow_lt_tenThird
  (x in (0,log 13)) : normalizedRow(x) < 10/3
```

and the consumer `c13PrimeTranslationSchur` gives

```text
|sum_i 2*w_i * integral_0^(log(13)-log(q_i))
    f(x)*f(x+log(q_i)) dx|
  <= (10/3) * integral_0^log(13) f(x)^2 dx.
```

Its only explicit side conditions are interval integrability of the test
function square, the overlap products, and the two truncated weighted row
integrands.  The difficult constant and all support geometry are discharged
internally.  The remaining prime-side bridge is correspondingly narrower:
instantiate these routine integrability obligations for the finite Fourier
polynomials, prove the complex real/imaginary energy identity and Parseval
normalization, and feed the result through the existing signed-mode parity
compression.  The continuous positive-Schur estimate itself is no longer an
open premise.

## Fourier/Parseval closes the cutoff-13 prime operator premise

The remaining operator passage has now been carried out in
`PrimeTranslationContinuousFourier`.  For an arbitrary finite integer mode
family, Lean defines the real cosine and sine polynomials

```text
C(x) = sum_i v_i cos(2*pi*m_i*x/L),
S(x) = sum_i v_i sin(2*pi*m_i*x/L),
```

and proves the pointwise product identity that expands
`C(x) C(x+y) + S(x) S(x+y)` into the double Fourier sum used by
`truncatedTranslationFourierEntry`.  Finite sum/integral interchange then
gives the exact, normalization-sensitive identity

```text
energy(truncatedTranslationFourierEntry L y)
  = (2/L) * integral_0^(L-y)
      (C(x) C(x+y) + S(x) S(x+y)) dx.
```

Summing this equality over the eight prime-power shifts identifies the full
finite translation-matrix energy with the two physical Schur forms divided by
`log 13`.  Separately, `finiteCosineSine_parseval` proves, for injective
integer modes,

```text
integral_0^L (C(x)^2 + S(x)^2) dx
  = L * sum_i v_i^2.
```

All continuity, measurability, and interval-integrability obligations are now
internal theorems.  In particular, the step supersolution height is proved
measurable and uniformly bounded, the weighted height ratios are bounded by
`2`, and every left/right truncated row integrand is interval integrable for
each continuous input.  Hence `c13PrimeTranslationSchur_continuous` has no
external integration side conditions beyond continuity of the test function.

Combining these identities yields the premise-free finite matrix estimate

```text
|energy(finitePrimeTranslationModeMatrix 13 ... mode, v)|
  <= (10/3) * sum_i v_i^2
```

for every injective integer mode family.  A further signed-mode injectivity
lemma handles `mode (+/- i)` whenever the original modes are injective and
strictly positive.  The existing even/odd compression identities therefore
close both cutoff-13 parity prime forms with the same `10/3` constant.

The V23 mainline now instantiates this result on the literal consecutive shell
map `old + 1 + j`.  It proves that map injective, supplies premise-free even
and odd shell prime bounds, and adds prime-closed coercivity consumers for both
standalone shells and actual matrix-tower tails.  In those consumers the pole
tail is already explicit and the prime term is fixed at `10/3`; the only
substantive operator estimate still exposed is the Archimedean off-diagonal
remainder.  This is the next proof target.  These results close a component of
the V23 reduction; they are not by themselves a proof of RH.

## 2026-09-02: initial post-3840 adjacent bridge closed

The Archimedean off-diagonal target identified above is now sharpened on the
specific geometry needed immediately after the rigorous finite frontier.
`AdjacentArchimedeanHilbertSchmidt.lean` decomposes the actual adjacent cross
block `(M,2M] x (2M,4M]` into its reflected Hankel leading term and two
centered remainders.  Reciprocal-square summation gives the premise-free
even/odd amplitude

```text
Arch_adjacent(M) <= 241/1000,   M >= 3840,
```

in place of the previous whole-core `667/1000` charge.  With the literal pole
and prime components the complete builder amplitude is `2719/750`; retaining
the first two dynamic diagonal gaps proves

```text
cross_builder(M,2M)^2
  <= (24/25) * baseEnergy(M,2M) * tailEnergy(M,2M)
```

for both parities and every `M >= 3840`.  Thus the analytic dyadic chain can
now start at the current finite endpoint rather than waiting until `13^5`.
The active boundary is the finite multiblock composition through `371293` and
its exact principal restriction, followed by the already isolated infinite
boundary-Weyl passage.

## 2026-09-02: adjacent coefficient sharpened to `37/40`

The follow-up module `AdjacentArchimedeanSharpGap.lean` replaces the coarse
`log` and `pi` decimals in the preceding bridge with kernel-checked bounds for
`log 2`, `log 3`, `log 5`, and `pi`.  The pole amplitude at the first scale is
`229/5000`, the complete cross amplitude is `27151/7500`, and the two diagonal
gaps are `428/125` and `207/50`.  Exact rational arithmetic yields, in both
parities,

```text
cross_builder(M,2M)^2
  <= (37/40) * baseEnergy(M,2M) * tailEnergy(M,2M),  M >= 3840.
```

The gain from `24/25` to `37/40` leaves a `3/40` local reserve for multiblock
transport.  The controlled rectangle is `(M,2M] x (2M,4M]`; in particular,
the first instance is `(3840,7680] x (7680,15360]`.  The separate rectangle
`[1,3840] x (3840,7680]` is still the initial finite/analytic seam and must be
closed by a recursive or preconditioned finite certificate before the full
dyadic tower can be assembled.

## 2026-09-02: rigorous N=3840 to N=7680 seam certificate

A 192-bit Arb run now closes the literal finite/analytic seam
`[0,3840] x (3840,7680]` with `q < 249/250` and recursive reserve
`rho < 1/12`.  It verifies all `29,495,040` solve-residual entries across the
two parities, embeds the floating Cholesky choices as exact dyadic triangular
matrices, and proves all `7680` preconditioned Gershgorin rows strictly
positive.  The certificate JSON hash is
`32FF3DEA7F17F65D9DE23DCE784B8CD142D08E282C4C6EC9611F5CF9E846376D`.

The direct-parity validator was also generalized so a direct certificate can
serve as the next recursive core while retaining source-hash/Git-blob
provenance checks.  CI now regenerates the N=7680 artifact and its two exact
3840-square bases.

Consequently the initial seam identified in the preceding section is closed.
The immediate structural target is the next two-channel recursion into
`(7680,15360]`: charge the adjacent `(3840,7680]` channel by the Lean theorem
`37/40`, and fit the older `[0,3840]` channel into the remaining `3/40` reserve
using the separated source transport.  This is still a finite/multiblock
continuation problem, not the final infinite boundary-Weyl identification.

## 2026-09-02: the first analytic multiblock budget is strictly subcritical

A new midpoint route diagnostic extends the historical-source decomposition
through the first genuinely analytic target shell `(7680,15360]`.  The file
`v23_c13_previous_core_to_N15360_transport_diagnostic.json` has SHA-256
`0417866453BC1DF9CF9C05188665D29C290F6B7FCB4E3207A444962C712FAFDC` and is
explicitly marked `MIDPOINT_DIAGNOSTIC_ONLY`; it selects the proof architecture
but is not used as a rigorous certificate or a Lean premise.

The diagnostic gives historical total relative coefficients approximately

```text
even: 0.004244062573749289,
odd:  0.005330188518377651,
```

both far below the formal aggregate allowance `1/15`.  Every *total* repeated
historical channel is strictly smaller than half its predecessor, and the
newest historical channels are about `0.00179` (even) and `0.00192` (odd),
well below the leading envelope `1/30`.  There is no total-channel exception at
this scale.  The source split reveals an important proof-design constraint:
the Archimedean component by itself can contract as slowly as approximately
`0.572`, whereas the combined Archimedean-plus-prime Loewner group contracts by
at most approximately `0.46217`.  The pole part also halves.  Thus the analytic
transport theorem should preserve the natural Loewner grouping instead of
applying separate triangle inequalities to Archimedean and prime pieces.  The
old odd `[1,20]` block likewise halves in total, but its separated two-piece
triangle bound is roughly `9.94` times the previous total because it destroys
essential cancellation; that fixed block must remain a structured sum.

The decisive new formal observation is that no improvement of the already
proved historical budget `2/27` is needed.  The sharpened adjacent estimate
fits it exactly as

```text
37/40 + 2/27 = 1079/1080,
1 - 1079/1080 = 1/1080.
```

`FirstAnalyticMultiblockBudget.lean` proves these identities and combines the
two relative estimates using the weighted square

```text
((37/40) * historicalCross - (2/27) * adjacentCross)^2 >= 0,
```

avoiding the factor two in the elementary triangle-square estimate.  It then
connects the result to the literal cutoff-13 even and odd adjacent builder
blocks.  The exported concrete consumers are

```text
c13EvenBuilderAdjacentWithDyadicHistorical_relative_1079Over1080
c13OddBuilderAdjacentWithFixedAndDyadicHistorical_relative_1079Over1080.
```

The even theorem consumes the existing `1/30` geometric dyadic envelope.  The
odd theorem consumes the independent fixed-block allowance `1/384` together
with the same regular dyadic family through the existing `2/27` adapter.  This
closes the multiblock *composition algebra* with a strict `1/1080` reserve.
The remaining source-level task is to prove the concrete half-transport and
leading-envelope hypotheses uniformly in the dyadic scale, preserving the
combined Loewner and fixed-block cancellations identified above; the infinite
boundary--Weyl limit remains a later, separate step.

## 2026-09-02: concrete combined-Loewner and pole half transport

`HistoricalCombinedLoewnerTransport.lean` now formalizes the grouping selected
by the N=15360 diagnostic on the literal cutoff-13 source.  For every historical
shell `(B,2B]` and remote target `(N,2N]` with `4B <= N`, it defines the actual
Fourier-normalized odd symbol

```text
F13 = (ArchimedeanSymbol13 + finitePrimeSymbol13) / pi
```

with the actual diagonal, proves its even/odd separated-row square estimates,
and lifts them through rectangular Cauchy to the complete cross form.  The
Archimedean and prime pieces are never separated in this chain.

The fixed-source matrix budget is proportional to `1/N`, so Lean proves its
exact scaling law under `N -> 2N`.  The new monotonicity theorem
`c13ShellDynamicGap_mono` then connects this algebra to the already closed
premise-free cutoff-13 shell coercivity.  The concrete endpoints

```text
c13EvenHistoricalCombinedLoewner_halfTransport_shellEnergy
c13OddHistoricalCombinedLoewner_halfTransport_shellEnergy
```

show that a previous combined-Loewner coefficient `q` becomes `q/2` against the
actual source-shell and doubled-target builder energies.  Their remaining
analytic inputs are displayed rather than hidden: the next weighted symbol
square bound and the preceding rectangular scalar budget.

The rational pole channel is stronger than the older fixed-prefix interface.
Because the low coordinates form `(B,2B]`, not `[1,B]`, both pole weight masses
decay:

```text
low mass  = O(1/B),
high mass = O(1/N),
pole squared coefficient = O(1/(B*N)).
```

The rank-one factorization and reciprocal-square shell bounds are entirely
kernel-checked.  Both even and odd pole coefficients halve exactly when `N`
doubles, and the theorems

```text
c13EvenHistoricalPole_halfTransport_shellEnergy
c13OddHistoricalPole_halfTransport_shellEnergy
```

normalize that fact by the same actual shell energies without a numerical
premise.

Finally, the module defines the literal positive-mode builder on
`(B,2B] ⊕ (N,2N]` and proves entrywise and bilinear identities

```text
actual builder cross = pole cross - combined-Loewner cross.
```

The endpoints

```text
c13HistoricalRemoteEvenBuilder_halfTransport_amplitude
c13HistoricalRemoteOddBuilder_halfTransport_amplitude
```

reassemble those two channels with the exact amplitude coefficient
`(ampPole + ampLoewner)^2`.  This is the root-free interface needed to prove a
one-half total transport using rational amplitude majorants, and it avoids the
fixed factor-two triangle loss.

This closes the concrete matrix representation, pole transport, coercive-energy
normalization, and structured two-source composition for every regular
historical shell.  It does not yet supply the source-specific combined-symbol
scalar inequality itself, the finite bridge values for every early shell, the
structured old odd `[1,20]` total, the sum over all historical shells, or the
infinite boundary--Weyl limit.  Those are now the exposed remaining boundaries;
no midpoint diagnostic is used as a theorem premise.

## 2026-09-02: the pole is itself Loewner, so the full builder is one symbol

The preceding two-amplitude route was mathematically valid but still discarded
one layer of cancellation.  `FullBuilderLoewnerTransport.lean` records the
stronger algebraic observation.  For

```text
g(x) = -scale * x / (a + b*x^2),
```

direct rational simplification gives

```text
(g(q) - g(p)) / (p - q)
  = scale * (a - b*p*q) / ((a + b*p^2) * (a + b*q^2)).
```

The right side is exactly the rational `W_{0,2}` pole kernel.  With the
corresponding diagonal value this identity also holds when `p=q`; Lean proves
the fully global theorem

```text
poleKernel_eq_oddDifferenceKernel_rationalPoleLoewner.
```

Therefore the complete cutoff-13 kernel

```text
pole - (Archimedean + finite-prime Loewner)
```

is one odd-symbol Loewner kernel, with symbol

```text
c13HistoricalBuilderLoewnerSymbol
  = logarithmicPoleLoewnerSymbol 13
      - c13HistoricalCombinedLoewnerSymbol.
```

The formal development identifies the literal even and odd remote builder
matrix entries and bilinear cross energies with this full symbol.  It then
repeats the separated-row estimate only once, on the complete source.  As a
result the actual builder itself, rather than two triangle-combined pieces,
has exact target-doubling transport `q -> q/2`.

The new arbitrary-distance endpoints are

```text
c13HistoricalRemoteEvenBuilder_dyadicTransport_fullLoewner
c13HistoricalRemoteOddBuilder_dyadicTransport_fullLoewner,
```

and their exact coefficient is `q * (1/2)^k`.  The finite-family endpoints

```text
c13HistoricalRemoteEvenBuilder_dyadicFamily_fullLoewner
c13HistoricalRemoteOddBuilder_dyadicFamily_fullLoewner
```

apply weighted Cauchy directly to actual historical builder matrices and prove
that an arbitrary finite family consumes at most `2 * leading`, uniformly in
the number of earlier regular shells.  This is the previously missing concrete
bridge into `relativeCoupling_of_dyadicChannelBudgets`.

The existing N=15360 midpoint diagnostic explains why the stronger grouping
matters.  In the old odd `[1,20]` channel, the actual full coefficient is about
`5.0704e-4`, while the pole/Loewner two-piece triangle coefficient is about
`1.1047e-2`, a factor of `21.79` larger.  The full-symbol representation keeps
that cancellation algebraically instead of treating the band as intrinsically
exceptional.  For regular channels the split loss is small, but the same single
representation now handles every distance.  These floating values are route
diagnostics only and are not theorem premises.

This closes the symbolic multi-step transport and regular finite-family
summation.  The exposed analytic boundary is narrower: prove or consume the
full-symbol square-sum estimate with one base rectangular budget for each
newly introduced shell, connect the finitely many source bands below `960` to
their certified energies, and then feed the resulting uniform coefficient into
the recursive reserve and infinite boundary-Weyl limit.  Neither those scalar
certificates nor the infinite limit is asserted here.

## 2026-09-02: Fourier normalization sharpens the full-symbol budget to 197/2000

`FullBuilderSymbolDyadicL2.lean` closes the regular dyadic square-sum adapter
for the complete builder symbol.  The first ingredient is a pure Lean estimate
for the rational-pole Loewner symbol:

```text
|logarithmicPoleLoewnerSymbol 13 x| <= 1/(4*x),  x > 0,
sum_{N<n<=2N} P(n)^2/n^2 <= 1/(32*N^3).
```

The proof reduces the pole scale to elementary bounds for
`sinh(log(13)/4)^2`, `log(13)`, and `pi`; no floating interval is assumed.

The decisive improvement is to use the normalization already present in the
literal historical kernel.  The companion Arb certificate controls the raw
combined symbol

```text
F(n) = ArchimedeanSymbol13(n) + finitePrimeSymbol13(n)
```

by `97/(100*N)` on every dyadic shell beginning at `N >= 1920`.  But the
actual Loewner symbol is `F/pi`.  From `pi > 3.14`, Lean obtains

```text
1/pi^2 <= 2500/24649,
sum historicalCombined(n)^2/n^2 <= (2425/24649)/N.
```

This factor was absent from the provisional unit-budget route.  A Young split
with parameter `1/3000`, proved from `(a + 3000*b)^2 >= 0`, then gives

```text
(a-b)^2 <= (3001/3000)*a^2 + 3001*b^2.
```

Combining the normalized raw-symbol term with the cubic pole tail proves, in
Lean and by exact rational arithmetic, that for every `N >= 1920`,

```text
sum_{N<n<=2N} builderSymbol(n)^2/n^2
  < (197/2000)/N.
```

At the first scale the rational upper expression is approximately
`0.0984395066`, leaving about `6.049e-5` below `197/2000`; these decimals only
describe the exact inequality and are not proof premises.  The even and odd
endpoints

```text
c13HistoricalRemoteEvenBuilder_dyadicTransport_of_rawCombined
c13HistoricalRemoteOddBuilder_dyadicTransport_of_rawCombined
```

feed the new constant directly into the previously proved
`q*(1/2)^k` transport theorem.  Thus the regular transport no longer carries a
unit full-symbol constant: it uses `197/2000`, an improvement by a factor
greater than ten.

The matching finite-family endpoints

```text
c13HistoricalRemoteEvenBuilder_dyadicFamily_of_rawCombined
c13HistoricalRemoteOddBuilder_dyadicFamily_of_rawCombined
```

perform the same substitution at a common target and retain the uniform
`2*leading` total envelope.  They expose only the raw target certificate and
the source rectangular budgets, so no separate full-symbol premise remains at
the multiblock call site.

The 256-bit Arb replay for the required raw premise passed with scaled upper
`0.9692102614364212589966291674788481...`, strict slack
`0.0007897385635787410033708325211519...`, and JSON SHA-256
`AADBBCD025B864902FD2634F54DB546C8364723967D8C7EAEBF4ABDACC368AFD`.
The independent 384-bit replay has SHA-256
`900DAA2D9C93F4B0D558EDE1BE41DFCB2AC1A095B5341436207AE5FF2BAA2830`.
CI now replays both `97/100` certificates in addition to the older unit
certificates used by downstream regression scripts.

The remaining regular-shell input is now only the source rectangular base
budget.  Separately, the finitely many source bands below `960`, including the
structured old odd band, must be attached to finite energy certificates before
the recursive reserve and infinite boundary-Weyl limit can be completed.

## 2026-09-02: exact parity moments remove the regular base-budget premise

`SharpParityFullBuilderTransport.lean` removes the last provisional
rectangular-budget hypothesis from every regular historical channel.  The old
row estimate bounded both parity compressions by

```text
32 * (f(q)^2/q^2 + f(p)^2/q^2),
```

which erases the powers of `p/q` and is too large at the critical separation
`N=4B`.  Expanding the exact odd-symbol Loewner numerators instead gives, for
`0 <= p` and `2p <= q`,

```text
even entry^2 <= (128/9) * (f(q)^2/q^2 + p^2*f(p)^2/q^4),
odd  entry^2 <= (128/9) * (p^2*f(q)^2/q^4 + f(p)^2/q^2).
```

Lean proves these inequalities directly from the off-diagonal parity formulas
and the denominator floor `(q^2-p^2)^2 >= (9/16)q^4`.  It then uses two
different scalar moments, rather than forcing both channels through one
Frobenius estimate:

```text
weighted target:  sum f(q)^2/q^2 <= (197/2000)/N,
unweighted source: sum f(p)^2       <= (21/100)B.
```

The second line follows from the raw unweighted combined-symbol estimate
`sum F(p)^2 <= 2B`, Fourier normalization by `1/pi`, and the rational-pole
tail.  At `N=4B`, exact summation of the retained moments gives

```text
even entry-square budget <= 499/1125,
odd  entry-square budget <= 1037/2250.
```

Both fit below the available coercive product:

```text
entry budget <= (1/30) * (428/125) * (207/50).
```

Consequently the literal complete builder matrices now have direct relative
coupling coefficient `1/30` at the base separation, with no
`rectangularSymbolSquareBudget` or `hPreviousBudget` premise.

The proof also retains the different decay rates.  At
`N=4B*2^k`, the `q^-4` terms decay as `2^(-3k)` and the remaining terms as
`2^(-k)`.  This yields theorem-checked actual-matrix bounds

```text
c13HistoricalRemoteEvenBuilder_dyadic_relative_oneThirtieth
c13HistoricalRemoteOddBuilder_dyadic_relative_oneThirtieth
```

with coefficient `(1/30)*2^(-k)`.  The new regular finite-family endpoints
sum these literal channels directly and fit them inside the established
`2/27` previous-core allocation.  Thus the regular source-shell obstruction
is no longer a missing base budget; the remaining finite work is confined to
the source bands below the regular `B>=3840` threshold and the structured odd
fixed block, followed by the recursive reserve/operator identification and
the infinite boundary-Weyl limit.

The companion Arb certifier now emits both norms from the same affine-prefix
certificate.  At `N=1920`, the 256-bit and independent 384-bit replays give

```text
weighted scaled upper        = 0.9692102614364212589966291674... < 0.97,
unweighted average upper     = 1.9129521415701273581392597166... < 2,
unweighted average slack     = 0.0870478584298726418607402833....
```

The unweighted conclusion is uniform for every integer `N>=1920`, just as the
weighted conclusion is.  These interval statements remain explicit analytic
inputs; the parity algebra, normalization, moment conversion, matrix Cauchy
step, coercive floors, dyadic propagation, and finite-family composition are
all checked in Lean.

## 2026-09-02: asymmetric parity weights lower the analytic source frontier to 960

`SharpParityLowFrontierTransport.lean` applies a second asymmetric split, now
inside the exact even and odd parity numerators.  The two channels need
opposite weights:

```text
even: (a-b)^2 <= (3/2)*a^2 + 3*b^2,
odd:  (a-b)^2 <= 3*a^2 + (3/2)*b^2.
```

This is materially sharper than using `2*a^2+2*b^2` in both sectors.  At
separation `N=4B` the corresponding entry-square constants become

```text
even: 151/375,
odd:  617/1500,
```

and for every positive dyadic distance `k` both are bounded by
`(8/25)*2^(-k)`.  The proof retains the target/source assignment of every
`q^-2` and `q^-4` moment rather than optimizing only a final decimal constant.

The module also reuses the already proved sharp cutoff-13 pole-scale inequality
to replace the old coarse pole tail by `1/(2B)`.  Exact elementary logarithm
bounds then give theorem-checked coercive floors

```text
c13ShellDynamicGap(B) >= 2       for B >= 960,
c13ShellDynamicGap(T) >= 24/5    for T >= 15360.
```

Since `(1/30)*2*(24/5)=8/25`, every historical source shell with `B>=960`
and common target `T>=15360` now satisfies the literal full-builder relative
coefficient `(1/30)*2^(-k)`.  The `k=0` channel uses the stronger existing
`428/125` source floor forced by `T=4B>=15360`; all `k>=1` channels use the new
uniform floor `2`.  This lowers the analytic source threshold from `3840` to
`960` without adding a rectangular-budget premise.

At the first target covered after the separately certified `T=7680` finite
seam, namely `T=15360`, there are three analytic historical shells:

```text
B = 3840, 1920, 960,
budget sum = 1/30 + 1/60 + 1/120 = 7/120.
```

The exact residual inside `2/27` is `17/1080`.  The finite certificate is
anchored at target coordinate `T=1920`, three dyadic halvings before `T=15360`.
Its complete even allocation is

```text
1/30 + 1/60 + 1/120 + 1/240 + 1/480 = 31/480,
(31/480) * (1/2)^3 = 31/3840,
17/1080 - 31/3840 = 53/6912 > 0.
```

The complete odd allocation has the same four regular bands, totaling `1/16`,
plus the fixed `[1,20]` exception at `1/384`; hence

```text
(1/16 + 1/384) * (1/2)^3 = 25/3072,
17/1080 - 25/3072 = 1051/138240 > 0.
```

Lean proves these transport and residual identities.  Thus the new analytic
frontier splices exactly into the complete certified finite allocation rather
than silently omitting its three larger regular bands.

The scalar source premise at `B=960` was replayed independently at 256 and 384
bits.  The affine-prefix certificate gives

```text
scaled weighted upper    = 0.9953092043212243611655675874... < 1,
unweighted average upper = 1.9397877368301653214535977573... < 2,
unweighted slack         = 0.0602122631698346785464022427....
```

The JSON SHA-256 values are
`2FA43F823DBB9FFFCB3D7A2B4FB1657D7849C43974C51D7A133212D0A0743DE4`
and
`BF649E6A47894C94B39C2AB8C4E472EC1828012A0436F205BD94198453205B45`.
The weaker weighted target `1` is used only to certify the old source shell;
remote target shells continue to consume the uniform `97/100` certificate.
The remaining historical exceptions are now genuinely fixed below `B=960`,
after which the live obstruction is their finite-energy attachment and the
recursive/infinite boundary-Weyl identification.

## 2026-09-02: finite source moments replace three growing remote certificates

`FiniteMomentLowModeTransport.lean` takes a different route through the three
standard shells immediately below the analytic frontier.  Instead of carrying
a complete finite Schur certificate from target `1920` through three successively
larger matrices, it keeps the remote target entirely analytic and extracts only
two invariants from each fixed source shell:

```text
even source: sum_{B<n<=2B} n^2 * builderSymbol(n)^2,
odd source:  sum_{B<n<=2B}       builderSymbol(n)^2,
both sectors: sourceGap * ||x||_2^2 <= sourceEnergy(x).
```

The exact reflected Loewner numerators then give the source-moment/target-moment
Frobenius budgets

```text
even = (64/9) * ((3/2)*B*(197/2000)/N
                 + 3*sourceSecond/(2*N^3)),
odd  = (64/9) * (3*(4*B^3)*(197/2000)/N^3
                 + (3/2)*sourceZero/(2*N)).
```

At the literal target `N=15360`, exact rational arithmetic selects:

| source shell | energy floor | even moment upper | odd moment upper | relative cost |
|---|---:|---:|---:|---:|
| `(480,960]` | `129/50` | `49740000` | `92` | `1/350` |
| `(240,480]` | `177/100` | `6274000` | `47` | `1/500` |
| `(120,240]` | `137/100` | `735000` | `219/10` | `1/795` |

The six specialized endpoints act on the literal full builder matrices.  For
example,

```text
c13HistoricalRemoteEvenBuilder_480_15360_relative_oneOver350
c13HistoricalRemoteOddBuilder_480_15360_relative_oneOver350
```

take a 480-dimensional source certificate and the already established analytic
target symbol premise; no `480 x 15360` remote matrix certificate occurs.  The
other four endpoints are the analogous `240/500` and `120/795` pairs.

After charging the analytic `B=3840,1920,960` channels and these three fixed
source channels, Lean proves the exact residual identity

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795
  = 96421/10017000
  > 0.0096.
```

The companion script `certify_finite_source_moment_floor.py` rigorously
discharges the finite premises with direct Arb formulas.  It evaluates the
complete builder symbol, proves every moment upper bound with positive interval
slack, constructs each unshifted parity source matrix, subtracts the rational
gap, and proves the resulting matrix positive by an exact-dyadic congruence and
strict interval Gershgorin.  Before those checks, a canonical full-matrix replay
through cutoff `120` proves that all `14641` even and `14400` odd
direct-minus-canonical entry intervals contain exact zero.

## 2026-09-02: coercivity-adapted partition closes `(20,120]`

A first attempt to treat `(20,120]` as one source interval was rejected rather
than rounded into a certificate: canonical parity indexing gives an odd
midpoint minimum eigenvalue near `0.09378`, too weak for the proposed common
gap.  The replacement is structural rather than a higher-precision retry.
`FiniteResidualBandTransport.lean` generalizes the source-moment proof from a
dyadic `(B,2B]` shell to an arbitrary consecutive interval `(A,A+M]`, then
partitions the residual band at its natural coercivity changes:

| source interval | dimension | common parity floor | even moment upper | odd moment upper | exact `sum n^2` | relative cost |
|---|---:|---:|---:|---:|---:|---:|
| `(60,120]` | `60` | `22/25` | `107500` | `49/4` | `509410` | `1/900` |
| `(30,60]` | `30` | `49/100` | `12110` | `27/5` | `64355` | `1/900` |
| `(20,30]` | `10` | `19/100` | `1530` | `47/20` | `6585` | `1/900` |

The exact arbitrary-interval Loewner entry identities feed the same analytic
target at `N=15360`; only these small source matrices remain numerical.  The
six literal endpoints are the even/odd pairs

```text
c13FiniteIntervalRemote{Even,Odd}Builder_60_60_15360_relative_oneOver900
c13FiniteIntervalRemote{Even,Odd}Builder_30_30_15360_relative_oneOver900
c13FiniteIntervalRemote{Even,Odd}Builder_20_10_15360_relative_oneOver900.
```

Their total cost is `1/300`.  Lean kernel-checks the two exact ledger endpoints

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795 - 3*(1/900)
  = 63031/10017000
  = 0.006292402...,

63031/10017000 - 1/3072
  = 7650593/1282176000
  = 0.005966882....
```

The second line also reserves the transported exceptional odd fixed-block
allowance.  Thus the finite source not yet incorporated by this moment route is
only the structured fixed block `[1,20]`; `(20,120]` is closed.

The extended certifier checks the three standard shells and these three
residual intervals in one direct/canonical replay.  At each precision all
`1680 + 200 = 1880` strict Gershgorin rows pass.  The smallest preconditioned
margin midpoint is `0.9999999999999608`; the largest radius is below `1.22e-69`
at 256 bits and below `3.63e-108` at 384 bits.  All twelve exact-dyadic
preconditioner hashes agree across the independent precision runs.  The
tightest scalar enclosure is the odd `(20,30]` moment:

```text
2.3445951216285382382958985633884... < 47/20,
slack = 0.00540487837146176170410143661158....
```

Local JSON SHA-256 values are
`71F9F0906D20FAA1653DD37A73B2481B77CE746AED951603AECD8812223EB9D7`
at 256 bits and
`38B31EF48DEDFD4C079D1023830171172867F594E07F25CA4BFA9F625D280341`
at 384 bits.  Both record script SHA-256
`4DB7918CB4040A8B9573AC59BD4BFBB763F99201B28AEB6BF9476D4DD73ADC54`.
CI replays both certificates and uploads both JSON files plus all twenty-four
preconditioner files.

This closes six finite source bands as external interval certificates attached
to kernel-checked analytic transport bridges.  It does not replace the
structured fixed-block argument, the fourteen finite middle bridges, the
recursive coefficient summation, or the infinite boundary--Weyl form/operator
identification; those are now the localized remaining boundaries.

## 2026-09-02: source-Gram whitening closes the fixed odd block directly

The last fixed interval behaves differently from the six moment-controlled
bands.  On `[1,20]` the unshifted odd source matrix has near-null directions, so
replacing its full energy by a scalar Euclidean gap makes the remote cost worse
by several orders of magnitude.  The new route preserves those directions.
Define the exact shifted/reference source matrix and remote crossblock by

```text
S = (249/250) * (H_odd,[1,20] + (1/1024) I),
C = H_odd,[1,20] x [15361,30720].
```

`FiniteFixedSourceGramTransport.lean` introduces the corresponding source
energy `c13OddFixedReferenceEnergy` and column energy

```text
sum_j (sum_i C_ij x_i)^2.
```

A finite Cauchy theorem first bounds the actual builder cross term by that
column energy times `||y||_2^2`.  The certificate interface retains the full
source geometry:

```text
C13OddFixedSourceGramCertificate 20 15360 (3/1250):
  ||C^T x||_2^2 <= (3/1250) * (x^T S x).
```

Since the target shell has the already proved analytic energy floor `24/5` and

```text
3/1250 = (1/2000) * (24/5),
```

Lean derives the literal endpoint
`c13OddFixedRemoteBuilder_20_15360_relative_oneOver2000`.  This is a direct
fixed-source-to-analytic-shell bridge: it does not use the earlier midpoint
half-transport hypothesis and does not construct or invert a `15360 x 15360`
target matrix.  The complete finite-source ledger now has the exact positive
remainder

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795 - 3*(1/900) - 1/2000
  = 23209/4006800
  = 0.0057924029....
```

The direct route spends slightly more than the conditionally transported
`1/3072` allowance, but removes the transport premise entirely and still keeps
more than `0.00579` reserve.

`certify_fixed_source_gram_floor.py` evaluates `210` source-triangle entries and
the complete `20 x 15360 = 307200` crossblock with direct Arb formulas.  Arb
then encloses all `6,144,000` products in `C*C^T` and proves

```text
(3/1250) S - C*C^T > 0
```

by an exact-dyadic congruence.  All `20/20` Gershgorin rows pass at both 256 and
384 bits.  The minimum preconditioned margin midpoint is
`0.999999999999867`; the largest radius is below `2.49e-68` at 256 bits and
below `7.81e-107` at 384 bits.  Both runs reload the identical preconditioner
with SHA-256
`8A09B178DEFD216CC37D23F6DA56E93846BF00832DFFB331B7B1E4B8647E5CB0`.
The midpoint generalized critical coefficient `0.00201123859...` is recorded
only as a diagnostic; the proof uses the strict interval matrix certificate at
the rational value `3/1250 = 0.0024`.

The 256-bit JSON SHA-256 is
`D0ABABA4F39D5914BE76CF03529A9C5EBA946054F9E7C6D0658432540BA1EE67`;
the 384-bit JSON SHA-256 is
`3B474B20C1D6B1D609CB016A3D7A44CD689497BDDCCFF0C43DB3FE83C0B431EC`.
Both record script SHA-256
`FC6A5A4E8C8D86BED026468DB1F8809BBAFB20B235DE470394B97F9B8BDB379F`.

Consequently every finite previous-core source block is now attached directly
to the first analytic target at `N=15360`.  The live finite obstruction has
moved to the fourteen middle-channel bridges; after those come the uniform
coefficient summation and infinite boundary--Weyl form/operator limit.

## 2026-09-02: rational Loewner compression replaces huge middle matrices

The adjacent middle channel has a structure that the previous scalar estimate
did not exploit.  If `p` lies in `(K,2K]` and `q` in `(2K,4K]`, its same-sign
piece is a rectangular Loewner matrix

```text
L(p,q) = (F(p)-F(q))/(p-q).
```

It therefore has displacement rank two:

```text
D_p L - L D_q = F(p) * 1^T - 1 * F(q)^T.
```

The reflected piece is the same construction on the separated negative target
interval.  This connects the CvS block directly to the explicit Zolotarev
singular-value theory of Beckermann--Townsend,
`On the singular values of matrices with displacement structure`
([arXiv:1609.09494](https://arxiv.org/abs/1609.09494),
[DOI 10.1137/16M1096426](https://doi.org/10.1137/16M1096426)).  Their general
displacement theorem gives `sigma_(j+2k) <= Z_k sigma_j` for a Loewner block;
the rank depends logarithmically, rather than linearly, on the bridge size.

A direct matrix-free FFT reconstruction was first checked against the dense
SVD.  For the first open bridge `K=1920`, the complete combined-Loewner norms
are

```text
even  0.93222685088685...
odd   0.91998164783758...
```

while the existing coarse diagonal floors allow norm
`0.92632438219167...`.  Thus the odd scalar route already passes, whereas the
even route misses by less than one percent and should retain the full finite
energy.  At `K=3840` the combined norms are about `0.96369032` and `0.98919717`,
against an allowed norm `1.11584462`; both pass with room.  Later norms are not
monotone (`K=30720` is about `1.17`), so monotone extrapolation was discarded.
The same FFT operator nevertheless scales beyond the dense frontier and
confirms that the growing logarithmic gaps, not monotonicity of the block, are
the correct mechanism.

The low-rank observation is much stronger than a fast matrix-vector product.
At `K=1920` the twentieth singular value is already below `4e-5`.  An explicit
ADI-style rational compression was then built.  Map the two mode intervals by
a Mobius transformation to `[-alpha,-1]` and `[1,alpha]`, and take logarithmic
shifts

```text
s_j = alpha^((j+1/2)/k),
r(w) = product_j (w+s_j)/(w-s_j).
```

For every `t in [1,alpha]`, one shift lies within half a logarithmic grid cell.
That factor has magnitude at most `tanh(log(alpha)/(4k))`; every other factor
is at most one.  Symmetry gives the rigorous residual ratio

```text
Z <= tanh(log(alpha)/(4k))^2.
```

Using `64` factors for the same-sign block and `12` for the much better
separated reflected block gives displacement-rank ledger

```text
2*64 + 2*12 = 152.
```

The tracked Arb audit
`certify_adjacent_loewner_compression_tail.py` verifies all fourteen dyadic
bridges at both 256 and 384 bits.  The largest same-sign residual bound occurs
at `K=15728640` and is

```text
0.0046860295734951956146961269... < 1/200;
```

the largest reflected bound is

```text
0.00018612896082536405... < 1/4000.
```

The 256/384-bit JSON SHA-256 values are respectively
`E5DD81C5655FB585457B06DC3505E5067F9C80F8A6286978A8CD410F79FC152C`
and
`4B3EA34EBCF8D007C8E9958C7B78E213B26463B62C892593319FAC5F7936ACA3`;
the script SHA-256 is
`CFB585B9F404550A30D24F44FA6B5EB1DBBFB5561B0184DAF48A11BA887A1C43`.

`AdjacentLoewnerCompression.lean` kernel-checks the posterior step.  If a
compressed block has norm `Y`, residual norm at most `z X`, and `z<1`, then
`X <= Y/(1-z)`.  The parity theorem keeps the sum of the two compressed blocks
intact and charges only residual inflations `1/199` and `1/3999`, preserving
the same-sign/reflected cancellation.  It then invokes the existing coercive
norm adapter to produce the relative-energy inequality.

This first compression package changes the computational and formal shape of
the fourteen middle bridges.  The sharper first-step result below supersedes
the provisional conclusion that `K=1920` must keep a dense direct full-energy
certificate.

## 2026-09-02: K1920 is reduced to rank 86 by a rebalanced energy split

The missing first bridge was not intrinsically a dense-matrix phenomenon.  Its
coarse failure came from applying a historical-core Archimedean loss to the
square adjacent source and target shells.  For `i,j : Fin M`, the positive
Hilbert denominator is at least `2*(M+1)`.  Hence its row sum is at most `1/2`,
and the reflected half-Hilbert leading form costs `1/4`.  Together with the
centered bound `43/3840`, Lean now proves the complete adjacent Archimedean
remainder bound

```text
1003/3840
```

for both parity sectors.  This raises the source and target coercive floors to

```text
a = 2257/768       at M >= 1920,
b = 351629/96000   at M >= 3840.
```

The K1920 rational compression can consequently use `31` same-sign and `12`
reflected factors, for rank cap `86`.  Independent 256/384-bit Arb runs prove

```text
z_same <= 19/4000,
z_reflected <= 3/16000,
```

and the new compressed-Gram certifier proves

```text
Y_same <= 8881/10000,
Y_reflected <= 22301/100000,
Y_even <= 93223/100000,
Y_odd <= 93223/100000.
```

For `C=U*V^T`, each Gram proof uses exact-dyadic `R` and independently checks
`G_U<R*R^T` and `R^T*G_V*R<epsilon^2 I` by strict interval Gershgorin.  Both
precisions pass `516` rows and select the same proof matrices.  The full
a-posteriori norm is therefore bounded in Lean by

```text
93223/100000 + (19/3981)*(8881/10000)
  + (3/15997)*(22301/100000)
  = 186377448887/199012678125
  < 23413/25000.
```

This is enough for the adjacent coefficient `11/135`, because

```text
(23413/25000)^2 <= (11/135)*a*b.
```

The original steady budget `4/27` can be split asymmetrically without any
loss:

```text
old core : 1/15,
adjacent : 11/135,
sum      : 4/27.
```

Thus the live K1920 boundary has moved again.  The residual-factor estimates,
rank-86 Gram bounds, sharp coercive floors, exact posterior, and weighted
two-channel recombination are closed.  `LoewnerAdiTelescope.lean` now also
closes the general ADI telescope over an arbitrary root/pole list and its
rank-two factorization.  The remaining first-step premises are the concrete
K1920 Arb root/pole lists and noncollision-certificate binding to the generic
theorem, and the old-core coefficient `<=1/15`; the latter is substantially looser than the recorded
midpoint coefficients but still requires a rigorous certificate or analytic
proof.  After this step, the other compressed finite bridges, uniform shell
ledger, source-specific form convergence, and infinite boundary--Weyl operator
identification remain.

The two adaptive residual artifacts have SHA-256
`DB39044FD42298074A6E2C84FEACE109D79EACDECAE25D1D0CE6CE6E54193363`
and
`9ECD64319225A57ECCB62F7FFB229B2AC43373D03AD173E56D6630D9F1B8E57C`.
The two CI-pinned `python-flint 0.8.0` compressed-Gram JSON artifacts have
SHA-256
`A89545C3E8988F7F7E27150E05E07A96784E7DB3B42E1BB4D894FB7FB1EB7A2A`
and
`25272CADF535B277EC0BD4D255F45B414AE2F1CB4E7FFF17D858AFF058CE3D08`;
their tracked script hash is
`22A48F56137882F30C3A5A2C4BCA093F9E7BE2CB2A13120689A61F1CF60788FB`.
The certifier also checks `98` deterministic factor-reconstruction entries,
all containing zero.  This now tests that the concrete Arb construction agrees
with the separately kernel-checked universal identity; the pending work is its
literal K1920 instantiation, not the telescope algebra itself.

### Strengthened K1920 old-core source Gram

The first old-core channel is now certified without a 3840-dimensional target
Schur complement.  Direct Arb parity formulas build the complete old/new
crossblock, including prime--Archimedean cancellation, pole terms, and the even
zero mode, and prove

```text
C*C^T < (13/100) R_q(old)
```

for both source dimensions `1921` and `1920`.  Combining this with the proved
target floor `351629/96000` gives the stronger coefficient `1/28`, since

```text
(1/28)*(351629/96000) - 13/100 = 2189/2688000.
```

The first-bridge total and recovered reserve are therefore

```text
old core + adjacent = 1/28 + 11/135 = 443/3780,
4/27 - 443/3780 = 13/420.
```

Independent 256/384-bit proofs pass `3841` strict Gershgorin rows and replay
the same exact-dyadic preconditioners at both precisions.  Their JSON hashes are
`5CC43F1E2E449FE3BDA62E197A860BB2E0133F450B24E47CDE8E66E7015E8494`
and
`29A8EC9313C577DC921B6411D14EE905E01E8DAB3736D89CB82D0CBC6AFB4E92`;
the final script hash is
`29AFD703D06AC1A4DFC45712C0E8BED786E79F018C42B655FF640411CD2D56CF`.
Lean now contains the finite rectangular Cauchy proof, source-Gram certificate
structure, target-floor adapter, `1/28` specialization, and weighted
`443/3780` recombination.  The old-core `1/15` item is therefore superseded;
the literal K1920 ADI shift binding is the remaining concrete first-bridge
algebraic interface.

### Literal K1920 ADI shift binding

That final algebraic interface is now implemented in
`K1920AdiShiftBinding.lean`.  The module does not replace roots and poles by
decimal constants: it defines the endpoint cross ratio, the associated
`alpha`, the logarithmic nodes

```text
exp(log(alpha) * (2*i+1)/(2*n)),
```

and a closed inverse cross-ratio map.  It therefore fixes exact `Fin 31` and
`Fin 12` shift functions for the same-sign and reflected geometries.  It also
embeds the following two Arb-certified pole-cell transcripts:

```text
same:
3841,3841,3841,3841,3842,3842,3843,3844,3845,3847,3849,
3852,3856,3861,3867,3876,3887,3903,3923,3949,3985,4031,
4094,4178,4292,4447,4660,4958,5384,6012,6983

reflected:
3942,4155,4384,4629,4893,5178,5484,5815,6173,6560,6980,7436.
```

The companion `certify_k1920_adi_shift_cells.py` evaluates those literal
formulas with Arb.  At both 256 and 384 bits it proves, for all 43 factors,

```text
same:      root < 2 < pole,
reflected: 0 < root and pole < 0,
m < 1920*abs(pole) < m+1.
```

This is `86` strict range comparisons plus `86` strict cell comparisons per
run.  The narrowest cell margins at 256 bits are
`0.0025378742375879395...` (same-sign) and
`0.0034431239246604142...` (reflected).  Cell integers are selected from
midpoints, then every strict comparison is proved from the full interval; the
midpoints themselves are not evidence.  An independent inverse cross-ratio
evaluation also checks all `43+43` production-minus-literal root/pole
residuals, each of which contains zero.  The 384-bit run consumes the 256-bit
artifact as a reference and confirms byte-for-byte equality of both cell
lists.

The final hashes are

```text
script: 4C10E789A68B0F9DE10456214363BF598FD3BAED2D926BFCA74EC590E16B4CC9
256:    0997E2C74CCB463E8DC1307B6C183ED305356954775BC16B5E81ADE2E4CD7858
384:    07CDCFCA9A2E64A13026FB36C6B67BA4318176A9A0811A8886848251C72F5548
```

From the interval-certificate fields, Lean proves the natural-grid exclusion
lemma, all same/reflected noncollisions, and the exact two literal
factorizations by direct application of the generic ADI telescope.  Axiom
audits for `gridCell_ne`, both noncollision theorems, and both literal
factorizations report only `propext`, `Classical.choice`, and `Quot.sound`.
Consequently the first K1920 bridge now has a complete, explicit interface:
rank-86 Gram caps, residual caps, coercive floors, the `1/28 + 11/135 =
443/3780` ledger, literal shifts, and exact factorization.  The finite Arb
inequalities remain named certificate premises rather than hidden kernel
claims.  The next finite work is the remaining twelve compressed bridge Grams;
after them remain the uniform coefficient summation, source-specific form
convergence, and the infinite boundary--Weyl closed-operator/no-crossing
identification.

## 2026-09-03: K3840 closes the second finite adjacent channel

The next channel after K1920 is now closed to an explicit rank-152 certificate:

```text
source = (3840,7680],
target = (7680,15360],
rank   = 2*64 + 2*12 = 152.
```

The new generic `AdjacentAdiShiftBinding.lean` contains the exact
mode-independent inverse Mobius construction, logarithmic nodes, grid-cell
exclusion, same/reflected noncollision lemmas, and ADI factorization adapters.
The K1920 leaf has been refactored onto this shared layer without changing its
external theorem names.  `K3840AdiShiftBinding.lean` then supplies the literal
64 same-sign and 12 reflected shifts and their complete Arb-certified cell
tables.

At each of 256 and 384 bits, the shift certifier passes 152 strict range checks,
152 strict cell-side checks, and all `76+76` independent literal-formula
residual replays.  The stable cell-list hashes are

```text
same:      03EA3A32E8FECDDC46843BBB018B446C22EA49F659D3E6E62D860A7C394DD9FF
reflected: F8384506770E832CAF44B30E97866F16724AF23C4CE21E0008D16F6929C62F30.
```

The parameterized compressed-Gram certifier proves, in full Arb interval
arithmetic,

```text
same-sign <= 99/100,
reflected <= 1/4,
even total <= 199/200,
odd total <= 199/200.
```

Both precisions have every left and right exact-dyadic Gershgorin row strictly
positive: `128/128` for same-sign, `24/24` for reflected, and `152/152` for
each total parity sector.  The reference audit matches the rank, reconstruction
samples, certificate dimensions, row positivity, and all selector and
preconditioner hashes.  The principal selectors are

```text
same:      5CC54EBD01A41812FC7D1672F75C5053904C29C5F34B65D1793E3DFA4193A8C6
reflected: DEEACB16604781E247916C6E1B8DD8F869639C5B254D60EEB16F3ACF90BD5E5E
total:     BD13BAF2B5F24090056DEEFC864F87BF95E24182CB03B95C25E83686A30B142D.
```

The Lean scalar ledger in `K3840AdjacentCompression.lean` is

```text
posterior
  = 199/200 + (1/199)*(99/100) + (1/3999)*(1/4)
  = 159166151/159160200,

(2/27)*(428/125)*(207/50) - posterior^2
  = 6326898111337867/126659846320200000 > 0.
```

Thus `relativeCoupling_of_k3840_rank152Compression` converts the explicit
finite premises into the relative-energy coefficient `2/27`.  The proof does
not turn the Arb inequalities into axioms: they remain named external
certificate premises, while the rank arithmetic, posterior, budget slack, and
energy conversion are kernel checked.

The local 256/384 shift JSON SHA-256 values are
`C846A8452CE896FBA1AB65770BF097221A07EDDFD2EE9BEE9703FA9B2D43598F`
and `9EF588B451DB328535252CDFA4766C1A2C77AE1F2D4D0E0754F66192142BA55C`;
the Gram JSON values are
`66506AC1CB51640EC732217F061D888218EAE3E82E66963A49FF1E717FC8BF7D`
and `07DB105012D6CC9D82552BF6251C7AE2755649B847ACC997F97AE4FDE9F6D463`.
They are local snapshot hashes because the documents contain volatile metadata;
the cross-precision and CI contract is structural equality plus stable internal
hashes.  The parameterized Gram and shift script hashes are respectively
`E30769B98F9911E043CB00E54595455C27B4BF34430BD0D48B0D39C2E8929681`
and `82DA3B656FBB7B83FC281EE969B3A5C7CE9E7BFD2379EB7F36128C8837389B06`.

The finite front is therefore K1920 plus K3840 complete, with twelve finite
adjacent compressed bridges still open.  The uniform coefficient sum,
source-specific form convergence, infinite closed boundary--Weyl operator,
limiting spectral/no-crossing step, and RH conclusion remain separate and
unproved.
