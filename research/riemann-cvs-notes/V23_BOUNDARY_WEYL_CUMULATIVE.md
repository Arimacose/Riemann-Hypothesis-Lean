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

Finally, `recursiveShellEnergy_ge_of_reserveProductLowerBound` separates the
remaining analytic obligation exactly: any uniform scalar floor

```text
reserveFloor <= product_(i<n) (1-u_i)
```

immediately yields `reserveFloor * E_0 <= E_n` at every finite stage.  Thus the
theorems `recursiveShellEnergy_limit_ge_of_reserveProductLowerBound` and
`recursiveShellEnergy_limit_pos_of_reserveProductLowerBound` pass that lower
bound to a convergent closed-form energy and make it strictly positive whenever
`reserveFloor>0` and `E_0>0`.  The next separated-band estimate may therefore
use the measured scale-dependent previous-core coefficients instead of
replacing each one by `4/9`.  Positivity of a uniform reserve floor is not
inferred from the finite algebra.  It remains a concrete analytic target, for
example via a summable upper envelope for the `u_i` and a separate
positive-product lemma.

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
`1/27`.  This replaces one opaque old-core matrix norm by three explicit
source obligations: identify the cross form as the sum of its dyadic-shell
pieces, prove that a fixed reserve times the sum of their nonnegative energies
is controlled by the recursive core, and establish the `2^(-i)` coefficient
envelope for the structured total crossblock (or an explicit allocation among
the prime, Archimedean, and pole pieces).  Those source estimates remain open;
the finite summation and budget conversion are now kernel-checked.

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
   `N=20 -> 120 -> 240 -> 480 -> 960 -> 1920 -> 3840`, prove the previous-core
   channel uniformly and certify the fourteen remaining finite middle-channel
   bridges through `K=15,728,640`; the new scalar-composition certificate gives
   the middle-channel coefficient `2/27` for every integer
   `K>=31,457,280`.  Then pass the resulting `q=999/1000` finite-support
   inequality to the closed high complement uniformly on compact domains with
   right endpoint `< 0`.  The exact `1/666` reserve, the optimized
   `4/9 -> 1/3 -> 4/27` steady recursion, and its two-channel Lean adapter are
   formalized.  The variable route `u_n^2 -> (1-u_n)` and the finite reserve-
   product induction and its strict closed-limit passage are also formalized;
   the analytic layer must now prove a positive uniform floor for those
   products from the separated-band previous-core estimates.  The finite- and
   dyadic-channel Cauchy adapters further reduce the previous-core coefficient
   `2/27` to a shell-distance envelope with leading coefficient `1/27` and
   squared decay `2^(-i)`.  The preconditioned-Schur certificates supply the
   `960 -> 1920` and `1920 -> 3840` bridges, while the strict
   `||T_13||<10/3` power certificate and centered Archimedean envelope close the
   eventual middle-channel scalar budget.  The remaining analytic work is
   concentrated in the prime previous-core crossblock, the finite middle
   bridges, their relative channel normalization, and the concrete
   Hilbert-compression adapter;
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
parity shell through `N=3840`, and emits its JSON and exact-dyadic
preconditioners together with the cumulative-residue interval certificate as
downloadable regression artifacts.
