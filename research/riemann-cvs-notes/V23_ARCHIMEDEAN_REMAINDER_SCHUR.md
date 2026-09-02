# V23 Archimedean remainder Schur closure

Date: 2026-09-02
Branch: `research/cvs-boundary-weyl-v23`
Lean module: `research/riemann-cvs-lean/RiemannCvs/ArchimedeanRemainderSchur.lean`
Coupling module: `research/riemann-cvs-lean/RiemannCvs/AsymptoticTailRelativeCoupling.lean`
Operator module: `research/riemann-cvs-lean/RiemannCvs/AsymptoticTailOperatorBound.lean`
Historical-core module: `research/riemann-cvs-lean/RiemannCvs/AsymptoticCoreHilbert.lean`
Sharp Hilbert module: `research/riemann-cvs-lean/RiemannCvs/AsymptoticCoreHilbertPi.lean`

## Result

The cutoff-13 asymptotic shell is now closed in Lean without a numerical
operator-norm premise.

For every consecutive positive-mode shell with

\[
960 \le N,\qquad M\le N,
\]

both actual parity matrices of the cutoff-13 CvS builder satisfy the stronger
uniform coercive inequalities

\[
x^{\mathsf T}A^{\mathrm{even}}_{N,M}x
  \ge \frac95\lVert x\rVert_2^2,\qquad
x^{\mathsf T}A^{\mathrm{odd}}_{N,M}x
  \ge \frac95\lVert x\rVert_2^2
\]

for every real vector \(x\in\mathbb R^M\). The corresponding even and odd
matrix-tower tail energies have the same \(9/5\) coercive floor whenever the
newest shell is no larger than the previous core. The earlier \(3/25\)
theorems remain available as conservative compatibility interfaces.

This is an asymptotic-shell theorem, not a proof of RH. The remaining global
boundary is to turn these closed newest-shell inequalities into the exact
cross-shell/cumulative boundary-Weyl no-crossing statement used by the final
limit argument, and to connect that eventual result to the finite prefix.

## New route

Earlier numerical work estimated the Archimedean parity remainder as an
operator, with a sharp constant near \(0.203\). The formal route here avoids
formalizing a discrete Hilbert-transform contraction. It instead uses a
coarser entrywise Schur estimate whose constant \(1/2\) still leaves a
strict complete CvS reserve.

Write

\[
S_c(x)=\frac12\Im\psi\!\left(\frac14+
 i\frac{\pi x}{\log c}\right)
 -\omega_c(x)G_c(x),\qquad
 e_c(x)=S_c(x)-\frac{\pi}{4}.
\]

For \(c=13\) and \(x\ge960\), the module proves

\[
|e_{13}(x)|\le \frac1{4x}.
\]

The proof is fully internal:

1. the already proved Euler--Maclaurin digamma estimate gives
   \[
   \left\|\psi(z)-\left(\log z-\frac1{2z}\right)\right\|
   \le \frac{\sqrt2}{6\,y^2},
   \qquad z=\frac14+iy;
   \]
2. the argument defect is identified with an arctangent and bounded by
   \[
   0\le\frac{\pi}{2}-\arg\!\left(\frac14+iy\right)
   =\arctan\!\frac1{4y}\le\frac1{4y};
   \]
3. the inverse term contributes at most \(1/(4y)\);
4. the geometric correction is nonnegative and its opposite-side cost is
   bounded by \(M_{13}/(2y)\), with
   \[
   M_{13}\le\frac7{25};
   \]
5. the elementary bounds
   \[
   \frac{x}{y}\le\frac{171}{200},\qquad
   \frac{x}{y^2}\le\frac{171}{200000}
   \]
   close both sides of the absolute-value estimate.

## Exact matrix identities

For positive integral modes \(n,m\), the reflected entry is rewritten as

\[
A_c(n,-m)=
-\frac1{2(n+m)}
-\frac{e_c(n)+e_c(m)}{\pi(n+m)}.
\]

For distinct same-sign modes,

\[
A_c(n,m)=
\frac{e_c(m)-e_c(n)}{\pi(n-m)}.
\]

Since distinct integer modes are separated by at least one and \(\pi>3\),
every even or odd remainder entry on an \(M\)-mode shell beginning after \(N\)
has absolute value at most

\[
\frac1{4N}+\frac{D}{3N^2}+\frac{2D}{3N},
\qquad D=\frac14.
\]

The generic finite estimate

\[
|x^{\mathsf T}Ax|
\le M\,\max_{i,j}|A_{ij}|\,\lVert x\rVert_2^2
\]

then gives

\[
|x^{\mathsf T}R^{\mathrm{even}}x|,
\ |x^{\mathsf T}R^{\mathrm{odd}}x|
\le\frac12\lVert x\rVert_2^2
\]

because \(M\le N\).

## Complete scalar budget

The remaining components were already formalized:

- diagonal floor: \(\log N-19/20\);
- prime-translation loss: \(10/3\);
- Archimedean remainder loss: \(1/2\);
- rational pole loss:
  \[
  \frac{\mathrm{PoleScale}_{13}}{8\pi^2N}\le\frac{13}{60}.
  \]

The pole estimate needs only the coarse bounds

\[
\sinh^2(\log13/4)\le169,\quad
\log13<513/200,\quad
\pi>3,\quad N\ge960.
\]

A first implementation used a 20-term rational arctanh lower sum to prove

\[
\log13>\frac{64}{25}.
\]

and hence obtained the conservative reserve \(3/25\) from
\(N\ge960>13^2\). A sharper exact argument uses the literal cutoff instead:

\[
960=2^6\cdot3\cdot5,
\]

while rational arctanh sums with respectively two, three, and four terms give

\[
\log2>\frac{69}{100},\qquad
\log3>\frac{109}{100},\qquad
\log5>\frac85.
\]

Consequently

\[
\log N\ge\log960
=6\log2+\log3+\log5
>\frac{683}{100}.
\]

The four loss constants sum exactly to five at the proved upper bounds, so the
complete explicit reserve is now

\[
\frac{683}{100}-
\left(\frac{19}{20}+\frac12+\frac{10}{3}+\frac{13}{60}\right)
\ge\frac95.
\]

Thus both parity shell energies and both actual tower-tail energies have a
uniform \(9/5\) coercive floor, with no remaining analytic or numerical
premise. This is fifteen times the first formal floor.

## Relative-coupling consequence

`AsymptoticTailRelativeCoupling.lean` inserts the closed \(9/5\) high gap into
the existing squared-norm Schur adapter. For the balanced recursive target
\(q=4/9\), the determinant budget

\[
B_{\mathrm{cross}}\le q\,g_{\mathrm{core}}g_{\mathrm{high}}
\]

now reduces exactly to the single scalar condition

\[
B_{\mathrm{cross}}\le\frac45 g_{\mathrm{core}}.
\]

The concrete even and odd tower theorems already contain the literal core,
cross, and tail energies. They therefore remove the high-block coercivity
premise from the recursive step rather than merely restating a generic Schur
lemma.

## Operator-compression advance

The first attempt to close the remaining cross budget with an entrywise
Frobenius or absolute-value Schur estimate was deliberately tested before being
formalized. Exploratory high-precision calculations gave the following warning
signs:

- on the adjacent split `[481,960]` versus `[961,1920]`, the squared Frobenius
  budgets are about `2.164` and `2.174`, while the spectral norms are only about
  `1.104` and `1.142`;
- on `[961,1920]` versus `[1921,3840]`, the squared Frobenius budgets rise to
  about `2.730`, although the spectral norms remain about `1.212` and `1.215`;
- taking absolute values before the Schur product is much worse: at cutoff
  `1920` it gives products about `20.74` and `17.55`.

These values are route-selection diagnostics, not proof inputs. They show that
entrywise absolute values erase precisely the cancellation that the analytic
argument must retain.

The formal replacement uses the exact decomposition

\[
A=D+E_{\rm pole}+E_{\rm arch}+E_{\rm prime}.
\]

The diagonal matrix `D` has zero cross block. On the full three-shell union
`[N+1,4N]`, the remaining quadratic forms satisfy

\[
|Q_{E_{\rm pole}}(z)|\le\frac{13}{60}\|z\|_2^2,
\qquad
|Q_{E_{\rm arch}}(z)|\le\frac{63}{50}\|z\|_2^2,
\qquad
|Q_{E_{\rm prime}}(z)|\le\frac{10}{3}\|z\|_2^2.
\]

Hence the total error operator has the scale-independent form bound

\[
|Q_E(z)|\le \frac{481}{100}\|z\|_2^2.
\]

The new polarization theorem applies this full quadratic-form estimate to the
two block vectors `(r*x,y)` and `(r*x,-y)` for every real `r`. The resulting
discriminant inequality keeps the same operator coefficient and proves

\[
|\operatorname{cross}_E(x,y)|^2
 \le \left(\frac{481}{100}\right)^2
       \|x\|_2^2\|y\|_2^2.
\]

This avoids both the Frobenius loss and the absolute-entry Schur loss.

The actual index equivalence is also internal: `Fin (3*N)` is split as
`Fin N ⊕ Fin (2*N)`, corresponding exactly to
`[N+1,2N] ⊕ [2N+1,4N]`. Lean proves that the two diagonal blocks are the
literal cutoff-13 even or odd shell matrices and that the builder cross block
equals the total-error cross block.

## Closed large-scale adjacent-shell coefficient

Rather than flattening the shell reserve to `9/5`, the new module retains

\[
g(N)=\log N-\frac{19}{20}
 -\left(\frac{\operatorname{poleScale}(13)}{8\pi^2N}
       +\frac12+\frac{10}{3}\right).
\]

The already proved pole estimate gives the simpler lower envelope

\[
g(N)\ge \log N-5.
\]

Since `371293 = 13^5` and the elementary arctanh certificate gives
`log 13 > 64/25`, every `N >= 371293` satisfies

\[
g(N)\ge\frac{39}{5},\qquad g(2N)\ge\frac{39}{5}.
\]

The remaining scalar comparison is then exact rational arithmetic:

\[
\left(\frac{481}{100}\right)^2
 < \frac49\left(\frac{39}{5}\right)^2.
\]

Consequently, for every `N >= 371293`, both actual parity matrices on the
adjacent dyadic shells satisfy

\[
|\operatorname{cross}(x,y)|^2
 \le \frac49\,Q_{[N+1,2N]}(x)\,Q_{[2N+1,4N]}(y).
\]

This is a new analytic all-scale theorem, independent of the exploratory
floating-point values. It is still an adjacent-shell statement rather than the
full historical-core/new-shell estimate required by the terminal tower.

## Summable dyadic envelope

The scale-dependent gain is also retained formally. Set

\[
N_n=13^5 2^n=371293\cdot2^n,
\qquad
L_n=\frac{39}{5}+\frac{69}{100}n.
\]

The exact identities for `log (13^5 2^n)`, together with
`log 13 > 64/25` and `log 2 > 69/100`, prove

\[
L_n\le g(N_n),\qquad L_n\le g(2N_n).
\]

Define the relative envelope

\[
q_n=\frac{(481/100)^2}{L_n^2}.
\]

Lean now proves all three facts needed for a multiscale use of this sequence:

1. `q_n >= 0`;
2. `(481/100)^2 <= q_n g(N_n) g(2N_n)`;
3. `Summable q_n`.

For the last point, the denominator is rewritten as

\[
L_n=\frac{69}{100}\left(n+\frac{260}{23}\right),
\]

so summability follows directly from the real shifted `p=2` series already in
Mathlib. The final even and odd theorems apply this summable coefficient to the
literal adjacent-shell builder matrices. Thus the expected
`1/(log N)^2`, equivalently `1/n^2` on dyadic scales, is no longer only an
asymptotic heuristic.

## Principal Lean theorems

- `c13_centeredLogarithmicArchimedeanSymbol_abs_le`
- `logarithmicCvSArchimedeanEntry_reflected_eq`
- `logarithmicCvSArchimedeanEntry_sameSign_eq`
- `energy_abs_le_card_mul_of_entry_abs_le`
- `c13_evenRemainder_energy_abs_le_half`
- `c13_oddRemainder_energy_abs_le_half`
- `c13_logarithmicCvSPoleTail_le_thirteenSixtieth`
- `c13_shell_complete_scalar_reserve_ge_threeTwentyFive`
- `c13_shell_complete_scalar_reserve_ge_nineFifths`
- `c13_logarithmicCvSBuilderEvenShell_energy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderOddShell_energy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderEvenShell_energy_ge_nineFifths_normSq`
- `c13_logarithmicCvSBuilderOddShell_energy_ge_nineFifths_normSq`
- `c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_nineFifths_normSq`
- `c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_nineFifths_normSq`
- `relativeCoupling_fourNinth_of_nineFifthsHighGap`
- `c13_logarithmicCvSBuilderEvenTowerCross_relative_fourNinth_of_squaredNormBudget`
- `c13_logarithmicCvSBuilderOddTowerCross_relative_fourNinth_of_squaredNormBudget`
- `finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound`
- `c13EvenShellTotalError_energy_abs_le_fourHundredEightyOneHundredths`
- `c13OddShellTotalError_energy_abs_le_fourHundredEightyOneHundredths`
- `c13ShellDynamicGap_ge_log_sub_five`
- `c13EvenAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget`
- `c13OddAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget`
- `c13_operatorBudget_le_fourNinth_dynamicGap_product`
- `c13EvenAdjacentDyadicShellCrossEnergy_relative_fourNinth_of_ge_371293`
- `c13OddAdjacentDyadicShellCrossEnergy_relative_fourNinth_of_ge_371293`
- `c13DyadicGapLower_le_dynamicGap`
- `c13DyadicRelativeEnvelope_budget`
- `summable_c13DyadicRelativeEnvelope`
- `c13EvenDyadicShellCrossEnergy_relative_summableEnvelope`
- `c13OddDyadicShellCrossEnergy_relative_summableEnvelope`
- `c13EvenArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths`
- `c13OddArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths`
- `c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird`
- `c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird`
- `c13EvenPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth`
- `c13OddPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth`
- `c13EvenBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths`
- `c13OddBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths`
- `c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq`
- `c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq`
- `c13EvenBuilderCoreNewest_relative_of_coreFloor`
- `c13OddBuilderCoreNewest_relative_of_coreFloor`
- `c13CoreNewestRelativeEnvelope_budget`
- `tendsto_c13CoreNewestRelativeEnvelope_zero`
- `c13EvenBuilderDyadicCoreNewest_relative_vanishingEnvelope`
- `c13OddBuilderDyadicCoreNewest_relative_vanishingEnvelope`
- `exists_c13CoreNewestRelativeEnvelope_lt_fourNinth`
- `c13CoreHilbertKernel_energy_abs_le_four`
- `c13CoreReflectedHilbertLeading_energy_abs_le_two`
- `c13CoreArchimedeanSameSign_entry_sq_sum_le_oneOverNineM`
- `c13CoreArchimedeanSameSign_energy_abs_le_oneEighth`
- `c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520`
- `c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter`
- `c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter`
- `c13_logarithmicCvSBuilderEvenCore_energy_ge_oneTwentieth`
- `c13_logarithmicCvSBuilderOddCore_energy_ge_oneTwentieth`
- `c13EvenBuilderDyadicCoreNewest_relative_fourNinth`
- `c13OddBuilderDyadicCoreNewest_relative_fourNinth`
- `c13CoreArchimedeanSameSign_energy_abs_le_oneNinetieth`
- `c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840`
- `c13OddCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840`
- `c13EvenCoreArchimedeanRemainder_energy_abs_le_7723Over3840`
- `c13OddCoreArchimedeanRemainder_energy_abs_le_7723Over3840`
- `c13_logarithmicCvSBuilderEvenCore_energy_ge_1109Over3840`
- `c13_logarithmicCvSBuilderOddCore_energy_ge_1109Over3840`
- `c13CoreNewestRelativeEnvelope_1109Over3840_lt_fourNinth`
- `c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_ge_190`
- `c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_ge_190`

The corresponding nonnegativity adapters are also retained.

## Full historical-core/newest-shell advance

The multiscale triangle route is no longer the only available interface.  A
direct rectangular estimate now treats the complete historical band `(M,N]`
against the newest dyadic shell `(N,2N]`.  Its decisive arithmetic observation
is that, whenever `M <= p <= N < q <= 2N`,

\[
p(q-p)\ge N.
\]

After centering the cutoff-13 Archimedean symbol at `pi/4`, the same-sign
divided difference is therefore at most `1/(6N)`.  In the reflected entry, the
constant part gives the Hilbert term `1/(2(p+q)) <= 1/(2N)`, while the two
centered remainders combine exactly into a term bounded by `1/(12pq)`.  Since
`p >= M`, each rectangular Archimedean entry is bounded by

\[
\frac1N\left(\frac23+\frac1{12M}\right).
\]

There are at most `N^2` entries in the rectangle, so a direct
Frobenius--Cauchy estimate loses no power of the scale.  For `M >= 960`, Lean
closes the rational bound

\[
\frac23+\frac1{12M}\le\frac{667}{1000}.
\]

The pole term is transferred through the exact equivalence
`Fin (2*N-M) ~= Fin (N-M) ⊕ Fin N`; consequently it retains the one-block
constant `13/60` instead of being counted twice.  The prime translation block
retains `10/3`.  Thus the complete off-diagonal error amplitude is

\[
\frac{13}{60}+\frac{667}{1000}+\frac{10}{3}
 =\frac{4217}{1000}.
\]

The diagonal main term vanishes on this off-diagonal rectangle, and the new
Lean theorems identify the resulting block with the literal cutoff-13 even and
odd builder matrices.  Hence the estimate applies to the actual historical
core/newest-shell coupling rather than to a surrogate matrix.

The historical-core premise is now discharged in
`AsymptoticCoreHilbert.lean`.  The new proof splits the full Archimedean
remainder on every consecutive core `(M,M+L]` into a reflected half-Hilbert
kernel and two centered corrections.  With the weight

\[
h_p=p^{-1/2},
\]

elementary telescoping bounds for the low and high parts of a row give the
dimension-free Schur estimate

\[
\left|\sum_{p,q}\frac{x_px_q}{p+q}\right|
 \le 4\sum_p x_p^2.
\]

The reflected leading term therefore costs at most `2`.  The centered
reflected correction is a rank-one envelope costing at most `1/11520` above
`M=960`.  For the same-sign divided-difference kernel, the pointwise square
bound factors through

\[
D_{ij}=\mathbf 1_{i\ne j}|i-j|^{-2},
\qquad \sum_jD_{ij}\le4,
\]

and the telescoping reciprocal-square sum

\[
\sum_{p>M}p^{-2}\le M^{-1}.
\]

The first coarse adapter records `1/8`, but the Hilbert--Schmidt square bound
itself gives the sharper rational estimate `1/90` because `M >= 960`.  In both
parity sectors the complete centered residual is therefore bounded by

\[
\frac1{90}+\frac1{11520}=\frac{43}{3840}.
\]

The full Archimedean allowance becomes `7723/3840`.  Reallocating the old
allowance `1/2` in the scalar reserve then leaves the exact uniform core floor

\[
\frac95+\frac12-\frac{7723}{3840}
 =\frac{1109}{3840}\approx0.288802.
\]

Lean therefore proves, without any upper bound on the core length, that every
cutoff-13 even and odd historical-core builder beginning at `M >= 960` has
Euclidean coercivity at least `1109/3840`.

Using this proved floor and the newest-shell dynamic gap, the complete relative
coefficient is bounded by

\[
q_n^{\rm core/new}
 =\frac{(4217/1000)^2}{(1109/3840)L_n},
\qquad
L_n=\frac{39}{5}+\frac{69}{100}n.
\]

Lean proves that this envelope is nonnegative, pays the exact operator budget,
tends to zero, and is already strictly below `4/9` for every `n >= 190`.
The final theorems are unconditional and apply to the literal even and odd
builder blocks.  This coefficient behaves like `1/n`; it is not the summable
`1/n^2` adjacent-shell envelope, and the two statements remain separate.

For reference, the existing finite-channel aggregation theorem
`relativeCoupling_of_finsetChannelBudgets` sums the relative budgets `q_i`
themselves, not their square roots.  The direct rectangular argument bypasses
that aggregation altogether for the full old-core channel.

## Pi-weighted Hilbert upgrade

The elementary constant `4` above is now retained only as a dependency-light
fallback.  `AsymptoticCoreHilbertPi.lean` formalizes the sharp weighted row
estimate.  For `p > 0`, set

\[
f_p(t)=\frac1{(p+t)\sqrt t}.
\]

The module proves that `f_p` is antitone on every positive ray and evaluates
its improper integral exactly:

\[
\int_0^\infty f_p(t)\,dt=\frac{\pi}{\sqrt p}.
\]

The proof uses Mathlib's change-of-variables theorem twice.  First `t=u^2`
turns the integrand into `2/(p+u^2)`; then `u=sqrt(p)*v` reduces it to the
standard identity

\[
\int_0^\infty\frac{dv}{1+v^2}=\frac\pi2.
\]

The integral comparison theorem for antitone functions then gives, for every
finite consecutive interval above `M >= 1`,

\[
\sum_q\frac{q^{-1/2}}{p+q}\le\frac\pi{\sqrt p}.
\]

Feeding this row certificate into the existing weighted-Schur theorem replaces
the quadratic-form constant `4` by `pi`, so the reflected half-Hilbert term
costs only `pi/2`.  To keep the rest of the budget in exact rational arithmetic,
the formal chain uses Mathlib's certified decimal upper bound on `pi` to prove

\[
\frac\pi2<\frac{11}{7}.
\]

The centered residual is unchanged.  Hence the complete Archimedean loss is

\[
\frac{11}{7}+\frac{43}{3840}
=\frac{42541}{26880},
\]

and the uniform historical-core coercive floor improves to

\[
\frac95+\frac12-\frac{42541}{26880}
=\frac{19283}{26880}\approx0.7173735.
\]

This is more than twice the previous `1109/3840` floor and applies to every
core length in both parity sectors.  Substitution into the exact full
core/newest envelope gives

\[
q_n^{\rm core/new}
=\frac{(4217/1000)^2}{(19283/26880)L_n}.
\]

Lean proves that this coefficient is strictly below `4/9` for every `n >= 70`.
It also proves that the same exact rational envelope is still at least `4/9`
at `n = 69`, so `70` is the first integer reached by this particular envelope.
The final even and odd theorems act on the literal builder blocks.  Since
`c13DyadicShellBase n = 371293 * 2^n`, this is an eventual analytic threshold,
not a claim about the unresolved finite prefix.

Principal new theorems:

- `integral_hilbertPiIntegrand`
- `integrableOn_hilbertPiIntegrand`
- `c13CoreHilbertKernel_row_le_pi`
- `c13CoreHilbertKernel_energy_abs_le_pi`
- `c13CoreReflectedHilbertLeading_energy_abs_le_elevenSevenths`
- `c13EvenCoreArchimedeanRemainder_energy_abs_le_42541Over26880`
- `c13OddCoreArchimedeanRemainder_energy_abs_le_42541Over26880`
- `c13_logarithmicCvSBuilderEvenCore_energy_ge_19283Over26880`
- `c13_logarithmicCvSBuilderOddCore_energy_ge_19283Over26880`
- `c13CoreNewestRelativeEnvelope_19283Over26880_lt_fourNinth`
- `c13CoreNewestRelativeEnvelope_19283Over26880_ge_fourNinth_at_69`
- `c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70`
- `c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70`

## Exact finite-matrix to boundary-Weyl adapter

`FiniteMatrixBoundaryWeylAdapter.lean` removes a previously implicit type
conversion.  For a concrete matrix on a sum index `iota ⊕ kappa`, it defines:

- the left-left and right-right matrices;
- the averaged rectangular cross matrix used by
  `finiteMatrixBlockCrossEnergy`;
- their bilinear maps on the actual Hilbert spaces
  `EuclideanSpace R iota` and `EuclideanSpace R kappa`.

The coordinate identities are exact:

```text
lowForm(x,x)  = finiteMatrixBlockBaseEnergy A x,
highForm(y,y) = finiteMatrixBlockTailEnergy A y,
coupling(x,y) = finiteMatrixBlockCrossEnergy A x y.
```

A `FiniteMatrixRelativeEnergyCertificate A q` now packages symmetry,
nonnegativity of both diagonal energies, and the relative cross inequality.
The theorem
`finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate` feeds that
package directly into `boundaryWeyl_mono_of_relativeEnergyCoupling`; its
positive-response companion is also formalized.  Hence no continuity norm,
matrix convention, or factor of two is hidden between the literal CvS block
and the abstract response theorem.

For the complete `(960,N] ⊕ (N,2N]` builder, both parity certificates are
constructed for `n >= 70`, and the even/odd boundary-Weyl monotonicity and
positivity wrappers leave only the three weak resolvent equations and the
finite positive response as explicit hypotheses.

## Adjacent-half multiband breakthrough

The threshold `n >= 70` comes from charging the entire historical interval
`(960,N]` the smallest mode-`960` gap.  It is not intrinsic to the newest
coupling.  `AsymptoticAdjacentCoreHilbertPi.lean` begins a different route:
split the historical interval into dyadic bands and first isolate the half
adjacent to the newest shell,

```text
(floor(N/2), N]  against  (N,2N].
```

At the first analytic scale `N = 13^5 = 371293`, one has

```text
floor(N/2) >= 6 * 13^4 = 171366.
```

The exact factorization

```text
log(6 * 13^4) = log 2 + log 3 + 4 log 13
```

together with the already proved rational bounds
`log 2 > 69/100`, `log 3 > 109/100`, and `log 13 > 64/25`
gives `log(floor(N/2)) > 12`.  After the pole, prime, and new pi-weighted
Archimedean losses, Lean obtains the much larger adjacent-core gap

```text
59/10 = 5.9.
```

The newest shell already has gap `39/5 = 7.8`.  Exact rational arithmetic
then verifies

```text
(4217/1000)^2
  <= (2/5) * (59/10) * (39/5).
```

Consequently the literal complete even and odd couplings between the adjacent
historical half and the newest shell satisfy relative coefficient `2/5` for
**every** `n >= 0`.  This simultaneously removes the `n >= 70` threshold for
the dominant adjacent band and improves its coefficient from `4/9` to `2/5`.
The corresponding Euclidean relative-energy certificates are already built,
so this block can be inserted directly into the boundary-Weyl form adapter.

This does not yet aggregate the older bands.  It changes the remaining
analytic target substantially: the adjacent half consumes `2/5`, leaving
`3/5` of a unit relative budget for all earlier bands.  Those bands are
separated from the newest shell by a distance comparable to their scale, so
the next source theorem should exploit the explicit off-diagonal prime
translation denominator and the existing centered Archimedean decay rather
than reusing the global `10/3` prime norm.

Principal additional theorems:

- `twelve_lt_log_nat_of_ge_six_mul_thirteenPowFour`
- `c13_adjacentPiCore_scalar_reserve_ge_fiftyNineTenths`
- `c13_logarithmicCvSBuilderEvenAdjacentCore_energy_ge_fiftyNineTenths`
- `c13_logarithmicCvSBuilderOddAdjacentCore_energy_ge_fiftyNineTenths`
- `c13_completeCrossBudget_le_twoFifths_adjacentGapProduct`
- `c13EvenBuilderDyadicAdjacentCoreNewest_relative_twoFifths`
- `c13OddBuilderDyadicAdjacentCoreNewest_relative_twoFifths`
- `finiteMatrixCouplingEuclideanForm_eq_crossEnergy`
- `finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate`
- `c13EvenBuilderDyadicAdjacentCoreNewest_relativeEnergyCertificate`
- `c13OddBuilderDyadicAdjacentCoreNewest_relativeEnergyCertificate`

## Full analytic core anchored at `3840`

The adjacent-half split reveals a second improvement that aligns directly with
the rigorous finite frontier.  The old uniform pole charge `13/60` was proved
at `M=960` and then reused for every larger historical start.  Its source
formula actually decays as `1/M`.  At `M >= 3840`, the existing rational pole
scale bound and `pi > 3` give the sharper formal estimate

```text
poleTail(M) <= 51/1000.
```

Also,

```text
3840 = 2^8 * 3 * 5,
```

so the elementary logarithm bounds already in the repository imply

```text
log M > 8*(69/100) + 109/100 + 8/5 = 821/100.
```

Combining this with the pi-weighted Archimedean loss and the prime bound gives
a complete historical-core coercive floor

```text
229/100 = 2.29
```

for every builder block beginning at `M >= 3840`.  The same retained pole
decay reduces the complete cross amplitude from `4217/1000` to the exact sum

```text
51/1000 + 667/1000 + 10/3 = 6077/1500.
```

At the first analytic shell, exact arithmetic verifies

```text
(6077/1500)^2
  <= (23/25) * (229/100) * (39/5).
```

Therefore the literal complete core `(3840,N]`, not merely its adjacent half,
has relative coefficient `23/25 < 1` against `(N,2N]` for every
`N = 371293*2^n`, including `n=0`.  Both parity sectors and their Euclidean
relative-energy certificates are formalized.  This replaces the previous
`n>=70` eventual full-core threshold by a scale-free coefficient once the
historical start is moved from `960` to the already certified cutoff `3840`.

It does not by itself identify the low block `[1,3840]` with the analytic core
or prove their cross estimate.  Its importance is architectural: the finite
certificate and analytic theorem now share the same anchor, and the remaining
bridge is a fixed-prefix-to-remote-core channel rather than seventy unproved
dyadic analytic steps.

Principal anchor theorems:

- `eightHundredTwentyOneHundredths_lt_log_nat_of_ge_3840`
- `c13_logarithmicCvSPoleTail_le_fiftyOneThousandths`
- `c13_anchor3840PiCore_scalar_reserve_ge_twoHundredTwentyNineHundredths`
- `c13_logarithmicCvSBuilderEvenAnchor3840Core_energy_ge_229Over100`
- `c13_logarithmicCvSBuilderOddAnchor3840Core_energy_ge_229Over100`
- `c13EvenCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500`
- `c13OddCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500`
- `c13_anchor3840_completeCrossBudget_le_twentyThreeTwentyFifths_gapProduct`
- `c13EvenBuilderDyadicAnchor3840CoreNewest_relative_23Over25`
- `c13OddBuilderDyadicAnchor3840CoreNewest_relative_23Over25`
- `c13EvenBuilderDyadicAnchor3840CoreNewest_relativeEnergyCertificate`
- `c13OddBuilderDyadicAnchor3840CoreNewest_relativeEnergyCertificate`

## Distance-sensitive fixed-prefix prime bridge

The first source component of the remaining `[1,3840]` bridge is now closed
in `PrimeTranslationSeparatedBands.lean`.  The global prime operator bound
`10/3` is intentionally insensitive to Fourier distance.  For a fixed prefix
and a remote shell that loss is artificial: the exact truncated-translation
formula gives, whenever `n != m`,

```text
|T_y(n,m)| <= 2 / (pi * |n-m|).
```

The eight cutoff-13 von-Mangoldt weights are each below their previously
certified rational envelopes, whose exact sum is

```text
491/1000 + 635/1000 + 347/1000 + 720/1000
  + 736/1000 + 246/1000 + 367/1000 + 724/1000
= 2133/500.
```

Using `pi > 3`, Lean therefore proves the simple scalar kernel bound

```text
|Prime13(n,m)| <= 3 / |n-m|.
```

The positive-mode even and odd parity entries contain both the difference and
sum denominators.  For a row in `[1,F]` and a column in `(N,2N]`, both are at
least `N+1-F`, hence

```text
|PrimeParity(i,j)| <= 6 / (N+1-F).
```

A rectangular Cauchy--Schwarz estimate retains the actual `F*N` entry count,
instead of replacing the rectangle by an `N*N` square.  The resulting squared
Euclidean coefficient is

```text
C(F,N) = F*N*(6/(N+1-F))^2.
```

For the certified finite frontier and first analytic shell,

```text
C(3840,371293) = 0.3801408381... < 2/5.
```

The decimal is explanatory only; Lean proves the rational inequality after
clearing the positive denominator.  More importantly, the coefficient has an
exact all-scale transport law

```text
C(F,2N) <= (1/2)*C(F,N)       (1 <= F <= N),
```

so that

```text
C(3840,371293*2^k) <= (2/5)*(1/2)^k.
```

This geometric envelope is proved for the actual CvS prime-error sign
convention and for the averaged finite-matrix cross coordinate in both parity
sectors.  It is the first fully formal fixed-prefix-to-remote-shell source
estimate.  In particular, the prime part of the finite/analytic bridge is no
longer represented by the nondecaying `10/3` norm.

Principal separated-band theorems:

- `abs_truncatedTranslationFourierEntry_le_two_div`
- `c13_logarithmicPrimeWeight_sum_lt_2133Over500`
- `c13_finitePrimeTranslationFourierEntry_abs_le_three_div`
- `c13_fixedRemoteEvenPrimeEntry_abs_le_six_div_gap`
- `c13_fixedRemoteOddPrimeEntry_abs_le_six_div_gap`
- `rectangular_bilinear_sq_le_card_product_of_entry_abs_le`
- `c13FixedRemotePrimeCoefficient_two_mul_le_half`
- `c13FixedRemotePrimeCoefficient_dyadic_le`
- `c13_fixed3840_remote_primeCoefficient_le_twoFifths`
- `c13_fixed3840_remote_primeCoefficient_dyadic_le`
- `c13_fixed3840_remoteEvenPrimeErrorCrossEnergy_sq_le_dyadic`
- `c13_fixed3840_remoteOddPrimeErrorCrossEnergy_sq_le_dyadic`

## Rank-one fixed-prefix pole bridge

The second source component is now closed in `PoleSeparatedBands.lean`.
The decisive observation is that the pole matrix is not merely bounded by a
small global norm: in each parity sector it is exactly rank one.  If `u` is
the appropriate pole weight, its fixed-prefix/remote cross coordinate factors
as

```text
(2*poleScale) * (sum_[1,F] u_n*x_n) * (sum_(N,2N] u_m*y_m),
```

up to the harmless odd-parity sign.  Applying Cauchy separately on the two
bands retains the remote reciprocal-square decay.  The formal elementary
bounds are

```text
sum_[1,F] u_n^2       <= 1/72,
sum_(N,2N] u_m^2      <= 1/(144*N),
logarithmicCvSPoleScale 13 <= 13872.
```

They imply the squared Euclidean coefficient

```text
P(N) = (2*poleScale)^2 * (1/72) * (1/(144*N)).
```

At the first analytic scale, exact rational arithmetic in Lean gives

```text
P(371293) <= 1/5.
```

Moreover `P(2*N) = P(N)/2` exactly, hence

```text
P(371293*2^k) <= (1/5)*(1/2)^k.
```

The theorem is stated for the actual even and odd pole matrices and those
matrices are proved by reflexivity to be component zero of the existing CvS
builder error vector.  Thus both the prime and pole parts of the finite to
analytic bridge now decay geometrically; neither uses the old global operator
loss.

Principal pole-band theorems:

- `fixedPrefix_inv_sq_sum_le_two`
- `fixedPrefixPoleOddWeight_sq_sum_le_oneSeventySecond`
- `fixedPrefixPoleEvenWeight_sq_sum_le_oneSeventySecond`
- `remotePoleOddWeight_sq_sum_le_oneOver144N`
- `remotePoleEvenWeight_sq_sum_le_oneOver144N`
- `finiteMatrixBlockCrossEnergy_rankOne_sq_le`
- `c13_fixedRemoteEvenBuilderError_zero`
- `c13_fixedRemoteOddBuilderError_zero`
- `c13_fixedRemotePoleCoefficient_le_oneFifth`
- `c13FixedRemotePoleCoefficient_dyadic_eq`
- `c13_fixed3840_remoteEvenPoleCrossEnergy_sq_le_dyadic`
- `c13_fixed3840_remoteOddPoleCrossEnergy_sq_le_dyadic`

## Complete fixed-prefix builder bridge

The Archimedean component and the literal three-source builder cross block are
now closed in `ArchimedeanSeparatedBands.lean`.  The new input at the bottom of
the spectrum is a premise-free rational estimate

```text
|centeredArchimedeanSymbol13(x)| <= 2/5,       x >= 1.
```

It follows directly from the proved digamma Euler--Maclaurin model, the
cutoff-13 geometric-mass bound, `log 13 < 513/200`, and `pi > 3`; no finite
floating-point table is used.  For a fixed mode `a` and remote mode `b`, the
same-sign and reflected entries retain the Fourier gap:

```text
|ArchSame(a,b)|       <= (13/60)/(N+1-F),
|ArchReflected(a,-b)| <= (43/60)/(N+1-F).
```

Both parity combinations therefore fit below the unit kernel

```text
|ArchParity(i,j)| <= 1/(N+1-F).
```

Rectangular Cauchy--Schwarz gives

```text
A(F,N) = F*N*(1/(N+1-F))^2
       = (1/36)*C_prime(F,N).
```

Consequently, at `F=3840`,

```text
A(3840,371293*2^k) <= (1/90)*(1/2)^k.
```

The Archimedean matrix is proved by reflexivity to be builder-error component
one.  Combining it with component zero (pole) and component two (the actual
prime-error sign convention), and using rational square-root majorants

```text
sqrt(1/5)  <= 448/1000,
sqrt(1/90) <= 106/1000,
sqrt(2/5)  <= 633/1000,
```

produces the complete literal builder estimate

```text
cross_builder(k)^2
  <= (1187/1000)^2 * (1/2)^k * ||x||^2 * ||y||^2.
```

The diagonal Archimedean matrix has zero fixed/remote cross entry, so the full
builder cross coordinate is proved equal to the three-source total error
coordinate, rather than merely compared to an auxiliary matrix.  Finally,

```text
(1/2)^k <= ((3/4)^k)^2
```

gives a summable amplitude envelope

```text
|cross_builder(k)| amplitude <= (6/5)*(3/4)^k,
sum_k (6/5)*(3/4)^k = 24/5.
```

This is the first formal, geometrically summable estimate for the complete
fixed-prefix-to-remote CvS builder channel in both parity sectors.

Principal complete-bridge theorems:

- `c13_centeredLogarithmicArchimedeanSymbol_abs_le_twoFifths`
- `c13_fixedRemoteArchimedeanSameSignEntry_abs_le`
- `c13_fixedRemoteArchimedeanReflectedEntry_abs_le`
- `c13_fixedRemoteEvenArchimedeanEntry_abs_le_one_div_gap`
- `c13_fixedRemoteOddArchimedeanEntry_abs_le_one_div_gap`
- `c13_fixedRemoteEvenBuilderError_one`
- `c13_fixedRemoteOddBuilderError_one`
- `c13_fixed3840_remoteArchimedeanCoefficient_dyadic_le`
- `c13_fixed3840_remoteEvenArchimedeanCrossEnergy_sq_le_dyadic`
- `c13_fixed3840_remoteOddArchimedeanCrossEnergy_sq_le_dyadic`
- `c13_fixedRemoteEvenBuilderError_sum_eq_total`
- `c13_fixedRemoteOddBuilderError_sum_eq_total`
- `c13_fixed3840_remoteEvenBuilderCrossEnergy_sq_le_dyadic`
- `c13_fixed3840_remoteOddBuilderCrossEnergy_sq_le_dyadic`
- `c13_fixed3840_remoteEvenBuilderCrossEnergy_sq_le_summableAmplitude`
- `c13_fixed3840_remoteOddBuilderCrossEnergy_sq_le_summableAmplitude`
- `summable_c13_fixedRemoteBuilderDyadicAmplitude`
- `tsum_c13_fixedRemoteBuilderDyadicAmplitude`

## Next formal boundary

The fixed historical-core floor and the full old-core/new-shell estimate are
now closed.  The next boundary is structural rather than an unproved local
operator estimate:

1. turn the rigorous finite computation through `3840` into an explicit Lean
   coercivity certificate, then close the remaining near bridge from that
   prefix into the initial analytic core `(3840,371293]`; the theorem above
   already controls every later dyadic remote shell;
2. combine the finite-prefix certificate, the anchored analytic-core
   `23/25` result, and the new summable fixed/remote builder channel in a
   multiblock Schur certificate; retain the adjacent `2/5` decomposition as a
   reserve-rich route for the near bridge;
3. instantiate the now-exact Euclidean form adapter with the actual finite and
   split weak resolvent equations, then connect its monotonic response to
   `BoundaryWeylCumulative`, `BoundaryGapNoCrossing`, and
   `ParityOrderContinuation`;
4. formulate the infinite dyadic block limit using the new explicit
   `(6/5)*(3/4)^k` summable amplitude, so finite-core coercivity passes to the
   limiting self-adjoint form without reintroducing a divergent square-root
   budget;
5. retain the adjacent-shell summable theorem as a separate tool for any
   later cumulative-residue estimate that genuinely requires summability.

This is a substantive new no-crossing ingredient, but the global continuation
and limiting identifications listed above are still separate obligations; the
result is therefore not, by itself, a proof of RH.

## 2026-09-02: the initial analytic adjacent shell now has a subunit coefficient

The previous whole-core Archimedean rectangle estimate charged every entry by
the same envelope and produced amplitude `667/1000`.  That estimate is stable
for an arbitrarily long historical core, but it is unnecessarily expensive for
the first genuinely adjacent pair

```text
low  = (M,2M],
high = (2M,4M].
```

`AdjacentArchimedeanHilbertSchmidt.lean` keeps the exact reflected formula and
splits the cross matrix into three pieces:

```text
same-sign centered quotient,
1/(2*(p+q)) reflected Hankel leading term,
reflected centered quotient.
```

The same-sign piece retains the distance `q-p`.  For each low row its squared
distance kernel is bounded by the elementary reciprocal-square mass

```text
sum_{j>=1} 1/j^2 <= 2,
```

which yields squared coefficient `1/(18*M)`.  The centered reflected piece
retains its `1/(12*p*q)` envelope and has squared coefficient
`1/(288*M^2)`.  The leading reflected rectangle has exactly `M*(2M)` entries,
each at most `1/(6M)`, so its squared Hilbert--Schmidt coefficient is `1/18`.
At `M >= 3840` the three rational amplitude majorants are therefore

```text
same-sign centered       <= 39/10000,
reflected leading        <= 237/1000,
reflected centered       <= 1/10000,
total Archimedean        <= 241/1000.
```

This replaces `667/1000` on the adjacent geometry without changing the exact
CvS builder matrix.  Adding the anchored pole and prime channels gives

```text
51/1000 + 241/1000 + 10/3 = 2719/750.
```

The dynamic shell gaps are also kept at the first scale.  Lean proves, for
every `M >= 3840`,

```text
c13ShellDynamicGap(M)   >= 27/8,
c13ShellDynamicGap(2*M) >= 813/200,
(2719/750)^2
  <= (24/25) * (27/8) * (813/200).
```

Consequently both literal even and odd builder blocks satisfy

```text
cross(M,2M)^2 <= (24/25) * baseEnergy * tailEnergy.
```

Principal new theorems:

- `c13AdjacentSameSignBilinear_sq_le`
- `c13AdjacentReflectedLeadingBilinear_sq_le`
- `c13AdjacentReflectedCenteredBilinear_sq_le`
- `c13EvenArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths`
- `c13OddArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths`
- `c13EvenBuilderAdjacentCrossEnergy_sq_le_2719Over750`
- `c13OddBuilderAdjacentCrossEnergy_sq_le_2719Over750`
- `c13EvenBuilderAdjacent_relative_24Over25`
- `c13OddBuilderAdjacent_relative_24Over25`

This removes the first-scale adjacent-shell obstruction at `3840`.  The next
formal step is to compose the finitely many dyadic blocks through a cutoff
beyond `371293`, then pass coercivity to the principal restriction ending
exactly at `371293`.  That multiblock composition and the later infinite limit
remain distinct obligations, so this result is a stronger bridge rather than
a completed RH proof.

## 2026-09-02: sharp constants expose a `3/40` adjacent reserve

`AdjacentArchimedeanSharpGap.lean` revisits only the constants in the preceding
operator proof; it does not weaken or replace any matrix identity.  Mathlib's
kernel-checked decimal bounds give

```text
log(3840) = 8*log(2) + log(3) + log(5) > 20633/2500,
pi > 314/100.
```

Together with `logarithmicCvSPoleScale 13 <= 13872`, the pole amplitudes improve
to `229/5000` at `M` and `229/10000` at `2M`.  The literal three-source
amplitude and the two dynamic gaps become

```text
229/5000 + 241/1000 + 10/3 = 27151/7500,
c13ShellDynamicGap(M)   >= 428/125,
c13ShellDynamicGap(2*M) >= 207/50.
```

Lean then closes the exact rational budget

```text
(27151/7500)^2 <= (37/40) * (428/125) * (207/50),
```

so both parity blocks satisfy

```text
cross_builder(M,2M)^2 <= (37/40) * baseEnergy * tailEnergy.
```

This retains `3/40` of local relative-energy budget, compared with `1/25` in
the first proof.  The main exported endpoints are
`c13EvenBuilderAdjacent_relative_37Over40` and
`c13OddBuilderAdjacent_relative_37Over40`; their proof dependencies are only
standard Lean quotient/extensionality principles.

Scope is important: this theorem controls the analytic adjacent pair
`(M,2M] x (2M,4M]`, beginning with `(3840,7680] x (7680,15360]`.  It does not
yet control the different first rectangle `[1,3840] x (3840,7680]`.  That
finite-prefix-to-first-shell bridge, followed by finite multiblock assembly and
the infinite boundary-Weyl limit, remains the active structural boundary.

## 2026-09-02: the finite prefix now crosses the first analytic seam

The remaining rectangle `[0,3840] x (3840,7680]` has now passed a full Arb
recursive-shell certificate, rather than only a floating midpoint probe.  The
first attempt exposed and repaired a provenance bug in
`certify_direct_parity_relative_shell.py`: a rigorous core generated by the
direct-parity script was incorrectly treated as if it had necessarily been
generated by `certify_preconditioned_relative_shell.py`.  The validator now
matches the embedded SHA-256 against both supported source generators (including
the recorded Git blob) before accepting the core.  Both the older
preconditioned-core route and the direct-parity continuation replay successfully.

Using the already certified N=3840 core, 192-bit Arb intervals, and exact
dyadic preconditioners, the new run proves

```text
q < 249/250,
rho < 1/12,
shift <= -1/1024,
cutoff 3840 -> 7680,
```

in both reflection parities.  Every verified solve residual contains zero:
`14,749,440/14,749,440` entries in the even sector and
`14,745,600/14,745,600` in the odd sector.  Exact congruence followed by
Gershgorin gives `3840/3840` strictly positive rows in each sector; the minimum
margin midpoint is approximately `0.9999999999999988`, while the largest
reported interval radius is below `1.85e-45`.

Local reproducibility record:

```text
JSON SHA-256  = 32FF3DEA7F17F65D9DE23DCE784B8CD142D08E282C4C6EC9611F5CF9E846376D
even basis    = 38DB000276B903CBD9BAFADFA697ED724C4EFBA02B54EDA4931E114EDD475857
odd basis     = 69C2D741327608FCF8E8AC4ADCDB629A20A0B7114E024E5BA84F5BC0FADEADDB
even transcript = 1C1000C16B230ADBD299C377D4FA61383E0052D67BEDB880FF9C479AC5F511C9
odd transcript  = 9742710B2F869E35F0E72039B3BDF2A738F2FEE20B8D00CEFD3B51C0CCCB5135
```

The workflow now regenerates and uploads the JSON plus both 3840-square exact
dyadic bases.  This closes the finite-prefix-to-first-shell seam.  The next
boundary is no longer `[0,3840] -> (3840,7680]`; it is the two-channel step into
`(7680,15360]`: combine the new `37/40` adjacent channel from `(3840,7680]`
with a separately controlled historical channel from `[0,3840]`, then iterate
the multiblock transport toward `371293`.

## 2026-09-02: weighted multiblock closure leaves `1/1080`

`FirstAnalyticMultiblockBudget.lean` now performs the exact two-source
composition required at the next step.  The adjacent analytic block costs
`37/40`, while the already formal historical dyadic adapter costs `2/27`; a
weighted Cauchy square proves that their summed cross form costs only the sum
of those coefficients:

```text
37/40 + 2/27 = 1079/1080 < 1.
```

The resulting reserve is exactly `1/1080`.  Concrete even and odd endpoints
consume the actual cutoff-13 adjacent builder, the `1/30` historical geometric
envelope, and, in the odd sector, the independent `1/384` fixed-block budget.
This removes a purely algebraic multiblock obstruction that would have survived
with the older adjacent coefficient `24/25`.

A separate N=15360 midpoint diagnostic confirms the intended grouping: total
historical channels all contract by a factor below `1/2`, but an isolated
Archimedean component need not.  The combined Archimedean-plus-prime Loewner
group does contract below `1/2`, and the old odd `[1,20]` block must be kept as
a structured total to preserve cancellation.  These diagnostic observations
guide the next source-level proof; they are not imported into Lean.  What
remains is the uniform concrete half-transport theorem and then the infinite
boundary--Weyl passage, not additional budget arithmetic.

## 2026-09-02: actual historical-shell half transport is connected

`HistoricalCombinedLoewnerTransport.lean` converts the N=15360 architectural
observation into a kernel-checked matrix theorem.  On `(B,2B]` to `(N,2N]` it
keeps the Archimedean and prime terms inside one normalized odd Loewner symbol,
proves exact `N -> 2N` halving of the fixed-source symbol-square matrix budget,
and normalizes the result by the premise-free dynamic cutoff-13 shell energies.
The only remaining Loewner inputs are the explicitly stated weighted symbol
square bound and preceding scalar budget.

The same file improves the rational pole treatment from a fixed-prefix mass to
two shell masses.  Consequently its squared coefficient is `O(1/(B*N))` and
halves exactly in the target scale.  Lean then identifies the literal builder
cross form as `pole - combinedLoewner` and combines the two transported pieces
at amplitude level, producing `(ampPole + ampLoewner)^2` without a factor-two
triangle loss.  Both parities have complete actual-matrix endpoints.

Thus the regular historical-shell representation and transport layer is no
longer open.  The remaining work is scalar and global: internalize/consume the
uniform combined-symbol estimate, discharge the early finite bridge budgets,
retain the exceptional old odd block as one structured total, sum all source
shells, and pass to the infinite boundary--Weyl limit.

## 2026-09-02: full-builder Loewner closure removes the two-source split

`FullBuilderLoewnerTransport.lean` strengthens the preceding transport layer.
The rational pole kernel is exactly the Loewner quotient of

```text
-scale * x / (a + b*x^2).
```

Hence the actual `pole - Archimedean - prime` remote block is a single odd
Loewner symbol, not merely a sum of one Loewner channel and one rank-two
channel.  Lean proves the equality entrywise, at the bilinear cross-energy
level, and for both parity compressions.

This gives exact `q/2` transport for the complete builder, iterates to
`q*(1/2)^k`, and connects any finite family of literal historical-shell
matrices to the existing geometric-budget summation theorem with total cost at
most `2*leading`.  It also preserves the cancellation in the old odd `[1,20]`
band that made the two-piece triangle route look exceptional.  The N=15360
midpoint data show the size of that distinction (`5.07e-4` actual versus
`1.10e-2` after the two-piece triangle), but no midpoint quantity enters the
Lean proof.

The regular multiscale representation, half transport, arbitrary-distance
iteration, and finite-family composition are now closed.  Remaining work is
to certify the scalar full-symbol square sums/base budgets, attach the finitely
many bands below the analytic `960` threshold to their finite energy
certificates, and complete the recursive/infinite boundary-Weyl passage.

## 2026-09-02: the scalar full-symbol constant falls below one tenth

`FullBuilderSymbolDyadicL2.lean` resolves the regular scalar square-sum part of
the preceding boundary.  It proves the rational-pole symbol bound
`|P(x)| <= 1/(4*x)` and the dyadic weighted tail `1/(32*N^3)` directly in
Lean.  It then observes that the literal combined Loewner symbol is not the raw
Arb symbol but its Fourier normalization `F/pi`.  The formal inequality
`pi > 3.14` converts the Arb target `97/100` into the historical-symbol target
`2425/24649`.

A deliberately asymmetric Young inequality, with weights `3001/3000` and
`3001`, assigns almost all slack to the cubic pole term.  Exact arithmetic at
the monotone endpoint `N=1920` then yields the uniform result

```text
full builder dyadic symbol budget < 197/2000 < 1/10.
```

This is more than a cosmetic replacement of the provisional constant `1`:
the rectangular source budget and every transported regular historical
coefficient now enter with a greater-than-tenfold improvement.  Both actual
parity-compressed builder matrices have direct corollaries consuming the raw
`97/100` certificate and transporting the sharper budget by `q*(1/2)^k`.

The external 256-bit replay passed with raw scaled upper
`0.9692102614364212589966291674788481...`; its artifact SHA-256 is
`AADBBCD025B864902FD2634F54DB546C8364723967D8C7EAEBF4ABDACC368AFD`.
The interval certificate remains an explicit scalar input to the Lean adapter,
while all normalization, pole absorption, endpoint monotonicity, and transport
algebra are theorem-checked.  The next obstruction is therefore the base
rectangular budget/finitely many early bands, followed by recursive reserve
closure and the infinite boundary-Weyl passage.

## 2026-09-02: sharp parity moments close the regular rectangular channel

The apparent base rectangular obstruction came from a lossy common estimate,
not from the complete builder itself.  `SharpParityFullBuilderTransport.lean`
uses the exact even and odd reflected Loewner numerators.  Under `2p<=q`, the
even channel retains `p^2*f(p)^2/q^4`, while the odd channel retains
`p^2*f(q)^2/q^4`; neither term is replaced by an unsuppressed `q^-2` mass.

Combining these formulas with the sharp weighted full-symbol constant
`197/2000` and the newly certified raw unweighted average `<2` produces the
exact base entry-square constants

```text
even: 499/1125,
odd:  1037/2250.
```

The worse odd value is still strictly below
`(1/30)*(428/125)*(207/50)`.  Hence both literal parity matrices satisfy the
required `1/30` relative-energy estimate at `N=4B` for every regular
`B>=3840`.  At `N=4B*2^k`, the proof propagates the actual entry moments with
coefficient `(1/30)*2^(-k)` and packages any finite regular family inside the
existing `2/27` previous-core budget.  This route does not consume the older
generic `rectangularSymbolSquareBudget` premise.

The current 256-bit affine-prefix replay gives unweighted average upper
`1.9129521415701273581...`, with slack `0.0870478584298726419...` below `2`;
the 384-bit replay returns the same enclosure at higher precision.  The
weighted `97/100` conclusion and this unweighted `2` conclusion are now emitted
together, ensuring that the two moments used by Lean refer to one source
certificate and one cutoff-13 symbol.

The next live boundary is finite/global rather than regular-rectangular:
attach the below-threshold bands and the odd fixed block to their exact energy
coordinates, then identify the resulting recursive shell form with the
infinite boundary-Weyl operator and pass to the uniform limit.

## 2026-09-02: weighted parity numerators reach the natural 960 coercive floor

`SharpParityLowFrontierTransport.lean` shows that the previous `B>=3840`
source cutoff was not intrinsic.  The even numerator is weighted
`(3/2,3)`, while the odd numerator is weighted `(3,3/2)`, matching which term
carries the remote target symbol.  Their dyadic Frobenius budgets are bounded
by `(8/25)*2^(-k)` as soon as `k>=1`.

Independently, the sharp pole-symbol work already implies

```text
poleScale/(8*pi^2*B) <= 1/(2B).
```

Together with exact logarithm bounds this yields builder-energy floors `2` on
every source shell `B>=960` and `24/5` on every target shell `T>=15360`.
The identity

```text
(1/30) * 2 * (24/5) = 8/25
```

then closes both actual parity matrices at every positive shell distance; the
zero-distance historical channel is even easier because `T>=15360` forces
`B>=3840`.  Hence all regular historical shells at or above the same `960`
cutoff where the Archimedean coercivity theorem begins are now analytic.

The coordinate `T=15360` is the first target covered by this theorem after the
separately certified finite seam at `T=7680`.  Its three analytic budgets total
`7/120` and leave `17/1080` for the fixed early shells.  The finite allocations
are anchored at target coordinate `T=1920` and therefore undergo three dyadic
halvings before they are attached here.  The complete even budget becomes
`(31/480)*(1/2)^3=31/3840`, leaving slack `53/6912`; the complete odd budget,
including the fixed `[1,20]` block, becomes
`(1/16+1/384)*(1/2)^3=25/3072`, leaving slack `1051/138240`.  These four exact
identities are checked in Lean.  The remaining task is thus no longer an
expanding below-threshold family: it is a fixed finite attachment problem for
shells below `960`, followed by the recursive reserve and infinite operator
limit.

## 2026-09-02: a finite-moment Schur bridge closes `(120,960]`

The transported-ledger argument above proves that enough budget exists, but it
still moves an old finite certificate through every intervening target.  A new
source-local construction avoids that dependency.  For a source band
`(B,2B]` and remote target `(N,2N]`, the exact parity estimates separate into a
small source moment and the already analytic target moment:

```text
even source moment = sum p^2 f(p)^2,
odd source moment  = sum     f(p)^2,
target weighted moment <= (197/2000)/N.
```

The `q^-4` term also consumes the elementary remote inverse fourth-power sum,
while the `q^-2` term consumes the inverse square sum.  This produces the Lean
definitions `c13EvenFiniteMomentRemoteBudget` and
`c13OddFiniteMomentRemoteBudget` without a lower bound on `B`.  Matrix Cauchy
converts the entry-square estimates to cross-energy estimates, and
`relativeCoupling_of_squaredNormBudget` combines them with a source floor and
the analytic target floor `24/5` at `N>=15360`.

The certificate interfaces are deliberately minimal:

```text
C13EvenFiniteSourceMomentCertificate B sourceSecond sourceGap
C13OddFiniteSourceMomentCertificate  B sourceZero   sourceGap.
```

They contain only the relevant scalar symbol moment and the quadratic source
floor.  For `B=480,240,120`, the exact selected tuples are

```text
(49740000, 92,   129/50,  1/350),
( 6274000, 47,  177/100, 1/500),
(  735000, 219/10, 137/100, 1/795),
```

where the entries are `(evenMoment, oddMoment, sourceGap, relativeCost)`.  Six
literal matrix theorems connect these records to the target `15360` block.
Their sum leaves

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795
  = 96421/10017000.
```

The new Arb certifier evaluates the same complete cutoff-13 builder symbol as
the direct parity kernel:

```text
f(n) = -poleScale*n/(log(13)^2 + 16*pi^2*n^2)
       - (archSymbol(n)+primeSymbol(n))/pi.
```

For each band it interval-sums both moments and proves positivity of the even
and odd matrices `H-sourceGap*I`.  Positivity uses a floating Cholesky basis
only as a selector; the saved doubles are reloaded byte-for-byte, embedded as
radius-zero dyadic Arb numbers, and checked by exact congruence plus strict
Gershgorin.  A canonical replay through cutoff `120` also checks all `14641`
even and `14400` odd direct-formula entries against the full reflected matrix,
with every difference interval containing zero.  Both a 256-bit and an
independent 384-bit run pass all six standard source matrices.
The largest source-moment values are

```text
B=480: even = 49735025.6414292310457642924280... < 49740000,
       odd  =       91.9883392171744386771882... < 92;
B=240: even =  6273031.3049495534120677941423... < 6274000,
       odd  =       46.7556363958564815585277... < 47;
B=120: even =   734034.2034987587578728165086... < 735000,
       odd  =       21.8048987999989431296010... < 219/10.
```

## 2026-09-02: an interval moment bridge closes the residual source band

The remaining `(20,120]` block should not be certified with one uniform source
gap.  A corrected direct odd-parity diagnostic gives a minimum eigenvalue near
`0.09378` for that unified block.  `FiniteResidualBandTransport.lean` therefore
introduces the consecutive source coordinate `finiteIntervalMode A M i` and
proves the complete even/odd Loewner moment estimates for every interval
`(A,A+M]`.  Splitting where the source coercivity changes gives:

```text
interval       evenMoment  oddMoment  exact sum(n^2)  commonGap  cost
(60,120]       107500      49/4       509410          22/25      1/900
(30,60]         12110      27/5        64355          49/100     1/900
(20,30]          1530      47/20        6585          19/100     1/900.
```

These are certificate inputs, not decimal replacements: each moment is proved
by an Arb interval upper enclosure, each rational gap by strict positive
definiteness, and the arbitrary-interval Lean theorem transports it to the same
analytic target shell.  The exact residual ledger becomes

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795 - 1/300
  = 63031/10017000 > 0,

63031/10017000 - 1/3072
  = 7650593/1282176000 > 0.
```

The second identity includes the already transported odd fixed-block charge.
Across the standard and residual blocks, each precision run proves all
`1880` Gershgorin rows strictly positive.  The twelve saved exact-dyadic
preconditioners have identical hashes at 256 and 384 bits.  In particular, the
tight residual moment is still separated strictly:

```text
sum_{20<n<=30} f(n)^2
  = 2.3445951216285382382958985633884...
  < 47/20
```

The combined 256-bit JSON SHA-256 is
`71F9F0906D20FAA1653DD37A73B2481B77CE746AED951603AECD8812223EB9D7`;
the 384-bit JSON SHA-256 is
`38B31EF48DEDFD4C079D1023830171172867F594E07F25CA4BFA9F625D280341`.
The script source hash recorded by both is
`4DB7918CB4040A8B9573AC59BD4BFBB763F99201B28AEB6BF9476D4DD73ADC54`.

This route is structurally stronger than another large remote finite matrix:
the numerical object never exceeds dimension `480`, while the target is handled
by the same analytic estimate used at later scales.  The unresolved finite
source is now only the structured fixed `[1,20]` block.  The fourteen finite
middle bridges, recursive coefficient summation, and closed boundary--Weyl
operator identification remain separate.

## 2026-09-02: full source geometry removes the fixed-block transport premise

The residual fixed odd block cannot efficiently use a scalar source gap: its
unshifted `[1,20]` matrix has nearly null directions.  A source-preconditioned
Gram estimate keeps exactly the energy that the earlier fixed-base Schur
certificate identified,

```text
S = (249/250) * (H_odd,[1,20] + (1/1024) I),
C = H_odd,[1,20] x [15361,30720].
```

The new external certificate proves the `20 x 20` Loewner inequality

```text
C*C^T <= (3/1250) S.
```

This statement controls every source direction simultaneously.  Finite
Cauchy--Schwarz turns it into

```text
|x^T C y|^2 <= (3/1250) * (x^T S x) * ||y||_2^2,
```

and the kernel-checked remote energy floor
`(24/5)||y||_2^2 <= H_remote(y)` gives exact relative cost `1/2000` because
`3/1250=(1/2000)(24/5)`.  Thus
`c13OddFixedRemoteBuilder_20_15360_relative_oneOver2000` reaches the analytic
target directly and does not assume that the original `1/384` finite Schur
coefficient halves three times.

The Arb construction evaluates the complete `20 x 15360` crossblock, encloses
`C*C^T`, and proves `(3/1250)S-C*C^T` positive by an exact-dyadic congruence.
Both independent precisions pass `20/20` strict rows and use preconditioner hash
`8A09B178DEFD216CC37D23F6DA56E93846BF00832DFFB331B7B1E4B8647E5CB0`.
The 256/384-bit JSON hashes are respectively
`D0ABABA4F39D5914BE76CF03529A9C5EBA946054F9E7C6D0658432540BA1EE67`
and
`3B474B20C1D6B1D609CB016A3D7A44CD689497BDDCCFF0C43DB3FE83C0B431EC`;
both record script hash
`FC6A5A4E8C8D86BED026468DB1F8809BBAFB20B235DE470394B97F9B8BDB379F`.

Charging this unconditional direct route leaves

```text
2/27 - 7/120 - 1/350 - 1/500 - 1/795 - 1/300 - 1/2000
  = 23209/4006800 > 0.
```

All finite previous-core source blocks are therefore connected to the analytic
`N=15360` shell.  The next finite target is the fourteen middle-channel
bridges, followed by the recursive coefficient sum and infinite operator
passage.

## 2026-09-02: displacement-rank route for the finite adjacent bridges

The fourteen middle blocks should not be represented as fourteen dense
matrices.  Their same-sign kernels are rectangular Loewner matrices and obey a
rank-two Sylvester displacement equation; the reflected kernels are Loewner
blocks on an even better separated interval pair.  Beckermann--Townsend's
Zolotarev bound for displacement-structured matrices therefore supplies the
right compression architecture.

The selected explicit compression maps each interval pair to
`[-alpha,-1]` and `[1,alpha]`, then uses logarithmically spaced rational shifts.
With 64 same-sign factors and 12 reflected factors, the combined rank cap is
152.  The elementary nearest-shift estimate gives

```text
Z <= tanh(log(alpha)/(4*k))^2.
```

Independent 256/384-bit Arb replays prove this is below `1/200` for every
same-sign bridge and below `1/4000` for every reflected bridge.  Their JSON
hashes are
`E5DD81C5655FB585457B06DC3505E5067F9C80F8A6286978A8CD410F79FC152C`
and
`4B3EA34EBCF8D007C8E9958C7B78E213B26463B62C892593319FAC5F7936ACA3`;
the tracked script hash is
`CFB585B9F404550A30D24F44FA6B5EB1DBBFB5561B0184DAF48A11BA887A1C43`.

`AdjacentLoewnerCompression.lean` proves the a posteriori step and preserves
cancellation in the combined compressed parity block.  The residual factors
inflate the two compressed norms only by `1/199` and `1/3999`.  This first
rank-152 architecture localized the finite work to small Gram matrices.  The
next section records a sharper first-bridge geometry which supersedes the
earlier claim that a direct full-energy certificate at `K=1920` is mandatory.

## 2026-09-02: rebalanced rank-86 compression clears the K1920 adjacent channel

The coarse first-bridge failure came from spending a historical-core
Archimedean constant on a square adjacent shell.  For source coordinates
`M+i+1` and `M+j+1`, every entry of the unscaled reflected Hilbert kernel obeys

```text
1 / ((M+i+1) + (M+j+1)) <= 1 / (2*(M+1)).
```

There are only `M` columns.  Its row sum is therefore at most
`M/(2*(M+1)) <= 1/2`, and ordinary Schur gives quadratic-form norm `1/2`.
The reflected leading matrix carries the additional factor `1/2`, so it costs
only `1/4`, rather than the generic historical-core allowance.  Adding the
already proved centered remainder `43/3840` yields the exact even/odd bound

```text
1/4 + 43/3840 = 1003/3840.
```

Relative to the old `1/2` loss this recovers `917/3840`.  The resulting
kernel-checked coercive floors are

```text
source M >= 1920 : 2257/768,
target M >= 3840 : 351629/96000,
```

in both parity sectors.  These statements are proved in
`AdjacentShellRebalancedCompression.lean`; they do not depend on numerical
eigenvalues.

At the first bridge the rational shifts can then be reduced to `31` same-sign
and `12` reflected factors, with combined rank

```text
2*31 + 2*12 = 86.
```

The independent 256/384-bit Arb tail replays give the same enclosures

```text
same-sign residual
  0.004729016336806176011156285610921492... < 19/4000,
reflected residual
  0.000185926254974419371752006879809042... < 3/16000.
```

Their JSON SHA-256 values are respectively
`DB39044FD42298074A6E2C84FEACE109D79EACDECAE25D1D0CE6CE6E54193363`
and
`9ECD64319225A57ECCB62F7FFB229B2AC43373D03AD173E56D6630D9F1B8E57C`;
both record the existing tail-certifier source hash
`CFB585B9F404550A30D24F44FA6B5EB1DBBFB5561B0184DAF48A11BA887A1C43`.

The new `certify_k1920_adjacent_compressed_gram.py` constructs the complete
cutoff-13 source symbol through mode `7680`, the explicit Arb Mobius maps and
ADI factors, and the small factor Grams `G_U=U^T U`, `G_V=V^T V`.  A floating
Cholesky computation only selects an exact-dyadic lower triangular matrix
`R`; after replaying every stored double as a radius-zero dyadic Arb number,
the certificate proves

```text
G_U < R*R^T,
R^T*G_V*R < epsilon^2*I
```

by exact congruence and strict interval Gershgorin.  Thus the compressed
operator bounds are

```text
same-sign <= 8881/10000,
reflected <= 22301/100000,
even total <= 93223/100000,
odd total <= 93223/100000.
```

The midpoint transformed norms `0.888088...`, `0.223002...`, `0.932228...`,
and `0.919988...` are diagnostics only.  Each precision proves `516` strict
Gershgorin rows.  All four Gram selectors and all eight positivity
preconditioners have byte-identical hashes across precisions; the three
distinct selector hashes are

```text
same-sign 49EE6C295E5CD6CB1C4BDF67B96B6764B47C30068150DC1D7AFBCA1C241ED2B9,
reflected 16DF2C9466A9A2A2C1A15A3855D1EDCC1421C46911BD7AE721A6DF427633DF05,
combined  25D9D6343A62A834B105CAC7CAC9ABFA71D64512E77DECBF016B7E22D9D2EBBC.
```

The script also checks `49+49` deterministic entries of
`X*(1-r(A)/r(B))-U*V^T`; all `98` interval residuals contain zero.  This is a
strong construction audit of the concrete implementation.  The general
entrywise identity is now kernel-checked in `LoewnerAdiTelescope.lean`: for an
arbitrary field, arbitrary ordered root/pole list, and any rank-two
displacement generator, it proves exactly two factor columns per shift and
rewrites the residual as the ordinary rational-product quotient.  Its scaled
Loewner specialization also derives exactly the balanced generators used by
the Python script; positive and reflected spectral intervals differ only in
the sign of the right coordinate.  The CI-pinned `python-flint 0.8.0`
256/384-bit Gram JSON SHA-256 values are
`A89545C3E8988F7F7E27150E05E07A96784E7DB3B42E1BB4D894FB7FB1EB7A2A`
and
`25272CADF535B277EC0BD4D255F45B414AE2F1CB4E7FFF17D858AFF058CE3D08`;
both record script SHA-256
`22A48F56137882F30C3A5A2C4BCA093F9E7BE2CB2A13120689A61F1CF60788FB`.

The initially tempting `921/1000` bound covers the odd diagnostic but not the
even block.  The first valid common cap was `933/1000`; a second exact-dyadic
Gram replay tightens it to `93223/100000` while also lowering both component
caps.  The exact posterior ledger is now

```text
93223/100000 + (19/3981)*(8881/10000)
  + (3/15997)*(22301/100000)
  = 186377448887/199012678125
  = 0.9365104306065174...
  < 23413/25000.
```

The rational norm `23413/25000` fits the sharper adjacent coefficient:

```text
(23413/25000)^2
  <= (11/135)*(2257/768)*(351629/96000).
```

Finally, the steady reference allowance is not intrinsically two equal
`2/27` channels.  At this first geometry it can be reallocated exactly as

```text
1/15 + 11/135 = 4/27.
```

Consequently the adjacent K1920 channel no longer needs a dense direct
full-energy certificate.  The abstract ADI telescope/factor identity is now
closed.  The rebalanced shell step retains two sharply localized concrete
interfaces: (1) bind the literal Arb K1920 root/pole lists and their interval
noncollision certificates to the generic theorem, and (2) prove the
old-core/new-shell relative coefficient
`<=1/15` at this first step.  The Gram, residual, coercive-floor, posterior,
and two-channel arithmetic sides are already certified.  Later compressed
bridges, the uniform coefficient summation, and the infinite closed-form/
operator passage remain separate global tasks.

## 2026-09-02: a source-side Gram closes the K1920 old-core channel at `1/28`

The old-core target does not require the 3840-dimensional Schur complement of
the complete new-shell energy.  Retaining the full recursive source geometry
and using the already proved target Euclidean floor reverses the elimination
direction.  For the complete direct-parity crossblock

```text
C : old modes [0,1920] or [1,1920]  ->  new modes [3841,7680]
```

the new interval certifier proves in both parity sectors

```text
C*C^T < (13/100) * R_q(old),       q = 249/250.
```

Here `R_q` is the shifted source reference with its complete low-low block
multiplied by `q`.  The crossblock is not split: it retains the combined
Archimedean/prime Loewner cancellation, the pole term, and the normalized even
zero-mode row.  Finite Cauchy--Schwarz and the kernel-checked target floor give

```text
|s^T C t|^2
  < (13/100) R_q(s,s) ||t||^2
  <= (1/28) R_q(s,s) H_new(t,t),

(1/28)*(351629/96000) - 13/100 = 2189/2688000 > 0.
```

This improves the requested old-core coefficient from `1/15` to `1/28`.
Together with the adjacent rank-86 coefficient,

```text
1/28 + 11/135 = 443/3780,
4/27 - 443/3780 = 13/420.
```

The Arb proof constructs about 9.22 million exact-form entries per sector,
encloses the source Grams of dimensions `1921` and `1920`, and proves all
`3841` exact-dyadic congruence/Gershgorin rows strictly positive.  Independent
256/384-bit runs select byte-identical preconditioners:

```text
even 3A05F5856A139DF80F930E5BE19E110374B2CAAD6BD0820F90465B8F4DCFF19A,
odd  6A1CD207291A38B228954C2273310C9144323E0C833186F0BCA991519699FD35.
```

Their JSON SHA-256 values are
`5CC43F1E2E449FE3BDA62E197A860BB2E0133F450B24E47CDE8E66E7015E8494`
and
`29A8EC9313C577DC921B6411D14EE905E01E8DAB3736D89CB82D0CBC6AFB4E92`;
both record final script SHA-256
`29AFD703D06AC1A4DFC45712C0E8BED786E79F018C42B655FF640411CD2D56CF`.
The small canonical replay also checks `14641+14400` direct-minus-canonical
entries, every interval containing exact zero.  Midpoint generalized thresholds
`0.0345884...` (even) and `0.1255003...` (odd) were used only to choose the
rational cap and are not proof evidence.

`AdjacentShellRebalancedCompression.lean` now proves the generic finite
rectangular Cauchy theorem, the minimal source-Gram certificate interface, the
source-Gram/target-floor adapter, the exact `1/28` specialization, and the
weighted `443/3780` recombination.  Thus the old-core first-step boundary is
closed to the same explicit finite-certificate interface as the adjacent Gram.
The remaining K1920 algebraic binding is the literal ADI root/pole lists and
their noncollision intervals; later compressed bridges and the infinite
operator passage remain separate.
