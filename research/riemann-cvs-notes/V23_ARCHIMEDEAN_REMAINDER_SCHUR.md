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
