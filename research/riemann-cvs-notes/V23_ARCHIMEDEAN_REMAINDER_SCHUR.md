# V23 Archimedean remainder Schur closure

Date: 2026-09-01
Branch: `research/cvs-boundary-weyl-v23`
Lean module: `research/riemann-cvs-lean/RiemannCvs/ArchimedeanRemainderSchur.lean`

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
  \ge \frac3{25}\lVert x\rVert_2^2,\qquad
x^{\mathsf T}A^{\mathrm{odd}}_{N,M}x
  \ge \frac3{25}\lVert x\rVert_2^2
\]

for every real vector \(x\in\mathbb R^M\). The corresponding even and odd
matrix-tower tail energies have the same \(3/25\) coercive floor whenever the
newest shell is no larger than the previous core.

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

A 20-term rational arctanh lower sum proves

\[
\log13>\frac{64}{25}.
\]

Since \(N\ge960>13^2\), this gives \(\log N>128/25\). The complete
explicit reserve is therefore

\[
\frac{128}{25}-
\left(\frac{19}{20}+\frac12+\frac{10}{3}+\frac{13}{60}\right)
=\frac3{25}.
\]

Thus both parity shell energies and both actual tower-tail energies have a
uniform \(3/25\) coercive floor, with no remaining analytic or numerical
premise.

## Principal Lean theorems

- `c13_centeredLogarithmicArchimedeanSymbol_abs_le`
- `logarithmicCvSArchimedeanEntry_reflected_eq`
- `logarithmicCvSArchimedeanEntry_sameSign_eq`
- `energy_abs_le_card_mul_of_entry_abs_le`
- `c13_evenRemainder_energy_abs_le_half`
- `c13_oddRemainder_energy_abs_le_half`
- `c13_logarithmicCvSPoleTail_le_thirteenSixtieth`
- `c13_shell_complete_scalar_reserve_ge_threeTwentyFive`
- `c13_logarithmicCvSBuilderEvenShell_energy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderOddShell_energy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_threeTwentyFive_normSq`
- `c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_threeTwentyFive_normSq`

The corresponding nonnegativity adapters are also retained.

## Next formal boundary

The strongest next target is a structural stitching theorem:

1. express the boundary-Weyl increment/cumulative residue in terms of the
   newly closed actual tower-tail quadratic forms;
2. use the uniform \(3/25\) high-block gap in the existing
   `relativeCoupling_of_coerciveNormBounds` or recursive-shell interface;
3. isolate the finite prefix below \(960\) as a compact exact certificate;
4. feed the combined result into the existing
   `BoundaryWeylCumulative`, `BoundaryGapNoCrossing`, and
   `ParityOrderContinuation` chain.

That step would turn the new local asymptotic coercivity theorem into a global
no-crossing advance.
