# Temple residual-scale obstruction at the fixed-index prolate ground scale

## 1. Why this audit is necessary

The lowest exact-parity odd prolate reference value has the scale

\[
e_-(\lambda)
\asymp
d_6(\lambda)\log\lambda,
\]

where

\[
d_6(\lambda)
\asymp
\lambda^{13}e^{-4\pi\lambda^2}.
\]

The next constrained odd prolate level is polynomially farther away:

\[
\mu_{1,-}-\mu_{0,-}
\asymp
G\lambda^8e_-(\lambda)
\]

for a positive fixed-index constant `G`.

At first sight the factor `lambda^8` appears to make Temple's inequality very
forgiving.  That is true only if the residual norm is linear in the defect.
A termwise estimate of the prime operator normally gives a square-root-defect
residual, which is much too large.

---

## 2. The square-root-defect scale

Let

\[
e=dL,
\qquad
\Delta=G\lambda^8e=G\lambda^8dL,
\]

where `d` is the concentration defect and `L` is the common logarithmic
conductor scale.

Suppose the residual is estimated only by

\[
\|r\|\le K L\sqrt d.
\]

Then

\[
\|r\|^2\le K^2L^2d.
\]

The Temple correction has the scale

\[
\frac{\|r\|^2}{\Delta}
\asymp
\frac{K^2L}{G\lambda^8}.
\]

The exponentially small factor `d` has disappeared.  Relative to the desired
ground scale,

\[
\boxed{
\frac{
\|r\|^2/\Delta
}{e}
\asymp
\frac{K^2}{G\lambda^8d}.
}
\]

Since `d=d_6(lambda)` is exponentially small, no fixed or polynomially growing
`K` can satisfy

\[
K^2<G\lambda^8d
\]

for large `lambda`.

Thus a proof that separately bounds the norm of each prime-dilation image by
the tail norm cannot close the Temple argument, even though the Rayleigh
expectation of the prime block is small by stationary phase.

---

## 3. The required scale

If one can instead prove the defect-linear residual estimate

\[
\boxed{
\|r\|\le K d L,
}
\]

then

\[
\frac{\|r\|^2}{\Delta}
\le
\frac{K^2}{G\lambda^8}e.
\]

A polynomial internal gap now does exactly what was hoped: for any fixed
fraction `eta`, the Temple loss is at most `eta e` once

\[
K^2\le\eta G\lambda^8.
\]

The scalar distinction between the two regimes is formalized in
`TempleResidualScale.lean`.

---

## 4. Consequence for the proof architecture

The fixed low-mode prime **form value** is now under control:

\[
|Q_{\rm prime}(t,t)|
=O(c^{-1/2})\|t\|^2.
\]

This does not imply a defect-linear operator residual.  The prime operator may
send one low-mode tail into many almost orthogonal dilation directions; its
expectation can be small while its norm is only of square-root-defect size.

Therefore the following route is insufficient:

\[
\text{small prime Rayleigh value}
+\lambda^8\text{ gap}
\Longrightarrow
\text{Temple ground-state theorem}.
\]

At least one additional structural cancellation is required.

The viable alternatives are now sharply separated:

1. **form-order / Schur route:** prove the complete odd quadratic form is
   bounded below without estimating the residual of one trial vector;
2. **operator-level intertwining:** show that the full archimedean, pole, and
   prime actions cancel to defect-linear order on the exact prolate candidate;
3. **no-crossing route:** establish boundary-overlap nonvanishing and use the
   Sylvester relation, avoiding a Temple estimate at every parameter;
4. **a different real-rootedness mechanism:** bypass the requirement that the
   prolate candidate be the global Weil ground state.

---

## 5. Updated interpretation of the stationary-phase result

The one-stationary-point theorem remains important.  It proves that the prime
block is lower order as a **quadratic form on the fixed low-mode space**, and
therefore preserves the quartic even/odd comparison there.

Its correct role is:

\[
\text{fixed low-block form comparison},
\]

not, by itself,

\[
\text{Temple residual control}.
\]

This distinction prevents a false claim that the odd-complement problem has
already been solved.

---

## 6. Current main target

The strongest remaining target is an operator-level identity or Schur estimate
of the form

\[
\left\|
Q_{\rm high}W_\lambda t_{6,\lambda}
\right\|
\le
K\,d_6(\lambda)\log\lambda,
\]

or an equivalent complete-form lower bound that avoids this residual
altogether.

A mere bound by

\[
K\sqrt{d_6(\lambda)}\log\lambda
\]

is provably insufficient at the exponentially small ground scale.

This is now the quantitative dividing line between a genuine ground-state
argument and a fixed-trial-value comparison.
