# Uniform stationary-phase replacement for the prime dilation estimate

## Status

This note supersedes the globally nonstationary phase target in
`PRIME_DILATION_OVERLAP_TARGET.md`.

The true radial prolate phase has one stationary point under every dilation
`r >= 2`.  The corrected estimate is weaker than `O(c^{-1})`, but it is still
summable against the von Mangoldt weights and is sufficient for the
prolate-to-Weil comparison.

The polynomial stationary geometry is formalized in

- `ProlateDilationStationaryPoint.lean`;
- `ProlateCrossDilationStationaryPoint.lean`;
- `ProlateScaledStationaryFamily.lean`;
- `ProlateScaledPhaseSeparation.lean`.

The oscillatory-integral argument below is conventional analysis rather than a
completed Lean formalization.

---

## 1. Radial phase and compact scaling

For the fixed-index radial PSWF phase write

\[
\xi_a'(x)=
\sqrt{\frac{x^2-a}{x^2-1}},
\qquad x>1,
\qquad 0\le a\le\frac12.
\]

For two fixed modes and a dilation `r >= 2`, put

\[
\Phi_{a,b,r}(x)=\xi_b(rx)-\xi_a(x),
\qquad
u=r^{-2},
\qquad
x=\sqrt{1+\nu s},
\]

and rescale the phase by

\[
\Psi_{u,a,b}(s)=r\Phi_{a,b,r}(x(s)).
\]

A direct calculation gives

\[
\Psi_s
=
\frac{1}{2\sqrt{1+us}}
\left[
\sqrt{\frac{1+u(s-b)}{1+u(s-1)}}
-
\sqrt{\frac{1-a+us}{s}}
\right].
\tag{1}
\]

The numerator after rationalizing the difference of square roots is

\[
N_{u,a,b}(s)
=
s\bigl(1+u(s-b)\bigr)
-
\bigl(1-a+us\bigr)
  \bigl(1+u(s-1)\bigr).
\tag{2}
\]

For `0 <= u <= 1/4`, `0 <= a,b <= 1/2`, and `s_1,s_2 >= 0`,

\[
\begin{aligned}
N(s_2)-N(s_1)
={}&(s_2-s_1)
\Bigl((1-u)^2+u(a-b)\\
&\qquad\qquad+u(1-u)(s_1+s_2)\Bigr).
\end{aligned}
\tag{3}
\]

The coefficient satisfies the uniform lower bound

\[
(1-u)^2+u(a-b)+u(1-u)(s_1+s_2)
\ge\frac7{16}.
\tag{4}
\]

The elementary identity behind the constant is

\[
(1-u)^2-\frac u2-\frac7{16}
=
\left(\frac14-u\right)
\left(\frac94-u\right).
\]

---

## 2. Unique stationary layer and linear phase separation

The cleared stationary equation has exactly one nonnegative root `s_*`, and

\[
\frac14<s_*<2.
\tag{5}
\]

Using (3)--(4),

\[
N(s)\ge\frac7{16}(s-s_*)
\qquad(s\ge s_*),
\tag{6}
\]

and

\[
-N(s)\ge\frac7{16}(s_*-s)
\qquad(s\le s_*).
\tag{7}
\]

On the compact stationary box

\[
0\le u\le\frac14,
\quad
0\le a,b\le\frac12,
\quad
\frac18\le s\le3,
\]

the positive denominator obtained when rationalizing (1) is bounded above by
`66`.  Indeed,

\[
\sqrt{1+us}\le\frac43,
\qquad
1+u(s-1)\le\frac32,
\]

\[
\sqrt{\frac{1+u(s-b)}{1+u(s-1)}}\le\frac32,
\qquad
\sqrt{\frac{1-a+us}{s}}<4,
\]

and the remaining factor is `s <= 3`.

Consequently,

\[
\boxed{
|\Psi_s(s)|
\ge
\frac7{1056}|s-s_*|
}
\tag{8}
\]

throughout the compact stationary box.  The radial convexity calculation shows
that `Psi_s` is increasing, so the two sides of the stationary point are
monotone nonstationary intervals.

---

## 3. Explicit split-and-integrate-by-parts lemma

Let `phi` be a real `C^2` phase on an interval, with one stationary point `s_*`,
monotone derivative, and

\[
|\phi'(s)|\ge\kappa|s-s_*|.
\tag{9}
\]

Let `g` be absolutely continuous.  Split at distance `delta` from `s_*`.
The central interval contributes at most

\[
2\delta\|g\|_\infty.
\tag{10}
\]

On each outer interval, integration by parts and monotonicity of `phi'` give

\[
\left|
\int e^{i\mu\phi(s)}g(s)\,ds
\right|
\le
\frac{
3\|g\|_\infty+\|g'\|_1
}{\mu\kappa\delta}.
\tag{11}
\]

Summing the two outer intervals and choosing

\[
\delta=(\mu\kappa)^{-1/2}
\]

yields the explicit bound

\[
\boxed{
\left|
\int e^{i\mu\phi(s)}g(s)\,ds
\right|
\le
\frac{
8\|g\|_\infty+\|g'\|_1
}{\sqrt{\mu\kappa}}.
}
\tag{12}
\]

For the radial prolate phase one may take

\[
\kappa=\frac7{1056}.
\]

The same proof covers a clipped central interval if `delta` is larger than the
distance to one endpoint.

---

## 4. Application to the Dunster radial expansion

For a fixed set of indices, the uniform radial expansion has the form

\[
R_{n,c}(x)
=C_{n,c}A_{n,c}(x)
\left[J_0(c\xi_{a_n}(x))+\mathcal R_{n,c}(x)\right],
\tag{13}
\]

with a uniform Bessel envelope and an `O(c^{-1})` remainder.  After

\[
x=\sqrt{1+r^{-2}s},
\]

the Hankel principal term produces an oscillatory integral with large
parameter

\[
\mu=\frac cr.
\]

For the moving prime cutoff used in the CvS construction,

\[
r\le\frac{c}{2\pi},
\qquad
\mu\ge2\pi.
\tag{14}
\]

The scaled amplitudes and one derivative form a compact bounded family for the
finite set of modes used in the parity argument.  Applying (12), and restoring
the Jacobian and radial normalizations, gives

\[
\boxed{
|\langle t_{n,c},D_rt_{k,c}\rangle|
\le
C_{n,k}
 c^{-1/2}r^{-3/2}
\|t_{n,c}\|\|t_{k,c}\|.
}
\tag{15}
\]

A final publication proof must quote the precise Dunster remainder theorem and
track the selected Fourier normalization, but no additional stationary
geometry is missing.

---

## 5. Summation over prime powers

Multiplying (15) by the prime weight `Lambda(r)/sqrt(r)` gives

\[
\frac{C_{n,k}}{\sqrt c}
\frac{\Lambda(r)}{r^2}
\|t_{n,c}\|\|t_{k,c}\|.
\]

Since

\[
\sum_{r\ge2}\frac{\Lambda(r)}{r^2}
=-\frac{\zeta'(2)}{\zeta(2)}
<\infty,
\]

the principal prime block satisfies

\[
\boxed{
|Q_{\rm prime}^{\rm main}(t_{n,c},t_{k,c})|
\le
C'_{n,k}c^{-1/2}
\|t_{n,c}\|\|t_{k,c}\|.
}
\tag{16}
\]

The uniform `O(c^{-1})` radial-envelope error, summed with the elementary bound

\[
\sum_{r\le X}\frac{\Lambda(r)}{\sqrt r}
=O(\sqrt X\log X),
\]

contributes at worst

\[
O(c^{-1/2}\log c)
\|t_{n,c}\|\|t_{k,c}\|,
\tag{17}
\]

which is still negligible compared with the common conductor scale
`asymp log(lambda)`.

---

## 6. Consequence for the Schur problem

For the first odd low/high pair,

\[
\frac{d_{10}}{d_6}=\Theta(\lambda^8),
\qquad
c=2\pi\lambda^2.
\]

After factoring the lowest odd energy, (16)--(17) give a normalized low/high
coupling no worse than `O(lambda^3)` (and with the logarithmic normalization,
`O(lambda^3/log(lambda))`).  Its square is `O(lambda^6)`, whereas the high
block is `Theta(lambda^8)`.

The multiplication-only implication is formalized in
`StationarySchurNoIntruder.lean`: once the actual odd high-block lower bound is
available, the stationary prime coupling is absorbed after a finite quadratic
threshold.

Thus the stationary prime interaction is no longer the dominant obstruction.
The remaining hard input is a lower bound for the **entire odd high-mode
complement**, including modes outside the fixed-index asymptotic family.

---

## 7. Evidence boundary

The following are now exact or formally isolated:

- the stationary polynomial and uniqueness;
- the `1/4 < s_* < 2` layer;
- the curvature and linear phase-separation constants;
- the scalar Schur absorption of an `O(lambda^3)` coupling;
- the convergent von Mangoldt summation once (15) holds.

The following still require source-level analytic completion:

- the precise fixed-index Dunster amplitude and derivative bounds in the
project normalization;
- the uniform treatment of the Bessel remainder in the overlap integral;
- the actual full odd-complement lower bound.

No statement in this note is an RH proof.
