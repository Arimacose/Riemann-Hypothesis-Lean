# Restricted prime block: completion by one-stationary-point analysis

## 1. Scope

This note replaces the false global-nonstationary-phase shortcut in the first
version of `PRIME_DILATION_OVERLAP_TARGET.md`.

It gives a complete proof architecture for the prime block on a fixed finite
family of exact-parity prolate leakage tails.  The only imported analytic input
is a uniform radial PSWF expansion with an explicit envelope error of relative
order `O(c^{-1})`, as in the large-parameter radial formulas used in the V17
mainline.

It does not address the full odd spectral complement and does not prove RH.

---

## 2. The unique stationary point

For fixed mode parameters `a,b` and integer dilation `r >= 2`, write

\[
\Phi_{a,b,r}(x)=\xi_b(rx)-\xi_a(x),
\qquad
\xi_a'(x)=\sqrt{\frac{x^2-a}{x^2-1}}.
\]

The exact polynomial reduction in
`ProlateCrossDilationStationaryPoint.lean` proves that, whenever

\[
0\le a,b\le\frac12,
\]

there is one exterior stationary point and it satisfies

\[
\frac1{4r^2}<x_*^2-1<\frac2{r^2}.
\]

The same calculation supplies the conservative curvature bound

\[
\boxed{
\Phi''_{a,b,r}(x_*)\ge\frac{r^3}{20}.
}
\]

The convexity module upgrades this pointwise fact to a monotone-derivative
split on the two sides of the critical point.

---

## 3. An elementary stationary-phase estimate

Let `phi` be twice continuously differentiable on an interval, with a unique
critical point `x0`, and suppose

\[
\phi''(x)\ge\kappa>0.
\]

Let `g` be absolutely continuous.  Put

\[
\delta=(\mu\kappa)^{-1/2}.
\]

Split the integral into the interval of radius `delta` around `x0` and the two
outer intervals.

The near part is bounded by

\[
2\delta\|g\|_\infty.
\]

On either outer interval,

\[
|\phi'(x)|\ge\kappa\delta.
\]

One integration by parts gives

\[
\left|
\int_{\rm one\ side}e^{i\mu\phi(x)}g(x)\,dx
\right|
\le
\frac{3\|g\|_\infty+\|g'\|_1}
{\mu\kappa\delta}.
\]

The coefficient three safely accounts for the inner boundary, the outer
boundary, and the integral of

\[
\frac{\phi''}{|\phi'|^2}
=-\frac d{dx}\frac1{|\phi'|}.
\]

Since

\[
(\mu\kappa\delta)^{-1}=\delta,
\]

one obtains

\[
\boxed{
\left|
\int e^{i\mu\phi(x)}g(x)\,dx
\right|
\le
\frac{8\|g\|_\infty+2\|g'\|_1}
{\sqrt{\mu\kappa}}.
}
\tag{1}
\]

The scalar bookkeeping is formalized in
`StationaryPhaseSplitBudget.lean`.

For the radial prolate phase, take `mu=c` and
`kappa=r^3/20`.  Equation (1) becomes

\[
\boxed{
|I_{n,k}^{\rm main}(r;c)|
\le
\sqrt{20}\,(8S_{n,k}+2V_{n,k})
\,c^{-1/2}r^{-3/2}
\|t_{n,c}\|\|t_{k,c}\|,
}
\tag{2}
\]

provided the normalized Hankel amplitude has uniform sup norm `S_{n,k}` and
uniform total variation `V_{n,k}`.  For a fixed finite set of mode indices,
these constants can be replaced by their maximum.

---

## 4. Summation of the stationary main term

The prime-power weight is

\[
w_r=\frac{\Lambda(r)}{\sqrt r}.
\]

Multiplying (2) by `w_r` gives

\[
\frac{\Lambda(r)}{\sqrt r}
|I_{n,k}^{\rm main}(r;c)|
\le
C_{n,k}c^{-1/2}
\frac{\Lambda(r)}{r^2}
\|t_{n,c}\|\|t_{k,c}\|.
\]

The absolutely convergent sum is

\[
\sum_{r\ge2}\frac{\Lambda(r)}{r^2}
=-\frac{\zeta'(2)}{\zeta(2)}.
\]

An exact value is unnecessary; any explicit finite upper bound is enough.
Consequently,

\[
\boxed{
|Q_{\rm prime}^{\rm main}(t_{n,c},t_{k,c})|
\le
C_{n,k}'c^{-1/2}
\|t_{n,c}\|\|t_{k,c}\|.
}
\tag{3}
\]

---

## 5. The uniform PSWF remainder does not need dilation decay

Write the normalized radial tail as

\[
t_{n,c}=t_{n,c}^{(0)}+e_{n,c},
\]

where `t^(0)` is the explicit Bessel/Hankel main term and the uniform radial
expansion gives

\[
\|e_{n,c}\|_2
\le
C_n c^{-1}\|t_{n,c}\|_2.
\tag{4}
\]

The main-error and error-error overlaps are controlled by Cauchy--Schwarz and
the unitarity of dilation:

\[
\left|
\langle e_{n,c},D_rt_{k,c}\rangle
\right|
+
\left|
\langle t_{n,c}^{(0)},D_re_{k,c}\rangle
\right|
\le
C_{n,k}c^{-1}
\|t_{n,c}\|\|t_{k,c}\|.
\tag{5}
\]

No factor in `r` is required in (5).  Chebyshev's estimate

\[
\psi(X)=\sum_{r\le X}\Lambda(r)\le C X
\]

and partial summation imply

\[
\sum_{r\le X}\frac{\Lambda(r)}{\sqrt r}
\le C'\sqrt X.
\]

In the moving-cutoff problem,

\[
X\le\frac{c}{2\pi}.
\]

Therefore the total contribution from (5) is also

\[
\boxed{
O(c^{-1/2})
\|t_{n,c}\|\|t_{k,c}\|.
}
\tag{6}
\]

This observation removes the strongest unverified demand in the old target:
a derivative-controlled, dilation-decaying remainder is not needed.  Only the
explicit main amplitude requires the one-stationary-point estimate.

---

## 6. Fixed-family prime-block conclusion

Combining (3) and (6), for every fixed finite family of mode indices there is a
constant `C` such that

\[
\boxed{
|Q_{\rm prime}(t,t)|
\le
C c^{-1/2}\|t\|^2
}
\tag{7}
\]

uniformly on its span.

Since

\[
c=2\pi\lambda^2,
\]

this is `O(lambda^{-1})` relative to the defect Gram matrix.  The common
archimedean conductor coefficient is `2 log lambda + O(1)`, so

\[
\frac{
\|Q_{\rm prime}\|_{\rm relative}
}{2\log\lambda}
=O\!\left(\frac1{\lambda\log\lambda}\right).
\]

Thus the restricted prime block cannot destroy the exact-parity
constrained-prolate quartic separation.

---

## 7. What remains to be checked before calling (7) a theorem of the project

The following source-normalization audit is still required:

1. identify the project's normalized exterior tails with the chosen radial
   PSWF convention, including the connection coefficient;
2. verify that the published uniform envelope error yields the relative
   `L^2` estimate (4), uniformly for the finite mode family;
3. record uniform `S` and `V` bounds for the explicit main amplitude after the
   endpoint scaling;
4. verify the prime-power dilation normalization and both exterior wings;
5. include the finite-rank pole block in the same normalized Gram basis.

These are now finite convention and constant checks.  The moving stationary
point and the summation over all prime powers no longer constitute conceptual
obstructions.

---

## 8. Updated main bottleneck

Once the preceding audit is completed, the fixed low-mode prolate-to-Weil
comparison is closed.  The remaining hard step is not the restricted prime
block but the complete odd complement:

\[
\boxed{
\text{exclude an odd high-mode intruder below the even ground scale.}
}
\]

This requires either a global odd-sector Schur/coercivity theorem or a
no-crossing mechanism that avoids estimating the whole complement at each
parameter.
