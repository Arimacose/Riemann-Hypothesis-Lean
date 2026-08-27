# Prime dilation-overlap target for fixed-index prolate leakage

## Purpose

A global operator-norm estimate for the finite prime block is too crude for the
lowest prolate scale: the sum of absolute von Mangoldt weights grows much faster
than the logarithmic archimedean coefficient.  The relevant quantity is instead
the prime block **restricted to the fixed-index exterior leakage tails**.

For endpoint-generated oscillatory tails, dilation by an integer changes the
carrier phase by a nonstationary amount.  This should supply an additional
factor \(1/[c(m-1)]\), making the prime contribution lower order relative to the
leakage mass.

---

## 1. Model exterior tail

Let \(c=2\pi\lambda^2\).  For one exterior wing, the fixed-index prolate
continuation is expected to have an endpoint-oscillatory expansion of the form

\[
t_{n,c}(y)
=
A_{n,c}\,
\frac{e^{icy}\,a_{n,c}(y)
      +\varepsilon_n e^{-icy}\,b_{n,c}(y)}{y},
\qquad y\ge1,
\]

where, for each fixed index \(n\),

\[
\sup_{c\ge c_0}
\left(
\|a_{n,c}\|_\infty+
\|b_{n,c}\|_\infty+
\|a'_{n,c}\|_{L^1}+
\|b'_{n,c}\|_{L^1}
\right)<\infty.
\]

The amplitude \(A_{n,c}\) contains the exponentially small fixed-index factor.
The total exterior mass should satisfy

\[
\|t_{n,c}\|_2^2
\asymp |A_{n,c}|^2.
\]

The exact power of \(c\) in \(A_{n,c}\) is supplied by the Fuchs asymptotic;
only a uniform relative profile estimate is needed below.

---

## 2. Dilation overlap

Let

\[
(D_mf)(y)=m^{1/2}f(my)
\]

be the unitary dilation.  A representative same-carrier term in

\[
I_{n,k}(m;c)
=
\langle t_{n,c},D_mt_{k,c}\rangle
\]

has phase

\[
e^{ic(m-1)y}.
\]

For \(m\ge2\), this phase has no stationary point on \([1,\infty)\).  One
integration by parts gives, schematically,

\[
\left|
\int_1^\infty
e^{ic(m-1)y}F_{n,k,m,c}(y)dy
\right|
\le
\frac{
|F_{n,k,m,c}(1)|+\|F'_{n,k,m,c}\|_1
}{c(m-1)}.
\]

The opposite-carrier terms have phase \(c(m+1)y\) and are at least as small.
Under the uniform profile bounds,

\[
\boxed{
|I_{n,k}(m;c)|
\le
\frac{C_{n,k}}{c(m-1)\sqrt m}
\|t_{n,c}\|_2\|t_{k,c}\|_2.
}
\]

A slightly different power of \(m\) is harmless; any summable majorant after
multiplication by \(\Lambda(m)/\sqrt m\) suffices.

---

## 3. Summing the prime block

The prime block contains weights of the form

\[
\frac{\Lambda(m)}{\sqrt m}.
\]

The preceding overlap estimate gives

\[
\begin{aligned}
\left|
\sum_{m\le\lambda^2}
\frac{\Lambda(m)}{\sqrt m}
I_{n,k}(m;c)
\right|
&\le
\frac{C_{n,k}}c
\|t_{n,c}\|_2\|t_{k,c}\|_2
\sum_{m\ge2}
\frac{\Lambda(m)}{m(m-1)}.
\end{aligned}
\]

The numerical series on the right converges absolutely.  Therefore

\[
\boxed{
|Q_{\mathrm{prime}}(t_{n,c},t_{k,c})|
\le
\frac{C'_{n,k}}c
\|t_{n,c}\|_2\|t_{k,c}\|_2.
}
\]

Since

\[
c=2\pi\lambda^2,
\]

this is \(O(\lambda^{-2})\) in units of the exterior Gram matrix and is
negligible relative to the logarithmic conductor scale.

---

## 4. Why the global norm is misleading

The triangle-inequality operator bound

\[
\|W_p\|
\le
2\sum_{m\le\lambda^2}
\frac{\Lambda(m)}{\sqrt m}
\]

ignores the carrier-phase change under dilation.  It is suitable for a fixed
cutoff finite-section theorem but not for the moving-cutoff prolate asymptotic.
The restricted oscillatory estimate above is the correct scale-sensitive
quantity.

---

## 5. Precise theorem needed from prolate asymptotics

For the fixed indices used in the parity proof, it is enough to establish:

1. an exterior expansion with a \(1/y\)-type integrable envelope;
2. uniform weighted \(C^1\) control of the envelope;
3. two-sided comparison between \(|A_{n,c}|^2\) and the exact concentration
   defect \(d_n(c)\);
4. uniformity under the finite set of dilation factors after summation, or a
   summable bound valid for every integer \(m\ge2\).

A pointwise leading asymptotic without a derivative/integrable remainder is not
sufficient for the prime sum.

---

## 6. Consequence for the Schur coupling

If the prime Gram matrix on the exact-parity tail basis is

\[
O(c^{-1})
\]

relative to the defect Gram, while the conductor part is

\[
\asymp\log\lambda,
\]

then prime low/high coupling is far below the threshold required by the
\(\Theta(\lambda^8)\) internal prolate gap.  The remaining pole block is finite
rank and can be treated by the same endpoint-amplitude estimates.

This would close the most dangerous perturbative part of the
prolate-to-Weil transfer.

---

## 7. Status

The nonstationary-phase calculation is elementary once the uniform exterior
profile is available.  The missing research input is a source-level uniform
fixed-index PSWF exterior asymptotic strong enough to justify the integration
by parts and the defect normalization.

Until that theorem is supplied, the \(O(c^{-1})\) prime estimate remains a
well-defined target rather than a proved property of the actual prolate tails.
