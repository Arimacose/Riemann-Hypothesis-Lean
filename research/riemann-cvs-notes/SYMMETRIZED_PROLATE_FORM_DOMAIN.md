# Form-domain realization of the exact-parity prolate vector

## Main point

The exact Fourier symmetrization

\[
S_\varepsilon p
=
\widetilde p+\varepsilon\mathcal F\widetilde p
\]

uses the zero extension \(\widetilde p\) of a smooth prolate eigenfunction from
the cutoff interval.  The zero extension may have endpoint jumps and is not
Schwartz.  This is not automatically fatal: the natural archimedean Weil form
has only logarithmic high-frequency growth, and a jump produces a
\(1/|s|\) Fourier tail, whose logarithmically weighted square is integrable.

Thus the correct objective is to extend the radical identity from a Schwartz
core to the closed logarithmic form domain, rather than to demand an
exponentially accurate Schwartz smoothing at the outset.

---

## 1. Logarithmic form domain

Introduce

\[
\mathcal D_{\log}
=
\left\{
 f\in L^2(\mathbb R):
 \int_{\mathbb R}
 \log(2+|s|)
 |\widehat f(s)|^2ds<\infty
\right\}.
\]

The exact archimedean multiplier differs from \(\log(2+|s|)\) by lower-order
terms, so \(\mathcal D_{\log}\) is the appropriate model form domain.

---

## 2. A zero-extended prolate mode belongs to the form domain

Let \(p\in C^1[-\lambda,\lambda]\), and let \(\widetilde p\) be its zero
extension.  For \(s\ne0\), integration by parts gives

\[
\widehat{\widetilde p}(s)
=
\frac{
 p(-\lambda)e^{is\lambda}
 -p(\lambda)e^{-is\lambda}
}{is}
+
\frac1{is}
\int_{-\lambda}^{\lambda}
 p'(x)e^{-isx}dx.
\]

Hence

\[
\left|\widehat{\widetilde p}(s)\right|
\le
\frac{
 |p(-\lambda)|+|p(\lambda)|+\|p'\|_{L^1}
}{|s|}.
\]

Therefore

\[
\int_{|s|\ge1}
\log(2+|s|)
\left|\widehat{\widetilde p}(s)\right|^2ds
<\infty,
\]

because

\[
\int_1^\infty
\frac{\log(2+s)}{s^2}ds<\infty.
\]

On compact frequency intervals, square integrability follows from Plancherel.
Thus

\[
\boxed{
\widetilde p\in\mathcal D_{\log}.
}
\]

No endpoint vanishing is required for this conclusion.

---

## 3. The Fourier component also belongs to the form domain

Because

\[
\widehat{\mathcal F\widetilde p}(s)
=
\widetilde p(-s)
\]

up to the Fourier-convention reflection, the Fourier transform of
\(\mathcal F\widetilde p\) is compactly supported in
\([-\lambda,\lambda]\).  Hence

\[
\int
\log(2+|s|)
\left|
\widehat{\mathcal F\widetilde p}(s)
\right|^2ds
\le
\log(2+\lambda)
\|p\|_2^2.
\]

Consequently,

\[
\boxed{
S_\varepsilon p
\in
\mathcal D_{\log}.
}
\]

The sharp exact-parity construction is therefore compatible with the model
archimedean form domain even though it is not Schwartz.

---

## 4. Prime and pole pieces at fixed cutoff

For any fixed cutoff, the prime-power translation block is a finite sum of
bounded truncated translations, and the pole block is finite rank.  They do not
enlarge the form domain.  Thus the full fixed-cutoff quadratic form is well
defined on \(S_\varepsilon p\), provided the archimedean form is realized as a
closed form with logarithmic symbol.

For the moving-cutoff asymptotic, the dependence of the bounded-part norm on the
cutoff must still be tracked, but domain membership holds separately at each
finite parameter.

---

## 5. Extension of the radical identity

The remaining functional-analytic step is not ordinary integrability; it is the
extension of the zeta/radical identity from a smooth core.

A suitable theorem would have the following form.

### Closed-form extension target

Let \(q_\lambda\) be the closed Weil form and let \(\mathcal C\) be the
Schwartz core on which the co-Poisson/radical identity is known.  Suppose
\(f_n\in\mathcal C\) satisfies

\[
f_n\longrightarrow S_\varepsilon p
\quad\text{in the }q_\lambda\text{ graph norm},
\]

and each \(f_n\) satisfies the two radical boundary conditions.  Then the
identity passes to the limit.

The approximation should preserve exact Fourier parity by applying

\[
\Pi_\varepsilon
=
\frac12(I+\varepsilon\mathcal F).
\]

A remaining scalar boundary error can be removed with one fixed Schwartz
Fourier-\(\varepsilon\) correction direction.  The correction coefficient must
be shown to tend to zero in graph norm.

---

## 6. Why this is better than exponentially sharp smoothing

A naive smoothing of the endpoint jump and a demand for direct
\(o(d_6(\lambda))\) control is unnecessarily severe.  The exact vector already
belongs to the closed logarithmic form domain.  If the radical identity extends
by form closure, no exponentially small smoothing width is required.

The revised obligation is:

\[
\boxed{
\text{prove constrained exact-parity vectors form a core-dense subset of the
closed radical form domain.}
}
\]

This is a standard-looking closed-form/core problem, not an exponential
approximation problem.

---

## 7. Current status and caveats

The integration-by-parts estimate above is elementary.  The following points
still require a source-level audit against the precise CvS/Weil definitions:

1. the exact normalization and high-frequency comparison of the archimedean
   symbol with \(\log(2+|s|)\);
2. closability and the identified form core;
3. continuity or correctability of the two boundary functionals along the
   chosen approximation;
4. boundedness of the co-Poisson/zeta map in the required graph norm;
5. passage of the radical truncation identity to the closure.

If these hold, exact Fourier symmetrization can be used at the optimal prolate
scale without first producing a Schwartz representative.
