# PSWF exterior ODE reduction for the logarithmic tail moment

## Goal

For a fixed-index prolate exterior tail \(t_{n,c}\), prove

\[
\frac{
\int_1^\infty \log y\,|t_{n,c}(y)|^2dy
}{
\int_1^\infty |t_{n,c}(y)|^2dy
}
=O(1)
\]

uniformly as \(c\to\infty\).  This is stronger than the coarse
\(O(\log\lambda)\) bound needed for the conductor comparison.

The reduction below shows that a standard-looking uniform Liouville--Green
estimate for the exterior PSWF equation is sufficient.

---

## 1. Exterior prolate equation

An angular prolate mode satisfies

\[
(1-y^2)\psi''(y)
-2y\psi'(y)
+
\bigl(\chi_n(c)-c^2y^2\bigr)\psi(y)
=0.
\]

For \(y>1\), this becomes

\[
\frac d{dy}
\left((y^2-1)\psi'(y)\right)
+
\bigl(c^2y^2-\chi_n(c)\bigr)\psi(y)
=0.
\]

Use

\[
y=\cosh u,
\qquad u>0.
\]

Then

\[
\psi_{uu}
+
\coth u\,\psi_u
+
\bigl(c^2\cosh^2u-\chi_n(c)\bigr)\psi
=0.
\]

Set

\[
v(u)=\sqrt{\sinh u}\,\psi(\cosh u).
\]

A direct calculation gives an equation of the form

\[
v''(u)+q_{n,c}(u)v(u)=0,
\]

where

\[
q_{n,c}(u)
=
c^2\cosh^2u-\chi_n(c)
+
\frac14
+
\frac1{4\sinh^2u},
\]

up to the sign convention of the last elementary correction, which must be
checked when the detailed proof is written.  Away from the endpoint transition,

\[
q_{n,c}(u)\asymp c^2\cosh^2u.
\]

---

## 2. Liouville--Green envelope

Let

\[
z(u)=\int_{u_0}^{u}\sqrt{q_{n,c}(s)}\,ds,
\qquad
w(z)=q_{n,c}(u)^{1/4}v(u).
\]

The transformed equation has the form

\[
w_{zz}+(1+r_{n,c}(z))w=0.
\]

The required uniform WKB input is that, for fixed \(n\), one can choose a
matching amplitude \(A_{n,c}\) such that

\[
|w(z)|+|w_z(z)|
\le C_n|A_{n,c}|
\]

for all \(u\ge u_0(c)\), with an integrable error bound

\[
\int|r_{n,c}(z)|dz\le C_n.
\]

This yields

\[
|\psi(\cosh u)|^2
\le
\frac{C_n|A_{n,c}|^2}
{c\sinh u\cosh u}.
\]

Because

\[
dy=\sinh u\,du,
\]

we obtain

\[
|\psi(y)|^2dy
\le
\frac{C_n|A_{n,c}|^2}{c\cosh u}\,du.
\]

The right-hand side decays exponentially as \(u\to\infty\).

---

## 3. Upper logarithmic moment

Since

\[
\log y=\log(\cosh u)\le u,
\]

\[
\int_{u_0}^{\infty}
\log(\cosh u)
|\psi(\cosh u)|^2\sinh u\,du
\le
\frac{C_n|A_{n,c}|^2}{c}
\int_{u_0}^{\infty}
\frac{u}{\cosh u}du.
\]

The last integral is finite.  Thus

\[
\int_1^\infty
\log y\,|\psi(y)|^2dy
\le
C_n'\frac{|A_{n,c}|^2}{c},
\]

provided the endpoint transition region is controlled by its uniform local
model.

---

## 4. Lower mass comparison

To convert the preceding absolute estimate into a normalized moment estimate,
it is enough to prove a matching lower bound

\[
\int_1^\infty|\psi(y)|^2dy
\ge
c_n\frac{|A_{n,c}|^2}{c}.
\]

A uniform oscillatory approximation on one fixed interval
\(u\in[u_1,u_2]\subset(0,\infty)\) suffices.  The WKB phase is strictly
monotone, and a mean-square estimate over many oscillations gives the lower
bound without requiring pointwise avoidance of zeros.

Combining upper and lower estimates yields

\[
\boxed{
\frac{
\int_1^\infty\log y\,|\psi(y)|^2dy
}{
\int_1^\infty|\psi(y)|^2dy
}
\le C_n.
}
\]

For a finite set of fixed indices, take the maximum constant.

---

## 5. Endpoint transition

The coordinate \(u=0\) is a singular endpoint and the exterior wavenumber
changes rapidly there.  A global proof needs a local Bessel-type transition
approximation on a shrinking neighborhood of \(u=0\), matched to the exterior
WKB solution.

The transition contribution only needs the two estimates

\[
\int_{1}^{y_0(c)}|\psi(y)|^2dy
\le
C_n\frac{|A_{n,c}|^2}{c},
\]

and

\[
\int_{1}^{y_0(c)}
\log y\,|\psi(y)|^2dy
\le
C_n\frac{|A_{n,c}|^2}{c}.
\]

The second is easier because \(\log y\) vanishes at the endpoint.

---

## 6. Connection with the Fuchs defect

The finite Fourier transform of a prolate eigenfunction is proportional to its
entire continuation.  Therefore the exterior leakage mass equals the fixed-index
concentration defect after normalization.  The Fuchs asymptotic identifies

\[
\frac{|A_{n,c}|^2}{c}
\asymp
1-\chi_n(c).
\]

For the log-moment argument, an exact asymptotic constant is unnecessary; a
uniform two-sided comparison is sufficient.

---

## 7. Prime-overlap compatibility

The same WKB representation gives the carrier phase

\[
\Phi_c(y)
\approx
c\sqrt{y^2-1}.
\]

Under dilation \(y\mapsto my\), the phase difference has derivative bounded
away from zero for every \(m\ge2\).  A derivative-controlled WKB remainder
therefore supplies the nonstationary-phase estimate required in
`PRIME_DILATION_OVERLAP_TARGET.md`.

Thus one uniform exterior theorem can potentially provide both:

1. the conductor logarithmic-moment upper bound;
2. the restricted prime-block decay.

---

## 8. Minimal literature/source audit

The next literature task is to locate a fixed-order, large-bandwidth PSWF
asymptotic that is uniform:

- through the endpoint transition;
- on the whole exterior half-line;
- with at least one derivative of the remainder;
- with normalization linked to the concentration defect.

If the available theorem lacks one of these features, the missing estimate
should be proved directly from the Liouville-transformed equation rather than
assumed.

This note is a reduction, not a completed PSWF asymptotic proof.
