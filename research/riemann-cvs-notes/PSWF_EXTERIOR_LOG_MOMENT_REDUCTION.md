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

To keep the two prolate spectra distinct, write \(\Lambda_n(c)\) for the
differential-equation separation eigenvalue.  The concentration singular value
will be denoted by \(\sigma_n(c)\) in Section 6.  In particular,
\(\Lambda_n(c)\) is unbounded and is not a number in \((0,1)\).  In the
[DLMF 30.2.1](https://dlmf.nist.gov/30.2.E1) convention,
\(\Lambda_n(c)=\lambda_n^0(c^2)+c^2\); hence
[DLMF 30.9.1](https://dlmf.nist.gov/30.9.E1) gives
\(\Lambda_n(c)=(2n+1)c+O(1)\) for fixed \(n\).

An angular prolate mode satisfies

\[
(1-y^2)\psi''(y)
-2y\psi'(y)
+
\bigl(\Lambda_n(c)-c^2y^2\bigr)\psi(y)
=0.
\]

For \(y>1\), this becomes

\[
\frac d{dy}
\left((y^2-1)\psi'(y)\right)
+
\bigl(c^2y^2-\Lambda_n(c)\bigr)\psi(y)
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
\bigl(c^2\cosh^2u-\Lambda_n(c)\bigr)\psi
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
c^2\cosh^2u-\Lambda_n(c)
-
\frac14
+
\frac1{4\sinh^2u},
\]

with the elementary correction fixed by substituting
\(\psi(\cosh u)=(\sinh u)^{-1/2}v(u)\).  Away from the endpoint transition,

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

Let \(\sigma_n(c)\in(0,1)\) denote the singular value of the compressed finite
Fourier transform and set

\[
d_n(c)=1-\sigma_n(c)^2.
\]

After the same normalization is used on the retained mode and its entire
continuation, the exterior leakage mass equals \(d_n(c)\).  A Fuchs asymptotic
controls this concentration defect.  It does not, by notation alone, identify
the defect with the differential separation eigenvalue \(\Lambda_n(c)\).

The WKB reduction additionally needs the matching amplitude \(A_{n,c}\) to be
tied to that normalization.  The sufficient statement is the two-sided
comparison

\[
c_n\frac{|A_{n,c}|^2}{c}
\le d_n(c)
\le C_n\frac{|A_{n,c}|^2}{c}.
\]

Thus the source audit has two logically separate obligations:

1. a Fuchs-type fixed-index estimate for \(d_n(c)\);
2. a matching/normalization theorem comparing the exterior WKB amplitude scale
   \(|A_{n,c}|^2/c\) with \(d_n(c)\).

For the log-moment argument, exact asymptotic constants are unnecessary; uniform
two-sided comparisons are sufficient.

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

## 8. Source audit and next proof obligation

[Dunster, *Asymptotics of prolate spheroidal wave functions* (2017),
DOI 10.7153/jca-11-01](https://files.ele-math.com/articles/jca-11-01.pdf)
provides a source matching most of the required radial estimate.  Its parameter
range includes every fixed \(m,n\) as \(c\to\infty\).  In the radial case:

- equation (3.5) gives a Bessel approximation, with an \(O(c^{-1})\) Bessel-
  envelope remainder, uniformly for the whole interval \(1<x<\infty\);
- equation (3.7) identifies the multiplicative constant by endpoint matching;
- equation (3.8) gives the far-field amplitude
  \([(x^2-1)(x^2-s^2)]^{-1/4}\), whose squared tail is of order \(x^{-2}\)
  and is therefore integrable with a \(\log x\) weight.

Here \(s\) denotes the paper's turning-point parameter; the paper calls it
\(\sigma\), but it is not the concentration singular value
\(\sigma_n(c)\) used in Section 6.

This source reduces the conductor-side analytic task to the following explicit
normalization lemma:

1. translate Dunster's \(m=0\) radial function and endpoint constant into the
   Fourier convention used by the repository;
2. integrate the Bessel envelope, including the endpoint region, to obtain

   \[
   \int_1^\infty \log x\,|\psi(x)|^2dx
   \le C_n\frac{|A_{n,c}|^2}{c};
   \]
3. prove the matching two-sided comparison
   \(|A_{n,c}|^2/c\asymp d_n(c)\) in that same normalization;
4. feed those scalar bounds to
   `ExteriorLogMomentTransfer.dilationLogMomentBoundsOfCommonScale`.

The displayed radial theorem does not itself state the derivative bound needed
for the separate prime-dilation overlap.  That bound must be extracted from the
underlying Olver error theorem or proved from the transformed equation.  It is
not needed for the conductor logarithmic-moment estimate above.

This note is a reduction, not a completed PSWF asymptotic proof.
