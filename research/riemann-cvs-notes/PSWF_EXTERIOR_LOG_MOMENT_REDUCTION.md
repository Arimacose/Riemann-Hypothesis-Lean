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

There is an exact normalization statement, rather than an additional
asymptotic hypothesis.  To avoid colliding with the differential separation
eigenvalue \(\Lambda_n(c)\), write

\[
\kappa_n(c)=\sigma_n(c)^2
\]

for the DLMF concentration eigenvalue.  With \(\tau=1\),
[DLMF 30.15.1](https://dlmf.nist.gov/30.15.E1) defines the globally normalized
band-limited mode

\[
\phi_{n,c}(x)
=
\sqrt{\frac{2n+1}{2}}\sqrt{\kappa_n(c)}\,
\operatorname{Ps}_n^0(x,c^2).
\]

[DLMF 30.15.7](https://dlmf.nist.gov/30.15.E7) and
[DLMF 30.15.8](https://dlmf.nist.gov/30.15.E8) give

\[
\int_{-1}^{1}|\phi_{n,c}(x)|^2dx=\kappa_n(c),
\qquad
\int_{\mathbb R}|\phi_{n,c}(x)|^2dx=1.
\]

Consequently the total exterior mass is exactly \(d_n(c)\).  Since every
fixed-index mode has definite parity, the positive radial branch has the exact
mass

\[
\boxed{
\int_1^\infty |\phi_{n,c}(x)|^2dx
=\frac{d_n(c)}2.
}
\]

The scalar identity is formalized as
`ExteriorLogMomentTransfer.oneSidedExteriorMassOfConcentration`.  Thus the
mass itself is no longer a normalization gap.

What remains is to express Dunster's radial envelope coefficient in units of
this exact defect.  If \(A_{n,c}\) denotes the coefficient after applying the
displayed DLMF global normalization, the sufficient one-sided comparison is

\[
\frac{|A_{n,c}|^2}{c}
\le C_n d_n(c).
\]

It can be obtained directly from a fixed exterior interval, without first
computing the common Fuchs constant: prove

\[
L_n\frac{|A_{n,c}|^2}{c}
\le
\int_2^3|\phi_{n,c}(x)|^2dx.
\]

The right-hand side is at most \(d_n(c)/2\), so the desired comparison follows
with \(C_n=(2L_n)^{-1}\).  Only this lower Bessel mean-square estimate remains
in the fixed-index normalization step.  Fuchs' asymptotic is still used
elsewhere for defect ratios and power counting, but it is not needed to
identify the exterior mass here.

For the log-moment argument, no exact asymptotic constant is needed; a positive
uniform \(L_n\) is sufficient.

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
fixed-index estimate:

1. translate Dunster's \(m=0\) radial function and endpoint constant into the
   Fourier convention used by the repository;
2. integrate the Bessel envelope, including the endpoint region, to obtain

   \[
   \int_1^\infty \log x\,|\psi(x)|^2dx
   \le C_n\frac{|A_{n,c}|^2}{c};
   \]
3. use the fixed-interval Bessel mean square to prove
   \(|A_{n,c}|^2/c\le C_n d_n(c)\) in that same normalization;
4. feed those scalar bounds to
   `ExteriorLogMomentTransfer.dilationLogMomentBoundsOfConcentrationDefectEnvelope`.

The elementary integration in the last step is now formalized.  With

\[
\rho_{n,c}(u)
=
|\psi(\cosh u)|^2\sinh u,
\]

the fixed-interval estimate converts Dunster's envelope to the single
defect-normalized input

\[
0\le\rho_{n,c}(u)
\le
\frac{U_n' d_n(c)}{\cosh u}.
\]

Together with the exact mass \(d_n(c)/2\), the Lean theorem proves, using the
coarse inequality
\(\operatorname{sech}u\le2e^{-u}\), that

\[
\int_0^\infty
\log(\cosh u)\rho_{n,c}(u)du
\le
2U_n'd_n(c)
=
4U_n'\int_1^\infty|\phi_{n,c}(x)|^2dx.
\]

It then combines this bound with the dilation identity to give the physical
logarithmic-moment interval.  Thus no improper-integral, normalization division,
or free lower-mass parameter remains outside Lean once the displayed pointwise
envelope is measured in units of the concentration defect.

### 8.1 Extracting the `sech` envelope from Dunster (3.5)

Write (E_0(z)=\operatorname{env}J_0(z)).  The envelope used by Dunster is the
one defined in [DLMF 2.8.33--2.8.34](https://dlmf.nist.gov/2.8#E33): it is a
fixed multiple of (J_0) below a positive matching point and
((J_0^2+Y_0^2)^{1/2}) above it.  The small- and large-argument Bessel
asymptotics therefore give a finite fixed constant

\[
B_0
:=
\sup_{z>0} zE_0(z)^2
<\infty.
\]

For (m=0), Dunster (3.5) has the form

\[
\psi(x)
=
A_{n,c}
\left\{
\frac{\eta}
{(x^2-1)(x^2-s^2)}
\right\}^{1/4}
\left[J_0(c\sqrt\eta)+O(c^{-1})E_0(c\sqrt\eta)\right].
\]

After fixing (n) and taking (c\ge c_n), uniformity of the remainder and

\[
E_0(z)^2\le\frac{B_0}{z}
\]

give

\[
|\psi(x)|^2
\le
\frac{C_n|A_{n,c}|^2}
{c\sqrt{(x^2-1)(x^2-s^2)}}.
\]

Under (x=\cosh u), multiplication by
(dx/du=\sinh u=\sqrt{x^2-1}) yields

\[
\rho_{n,c}(u)
\le
\frac{C_n|A_{n,c}|^2}
{c\sqrt{x^2-s^2}}.
\]

Dunster (3.10) gives (s^2=O_n(c^{-1})).  Enlarging (c_n) so that
(0\le s^2\le1/2), and using (x\ge1), gives

\[
x^2-s^2\ge\frac{x^2}{2},
\qquad
\rho_{n,c}(u)
\le
\frac{\sqrt2C_n|A_{n,c}|^2/c}{\cosh u}.
\]

This is the pointwise hypothesis of
`dilationLogMomentBoundsOfSechEnvelope`.  After the DLMF normalization audit in
Section 6, the positive exterior mass is exactly \(d_n(c)/2\).  The remaining
analytic conversion is therefore the fixed-interval estimate

\[
L_n|A_{n,c}|^2/c
\le
\int_2^3|\phi_{n,c}(x)|^2dx
\le d_n(c)/2.
\]

### 8.2 Fixed-interval Bessel mean square

On \(I=[2,3]\), Dunster's turning parameter satisfies \(s^2=O_n(c^{-1})\),
so every algebraic prefactor in (3.5) is uniformly bounded above and below.
The radial coordinate \(\xi(x)\) is smooth there and satisfies

\[
0<a_n\le\xi'(x)\le b_n,
\qquad x\in I,
\]

for all sufficiently large \(c\).  The large-positive-argument expansion
[DLMF 10.17.3](https://dlmf.nist.gov/10.17.E3), with its real-argument error
bounds from DLMF 10.17(iii), gives uniformly on \(I\)

\[
J_0(c\xi(x))
=
\sqrt{\frac{2}{\pi c\xi(x)}}
\left(\cos(c\xi(x)-\pi/4)+O_n(c^{-1})\right).
\]

Inserting this into Dunster (3.5) shows that the main squared density is a
positive bounded weight times
\(c^{-1}\cos^2(c\xi(x)-\pi/4)\).  Since

\[
\cos^2\theta=\frac12+\frac12\cos(2\theta),
\]

one integration by parts, using the displayed lower bound for \(\xi'\), yields

\[
\int_2^3 w_{n,c}(x)
\cos^2(c\xi(x)-\pi/4)dx
\ge \ell_n>0
\]

for all sufficiently large \(c\).  Dunster's
\(O(c^{-1})\operatorname{env}J_0\) remainder contributes
\(O_n(|A_{n,c}|^2c^{-2})\) to the cross term and a still smaller squared-error
term on this fixed interval.  After enlarging the threshold once more, this
proves the required positive constant \(L_n\).

The nonoscillatory algebra is now formalized in the set-integral theorems
`ExteriorLogMomentTransfer.weightedCosSqIntegralIdentity` and
`ExteriorLogMomentTransfer.weightedCosSqIntegralLower`, with interval-integral
counterparts for the fixed compact interval.  Once integration by parts
supplies

\[
-\frac12\int_2^3 w_{n,c}(x)dx
\le
\int_2^3 w_{n,c}(x)\cos(2c\xi(x)-\pi/2)dx,
\]

Lean retains one quarter of the weight mass.  The linear-phase integration by
parts itself is also formalized in
`linearPhaseIntegrationByPartsIdentity` and
`linearPhaseOscillatoryIntegralBoundByVariation`: after the monotone change of
variables \(y=\xi(x)\), the oscillatory term is bounded by

\[
\frac{|W(y_2)|+|W(y_1)|+
\int_{y_1}^{y_2}|W'(y)|dy}{2c}.
\]

The combined theorem
`linearPhaseWeightedCosSqLowerOfVariation` closes the linear-phase version of
this generic fixed-interval mean-square step directly: whenever the displayed
endpoint-plus-variation budget is at most half of the weight mass, the weighted
squared cosine retains at least one quarter of that mass.

The additional theorems `nonlinearPhaseIntegrationByPartsIdentity`,
`nonlinearPhaseOscillatoryIntegralBoundByVariation`, and
`nonlinearPhaseWeightedCosSqLowerOfVariation` now eliminate the need to
formalize a separate measure-theoretic substitution.  On `[2,3]`, set
`W = w_{n,c}/ξ'` and prove the pointwise factorization `w_{n,c}=W ξ'`; Lean then
performs integration by parts directly in the original `x` variable and gives
the same endpoint-plus-variation bound.

Theorems
`massLowerOfReferenceAndErrorBudget` and
`massLowerOfReferenceAndQuarterError` then absorb Dunster's explicit
remainder into the actual radial mass.  The remaining source-specific
formalization boundary is therefore source-specific: define
\(W=w_{n,c}/\xi'\) on `[2,3]`, verify its factorization and derivative data, and
prove uniform endpoint and total-variation bounds for \(W\), together with the
explicit Dunster remainder budget.  The nonlinear-phase integration-by-parts,
remainder absorption, defect normalization, and logarithmic-moment algebra are
already in Lean.

The displayed radial theorem does not itself state the derivative bound needed
for the separate prime-dilation overlap.  That bound must be extracted from the
underlying Olver error theorem or proved from the transformed equation.  It is
not needed for the conductor logarithmic-moment estimate above.

This note is a reduction, not a completed PSWF asymptotic proof.
