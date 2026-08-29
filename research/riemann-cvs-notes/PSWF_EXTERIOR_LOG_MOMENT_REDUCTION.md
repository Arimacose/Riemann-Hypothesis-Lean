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

The main weight is now explicit.  Dunster (3.1) gives \(\eta=\xi^2\); combining
the fourth-root prefactor in (3.5) with the leading squared Bessel amplitude
\(2/(\pi c\xi)\) leaves, up to the global constant \(2/\pi\),

\[
w_a(x)=\frac{1}{\sqrt{(x^2-1)(x^2-a)}},
\qquad a=s^2.
\]

Lean definitions `prolateFixedWeightRadicand` and `prolateFixedWeight` encode
this formula.  On \(0\le a\le1/2\), \(2\le x\le3\), the theorem
`prolateFixedWeightBounds` proves

\[
\frac19\le w_a(x)\le\frac13,
\]

and `prolateFixedWeightMassLowerOnTwoThree` proves the integral lower bound
\(\int_2^3w_a(x)dx\ge1/9\), including continuity and interval integrability.

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

The source relation for the positive radial slope has now also been reduced to
explicit Lean functions and derivative formulas.  The earlier algebraic lemma
`ProlateDilationStationaryPoint.prolateSlopeBoundsOnTwoThree` proves

\[
1\le \xi'(x)\le 2,\qquad 2\le x\le3,
\]

from \(0\le s^2\le1/2\) and the cleared identity
\((x^2-1)\xi'(x)^2=x^2-s^2\).  The new definition
`prolateFixedPhaseSlope` is the positive square root

\[
p_a(x)=\sqrt{\frac{x^2-a}{x^2-1}},
\]

and `prolateFixedPhaseSlope_hasDerivAt` verifies the source-specific formula

\[
p_a'(x)=\frac{x(a-1)}{p_a(x)(x^2-1)^2}.
\]

On the same parameter rectangle Lean now proves all of the crude constants
needed by integration by parts:

\[
1\le p_a\le2,
\qquad |p_a'|\le\frac13,
\qquad |w_a'|\le2.
\]

Here `prolateFixedWeight_hasDerivAt` checks the exact derivative

\[
w_a'(x)=
-\frac{x(2x^2-a-1)}{\bigl(\sqrt{(x^2-1)(x^2-a)}\bigr)^3}.
\]

For the reduced weight \(W_a=w_a/p_a\), the definitions
`prolateFixedReducedWeight` and `prolateFixedReducedWeightDerivative` instantiate
the quotient rule.  Theorems
`prolateFixedReducedWeight_abs_le_one_third` and
`prolateFixedReducedWeightDerivative_abs_le_three` give

\[
|W_a|\le\frac13,
\qquad |W_a'|\le3.
\]

Continuity and interval integrability of the explicit slope and reduced-weight
derivative are also formalized, so `intervalVariationBoundOnTwoThree` gives
\(\int_2^3|W_a'|\le3\).  Combining endpoint bound \(1/3\), variation bound
\(3\), weight mass \(1/9\), and doubled oscillatory frequency \(2c\), the
uniform-budget inequality is valid for \(c\ge33\).  The theorem
`prolateFixedIntervalWeightedCosSqLower` therefore proves, for every phase with
derivative \(p_a\) on `[2,3]` and every offset \(\theta\),

\[
\frac1{36}\le
\int_2^3 w_a(x)\cos^2\!\bigl(c\xi(x)+\theta\bigr)\,dx,
\qquad c\ge33.
\]

Thus the leading fixed-interval oscillatory lower bound is no longer an open
calculus or variation obligation in the Lean development.

The phase is now closed as an internal object as well.  Lean defines

\[
\xi_a^{[2]}(x)=\int_2^x p_a(t)\,dt
\]

as `prolateFixedPhase` and proves
`prolateFixedPhase_hasDerivAt`.  Theorems
`prolateFixedPhaseWeightedCosSqLower` and
`prolateFixedPhaseActualMassLowerOfInvFrequencyError` specialize the leading
and error-absorption results to this explicit primitive.  Dunster's phase from
(2.7) has the same derivative on `[2,3]`; its different lower integration limit
therefore changes only the additive phase offset already quantified by these
theorems.

That phase identification is now itself a Lean theorem rather than an informal
calculus remark.  `sourcePhase_eq_prolateFixedPhase_add_base` proves that every
source phase with derivative `prolateFixedPhaseSlope a` satisfies

\[
\xi_{\mathrm{source}}(x)
=\xi_a^{[2]}(x)+\xi_{\mathrm{source}}(2)
\qquad (2\le x\le3).
\]

The companion theorem `sourcePhaseCosine_eq_prolateFixedPhaseCosine` pushes
this equality through the oscillatory factor and produces the exact adjusted
offset

\[
c\,\xi_{\mathrm{source}}(2)+\theta.
\]

The remainder conversion is now formalized at function level rather than only
as scalar algebra.  `intervalSqReferenceSplit` integrates
\((f+e)^2\le2f^2+2e^2\), and
`prolateFixedIntervalErrorMassUpper` converts a pointwise estimate

\[
|e(x)|^2\le \kappa\,\mathcal A\,w_a(x)
\]

into \(\int_2^3|e|^2\le(\kappa/3)\mathcal A\).  Consequently
`prolateFixedIntervalActualMassLowerOfErrorBudget` proves

\[
\frac{\mathcal A}{144}
\le \int_2^3|f(x)|^2dx
\]

whenever \(48\kappa\le1\).  Its fixed-index specialization
`prolateFixedIntervalActualMassLowerOfInvFrequencyError` takes
\(\kappa=K^2/c^2\), so the explicit absorption threshold is
\(48K^2\le c^2\).

The source asymptotics naturally arrive in two stages rather than as one
pre-combined error: Dunster's uniform PSWF-to-Bessel remainder, followed by the
large-argument Bessel-to-cosine remainder.  Lean now mirrors that structure.
The scalar lemma `sq_add_le_two_invFrequencyErrorBudget` proves

\[
|e_D+e_B|^2
\le
\frac{2(K_D^2+K_B^2)}{c^2}\,\mathcal A\,w_a
\]

from the two separate pointwise squared estimates.  The theorem
`prolateFixedPhaseActualMassLowerOfSeparatedErrors` constructs the combined
error and its interval integrability internally, composes the two functional
identities through the intermediate Bessel term, and retains
\(\mathcal A/144\) whenever

\[
96(K_D^2+K_B^2)\le c^2.
\]

The leading function is also closed as an internal object.  Lean defines
`prolateFixedCosineReference` by

\[
r_{a,c,\theta,\mathcal A}(x)
=
\sqrt{\mathcal A w_a(x)}
\cos\!\bigl(c\xi_a^{[2]}(x)+\theta\bigr).
\]

`prolateFixedCosineReference_sq` proves its exact squared normalization, while
`prolateFixedCosineReferenceContinuousOnTwoThree` and
`prolateFixedCosineReferenceSqIntervalIntegrable` discharge the continuity and
integrability hypotheses that were previously supplied manually.

Dunster's fixed-index parameter estimate can now enter through the source
shape \(a\le K_a/c\).  The lemma
`prolateParameter_le_half_of_invFrequency` proves

\[
a\le\frac{K_a}{c},\qquad 2K_a\le c
\quad\Longrightarrow\quad
a\le\frac12.
\]

Consequently `prolateFixedPhaseActualMassLowerOfCanonicalReference` needs
neither an abstract reference function, nor its square identity or
integrability, nor a separately assumed \(a\le1/2\).  It derives all of them
before invoking the separated-error mass theorem.

The source normalization has now been pushed one layer further.  Lean defines
the exact Dunster prefactor

\[
q_{a,\xi}(x)
=\frac{\sqrt{\xi(x)}}
       {\sqrt{\sqrt{(x^2-1)(x^2-a)}}},
\]

the leading Bessel scale

\[
b_c(\xi)=\sqrt{\frac{2}{\pi c\xi}},
\]

and the intermediate function

\[
g(x)=Nq_{a,\xi}(x)J_0(c\xi(x)).
\]

These are `prolateFixedDunsterPrefactor`, `besselJ0LeadingScale`, and
`prolateFixedBesselIntermediate`.  The theorem
`prolateFixedDunsterBesselScale_sq` verifies the exact cancellation

\[
\bigl(Nq_{a,\xi}(x)b_c(\xi(x))\bigr)^2
=N^2\frac{2}{\pi c}\,w_a(x).
\]

Thus the repository amplitude is no longer a free adapter variable:
`prolateFixedDunsterAmplitude N c = N^2(2/(\pi c))`.  The source cosine
reference uses the literal Dunster phase \(c\xi(x)-\pi/4\), and
`prolateFixedSourceCosineReference_sq` converts its square to the internal
primitive with the exact offset \(c\xi(2)-\pi/4\).

The source phase and regularity bookkeeping are closed too.  From
\(\xi(2)\ge1\) and \(\xi'=p_a\), Lean proves \(\xi(x)\ge1\) on `[2,3]` and
derives continuity of the prefactor, Bessel intermediate, source cosine
reference, and the two difference errors.  Therefore
`prolateFixedSourceActualMassLowerOfRawDunsterBesselErrors` takes the actual
mode, a continuous `J0` function, the phase derivative, and the two raw
pointwise estimates directly; it constructs every intermediate/error function
and every integrability proof internally.

The large-argument coefficient arithmetic is explicit rather than hidden in a
symbolic \(K_B\).  For order zero the first relevant DLMF coefficients give

\[
\frac1{8z}+\frac9{128z^2}+\frac{75}{1024z^3}
\le \frac{275}{1024z},\qquad z\ge1.
\]

This is `dlmfJ0FirstRemainderBudget`.  The theorem
`besselJ0LeadingCosineErrorOfDlmfBudget` converts the corresponding absolute
error into the squared source interface with the fixed constant
\(K_B=275/1024\).  Consequently
`prolateFixedSourceActualMassLowerOfDlmfDunsterErrors` leaves only \(K_D\)
symbolic and uses the concrete threshold

\[
96\left(K_D^2+(275/1024)^2\right)\le c^2.
\]

The fixed-interval estimate is now composed with the exterior envelope as
well.  If the `[2,3]` mass is bounded above by the positive exterior mass and
the hyperbolic density satisfies the established `sech` envelope with
coefficient `upper`, then
`dilationLogMomentBoundsOfProlateFixedPhaseApproximation` proves

\[
(\log R)M\le \mathcal H
\le (\log R+288\,\mathrm{upper})M.
\]

The constant is exactly \(2\,\mathrm{upper}/(1/144)=288\,\mathrm{upper}\).
This is the conductor-ready composition that the earlier reduction left as a
manual chain of inequalities.

The parallel theorem
`dilationLogMomentBoundsOfSeparatedDunsterBesselErrors` exposes the two source
remainders independently and reaches the same conductor bounds directly.  No
manual construction of a single opaque `error` function or a square-root
combined constant is needed at the source-adapter boundary.

The stronger wrapper
`dilationLogMomentBoundsOfCanonicalReferenceAndSeparatedErrors` additionally
builds the canonical reference and converts \(a\le K_a/c\) into the fixed
parameter rectangle internally.  Its remaining analytic inputs now match the
source expansion directly: actual-to-intermediate identity,
intermediate-to-canonical-reference identity, and the two pointwise error
bounds.

The concrete wrapper `dilationLogMomentBoundsOfDlmfDunsterSource` now performs
the same conductor composition directly from the Dunster-prefactor/J0 source
data.  It derives \(a\le1/2\), fixes \(K_B=275/1024\), constructs both errors,
proves their continuity, obtains the fixed-interval mass lower bound, and then
applies the `sech` envelope to return the same
\((\log R+288\,\mathrm{upper})M\) upper bound.

The abstract `J0` argument has now been replaced by a repository function as
well.  `BesselJ0Series.besselJ0` is defined by the canonical real series

\[
J_0(x)=\sum_{n=0}^{\infty}
\frac{(-1)^n(x^2/4)^n}{(n!)^2}.
\]

Lean proves absolute summability at every real argument by comparison with
\(\sum |x^2/4|^n/n!\), uniform convergence on every symmetric compact
interval, and therefore global continuity.  It also proves evenness,
\(J_0(0)=1\), the first two nonconstant terms, and the exact recurrence

\[
t_{n+1}(x)
=-\frac{x^2/4}{(n+1)^2}t_n(x).
\]

`BesselJ0DifferentialEquation` now differentiates this concrete series twice,
with compact-interval summable majorants for both derivative series.  Lean
proves the two global derivative identities, the initial values

\[
J_0'(0)=0,\qquad J_0''(0)=-\frac12,
\]

and the order-zero equation

\[
x^2J_0''(x)+xJ_0'(x)+x^2J_0(x)=0
\]

on the whole real axis.  This removes the differential-equation
characterization of the repository series from the remaining DLMF boundary.
The integral bridge below is proved directly from the same coefficients, so it
does not rely on uniqueness at the singular point.

That bridge is now explicit.  `BesselJ0IntegralRepresentation` evaluates the
even sine moments, controls the integrated cosine series by the summable
`cosh |x|` series, and applies dominated convergence to prove

\[
J_0(x)=\frac1\pi\int_0^\pi \cos(x\sin t)\,dt
\qquad (x\in\mathbb R).
\]

The concrete repository series is therefore connected to a real oscillatory
integral without appealing to ordinary ODE uniqueness at the regular singular
point.  `BesselJ0StationaryPhase` now translates the stationary point
`t=\pi/2` to the origin, proves the centered and half-interval formulas

\[
J_0(x)=\frac2\pi\int_0^{\pi/2}\cos(x\cos u)\,du,
\]

and certifies that this is the unique critical point, with first derivative
zero and second derivative `-1`.  The exact coordinate
`s=2\sin(u/2)` is strictly increasing on the reduced interval and turns the
phase into `\cos u=1-s^2/2`; the integrand is also split into its exact cosine
and sine quadratic-oscillation sectors.  The remaining DLMF task now starts at
the transformed Jacobian and its even-power remainder bounds.

The specializations
`prolateFixedSourceActualMassLowerOfConcreteJ0DlmfDunsterErrors` and
`dilationLogMomentBoundsOfConcreteJ0DunsterSource` consequently remove both
the abstract Bessel function and its continuity hypothesis from the fixed-mass
and conductor interfaces.

The next DLMF layer is now explicit as well.  Following
[NIST DLMF 10.17.1 and 10.17.3](https://dlmf.nist.gov/10.17),
`BesselJ0Dlmf.orderZeroCoefficient` specializes the Hankel coefficients at
order zero and Lean proves

\[
a_0=1,\qquad a_1=-\frac18,\qquad
a_2=\frac9{128},\qquad a_3=-\frac{75}{1024}.
\]

For positive real argument, the DLMF real-axis rule bounds the even-series
remainder after (a_0) by (9/(128z^2)), and the odd-series remainder after
(a_1/z) by (75/(1024z^3)).  The proof-complete theorem
`leadingCosine_error_of_separated_remainders` now combines exactly those two
bounds, using only the triangle inequality and the unit bounds for sine and
cosine, into

\[
\left|\sqrt{\frac2{\pi z}}\cos\left(z-\frac\pi4\right)-J_0(z)\right|
\le
\sqrt{\frac2{\pi z}}
\left(\frac1{8z}+\frac9{128z^2}+\frac{75}{1024z^3}\right).
\]

`BesselJ0Dlmf.HasFirstDlmfRemainderBound` names the remaining global analytic
statement.  `concreteJ0DlmfAbsoluteErrorPointwiseOfGlobal` proves that this one
positive-axis predicate automatically supplies the old pointwise hypothesis on
([2,3]): (c\ge33) and the source-phase derivative imply
(c\,\xi(x)>0).  The new wrappers
`prolateFixedSourceActualMassLowerOfConcreteJ0GlobalDlmf` and
`dilationLogMomentBoundsOfConcreteJ0GlobalDlmfSource` therefore accept the
single global predicate directly.

The remaining source-specific fixed-interval obligation is now narrower:
construct the even and odd DLMF remainders from the exact quadratic coordinate
and prove their first-neglected-term bounds; state Dunster's uniform PSWF-to-Bessel error
in the exact normalized prefactor above; and supply a concrete
(a\le K_a/c\) estimate, its eventual threshold, and the source-phase
derivative.  The Bessel function, its global convergence, continuity, two
termwise derivatives, initial data, order-zero differential equation, and real
Poisson--Schlafli integral representation, the
first DLMF coefficient specialization, separated-remainder combination,
source-interval transport, source function definitions,
phase-base conversion, error construction, leading weight and mass, every
required derivative and variation constant, nonlinear integration by parts,
the leading \(1/36\) lower bound, complete two-error absorption to
\(\mathcal A/144\), defect normalization, and the conductor-ready
logarithmic-moment composition are already in Lean.

The displayed radial theorem does not itself state the derivative bound needed
for the separate prime-dilation overlap.  That bound must be extracted from the
underlying Olver error theorem or proved from the transformed equation.  It is
not needed for the conductor logarithmic-moment estimate above.

This note is a reduction, not a completed PSWF asymptotic proof.
