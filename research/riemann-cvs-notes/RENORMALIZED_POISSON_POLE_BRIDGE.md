# Renormalized Poisson bridge for unconstrained low modes

## 1. The obstruction

The fixed-Hermite exterior-tail argument uses source functions satisfying

\[
f(0)=\widehat f(0)=0.
\tag{1}
\]

Under these two conditions the map

\[
\mathcal E(f)(u)=u^{1/2}\sum_{n\ge1}f(nu)
\tag{2}
\]

intertwines additive Fourier sign with multiplicative inversion parity and its
image lies in the radical framework used by the Weil-tail splitting identity.

The lowest unconstrained Hermite/prolate modes \(h_0\) and \(h_2\), which are
needed for the eighth-power boundary-constraint gap, do not satisfy (1).  It is
therefore incorrect to apply the same radical identity to them without a
correction.

Poisson summation shows that this obstruction has a very rigid form: it is
exactly two-dimensional and coincides with the pole-mode subspace.

---

## 2. A one-parameter corrected transform

For an even function let

\[
S_f(u)=\sum_{n\ge1}f(nu).
\tag{3}
\]

Poisson summation gives

\[
f(0)+2S_f(u)
 =u^{-1}\bigl(\widehat f(0)+2S_{\widehat f}(u^{-1})\bigr),
\tag{4}
\]

or

\[
S_{\widehat f}(u^{-1})
 =uS_f(u)+\frac{uf(0)-\widehat f(0)}2.
\tag{5}
\]

Write \(r=u^{1/2}\).  For any scalar \(a\), define

\[
\boxed{
\mathcal E_a(f)(u)
 =rS_f(u)+ar f(0)
   +\left(a-\frac12\right)r^{-1}\widehat f(0).
}
\tag{6}
\]

A direct substitution into (5) gives the exact identity

\[
\boxed{
\mathcal E_a(\widehat f)(u^{-1})
 =\mathcal E_a(f)(u).
}
\tag{7}
\]

Thus no zero-value assumption is required.

If

\[
\widehat f=\varepsilon f,
\qquad \varepsilon\in\{+1,-1\},
\tag{8}
\]

then

\[
\boxed{
\mathcal E_a(f)(u^{-1})
 =\varepsilon\mathcal E_a(f)(u).
}
\tag{9}
\]

Hence the lowest unconstrained Fourier classes can also be represented by
exact inversion-parity functions, provided the two zero modes are retained in
the definition.

---

## 3. Renormalization ambiguity equals the pole subspace

For two choices \(a,b\),

\[
\boxed{
\mathcal E_b(f)(u)-\mathcal E_a(f)(u)
 =(b-a)\left(u^{1/2}f(0)
       +u^{-1/2}\widehat f(0)\right).
}
\tag{10}
\]

Therefore all corrected transforms define the same class modulo

\[
\mathcal P
 =\operatorname{span}\{u^{1/2},u^{-1/2}\}.
\tag{11}
\]

This is precisely the two-dimensional space singled out by the pole
contribution in the explicit formula.  Two convenient gauges are

\[
\mathcal E_{1/2}(f)(u)
 =u^{1/2}\left(S_f(u)+\frac{f(0)}2\right),
\tag{12}
\]

and

\[
\mathcal E_0(f)(u)
 =u^{1/2}S_f(u)
  -\frac12u^{-1/2}\widehat f(0).
\tag{13}
\]

Their difference is

\[
\frac12\left(u^{1/2}f(0)
 +u^{-1/2}\widehat f(0)\right).
\tag{14}
\]

The formal scalar identities (6)--(14) are verified in
`RiemannCvs/RenormalizedPoissonBridge.lean`.

---

## 4. Interpretation for the constraint-gap route

The new structure suggests replacing the invalid step

\[
\text{apply the zero-value radical identity directly to }h_0,h_2
\tag{15}
\]

by

\[
\text{represent }h_0,h_2
\text{ through }\mathcal E_a
\text{ and separate the pole block }\mathcal P.
\tag{16}
\]

There are two possible analytic implementations.

### 4.1 Quotient formulation

Construct the Weil space modulo \(\mathcal P\), prove that the class of
\(\mathcal E_a(f)\) is independent of \(a\), and establish a radical or
isometric identity in this quotient.  Then the lowest unconstrained reference
modes can be compared with constrained modes without carrying algebraic
\(u^{\pm1/2}\) tails.

### 4.2 Explicit pole Schur complement

Keep \(\mathcal P\) as a finite block and decompose

\[
QW=
\begin{pmatrix}
Q_{\rm physical} & B^*\\
B & Q_{\rm pole}
\end{pmatrix}.
\tag{17}
\]

The change of gauge in (10) acts only in the pole block.  A finite-dimensional
Schur complement can then make the physical comparison gauge independent.
This approach aligns with the exact rank-two pole matrix already present in
the finite CvS model.

Either route would turn the two vanishing conditions from a hard domain wall
into a finite-rank correction.

---

## 5. A useful special feature of Fourier eigenfunctions

For a Fourier eigenfunction satisfying (8),

\[
\widehat f(0)=\varepsilon f(0).
\tag{18}
\]

The pole correction becomes

\[
(b-a)f(0)
 \left(u^{1/2}+\varepsilon u^{-1/2}\right).
\tag{19}
\]

Thus each Fourier class couples to only one inversion-parity pole direction:

\[
p_+(u)=u^{1/2}+u^{-1/2},
\qquad
p_-(u)=u^{1/2}-u^{-1/2}.
\tag{20}
\]

The relevant correction is consequently rank one **inside each parity
sector**, not rank two.  This is favorable for an explicit one-pole Schur
complement and may reduce the unconstrained bridge to a scalar resolvent
estimate.

---

## 6. New focused analytic target

For each sign, let \(v_{\pm,\lambda}\) denote the retained interval part of a
corrected transform of the lowest unconstrained mode, and let
\(p_{\pm,\lambda}\) be the retained parity-matched pole vector from (20).
The immediate target is an estimate of the form

\[
QW_\pm\big|_{\operatorname{span}\{v_{\pm,\lambda},p_{\pm,\lambda}\}}
 =
\begin{pmatrix}
a_\pm & b_\pm\\
b_\pm & c_\pm
\end{pmatrix},
\tag{21}
\]

with a certified lower or upper Schur value

\[
a_\pm-\frac{b_\pm^2}{c_\pm-\mu}.
\tag{22}
\]

If the physical part retains the fixed-index
\(\lambda^{-8}\) separation and the one-pole correction is
\(o(\nu_{\pm})\), then the strict boundary-constraint gaps follow.  The
existing Lean modules `SchurQuadraticForm`, `NormalizedBlockSchur`, and
`ConstraintGapTransfer` already formalize the finite scalar implications once
these analytic estimates are supplied.

---

## 7. What has and has not been achieved

The identity (7) is an exact structural advance: it shows that nonzero source
values do not destroy the Fourier/inversion grading bridge; they introduce only
a pole-mode ambiguity.

It does **not** yet prove:

- that a corrected unconstrained mode belongs to the domain of the completed
  Weil operator;
- that the quotient by \(\mathcal P\) is positive or radical in the required
  sense;
- a bound on the pole coupling \(b_\pm\);
- the eighth-power unconstrained/constrained gap for the actual Weil operator;
- no crossing, simple-even, or RH.

The next proof-level task is therefore sharply defined: audit the completed
Weil space and derive the one-pole parity-sector Schur block associated with
(20).
