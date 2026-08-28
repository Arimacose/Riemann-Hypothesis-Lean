# V18 mainline update: the global parity problem is now a no-crossing problem

## Executive statement

The current CvS--prolate route has reached a useful structural simplification.
Two operator-level facts are already available in the literature:

1. Bombieri proves continuity of the even and odd localized Weil variational
   infima as the support parameter varies.
2. Suzuki proves that, for sufficiently small support, the localized Weil
   ground eigenvalue is simple and its eigenfunction is even.

Therefore a new large-support parity anchor is not logically necessary.  To
propagate the known small-support ordering to every support, it is enough to
rule out an even/odd ground-state crossing.

The preferred no-crossing mechanism is the rank-one Sylvester identity.  A
common even/odd eigenvalue forces one of two boundary overlaps to vanish.  A
strict gap between each unconstrained ground value and the corresponding
boundary-constrained minimum makes both overlaps nonzero and hence excludes a
crossing.

The pure fixed-index prolate model supplies an eighth-power reference margin
for those strict boundary gaps.  The new quantitative observation in this
update is that the actual constrained lower bridge may be extremely weak and
still suffice: a `lambda^-7` lower comparison leaves a linear asymptotic
margin, and even a linearly growing unconstrained upper comparison is compatible
with a `lambda^-6` constrained lower bridge.

The remaining hard problem is therefore not a sharp prolate-to-Weil isometry.
It is the much weaker but global statement that the actual boundary-constrained
Weil form retains **some positive fraction decaying slower than
`lambda^-8`** of the first constrained prolate scale.

---

## 1. Literature anchor and continuity

Bombieri, *Remarks on Weil's quadratic functional in the theory of prime
numbers, I* (2000), Theorem 5, proves that the even and odd localized infima

\[
\mu_+(M),\qquad \mu_-(M)
\]

are continuous decreasing functions of the support parameter `M`.

Suzuki, *Weil's quadratic form via the screw function* (arXiv:2606.09096,
v2, 2026), Theorem 1.4, proves that for sufficiently small interval size the
lowest eigenvalue of the localized self-adjoint Weil operator is positive,
simple, and has an even eigenfunction.

Hence there is an operator-level anchor `M0` with

\[
\mu_+(M_0)<\mu_-(M_0).
\]

If equality never occurs on the connected parameter ray, continuity preserves
this strict ordering globally.  The topological implication is formalized in
`ParityOrderContinuation.lean`.

---

## 2. The naive Perron shortcut is false in the CvS Fourier basis

A possible shortcut was to prove that each parity block is, after a diagonal
sign gauge, a symmetric irreducible Z-matrix.  Perron--Frobenius would then
force a fixed sign pattern for the ground eigenvector and could make the
boundary overlap manifestly nonzero.

The new Arb audit `audit_parity_offdiagonal_signs.py` rules out this naive
route.  At `c=13`, `N=20`, `500` bits, every off-diagonal sign is certified:

- even block: 128 positive and 82 negative entries;
- odd block: 72 positive and 118 negative entries;
- no interval entry straddles zero;
- neither block admits a diagonal `+/-1` gauge making every off-diagonal entry
  negative.

Thus the current Fourier parity matrices do not have the simple Z-matrix
structure required for a direct Perron proof.  This is a falsification of a
shortcut, not evidence against simple-even itself.

---

## 3. Eighth-power boundary-gap margin

For fixed-index prolate defects,

\[
\frac{d_0}{\nu_+}
\sim
\frac{33}{65536\pi^4}\lambda^{-8},
\qquad
\frac{d_2}{\nu_-}
\sim
\frac{585}{65536\pi^4}\lambda^{-8}.
\]

The larger coefficient is already below `1/8000` before the factor
`lambda^-8` is applied.

The generic scalar transfer is:

\[
q_{\rm low}\le M e_{\rm low},
\qquad
m e_{\rm con}\le\nu_{\rm con},
\qquad
\lambda^8 e_{\rm low}\le C e_{\rm con},
\]

and

\[
MC<m\lambda^8
\]

imply

\[
q_{\rm low}<\nu_{\rm con}.
\]

This is already formalized in `ConstraintGapTransfer.lean`.

---

## 4. New weak-bridge corollaries

The new module `WeakConstraintGapBudget.lean` records two useful consequences.

### 4.1 A `lambda^-7` constrained lower bound is enough

If

\[
q_{\rm low}\le M e_{\rm low},
\qquad
\frac{m_0}{\lambda^7}e_{\rm con}\le\nu_{\rm con},
\]

then the eighth-power reference gap gives the strict actual gap as soon as

\[
\boxed{MC<m_0\lambda.}
\]

Thus a constrained lower comparison may lose seven powers of `lambda` and
still succeed.

### 4.2 Linear upper growth plus `lambda^-6` lower decay is enough

Even if the unconstrained upper bridge is only

\[
q_{\rm low}\le M_0\lambda\,e_{\rm low},
\]

it is enough to have

\[
\frac{m_0}{\lambda^6}e_{\rm con}\le\nu_{\rm con},
\]

because the remaining condition is only

\[
\boxed{M_0C<m_0\lambda.}
\]

for sufficiently large `lambda`.

This materially weakens the analytic target.  A uniform `O(1)` condition
number is far more than necessary for the no-crossing route.

---

## 5. Fixed-index bridge status

The fixed-index prolate-to-Weil comparison has advanced substantially:

- the pure constrained-prolate parity ratio is `Theta(lambda^-4)`;
- the higher-pole secular correction is `O(lambda^-7)`;
- the exterior logarithmic moment has a uniform fixed-index bound;
- the radial prime-dilation phase has one unique endpoint-layer stationary
  point, with a uniform curvature lower bound;
- the prime overlap is reduced to a compact-parameter stationary-phase theorem;
- the stationary-point algebra and log-moment scalar transfer now pass an
  independent Lean/Mathlib CI gate.

These results control the low fixed-index sector.  They do not yet give a lower
bound on the **entire** boundary-constrained subspace.

---

## 6. The current hard theorem

A sufficient large-parameter theorem now has a deliberately weak form.
For each parity sign, let `P_lambda` denote the pure constrained-prolate
reference form and let `QW_lambda` be the actual localized Weil form.  It would
suffice to prove, on the complete boundary-constrained subspace,

\[
QW_\lambda(f)
\ge
c\lambda^{-q} P_\lambda(f),
\qquad q<8,
\]

for sufficiently large `lambda`, together with a compatible unconstrained
upper trial estimate whose polynomial growth exponent leaves total exponent
strictly below eight.

For example,

\[
QW_\lambda(f)\ge c\lambda^{-6}P_\lambda(f)
\]

would already be enough even with a linearly growing unconstrained upper
comparison.

This theorem is much weaker than global Weil positivity, but it is still a
nontrivial arithmetic lower bound on a large constrained subspace.  No proof is
currently known in this project.

---

## 7. Why the remaining problem should not be understated

The localized Weil form is positive for sufficiently short support, but global
positivity over all supports is equivalent to RH.  A lower bound on a carefully
chosen constrained subspace is weaker than full positivity, yet an arbitrary
high-mode negative intruder could still invalidate the desired constraint gap.
The existing fixed-mode stationary-phase estimates do not exclude such an
intruder.

Consequently the present route has genuinely reduced the required estimate,
but has not trivialized it.  The no-crossing theorem will be a substantive RH
advance only when this complete-subspace lower bridge is proved without
assuming a statement equivalent to Weil positivity.

---

## 8. Immediate research priorities

1. Complete the compact-parameter stationary-phase constants for the fixed
   prolate prime block.
2. Search for a decomposition of the boundary-constrained space into a fixed
   prolate low block plus a complement on which a very weak
   `lambda^-q`, `q<8`, lower bound can be proved.
3. Audit the continuous Sylvester identity and boundary functionals against the
   exact Suzuki/Bombieri form domain.
4. Use interval spectral certificates only for the remaining compact parameter
   interval after a genuine large-parameter no-crossing theorem is available.
5. Keep the Suzuki characteristic-function limit as an independent fallback
   route; it should not be conflated with the CCM ground-state convergence
   problem.

---

## Status

No RH proof is claimed.  The new contribution is a sharper reduction of the
global parity problem and a machine-checked demonstration that the required
constrained lower bridge can deteriorate polynomially by almost eight powers
without destroying the no-crossing argument.
