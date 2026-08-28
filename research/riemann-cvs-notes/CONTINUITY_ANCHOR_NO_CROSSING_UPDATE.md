# Continuity + small-support anchor: the parity problem reduces to no crossing

## Executive statement

Two analytic inputs that had previously been treated as future obligations are
already available in the literature for the actual Weil variational problem:

1. Bombieri proves that the lowest even and odd Rayleigh infima are continuous
   decreasing functions of the support parameter.
2. Suzuki proves that for sufficiently small support the lowest eigenvalue is
   simple and its eigenfunction is even.

Consequently, the global simple-even problem does **not** require constructing
a new large-parameter parity anchor.  It is enough to rule out an even/odd
crossing on the connected parameter ray.  This makes the boundary-overlap /
Sylvester route structurally more important than the earlier direct odd-sector
Temple route.

This note is an architecture update, not a proof of no crossing.

---

## 1. Bombieri's continuity theorem

In *Remarks on Weil's quadratic functional in the theory of prime numbers, I*,
Theorem 5, Bombieri defines the even and odd infima

\[
\mu_+(M),\qquad \mu_-(M)
\]

of the Weil quadratic functional on the unit sphere of
\(L^2([M^{-1},M])\), and proves that both are continuous decreasing functions
of \(M\).

Thus the gap

\[
g(M)=\mu_-(M)-\mu_+(M)
\]

is continuous.

The relevant source is Bombieri (2000), Theorem 5, pp. 199--200.

---

## 2. Suzuki's small-support anchor

Suzuki's screw-function realization proves that, for sufficiently small
interval length, the lowest eigenvalue of the self-adjoint Weil operator is
simple and its eigenfunction is even.  Hence there exists an anchor parameter
\(M_0>1\) such that

\[
\boxed{\mu_+(M_0)<\mu_-(M_0).}
\]

This is an operator-level anchor, not a finite Galerkin observation.

---

## 3. Topological consequence

If one proves

\[
\boxed{\mu_+(M)\ne\mu_-(M)\quad\text{for every }M\ge M_0,}
\]

then continuity alone gives

\[
\boxed{\mu_+(M)<\mu_-(M)\quad\text{for every }M\ge M_0.}
\]

The scalar/topological implication is already formalized in
`RiemannCvs/ParityOrderContinuation.lean`.

Therefore the large-parameter `lambda^-4` prolate parity separation remains
valuable as quantitative evidence and as a route to boundary-gap estimates,
but it is no longer logically necessary as the *anchor* for global parity.

---

## 4. Continuous rank-one Sylvester identity

There is also a natural continuous analogue of the finite CvS displacement
identity.  Suppose, schematically, that on a symmetric interval \([-a,a]\)

\[
(Qf)(x)=\int_{-a}^a h(x-y)f(y)\,dy
\]

with even kernel \(h\).  Differentiating and integrating by parts gives

\[
(DQ-QD)f(x)
=h(x+a)f(-a)-h(x-a)f(a).
\]

For even \(f\), this is rank one:

\[
(DQ_+-Q_-D)f
=f(a)\,[h(x+a)-h(x-a)].
\]

For an odd eigenfunction \(g\), self-adjointness and parity give

\[
\langle h(\cdot+a)-h(\cdot-a),g\rangle
=-2\lambda g(a)
\]

when \(Qg=\lambda g\).

Thus, away from the zero eigenvalue, a common even/odd eigenvalue forces an
endpoint overlap to vanish.  This is the continuous counterpart of the
already-formalized finite rank-one Sylvester obstruction.

The precise CvS/Weil kernel is distributional rather than a smooth convolution
kernel, so the integration-by-parts identity must be established on a core and
extended to the operator/form domain before it can be used as a theorem.

---

## 5. New bottleneck

The parity problem can now be organized as

\[
\text{Suzuki small-support simple-even anchor}
+\text{Bombieri continuity}
+\text{global no crossing}
\Longrightarrow
\text{global even ground state}.
\]

The only genuinely new global ingredient in this chain is no crossing.

The current quantitative route to no crossing is still the strict
boundary-constraint gap:

\[
\mu_\pm(M)<\nu_\pm(M),
\]

because it forces the relevant boundary overlaps to be nonzero.  The pure
prolate model supplies an exceptionally forgiving `lambda^-8` reference
margin for these gaps.  The remaining analytic task is to transfer enough of
that margin to the actual Weil operator without assuming global Weil
positivity.

---

## 6. Research priority update

The preferred order is now:

1. finish the fixed-index prolate-to-Weil tail comparison, including the
   corrected stationary-phase prime estimate;
2. use the `lambda^-8` unconstrained/constrained reference gap to prove
   nonzero boundary overlaps for sufficiently large parameter;
3. certify the remaining compact parameter interval by rigorous interval
   spectral/boundary-overlap computation if necessary;
4. combine with Bombieri continuity and the Sylvester obstruction to obtain
   global parity ordering;
5. derive simplicity from the displacement identity;
6. return to the ground-state/prolate-to-Xi convergence bridge.

This route avoids reproving a global parity anchor that the existing literature
already supplies.
