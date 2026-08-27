# Exact-parity prolate candidates and a Temple-scale audit

## Purpose

The fixed-Hermite boundary-layer calculation gives a useful comparison between
two **actual Weil trial values**.  It does not, by itself, compare the true even
and odd ground values.  This note audits whether the fixed-Hermite odd vector is
a viable Temple trial state and records a more promising exact-parity prolate
construction.

The conclusion is a change of emphasis:

> Fixed-Hermite vectors are good explicit form-domain probes, but they are
> exponentially too expensive to serve as ground-state Temple vectors if the
> fixed-index prolate scale is the correct low-energy scale.

The preferred asymptotic trial state should retain the optimal prolate defect
while enforcing exact Fourier/inversion parity.

---

## 1. The exponential scale mismatch

The fixed-Hermite exterior masses derived in
`FIXED_HERMITE_WEIL_BOUNDARY_LAYER.md` have the scales

\[
e_+^{\mathrm H}(\lambda)
  \asymp \lambda^7 e^{-2\pi\lambda^2},
\qquad
e_-^{\mathrm H}(\lambda)
  \asymp \lambda^{11} e^{-2\pi\lambda^2}.
\]

The fixed-index prolate defects used in
`EXACT_CONSTRAINED_PROLATE_PARITY.md` have the scales

\[
d_4(\lambda)
  \asymp \lambda^9 e^{-4\pi\lambda^2},
\qquad
d_6(\lambda)
  \asymp \lambda^{13} e^{-4\pi\lambda^2}.
\]

Consequently,

\[
\frac{e_+^{\mathrm H}}{d_4}
  \asymp \lambda^{-2}e^{2\pi\lambda^2},
\qquad
\frac{e_-^{\mathrm H}}{d_6}
  \asymp \lambda^{-2}e^{2\pi\lambda^2}.
\]

Thus the fixed-Hermite trial values lie exponentially above the optimal
fixed-index prolate scale.  If the actual low Weil spectrum follows the prolate
ladder, a fixed-Hermite Rayleigh value is not expected to lie below the second
odd eigenvalue.  The basic Temple hypothesis

\[
\theta_-<\mu_{1,-}
\]

would then fail long before residual estimates become relevant.

This does **not** invalidate the fixed-Hermite form comparison.  It changes its
role: it is an explicit test of the Weil boundary-layer mechanism, not yet a
ground-state certificate.

---

## 2. The quantitative Temple requirement

Suppose a normalized odd trial state has Rayleigh value \(\theta_-\), residual
square \(R_-^2\), and a certified lower bound \(\mu_{1,-}\) for the next odd
spectral value.  Temple gives

\[
\mu_{0,-}
\ge
\theta_-
-
\frac{R_-^2}{\mu_{1,-}-\theta_-}.
\]

To retain a fraction \(1-\eta\) of the odd trial scale, one needs

\[
R_-^2
\le
\eta\,\theta_-
\bigl(\mu_{1,-}-\theta_-\bigr).
\]

For an exponentially small ground scale this is substantially stronger than
an \(O(\theta_-)\) residual-square estimate.  If the gap is itself on the same
exponential scale, the residual norm must be of the order of the eigenvalue,
not merely of its square root.

The Lean module `OddTempleParityTransfer.lean` records a generous sufficient
budget.  It shows that, after the quartic reference-mass margin is available,
one-quarter relative-form errors in each trial direction and a one-quarter
Temple loss are already more than sufficient.  What remains analytic is to
produce a trial state at the correct prolate scale for which the Temple gap
condition is true.

---

## 3. Exact Fourier symmetrization without loss of prolate scale

Let \(P_\lambda\) be the cutoff projection, let
\(Q_\lambda=1-P_\lambda\), and let \(\mathcal F\) be the additive Fourier
involution on the real-even ambient space.  For a time-limited vector
\(p=P_\lambda p\) and \(\varepsilon\in\{+1,-1\}\), define

\[
S_\varepsilon p
:=
p+\varepsilon\mathcal Fp.
\]

Then

\[
\mathcal F(S_\varepsilon p)
=
\varepsilon S_\varepsilon p.
\]

Moreover,

\[
Q_\lambda(S_\varepsilon p)
=
\varepsilon Q_\lambda\mathcal Fp.
\]

Hence imposing exact Fourier parity does not enlarge the exterior leakage.

If \(p\) is a normalized eigenvector of the compressed Fourier operator,

\[
P_\lambda\mathcal Fp
=
\varepsilon\sigma p,
\qquad -1<\sigma<1,
\]

then

\[
P_\lambda S_\varepsilon p
=(1+\sigma)p,
\]

\[
\|Q_\lambda S_\varepsilon p\|^2
=1-\sigma^2,
\]

and

\[
\|S_\varepsilon p\|^2
=2+2\sigma.
\]

After normalizing the global exact-parity vector, its exterior mass is

\[
\boxed{
\frac{1-\sigma^2}{2+2\sigma}
=
\frac{1-\sigma}{2}.
}
\]

Thus exact parity preserves the fixed-index prolate exponential scale.  The
algebra and normalization identity are formalized in
`SymmetrizedProlateBridge.lean`.

---

## 4. The correct boundary constraint

Let \(\ell\) denote the source boundary functional whose vanishing is needed
for the radical construction.  The symmetrized vector satisfies

\[
\ell(S_\varepsilon p)=0
\]

provided

\[
\boxed{
\ell(p)+\varepsilon\ell(\mathcal Fp)=0.
}
\]

Once this holds, exact Fourier parity also gives vanishing of the transformed
boundary functional.

This is a warning against silently substituting a constraint on \(p\) alone.
For compressed prolate vectors, evaluation and transformed evaluation need not
coincide exactly.  The constrained secular problem used in the final proof must
be matched to this exact symmetrized boundary functional.

---

## 5. The form-domain obstruction

The preceding construction is algebraically exact, but a zero-extended
prolate eigenfunction need not be Schwartz and may have endpoint jumps.  The
following analytic obligations remain:

1. prove that \(S_\varepsilon p\) belongs to the required Weil form domain; or
2. construct a smooth exact-parity approximation with errors
   \(o(d_6(\lambda))\) in the odd reference scale;
3. show that smoothing preserves the exact boundary constraint, or correct it
   by a quantitatively controlled finite-rank adjustment.

A merely \(o(1)\) approximation is insufficient because the target eigenvalues
are exponentially small.

---

## 6. Revised main line

The asymptotic simple-even route should now be organized as follows.

### Stage A: optimal exact-parity radical candidates

Construct exact Fourier \(+1\) and \(-1\) radical vectors from the first
boundary-constrained prolate modes, preserving exterior masses of orders
\(d_4\) and \(d_6\).

### Stage B: Weil form on prolate leakage tails

Prove, uniformly on the relevant fixed-index tail spaces,

\[
QW_\lambda(t)
=
\bigl(2\log\lambda+O(1)\bigr)\|t\|^2.
\]

Only an \(O(1)\) relative condition number is needed to preserve the
\(\lambda^{-4}\) parity margin.

### Stage C: full odd-sector lower bound

Use either:

- a Temple estimate for the optimal odd prolate trial state; or
- a low/high Schur complement estimate based on the
  \(\Theta(\lambda^8)\) internal prolate gap.

The higher-pole correction is already only \(O(\lambda^{-7})\), so it is below
the parity signal.

### Stage D: no crossing and simplicity

Combine one asymptotic strict ordering with continuity and the boundary-gap
Sylvester obstruction.  Then use the displacement relation to obtain
simplicity of the even ground state.

---

## 7. Current research status

The following pieces are now sharply separated:

- **proved/formalized algebra:** exact Fourier symmetrization, tail preservation,
  Temple error budgets, quartic parity transfer;
- **established prolate asymptotics:** the exact constrained-root
  \(\lambda^{-4}\) ratio and \(O(\lambda^{-7})\) high-pole correction,
  conditional on the cited fixed-index prolate inputs;
- **not yet proved:** form-domain realization of the exact-parity prolate
  vector, uniform Weil-tail comparison on that vector, and the full odd-sector
  Temple/Schur lower bound.

This audit prevents a false shortcut: ordering two fixed-Hermite trial values is
not the same as ordering the true sector ground states.  The exact-parity
prolate construction is designed to restore the correct exponentially small
scale.
