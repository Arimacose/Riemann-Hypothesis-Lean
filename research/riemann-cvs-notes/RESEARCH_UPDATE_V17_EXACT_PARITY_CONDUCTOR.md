# V17 research update: exact-parity prolate and conductor bridge

## Status summary

This update records a revision of the asymptotic CvS/prolate main line.  It does
not prove the Riemann hypothesis and does not yet prove that the actual Weil
ground state is simple and even.

The main progress is structural:

1. exact additive Fourier parity can be imposed on compressed prolate vectors
   without losing their optimal fixed-index exterior-defect scale;
2. the constrained secular hierarchy and its quartic even/odd separation
   survive that exact symmetrization;
3. the archimedean logarithmic energy of a prolate leakage tail satisfies an
   exact conductor identity;
4. the conductor lower bound on a fixed low-mode block reduces to a
   defect-weighted scalar inequality;
5. the remaining dangerous prime contribution is reduced to a concrete
   dilation-overlap estimate for endpoint-oscillatory PSWF tails;
6. an odd-sector Temple/Schur lower bound is still required before trial-vector
   ordering becomes true ground-state ordering.

---

## 1. Correction to the fixed-Hermite shortcut

The explicit fixed-Hermite radical tails have exterior masses of the form

\[
e_+^{\mathrm H}
\asymp
\lambda^7e^{-2\pi\lambda^2},
\qquad
 e_-^{\mathrm H}
\asymp
\lambda^{11}e^{-2\pi\lambda^2}.
\]

The fixed-index prolate defects have the sharper scale

\[
d_4
\asymp
\lambda^9e^{-4\pi\lambda^2},
\qquad
 d_6
\asymp
\lambda^{13}e^{-4\pi\lambda^2}.
\]

Thus fixed-Hermite vectors are exponentially above the pure prolate defect
scale.  This does not invalidate them as explicit Weil-form probes, because the
actual Weil spectrum has not yet been proved comparable to the prolate defect
operator.  It does show that comparing the two fixed-Hermite trial values is
not, by itself, a Temple proof of the true sector ordering.

The generic Temple budgets are formalized in
`OddTempleParityTransfer.lean`.

---

## 2. Exact Fourier symmetrization

Let \(P\) be the time cutoff, let \(\mathcal F^2=1\) on the real-even ambient
space, and let

\[
P\mathcal Fp_n
=
\varepsilon_n\sigma_n p_n,
\qquad
\varepsilon_n\in\{+1,-1\},
\qquad
0<\sigma_n<1.
\]

Define

\[
S_np_n
:=
p_n+\varepsilon_n\mathcal Fp_n.
\]

Then

\[
\mathcal F S_n
=
\varepsilon_nS_n.
\]

Writing \(Q=1-P\),

\[
QS_n
=
\varepsilon_nQ\mathcal Fp_n.
\]

For a normalized principal vector,

\[
\|S_n\|^2=2+2\sigma_n,
\]

and the normalized exact-parity exterior defect is

\[
\boxed{
\widetilde d_n
=
\frac{1-\sigma_n^2}{2+2\sigma_n}
=
\frac{1-\sigma_n}{2}.
}
\]

Since \(d_n=1-\sigma_n^2\),

\[
\frac14d_n
\le
\widetilde d_n
\le
\frac12d_n,
\]

and for fixed index

\[
\widetilde d_n\sim\frac14d_n.
\]

The normalized squared boundary residue becomes

\[
\boxed{
\widetilde r_n
=
\frac{1+\sigma_n}{2}r_n
\sim r_n.
}
\]

These identities are isolated in:

- `SymmetrizedProlateBridge.lean`;
- `SymmetrizedProlateSecular.lean`;
- `SymmetrizedProlateGap.lean`.

---

## 3. Exact-parity constrained secular ratio

The exact two-pole secular weight changes by

\[
\frac{a_0r_0}{a_0r_0+a_1r_1}
-
\frac{r_0}{r_0+r_1}
=
\frac{r_0r_1(a_0-a_1)}
{(a_0r_0+a_1r_1)(r_0+r_1)},
\]

where

\[
a_j=\frac{1+\sigma_j}{2}.
\]

Because \(a_j\to1\), the Hermite residue limits remain

\[
\eta_+\to\frac8{11},
\qquad
\eta_-\to\frac8{13}.
\]

Also

\[
\frac{\widetilde d_4}{\widetilde d_6}
=
\frac{d_4}{d_6}
\frac{1+\sigma_6}{1+\sigma_4}
\sim
\frac{d_4}{d_6}.
\]

Hence the exact-parity constrained-prolate model retains

\[
\boxed{
\frac{\widetilde\nu_+}{\widetilde\nu_-}
\sim
\frac{195}{1408\pi^2}\lambda^{-4}.
}
\]

A constant-factor version is already enough for the later Weil transfer.

---

## 4. Exact conductor identity

Let

\[
t_n=Q\mathcal Fp_n,
\qquad
d_n=1-\sigma_n^2.
\]

The compressed Fourier relation implies

\[
\boxed{
\mathcal Ft_n
=
d_np_n-arepsilon_n\sigma_nt_n.
}
\]

Let \(M=\log|x|\) and

\[
\mathcal H=M+\mathcal FM\mathcal F.
\]

Because retained and exterior supports are disjoint,

\[
\boxed{
\langle t_n,\mathcal Ht_n\rangle
=
(1+\sigma_n^2)
\langle t_n,Mt_n\rangle
+d_n^2\langle p_n,Mp_n\rangle.
}
\]

Equivalently,

\[
\langle t_n,\mathcal Ht_n\rangle
=
(2-d_n)\langle t_n,Mt_n\rangle
+d_n^2\langle p_n,Mp_n\rangle.
\]

This replaces an unproved identification of the prolate tail with the
fixed-Hermite spatial boundary layer.  It is formalized in
`ProlateConductorIdentity.lean`.

---

## 5. Defect-weighted low-block coercivity

For a same-sign combination of orthogonal fixed-index tails, suppose every
active defect satisfies \(d_i\le\delta\).  If multiplication by \(M\) is
bounded below by \(L\) on the exterior support and by \(-C\) on the relevant
retained low-mode space, the exact Fourier-tail decomposition gives

\[
\boxed{
Q_{\mathcal H}(a)
\ge
\bigl(2L-(L+C)\delta\bigr)
\sum_i d_i|a_i|^2.
}
\]

For fixed indices, \(\delta\) is exponentially small.  Thus even a retained
logarithmic bound growing polynomially in the parameter is harmless at this
stage.

The scalar certificate is in
`ConductorDefectCoercivity.lean`.

---

## 6. Correct logarithmic-moment target

On the exterior support,

\[
\langle t,\log|x|t\rangle
\ge
\log\lambda\,\|t\|^2.
\]

For the even trial upper bound it is enough to prove the coarse estimate

\[
\langle t,\log|x|t\rangle
\le
K\log\lambda\,\|t\|^2
\]

for a fixed constant \(K\) on the required finite fixed-index family.  An exact
limiting profile and an exact coefficient two are not necessary.

`PROLATE_LOG_MULTIPLIER_CONDUCTOR_AUDIT.md` records this corrected target.

---

## 7. Prime dilation-overlap target

A global norm bound for the prime block is too crude.  For an exterior
fixed-index tail with endpoint-oscillatory carrier, dilation by \(m\ge2\)
changes the phase by a nonstationary amount.  The target estimate is

\[
\boxed{
|\langle t_{n,c},D_mt_{k,c}\rangle|
\le
\frac{C_{n,k}}
{c(m-1)\sqrt m}
\|t_{n,c}\|\|t_{k,c}\|.
}
\]

After multiplying by \(\Lambda(m)/\sqrt m\), the series

\[
\sum_{m\ge2}
\frac{\Lambda(m)}{m(m-1)}
\]

converges.  The resulting prime block would be \(O(c^{-1})\) relative to the
defect Gram matrix and negligible compared with the conductor scale.

This is currently a precise analytic target, not a proved property of actual
PSWF tails.  See `PRIME_DILATION_OVERLAP_TARGET.md`.

---

## 8. Form-domain realization

The zero extension of a \(C^1\) prolate mode has Fourier decay \(O(1/|s|)\)
by integration by parts.  Therefore it belongs to the logarithmic model form
domain

\[
\int
\log(2+|s|)|\widehat f(s)|^2ds<\infty.
\]

The exact Fourier symmetrization also belongs to that domain.  The right
functional-analytic task is therefore to extend the radical identity from a
Schwartz core to the closed logarithmic form domain while preserving/correcting
the two boundary conditions.  Exponentially accurate Schwartz smoothing should
not be assumed necessary before the closure theorem is audited.

See `SYMMETRIZED_PROLATE_FORM_DOMAIN.md`.

---

## 9. Current bottleneck

The active asymptotic chain is now

\[
\text{exact-parity constrained prolate hierarchy}
\]

\[
\Downarrow
\]

\[
\text{conductor coercivity}
+
\text{exterior log-moment upper bound}
+
\text{prime/pole restricted estimates}
\]

\[
\Downarrow
\]

\[
\text{actual Weil low-block comparison}
+
\text{odd complement Schur/Temple lower bound}
\]

\[
\Downarrow
\]

\[
\text{strict simple-even Weil ground state}.
\]

The two principal unresolved analytic inputs are:

1. a uniform fixed-index PSWF exterior asymptotic with derivative/integrable
   remainder strong enough for the dilation-overlap estimate;
2. a full odd-sector lower bound controlling the complement and low/high
   coupling after the actual prime and pole forms are included.

Only after those are proved does the later ground-state-to-\(\Xi\) convergence
problem become the dominant RH gap.

---

## 10. Machine status

The new repository is `Arimacose/Riemann-Hypothesis-Lean`, and the active branch
is `research/cvs-prolate-v17`.

The previously established `CommonLeadingWeilTransfer.lean` workflow had a
green kernel/axiom audit before this update.  The newly added exact-parity,
Temple, conductor, secular, gap, normalization, and coercivity modules have
been submitted with dedicated workflows and an aggregate umbrella build.  They
must be treated as **CI-pending until the latest aggregate run is inspected and
all failures, if any, are repaired**.

No theorem in this update should be described as an RH proof.
