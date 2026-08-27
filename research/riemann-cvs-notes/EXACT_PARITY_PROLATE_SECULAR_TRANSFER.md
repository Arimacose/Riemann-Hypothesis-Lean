# Exact-parity prolate secular transfer

## Main conclusion

The fixed-index constrained-prolate hierarchy survives the passage from a
compressed Fourier eigenvector to an **exact** Fourier-parity global vector.
The relevant defects and boundary residues are modified by explicit factors
that tend to common constants.  Consequently the leading quartic parity ratio
is unchanged:

\[
\boxed{
\frac{\widetilde\nu_+(\lambda)}
     {\widetilde\nu_-(\lambda)}
\sim
\frac{195}{1408\pi^2}\lambda^{-4}.
}
\]

Here \(\widetilde\nu_\pm\) denotes the boundary-constrained exterior mass in
the exact Fourier \(\pm1\) symmetrized prolate model.  This statement still
precedes the actual Weil-form comparison and the full sector lower bound.

---

## 1. Principal vectors of time and frequency cutoff

Let \(P=P_\lambda\) be the time-cutoff projection and let \(\mathcal F\) be
the additive Fourier involution on the reflection-even real Hilbert space.
Choose orthonormal compressed Fourier eigenvectors \(p_n\in\operatorname{ran}P\)
with

\[
P\mathcal Fp_n
=
\varepsilon_n\sigma_n p_n,
\qquad
0<\sigma_n<1,
\qquad
\varepsilon_n\in\{+1,-1\}.
\]

The usual concentration eigenvalue and defect are

\[
\chi_n=\sigma_n^2,
\qquad
d_n=1-\chi_n=1-\sigma_n^2.
\]

For fixed index, \(\sigma_n\to1\) as \(\lambda\to\infty\).

---

## 2. Exact Fourier-parity vectors

Within one Fourier sign class, define

\[
S_n
=
p_n+\varepsilon_n\mathcal Fp_n.
\]

Then

\[
\mathcal FS_n=\varepsilon_n S_n.
\]

Since \((1-P)p_n=0\),

\[
(1-P)S_n
=
\varepsilon_n(1-P)\mathcal Fp_n.
\]

The retained and exterior norms are

\[
PS_n=(1+\sigma_n)p_n,
\]

\[
\|(1-P)S_n\|^2
=1-\sigma_n^2,
\]

\[
\|S_n\|^2
=2+2\sigma_n.
\]

After normalization,

\[
g_n
:=
\frac{S_n}{\sqrt{2+2\sigma_n}},
\]

its exterior defect is exactly

\[
\boxed{
\widetilde d_n
:=
\|(1-P)g_n\|^2
=
\frac{1-\sigma_n^2}{2+2\sigma_n}
=
\frac{1-\sigma_n}{2}.
}
\]

Equivalently,

\[
\widetilde d_n
=
\frac{d_n}{2(1+\sigma_n)}
\sim
\frac14 d_n.
\]

Thus exact Fourier symmetrization preserves all fixed-index exponential and
polynomial defect ratios.

The algebraic identities are formalized in
`SymmetrizedProlateBridge.lean` and
`SymmetrizedProlateSecular.lean`.

---

## 3. Exact boundary residues

Let \(\ell\) be evaluation at the distinguished source boundary point.  For a
compressed eigenvector, the relation at that point gives

\[
\ell(\mathcal Fp_n)
=
\varepsilon_n\sigma_n\ell(p_n)
\]

whenever the point lies in the retained interval and the compressed Fourier
identity is valid pointwise there.

Therefore

\[
\ell(S_n)
=(1+\sigma_n)\ell(p_n).
\]

If

\[
r_n:=|\ell(p_n)|^2,
\]

then the squared boundary residue of the normalized exact-parity vector is

\[
\boxed{
\widetilde r_n
=
\frac{(1+\sigma_n)^2r_n}{2+2\sigma_n}
=
\frac{1+\sigma_n}{2}r_n.
}
\]

Hence

\[
\widetilde r_n\sim r_n.
\]

For two modes, replacing \(r_0,r_1\) by
\(a_0r_0,a_1r_1\), where

\[
a_j=\frac{1+\sigma_j}{2},
\]

changes the upper-pole secular weight by the exact amount

\[
\frac{a_0r_0}{a_0r_0+a_1r_1}
-
\frac{r_0}{r_0+r_1}
=
\frac{r_0r_1(a_0-a_1)}
{(a_0r_0+a_1r_1)(r_0+r_1)}.
\]

Since \(a_0-a_1\to0\), the Hermite limiting weights remain

\[
\eta_+\to\frac8{11},
\qquad
\eta_-\to\frac8{13}.
\]

---

## 4. The constrained exact-parity root

For diagonal normalized defects \(\widetilde d_0<\widetilde d_1\) and
normalized squared residues \(\widetilde r_0,\widetilde r_1\), the two-mode
boundary-zero energy is

\[
\widetilde\nu
=
\frac{
\widetilde r_1\widetilde d_0
+
\widetilde r_0\widetilde d_1
}{
\widetilde r_0+\widetilde r_1
}
=
\widetilde d_0
+
\frac{\widetilde r_0}
     {\widetilde r_0+\widetilde r_1}
(\widetilde d_1-\widetilde d_0).
\]

The full higher-pole secular equation has the same structure with
\(d_n,r_n\) replaced by \(\widetilde d_n,\widetilde r_n\).
Because

\[
\widetilde d_n\sim\frac14d_n,
\qquad
\widetilde r_n\sim r_n,
\]

all fixed-index gap ratios are unchanged.  In particular, the existing
Parseval/Fuchs estimate for the normalized higher-pole correction remains of
strictly smaller order than the quartic parity signal.  A fresh constant audit
is still required before reusing the precise \(O(\lambda^{-7})\) coefficient,
but the power counting is unchanged.

---

## 5. Quartic ratio

The exact defect-ratio identity is

\[
\frac{\widetilde d_4}{\widetilde d_6}
=
\frac{d_4}{d_6}
\frac{1+\sigma_6}{1+\sigma_4}.
\]

Since both singular values tend to one,

\[
\frac{1+\sigma_6}{1+\sigma_4}\to1.
\]

Using

\[
\frac{d_4}{d_6}
\sim
\frac{15}{128\pi^2}\lambda^{-4}
\]

and the limiting secular-weight ratio \(13/11\),

\[
\boxed{
\frac{\widetilde\nu_+}{\widetilde\nu_-}
\sim
\frac{13}{11}
\frac{15}{128\pi^2}\lambda^{-4}
=
\frac{195}{1408\pi^2}\lambda^{-4}.
}
\]

A coarse non-asymptotic statement also holds: for
\(0\le\sigma_4,\sigma_6\le1\), passage from squared defects to normalized
symmetrized defects costs at most a factor two.  The available quartic margin
can easily absorb this fixed distortion.

---

## 6. What this accomplishes

This construction removes one previous ambiguity:

- approximate compressed Fourier parity need not be projected after applying
  the zeta map;
- exact Fourier parity can be imposed at the source;
- the exterior leakage remains at the optimal prolate defect scale;
- the boundary secular data have explicit perturbation factors.

Thus the pure prolate quartic mechanism can be transported to an exact-parity
source model without losing its exponential scale.

---

## 7. Remaining analytic obligations

The following steps are still open.

1. **Pointwise/form-domain realization.**  Establish that the chosen principal
   vectors and their exact symmetrizations belong to the source domain needed by
   the zeta/Weil construction, or construct approximants with errors negligible
   relative to \(d_6\).

2. **Exact boundary identification.**  Verify that the boundary functional used
   in the prolate secular problem is exactly the one required for
   \(f(0)=\widehat f(0)=0\) after symmetrization.

3. **Weil boundary-layer comparison.**  Prove uniformly on the fixed-index
   exact-parity tail spaces that

   \[
   QW_\lambda(t)
   =
   \bigl(2\log\lambda+O(1)\bigr)\|t\|^2.
   \]

4. **Full odd-sector lower bound.**  Control the complement and coupling by a
   Temple or Schur estimate.

The exact-parity secular transfer solves the parity-enforcement bookkeeping; it
does not yet solve these analytic steps.
