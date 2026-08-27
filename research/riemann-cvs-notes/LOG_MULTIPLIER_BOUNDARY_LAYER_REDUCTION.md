# Boundary-layer reduction for the archimedean logarithmic multiplier

## Executive statement

The large-parameter Weil/prolate bridge does not require a full operator-norm
comparison between the Weil form and the prolate concentration operator.  For a
fixed finite family of leakage tails, it is enough to prove a boundary-layer
profile theorem in logarithmic coordinates.

The universal mechanism is:

\[
\text{boundary-layer width }\delta_\lambda=\lambda^{-2}
\quad\Longrightarrow\quad
\log|D|\text{ energy }
=
\bigl(2\log\lambda+O(1)\bigr)L^2\text{ mass}.
\]

This note isolates the exact scaling calculation and states a concrete analytic
input that would close the common-leading Weil-tail estimate for fixed-index
prolate candidates.

---

## 1. One-wing exact scaling identity

Let \(\phi\in L^2(\mathbb R)\), let \(a_\lambda\in\mathbb C\), and let
\(\delta_\lambda>0\).  Define a boundary-layer profile in logarithmic
coordinate \(u\) by

\[
g_\lambda(u)
=
a_\lambda\,
\phi\!\left(\frac{u-u_\lambda}{\delta_\lambda}\right).
\]

With a unitary Fourier convention,

\[
\widehat g_\lambda(s)
=
a_\lambda\delta_\lambda
 e^{-isu_\lambda}
 \widehat\phi(\delta_\lambda s).
\]

Therefore

\[
\|g_\lambda\|_2^2
=
|a_\lambda|^2\delta_\lambda\|\phi\|_2^2.
\]

Assume

\[
\int_{\mathbb R}
  |\log|\xi||\,|\widehat\phi(\xi)|^2\,d\xi
<\infty.
\]

A change of variable \(\xi=\delta_\lambda s\) gives the exact identity

\[
\begin{aligned}
\langle g_\lambda,\log|D|g_\lambda\rangle
&=
|a_\lambda|^2\delta_\lambda
\int
\bigl(\log|\xi|-\log\delta_\lambda\bigr)
|\widehat\phi(\xi)|^2\,d\xi \\
&=
-\log\delta_\lambda\,\|g_\lambda\|_2^2
+
|a_\lambda|^2\delta_\lambda
\int \log|\xi|\,|\widehat\phi(\xi)|^2\,d\xi.
\end{aligned}
\]

Hence

\[
\boxed{
\frac{
\langle g_\lambda,\log|D|g_\lambda\rangle
}{
\|g_\lambda\|_2^2
}
=
-\log\delta_\lambda+C_\phi,
}
\]

where

\[
C_\phi
=
\frac{
\int\log|\xi|\,|\widehat\phi(\xi)|^2d\xi
}{
\|\phi\|_2^2
}.
\]

For

\[
\delta_\lambda=\lambda^{-2},
\]

this becomes

\[
\boxed{
\frac{
\langle g_\lambda,\log|D|g_\lambda\rangle
}{
\|g_\lambda\|_2^2
}
=
2\log\lambda+C_\phi.
}
\]

No asymptotic approximation is used in this one-wing calculation.

---

## 2. The actual archimedean symbol

Let \(m(s)\) be the archimedean Mellin multiplier occurring in the explicit
formula.  The required high-frequency estimate has the form

\[
m(s)=\log|s|+c_\infty+\rho(s),
\qquad
\rho(s)\longrightarrow0
\quad(|s|\to\infty),
\]

with a global bound adequate for dominated convergence.

Under the preceding logarithmic-moment hypothesis,

\[
\frac{\langle g_\lambda,m(D)g_\lambda\rangle}
     {\|g_\lambda\|_2^2}
=
-\log\delta_\lambda
+c_\infty+C_\phi+o(1).
\]

Thus at boundary width \(\lambda^{-2}\),

\[
\boxed{
\langle g_\lambda,m(D)g_\lambda\rangle
=
\bigl(2\log\lambda+O(1)\bigr)
\|g_\lambda\|_2^2.
}
\]

The coefficient \(2\log\lambda\) is independent of the mode and of the
boundary amplitude.  Mode dependence enters only through an \(O(1)\) profile
constant.

---

## 3. Two inversion-related wings

An inversion-even or inversion-odd tail has two boundary layers near the two
ends of the logarithmic cutoff interval.  Write schematically

\[
t_{\lambda,\varepsilon}(u)
=
g_{\lambda,+}(u)
+
\varepsilon g_{\lambda,-}(u),
\qquad
\varepsilon\in\{+1,-1\}.
\]

After boundary-layer rescaling, the cross term contains an oscillatory phase
whose frequency is the endpoint separation divided by
\(\delta_\lambda\).  For the multiplicative cutoff this tends to infinity.
If the weighted Fourier product is in \(L^1\), the Riemann--Lebesgue lemma gives

\[
\langle g_{\lambda,+},m(D)g_{\lambda,-}\rangle
=o\!\left(
\|g_{\lambda,+}\|_2^2+
\|g_{\lambda,-}\|_2^2
\right).
\]

Consequently, the leading coefficient is the same in the inversion-even and
inversion-odd sectors:

\[
Q_{\infty}(t_{\lambda,\varepsilon})
=
\bigl(2\log\lambda+O(1)\bigr)
\|t_{\lambda,\varepsilon}\|_2^2.
\]

This is precisely the common-leading structure needed by
`CommonLeadingWeilTransfer.lean`.

---

## 4. A finite-family profile theorem is sufficient

Let \(t_{n,\lambda}\) denote the exterior leakage tails associated with a fixed
set of exact-parity prolate modes, for example

\[
n\in\{0,4,8\}
\quad\text{or}\quad
n\in\{2,6,10\}.
\]

It is enough to prove the following.

### Boundary-layer profile hypothesis

For each fixed \(n\), there exist amplitudes \(a_{n,\lambda}\), a common scale
\(\delta_\lambda=\lambda^{-2}\), and profiles \(\phi_n\) such that the
rescaled wing converges in a weighted Fourier norm:

\[
\frac{
 t_{n,\lambda}(u_{\lambda}+\delta_\lambda y)
}{a_{n,\lambda}}
\longrightarrow
\phi_n(y),
\]

and

\[
\int
(1+|\log|\xi||)
\left|
\widehat{\phi_{n,\lambda}}(\xi)
-
\widehat{\phi_n}(\xi)
\right|^2d\xi
\longrightarrow0.
\]

Then, uniformly on the fixed finite span,

\[
\boxed{
Q_{\infty,\lambda}(t)
=
\bigl(2\log\lambda\bigr)\|t\|_2^2
+O(1)\|t\|_2^2.
}
\]

Equivalently, the normalized finite Gram matrix satisfies

\[
\frac{1}{2\log\lambda}
G^{\mathrm{arch}}_\lambda
=I+O\!\left(\frac1{\log\lambda}\right).
\]

This is much weaker than full operator convergence and is tailored to the
fixed-index parity proof.

---

## 5. Prime and pole blocks

The remaining terms should be treated as perturbations of the common
archimedean scale.

### Pole block

The pole contribution is finite rank.  On a boundary layer whose total mass is
\(e_{n,\lambda}\), it is enough to prove

\[
|Q_{\mathrm{pole}}(t)|
\le C_{\mathrm{pole}}e_{n,\lambda}
\]

with a mode-independent constant on the fixed family.

### Prime block

For each prime-power translation, same-wing overlap is controlled by the
translation autocorrelation of the limiting profile.  Cross-wing overlap is
oscillatory or exponentially suppressed.  The target estimate is

\[
|Q_{\mathrm{prime}}(t)|
\le C_{\mathrm{prime}}(\lambda)\|t\|_2^2,
\qquad
C_{\mathrm{prime}}(\lambda)=o(\log\lambda),
\]

or merely a uniform \(O(1)\) bound.  Either is sufficient.

The prime estimate must be proved for the actual moving cutoff and cannot be
replaced by a fixed-cutoff operator-norm bound that grows with the number of
prime powers.

---

## 6. Consequence for parity transfer

Suppose the finite-family theorem yields

\[
\left|
QW_\lambda(t_{n,\lambda})
-
2\log\lambda\,
\|t_{n,\lambda}\|_2^2
\right|
\le
C\|t_{n,\lambda}\|_2^2
\]

uniformly for the required modes.  Then, for large enough \(\lambda\),

\[
\frac12(2\log\lambda)\|t\|^2
\le
QW_\lambda(t)
\le
\frac32(2\log\lambda)\|t\|^2.
\]

A fixed condition number is enough.  Combining this with the exact-parity
prolate defect ratio gives the same strict \(\lambda^{-4}\) ordering after a
possibly larger finite threshold.

The higher-pole secular correction remains \(O(\lambda^{-7})\), so it does not
compete with the parity signal.

---

## 7. What this reduction changes

The principal asymptotic analytic target is no longer

\[
\|QW_\lambda-P_\lambda\|_{\mathrm{op}}\to0
\]

on an infinite-dimensional space.  It is the more concrete statement:

\[
\boxed{
\text{fixed-index prolate leakage has a universal }
\lambda^{-2}
\text{ boundary profile in log coordinate,}
}
\]

with convergence strong enough to pass one logarithmic Fourier moment.

Once that profile theorem is available, the dominant archimedean part follows
from an exact scaling identity, and only bounded prime/pole remainders remain.
This is the current preferred route for closing the prolate-to-Weil form bridge.
