# Fixed-Hermite boundary layers and the actual Weil tail form

## Status and scope

This note develops a large-parameter estimate for the **actual full Weil
quadratic form** on the two explicit exterior tails supplied by the first
boundary-zero Hermite vectors in the additive Fourier `+1` and `-1` classes.

The target estimate is

\[
QW(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)
   \|t_{\pm,\lambda}\|_2^2,
\tag{1}
\]

with an `O(1)` bound uniform in the two signs.  Combined with the exact tail
mass asymptotic

\[
\frac{\|t_{+,\lambda}\|_2^2}
     {\|t_{-,\lambda}\|_2^2}
 \sim \frac{195}{88\pi^2}\lambda^{-4},
\tag{2}
\]

this gives

\[
\frac{QW(t_{+,\lambda})}
     {QW(t_{-,\lambda})}
 \sim \frac{195}{88\pi^2}\lambda^{-4}.
\tag{3}
\]

Equation (3) is an ordering of two explicit Weil trial directions.  It does
**not** by itself lower-bound the entire odd sector, and therefore does not prove
the simple-even hypothesis or the Riemann Hypothesis.

The derivation below is intended as a proof-level analytic reduction, but it has
not yet received independent expert audit and is not formalized in Lean.  Lean
formalizes only the finite scalar implication from a common leading coefficient
to strict parity ordering.

Primary conventions are those of Connes--Consani--Moscovici,
*Zeta Spectral Triples*, arXiv:2511.22755, and *Zeta zeros and prolate wave
operators*, arXiv:2310.18423.

---

## 1. The two exact radical vectors

Let

\[
\widetilde\psi_+
 =\sqrt{\frac8{11}}\left(h_4-\sqrt{\frac38}\,h_0\right),
\qquad
\widetilde\psi_-
 =\sqrt{\frac8{13}}\left(-h_6+\sqrt{\frac58}\,h_2\right).
\tag{4}
\]

They are unit vectors and satisfy

\[
\widehat{\widetilde\psi_+}=\widetilde\psi_+,
\qquad
\widehat{\widetilde\psi_-}=-\widetilde\psi_-,
\qquad
\widetilde\psi_\pm(0)
 =\widehat{\widetilde\psi_\pm}(0)=0.
\tag{5}
\]

Define

\[
F_\pm(u)=\mathcal E(\widetilde\psi_\pm)(u)
 =u^{1/2}\sum_{m\ge1}\widetilde\psi_\pm(mu).
\tag{6}
\]

Poisson summation gives exact inversion parity

\[
F_+(u^{-1})=F_+(u),
\qquad
F_-(u^{-1})=-F_-(u).
\tag{7}
\]

For \(\lambda\ge2\), let

\[
t_{\pm,\lambda}
 =1_{(0,\lambda^{-1})\cup(\lambda,\infty)}F_\pm,
\qquad
 e_\pm(\lambda)=\|t_{\pm,\lambda}\|_2^2.
\tag{8}
\]

The symmetric cutoff preserves the two exact parity classes.

---

## 2. Exact leading tail-mass ratio

The explicit unnormalized Hermite combinations are

\[
\psi_+(x)
 =A_+x^2(2\pi x^2-3)e^{-\pi x^2},
\qquad
A_+=\frac{2\,2^{3/4}\sqrt3\,\pi}{3},
\tag{9}
\]

and

\[
\psi_-(x)
 =-A_-x^2(8\pi^2x^4-30\pi x^2+15)e^{-\pi x^2},
\qquad
A_-=\frac{2\,2^{1/4}\sqrt5\,\pi}{15}.
\tag{10}
\]

Their positive prefactors satisfy

\[
\frac{A_+}{A_-}=\sqrt{30}.
\tag{11}
\]

For fixed sign and \(u\to\infty\), the term \(m=1\) in (6) dominates all
integer dilates.  Indeed every term has the same sign for \(u\ge2\), and the
relative contribution of \(m\ge2\) is bounded by a fixed polynomial times
\(e^{-3\pi u^2}\).  Consequently

\[
F_+(u)
 =c_+u^{9/2}e^{-\pi u^2}\bigl(1+O(u^{-2})\bigr),
\tag{12}
\]

\[
F_-(u)
 =-c_-u^{13/2}e^{-\pi u^2}\bigl(1+O(u^{-2})\bigr),
\tag{13}
\]

where

\[
c_+=\sqrt{\frac8{11}}\,(2\pi A_+),
\qquad
c_-=\sqrt{\frac8{13}}\,(8\pi^2 A_-).
\tag{14}
\]

Since \(d^*u=du/u\), the standard Gaussian-tail estimate

\[
\int_\lambda^\infty u^k e^{-2\pi u^2}\,du
 \sim \frac{1}{4\pi}
       \lambda^{k-1}e^{-2\pi\lambda^2}
\tag{15}
\]

gives, after doubling for the two inversion-related wings,

\[
e_+(\lambda)
 \sim \frac{c_+^2}{2\pi}
       \lambda^7e^{-2\pi\lambda^2},
\tag{16}
\]

\[
e_-(\lambda)
 \sim \frac{c_-^2}{2\pi}
       \lambda^{11}e^{-2\pi\lambda^2}.
\tag{17}
\]

The exact leading-coefficient ratio is

\[
\begin{aligned}
\frac{c_+^2}{c_-^2}
 &=\frac{13}{11}
   \left(\frac{A_+}{A_-}\right)^2
   \left(\frac{2\pi}{8\pi^2}\right)^2\\
 &=\frac{13}{11}\frac{30}{16\pi^2}
 =\frac{195}{88\pi^2}.
\end{aligned}
\tag{18}
\]

Equations (16)--(18) prove (2).  The previously proved non-asymptotic estimate

\[
\lambda^4e_+(\lambda)
 \le\frac9{16}e_-(\lambda),
\qquad \lambda\ge2,
\tag{19}
\]

remains useful because it leaves a much wider error budget than the sharp
constant in (18).

---

## 3. Logarithmic boundary-layer coordinates

Write

\[
L=\log\lambda,
\qquad
\delta=\lambda^{-2}.
\tag{20}
\]

On the upper wing define

\[
g_{\pm,\lambda}(x)=F_\pm(e^x),
\qquad x\ge L.
\tag{21}
\]

The natural boundary coordinate is

\[
x=L+\delta y,
\qquad y\ge0.
\tag{22}
\]

For suitable nonzero amplitudes \(b_{\pm,\lambda}\), set

\[
g_{\pm,\lambda}(L+\delta y)
 =b_{\pm,\lambda}\phi_{\pm,\lambda}(y).
\tag{23}
\]

The Gaussian identity

\[
\lambda^2\bigl(e^{2\delta y}-1\bigr)
 \ge2y
\tag{24}
\]

and the fixed polynomial degrees in (9)--(10) imply uniform constants
\(c_0,C_0>0\) such that, for both signs and all sufficiently large \(\lambda\),

\[
c_0\le\|\phi_{\pm,\lambda}\|_2^2\le C_0,
\qquad
\|\phi_{\pm,\lambda}\|_1
 +\|\phi'_{\pm,\lambda}\|_1\le C_0.
\tag{25}
\]

More precisely, both normalized profiles converge in these norms to a nonzero
multiple of

\[
\phi_\infty(y)=1_{[0,\infty)}(y)e^{-2\pi y}.
\tag{26}
\]

The contribution of the dilates \(m\ge2\) is uniformly
\(O(e^{-3\pi\lambda^2})\) relative to the first term, so it does not alter
(25).

These bounds also place the sharp-cutoff tails in the logarithmic Fourier-form
domain: a one-sided jump gives Fourier decay \(O(|s|^{-1})\), and
\(\log(1+|s|)|s|^{-2}\) is integrable.

---

## 4. One-wing logarithmic multiplier estimate

Use the logarithmic Fourier transform

\[
\widehat g(s)=\int_{\mathbb R}g(x)e^{-isx}\,dx.
\tag{27}
\]

From (23),

\[
\widehat g_{\pm,\lambda}(s)
 =b_{\pm,\lambda}\delta e^{-isL}
  \widehat\phi_{\pm,\lambda}(\delta s).
\tag{28}
\]

Let

\[
A_{\log}(g)
 =\int_{\mathbb R}|\widehat g(s)|^2
   \log(1+|s|)\frac{ds}{2\pi}.
\tag{29}
\]

Changing variables \(\xi=\delta s\) and using

\[
\log(1+|s|)
 =\log(\delta^{-1})+\log(\delta+|\xi|)
\tag{30}
\]

gives

\[
\frac{A_{\log}(g_{\pm,\lambda})}
     {\|g_{\pm,\lambda}\|_2^2}
 =\log(\delta^{-1})+R_{\pm,\lambda},
\tag{31}
\]

where

\[
R_{\pm,\lambda}
 =\frac{
   \int |\widehat\phi_{\pm,\lambda}(\xi)|^2
          \log(\delta+|\xi|)\,d\xi
 }{
   \int |\widehat\phi_{\pm,\lambda}(\xi)|^2\,d\xi
 }.
\tag{32}
\]

The remainder is uniformly bounded.  For \(|\xi|\le1\),

\[
|\widehat\phi(\xi)|\le\|\phi\|_1,
\tag{33}
\]

and \(\int_0^1|\log(\delta+\xi)|d\xi\) is uniformly bounded.  For
\(|\xi|\ge1\), integration by parts and (25) give

\[
|\widehat\phi(\xi)|
 \le\frac{|\phi(0)|+\|\phi'\|_1}{|\xi|}
 \le\frac{C}{|\xi|},
\tag{34}
\]

while \(\int_1^\infty\log(1+\xi)\xi^{-2}d\xi<\infty\).  The denominator in
(32) stays bounded away from zero by (25) and Plancherel.  Hence

\[
A_{\log}(g_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)
  \|g_{\pm,\lambda}\|_2^2.
\tag{35}
\]

---

## 5. The two wings: exact cancellation of the leading cross term

Let \(Jg(x)=g(-x)\) and \(\varepsilon_+=1\), \(\varepsilon_-=-1\).  In
logarithmic coordinates the complete tail is

\[
t_{\pm,\lambda}
 =g_{\pm,\lambda}+\varepsilon_\pm Jg_{\pm,\lambda}.
\tag{36}
\]

The two summands have disjoint supports, so

\[
\langle g_{\pm,\lambda},Jg_{\pm,\lambda}\rangle=0,
\qquad
\|t_{\pm,\lambda}\|_2^2
 =2\|g_{\pm,\lambda}\|_2^2.
\tag{37}
\]

The important point is that the large scalar part in (30) has **no cross
term at all**:

\[
\log(\delta^{-1})
 \langle g_{\pm,\lambda},Jg_{\pm,\lambda}\rangle=0.
\tag{38}
\]

Only the remainder multiplier \(\log(\delta+|\xi|)\) contributes to the
interaction of the two wings.  By Cauchy--Schwarz with the absolute logarithmic
moment estimated in (33)--(34), this cross contribution is

\[
O(1)\|g_{\pm,\lambda}\|_2^2.
\tag{39}
\]

Thus no oscillatory-integral or stationary-phase estimate is required, and

\[
A_{\log}(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)e_\pm(\lambda).
\tag{40}
\]

This exact cancellation is stronger and cleaner than treating the two wings by
rapid-oscillation arguments.

---

## 6. The archimedean Weil multiplier

The archimedean part of the full Weil form is the Fourier multiplier

\[
m(s)=2\theta'(s)
 =-\log\pi+
   \Re\psi\!\left(\frac14+\frac{is}{2}\right).
\tag{41}
\]

The standard digamma asymptotic in the right half-plane gives

\[
m(s)=\log|s|-\log(2\pi)+O(|s|^{-1})
\qquad(|s|\to\infty).
\tag{42}
\]

Since \(m\) is continuous on bounded intervals,

\[
m(s)-\log(1+|s|)\in L^\infty(\mathbb R).
\tag{43}
\]

A bounded multiplier changes a quadratic form by at most a constant times the
squared norm.  Combining (40) and (43),

\[
A_\infty(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)e_\pm(\lambda).
\tag{44}
\]

The `O(1)` constant may differ between intermediate estimates, but a common
uniform bound works for the two fixed signs.

---

## 7. The pole term is smaller by \(\lambda^{-1}\)

The pole contribution has the form

\[
P_0(t)=2\Re\left(
 \widehat t(i/2)\overline{\widehat t(-i/2)}
\right).
\tag{45}
\]

For one wing, (23) gives

\[
\int_L^\infty |g(x)|e^{x/2}dx
 \le C|b_{\pm,\lambda}|\delta\lambda^{1/2},
\tag{46}
\]

and

\[
\int_L^\infty |g(x)|e^{-x/2}dx
 \le C|b_{\pm,\lambda}|\delta\lambda^{-1/2}.
\tag{47}
\]

Since

\[
\|g_{\pm,\lambda}\|_2^2
 \asymp |b_{\pm,\lambda}|^2\delta,
\tag{48}
\]

and the reflected wing exchanges the two exponential weights,

\[
|P_0(t_{\pm,\lambda})|
 \le C\lambda^{-1}e_\pm(\lambda).
\tag{49}
\]

---

## 8. Prime translations: same-wing and cross-wing parts

For a real logarithmic tail set

\[
C_t(y)=\int_{\mathbb R}t(x)t(x+y)dx.
\tag{50}
\]

The prime part of the full Weil form is

\[
P_{\rm pr}(t)
 =\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
   \bigl(C_t(\log n)+C_t(-\log n)\bigr)
 =2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}C_t(\log n).
\tag{51}
\]

The second equality uses the reality of the tail.

For \(u\ge2\), the explicit formulas and the same-sign dilation sums give
constants \(c,C>0\) and

\[
a_+=\frac92,
\qquad
a_-=\frac{13}{2},
\tag{52}
\]

such that

\[
c\,u^{a_\pm}e^{-\pi u^2}
 \le |F_\pm(u)|
 \le C\,u^{a_\pm}e^{-\pi u^2}.
\tag{53}
\]

### 8.1 Same-wing overlap

For \(n\ge2\), the upper-upper correlation is

\[
\int_\lambda^\infty F_\pm(u)F_\pm(nu)\frac{du}{u}.
\tag{54}
\]

Relative to the tail mass, it is bounded by a fixed polynomial in \(n\) times

\[
e^{-\pi(n^2-1)\lambda^2}.
\tag{55}
\]

The lower-lower term has the same bound.  Summing (55), even with
\(\Lambda(n)\le\log n\), gives

\[
|P_{\rm same}(t_{\pm,\lambda})|
 \le Ce^{-c\lambda^2}e_\pm(\lambda).
\tag{56}
\]

### 8.2 Cross-wing overlap

A lower wing can meet an upper wing after translation only when
\(n>\lambda^2\).  Its absolute correlation is bounded by

\[
\int_\lambda^{n/\lambda}
 |F_\pm(u)F_\pm(n/u)|\frac{du}{u}.
\tag{57}
\]

The polynomial powers cancel in the integration variable:

\[
|F_\pm(u)F_\pm(n/u)|
 \le Cn^{a_\pm}
 e^{-\pi(u^2+n^2/u^2)}.
\tag{58}
\]

Using

\[
u^2+\frac{n^2}{u^2}\ge2n,
\qquad
\log\frac{n}{\lambda^2}
 \le\frac{n-\lambda^2}{\lambda^2},
\tag{59}
\]

and the lower tail estimate following from (53), one obtains

\[
\frac{|C_{\rm cross}(\log n)|}{e_\pm(\lambda)}
 \le C
 \left(\frac{n}{\lambda^2}\right)^{a_\pm}
 (n-\lambda^2)e^{-2\pi(n-\lambda^2)}.
\tag{60}
\]

The right side is summable uniformly after writing \(n=\lambda^2+k\).  Since
\(\Lambda(n)\le\log n\) and \(n^{-1/2}\asymp\lambda^{-1}\) in the only
non-negligible range,

\[
|P_{\rm cross}(t_{\pm,\lambda})|
 \le C\frac{\log(2+\lambda)}{\lambda}
 e_\pm(\lambda).
\tag{61}
\]

No prime-gap theorem or distributional information about primes is used.
Combining (56) and (61),

\[
|P_{\rm pr}(t_{\pm,\lambda})|
 \le C\frac{\log(2+\lambda)}{\lambda}
 e_\pm(\lambda).
\tag{62}
\]

The sign of the cross-wing term depends on inversion parity, but its magnitude
is already lower order than the common archimedean scale.

---

## 9. Full Weil-tail asymptotic

The full Weil form decomposes as

\[
QW(t)=A_\infty(t)+P_0(t)-P_{\rm pr}(t).
\tag{63}
\]

Equations (44), (49), and (62) yield

\[
\boxed{
QW(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)e_\pm(\lambda).
}
\tag{64}
\]

In particular, both energies are positive for sufficiently large \(\lambda\),
and

\[
\frac{QW(t_{+,\lambda})}{QW(t_{-,\lambda})}
 =\frac{e_+(\lambda)}{e_-(\lambda)}
  \left(1+O\!\left(\frac1{\log\lambda}\right)\right).
\tag{65}
\]

Using (2),

\[
\boxed{
\frac{QW(t_{+,\lambda})}{QW(t_{-,\lambda})}
 \sim \frac{195}{88\pi^2}\lambda^{-4}.
}
\tag{66}
\]

A weaker but more robust finite-scale consequence follows from (19): once the
common-scale error is at most fifty percent, the Lean theorem
`fixedHermiteParityFromHalfRelativeError` already forces strict ordering.

---

## 10. Transfer to retained interval trial vectors

The range of \(\mathcal E\) on the boundary-zero even Schwartz space lies in
the radical of the full Weil form.  Write

\[
F_\pm=g_{\pm,\lambda}+t_{\pm,\lambda},
\tag{67}
\]

where \(g\) is retained on \([\lambda^{-1},\lambda]\).  The radical splitting
identity gives

\[
QW(g_{\pm,\lambda},g_{\pm,\lambda})
 =QW(t_{\pm,\lambda},t_{\pm,\lambda}).
\tag{68}
\]

Thus (66) gives a strict large-parameter ordering for the two **actual retained
Weil trial energies**:

\[
QW(g_{+,\lambda})<QW(g_{-,\lambda})
\qquad(\lambda\text{ sufficiently large}).
\tag{69}
\]

This closes the scalar `reference tail norm -> actual Weil energy` bridge for
the two fixed-Hermite anchor directions, subject to independent audit of the
analytic estimates above.

---

## 11. What remains open

Equation (69) compares two trial values.  Variationally,

\[
\mu_+(\lambda)\le R(g_{+,\lambda}),
\qquad
\mu_-(\lambda)\le R(g_{-,\lambda}),
\tag{70}
\]

so their ordering does not imply
\(\mu_+(\lambda)<\mu_-(\lambda)\).  The remaining large-parameter obstacle is
an **odd-sector lower bound**, for example through one of:

1. a Temple estimate for a genuine odd approximate eigenvector;
2. a low/high Schur-complement certificate with a uniform odd complement gap;
3. a constrained-ground/no-crossing theorem that identifies the relevant odd
   branch.

The fixed-Hermite boundary-layer theorem supplies a robust even trial upper
bound and a verified common-scale mechanism.  The prolate candidate remains the
preferred object for residual control and for convergence toward the Riemann
`Xi` function.

---

## 12. Formalization boundary

`RiemannCvs/CommonLeadingWeilTransfer.lean` proves the exact finite scalar
implications used after (64):

- asymmetric common-leading errors;
- symmetric absolute relative-form errors;
- survival of the fixed-Hermite `9/(16 lambda^4)` margin under fifty-percent
  relative distortion.

It does not formalize:

- the explicit Hermite/`E` estimates;
- the logarithmic Fourier multiplier argument;
- the pole or prime correlation bounds;
- the full Weil explicit formula;
- any ground-state or Riemann-Hypothesis conclusion.
