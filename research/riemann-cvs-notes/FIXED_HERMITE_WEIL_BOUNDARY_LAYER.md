# Fixed-Hermite boundary layers and the actual Weil form

## 1. Purpose and status

This note attacks the remaining scalar bridge

\[
\text{reference exterior-tail mass}
\quad\Longrightarrow\quad
\text{actual Weil tail energy}
\]

for the first exact Fourier `+1` and `-1` Hermite radical vectors.  The main
conclusion is the following large-parameter comparison.

> **Boundary-layer theorem.**  Let
> \(F_\pm=\mathcal E(\widetilde\psi_\pm)\), where
> \(\widetilde\psi_\pm\) are the unit-normalized fixed-Hermite radical vectors
> defined below.  Let \(t_{\pm,\lambda}\) be the restriction of \(F_\pm\) to the
> exterior of \([\lambda^{-1},\lambda]\).  Then
> \[
> QW(t_{\pm,\lambda})
> =\bigl(2\log\lambda+O(1)\bigr)
>   \|t_{\pm,\lambda}\|_2^2,
> \qquad \lambda\to\infty.
> \tag{1}
> \]
> Moreover,
> \[
> \frac{QW(t_{+,\lambda})}{QW(t_{-,\lambda})}
> \sim
> \frac{195}{88\pi^2}\lambda^{-4}.
> \tag{2}
> \]

The result concerns two explicit trial directions.  It does **not** lower-bound
the entire inversion-odd sector and therefore does not yet prove that the true
Weil ground state is even.  Its significance is that it closes the
`reference-tail -> actual-Weil-energy` comparison on these directions without
assuming an abstract relative-form conjecture.

The scalar implication from a common leading coefficient to strict parity
ordering is formalized separately in
`RiemannCvs/CommonLeadingWeilTransfer.lean`.  The Fourier, Gaussian-tail, prime
correlation, and form-domain analysis in this note is not yet formalized in
Lean.

## 2. Exact radical vectors and inversion parity

Use the unitary additive Fourier convention

\[
\widehat f(y)=\int_{\mathbb R}f(x)e^{2\pi ixy}\,dx.
\]

The first boundary-zero vectors in the two Fourier classes are

\[
\psi_+(x)=h_4(x)-\sqrt{\frac38}\,h_0(x),
\qquad
\psi_-(x)=-h_6(x)+\sqrt{\frac58}\,h_2(x).
\tag{3}
\]

They satisfy

\[
\widehat{\psi_+}=\psi_+,
\qquad
\widehat{\psi_-}=-\psi_-,
\qquad
\psi_\pm(0)=\widehat\psi_\pm(0)=0,
\tag{4}
\]

and

\[
\|\psi_+\|_2^2=\frac{11}{8},
\qquad
\|\psi_-\|_2^2=\frac{13}{8}.
\tag{5}
\]

Write

\[
\widetilde\psi_+=\sqrt{\frac8{11}}\,\psi_+,
\qquad
\widetilde\psi_-=\sqrt{\frac8{13}}\,\psi_-.
\tag{6}
\]

For

\[
\mathcal E(f)(u)=u^{1/2}\sum_{m\ge1}f(mu),
\qquad u>0,
\tag{7}
\]

Poisson summation gives

\[
F_+(u^{-1})=F_+(u),
\qquad
F_-(u^{-1})=-F_-(u),
\qquad
F_\pm:=\mathcal E(\widetilde\psi_\pm).
\tag{8}
\]

Thus the two vectors have exact multiplicative inversion parity.  The range of
`E` on the boundary-zero even Schwartz space is the radical of the full Weil
form in the Connes--Consani framework.

## 3. Exact exterior-mass asymptotic

The explicit Hermite formulas are

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

Let \(c_+\) and \(c_-\) denote the leading coefficients of the normalized
vectors in (6):

\[
\widetilde\psi_+(x)
 =c_+x^4e^{-\pi x^2}(1+O(x^{-2})),
\tag{11}
\]

\[
\widetilde\psi_-(x)
 =-c_-x^6e^{-\pi x^2}(1+O(x^{-2})).
\tag{12}
\]

Their squared ratio is

\[
\begin{aligned}
\frac{c_+^2}{c_-^2}
&=\frac{13}{11}
  \frac{(A_+\,2\pi)^2}{(A_-\,8\pi^2)^2}\\
&=\frac{13}{11}\frac{30}{16\pi^2}
 =\boxed{\frac{195}{88\pi^2}}.
\end{aligned}
\tag{13}
\]

For \(u\to\infty\), the `m=1` summand in (7) dominates exponentially:

\[
F_\pm(u)
 =u^{1/2}\widetilde\psi_\pm(u)
  \left(1+O\!\left(u^M e^{-3\pi u^2}\right)\right)
\tag{14}
\]

for a fixed integer \(M\).  Indeed, all summands have the same sign once
\(u\ge2\), and the `m`-th term with \(m\ge2\) gains
\(e^{-\pi(m^2-1)u^2}\).

Let

\[
e_\pm(\lambda)
 =\|t_{\pm,\lambda}\|_{L^2(\mathbb R_+^*,d^*u)}^2.
\tag{15}
\]

By (8), the lower and upper exterior wings have equal mass.  Hence (14) and the
standard Gaussian-tail formula

\[
\int_\lambda^\infty u^k e^{-2\pi u^2}\,du
 \sim \frac{1}{4\pi}
       \lambda^{k-1}e^{-2\pi\lambda^2}
\tag{16}
\]

give

\[
e_+(\lambda)
 \sim \frac{c_+^2}{2\pi}
       \lambda^7e^{-2\pi\lambda^2},
\tag{17}
\]

\[
e_-(\lambda)
 \sim \frac{c_-^2}{2\pi}
       \lambda^{11}e^{-2\pi\lambda^2}.
\tag{18}
\]

Therefore

\[
\boxed{
\frac{e_+(\lambda)}{e_-(\lambda)}
 \sim \frac{195}{88\pi^2}\lambda^{-4}.
}
\tag{19}
\]

The earlier pointwise argument also supplies the stronger finite-scale but less
sharp estimate

\[
\lambda^4e_+(\lambda)\le\frac9{16}e_-(\lambda),
\qquad \lambda\ge2.
\tag{20}
\]

## 4. Logarithmic boundary-layer profile

Put

\[
L=\log\lambda,
\qquad
\delta=\lambda^{-2},
\qquad
h_\pm(x)=F_\pm(e^x).
\tag{21}
\]

Let \(g_{\pm,\lambda}=1_{[L,\infty)}h_\pm\) be the upper exterior wing.  The
Gaussian in (9)--(10) shows that the natural boundary-layer width in the log
variable is \(\delta\).  More precisely, with

\[
a_+=\frac92,
\qquad
a_-=\frac{13}{2},
\qquad
b_{\pm,\lambda}=\lambda^{a_\pm}e^{-\pi\lambda^2},
\tag{22}
\]

one may write

\[
g_{\pm,\lambda}(L+\delta y)
 =b_{\pm,\lambda}\phi_{\pm,\lambda}(y),
\qquad y\ge0.
\tag{23}
\]

The explicit formulas and the exponentially dominated Riemann sum imply
uniform constants \(c,C>0\) such that, for both signs and every
\(\lambda\ge2\),

\[
c\le\|\phi_{\pm,\lambda}\|_2\le C,
\tag{24}
\]

and

\[
\|\phi_{\pm,\lambda}\|_1
 +\|\phi'_{\pm,\lambda}\|_1
 +\|y\phi_{\pm,\lambda}\|_1
 \le C.
\tag{25}
\]

A direct dominating function follows from

\[
\lambda^2\left(e^{2\delta y}-1\right)\ge2y
\tag{26}
\]

and the fact that all polynomial factors grow only as \(e^{O(\delta y)}\).
Thus the profiles and their first derivatives are bounded by a uniform
exponential in \(y\).  They converge locally and in every norm needed below to
a nonzero multiple of

\[
\phi_\infty(y)=1_{[0,\infty)}(y)e^{-2\pi y}.
\tag{27}
\]

## 5. Archimedean contribution

For the multiplicative Fourier transform

\[
\widehat t(s)=\int_{\mathbb R}t(x)e^{-isx}\,dx,
\tag{28}
\]

the archimedean part of the Weil quadratic form is

\[
A_\infty(t)
 =\int_{\mathbb R}|\widehat t(s)|^2m(s)\frac{ds}{2\pi},
\qquad
m(s)=2\theta'(s).
\tag{29}
\]

The digamma formula gives

\[
m(s)=-\log\pi
 +\Re\psi\!\left(\frac14+\frac{is}{2}\right).
\tag{30}
\]

The standard digamma estimate in a fixed right half-plane implies

\[
m(s)-\log(1+|s|)\in L^\infty(\mathbb R).
\tag{31}
\]

### Boundary-layer Fourier lemma

Suppose

\[
g_\delta(L+\delta y)=b_\delta\phi_\delta(y),
\qquad y\ge0,
\tag{32}
\]

where the family \(\phi_\delta\) satisfies (24)--(25).  Scaling the Fourier
variable gives

\[
\frac{
 \langle\log(1+|D|)g_\delta,g_\delta\rangle
}{\|g_\delta\|_2^2}
 =\log(\delta^{-1})+O(1).
\tag{33}
\]

Indeed, after \(\xi=\delta s\), the remainder is the normalized integral

\[
\int_{\mathbb R}
 |\widehat\phi_\delta(\xi)|^2
 \log(\delta+|\xi|)\frac{d\xi}{2\pi}.
\tag{34}
\]

It is uniformly bounded: near zero use
\(|\widehat\phi_\delta|\le\|\phi_\delta\|_1\) and the local integrability of
`log`; for \(|\xi|\ge1\), integration by parts and (25) give
\(|\widehat\phi_\delta(\xi)|\le C/|\xi|\).

The full tail is

\[
t_{\pm,\lambda}(x)
 =g_{\pm,\lambda}(x)
  \pm g_{\pm,\lambda}(-x).
\tag{35}
\]

The two wings are disjoint in physical space, so their ordinary squared norms
add exactly.  For the logarithmic multiplier, the cross term is still only
\(O(\|t\|_2^2)\).  In scaled Fourier variables it contains the oscillatory
factor

\[
\exp\left(-2i\frac{L}{\delta}\xi\right).
\tag{36}
\]

Splitting at \(|\xi|=\delta\) and integrating by parts elsewhere, (25) gives a
bound

\[
O\!\left(\frac{\delta\log(1/\delta)}{L}\right)
 \|t\|_2^2,
\tag{37}
\]

which is more than sufficient.  The bounded multiplier difference in (31)
contributes only \(O(\|t\|_2^2)\).

Since \(\log(\delta^{-1})=2\log\lambda\), we obtain

\[
\boxed{
A_\infty(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)e_\pm(\lambda).
}
\tag{38}
\]

## 6. Pole contribution

The pole term is

\[
P_0(t)
 =2\Re\left(
   \widehat t(i/2)\overline{\widehat t(-i/2)}
  \right).
\tag{39}
\]

Using (23)--(25), an upper-wing exponential moment satisfies

\[
\left|\int_L^\infty
  g_{\pm,\lambda}(x)e^{x/2}\,dx\right|^2
 \le C\lambda^{-1}\|g_{\pm,\lambda}\|_2^2.
\tag{40}
\]

The opposite moment is handled by the reflected wing and exact inversion
parity.  Therefore

\[
\boxed{
|P_0(t_{\pm,\lambda})|
 \le C\lambda^{-1}e_\pm(\lambda).
}
\tag{41}
\]

## 7. Prime contribution

For a real log-coordinate function \(t\), set

\[
C_t(y)=\int_{\mathbb R}t(x)t(x+y)\,dx.
\tag{42}
\]

The prime part of the full Weil form is bounded by

\[
2\sum_{n\ge2}rac{\Lambda(n)}{\sqrt n}
 |C_t(\log n)|.
\tag{43}
\]

Here \(\Lambda(n)=0\) away from prime powers, so summing over all integers only
enlarges the estimate.

For \(u\ge2\), the explicit Hermite formulas and same-sign Riemann sums give

\[
c_\pm u^{a_\pm}e^{-\pi u^2}
 \le |F_\pm(u)|
 \le C_\pm u^{a_\pm}e^{-\pi u^2}.
\tag{44}
\]

### 7.1 Same-wing correlations

A translation by \(\log n\), \(n\ge2\), sends the upper argument `u` to `nu`.
Equation (44) gives

\[
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 |C_{\rm same}(\log n)|
 \le Ce^{-c\lambda^2}e_\pm(\lambda).
\tag{45}
\]

The lower-lower contribution is identical in magnitude.

### 7.2 Cross-wing correlations

A lower-to-upper overlap is possible only if

\[
\log n>2L,
\qquad\text{equivalently}\qquad n>\lambda^2.
\tag{46}
\]

After writing the lower coordinate as `u^{-1}`, the relevant integral is
bounded by

\[
C n^{a_\pm}
 \int_\lambda^{n/\lambda}
 \exp\!\left(-\pi\left(u^2+\frac{n^2}{u^2}\right)\right)
 \frac{du}{u}.
\tag{47}
\]

Since

\[
u^2+\frac{n^2}{u^2}\ge2n,
\tag{48}
\]

and

\[
\log\frac{n}{\lambda^2}
 \le\frac{n-\lambda^2}{\lambda^2},
\tag{49}
\]

comparison with the lower bound for the tail norm yields

\[
\frac{|C_{\rm cross}(\log n)|}{e_\pm(\lambda)}
 \le
 C\left(\frac{n}{\lambda^2}\right)^{a_\pm}
 (n-\lambda^2)
 e^{-2\pi(n-\lambda^2)}.
\tag{50}
\]

Using only \(\Lambda(n)\le\log n\), the exponentially convergent sum in
\(n-\lambda^2\) gives

\[
\boxed{
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 |C_t(\log n)|
 \le
 C\frac{\log(2+\lambda)}{\lambda}
 e_\pm(\lambda).
}
\tag{51}
\]

No next-prime estimate or prime-gap theorem enters this bound.

## 8. Actual Weil-tail asymptotic

The full Weil form decomposes into the archimedean, pole, and prime terms:

\[
QW(t)=A_\infty(t)+P_0(t)-P_{\rm prime}(t).
\tag{52}
\]

Combining (38), (41), and (51),

\[
\boxed{
QW(t_{\pm,\lambda})
 =\bigl(2\log\lambda+O(1)\bigr)e_\pm(\lambda).
}
\tag{53}
\]

In particular, both tail energies are positive for all sufficiently large
\(\lambda\), and their scalar distortion relative to the reference tail norm
has condition number tending to one.

Equations (19) and (53) give

\[
\boxed{
\frac{QW(t_{+,\lambda})}{QW(t_{-,\lambda})}
 \sim
 \frac{195}{88\pi^2}\lambda^{-4}.
}
\tag{54}
\]

The weaker finite-scale reference estimate (20), together with (53), is already
enough to obtain strict ordering without using the sharp constant in (54).
Indeed, for large \(\lambda\), both energies lie within fifty percent of the
common leading scale

\[
A_\lambda=2\log\lambda.
\tag{55}
\]

`CommonLeadingWeilTransfer.fixedHermiteParityFromHalfRelativeError` formally
verifies that (20) and this coarse error budget imply

\[
QW(t_{+,\lambda})<QW(t_{-,\lambda}).
\tag{56}
\]

## 9. Transfer to retained trial vectors

Write

\[
F_\pm=g_{\pm,\lambda}^{\rm in}+t_{\pm,\lambda},
\tag{57}
\]

where the first term is retained on
\([\lambda^{-1},\lambda]\).  Since \(F_\pm\) lies in the radical of the full
Weil form, symmetry and bilinearity give the exact identity

\[
QW(g_{\pm,\lambda}^{\rm in})
 =QW(t_{\pm,\lambda}).
\tag{58}
\]

Therefore (54)--(56) are also actual Weil-energy statements for two explicit
compactly supported trial vectors of exact opposite inversion parity:

\[
\boxed{
\frac{
 QW(g_{+,\lambda}^{\rm in})
}{
 QW(g_{-,\lambda}^{\rm in})
}
 \sim
 \frac{195}{88\pi^2}\lambda^{-4}.
}
\tag{59}
\]

This closes the actual-Weil comparison on the two fixed-Hermite anchor
directions.

## 10. What remains open

Equation (59) compares two trial values.  It gives an upper bound in each parity
sector, not a lower bound on the full odd sector.  The next main-chain theorem
must control arbitrary inversion-odd competitors.  Two viable routes remain:

1. a Temple estimate for the explicit odd trial vector, using a lower bound for
   the next odd spectral value and a residual estimate;
2. a low/high Schur decomposition in the odd sector, using the logarithmic
   high-mode coercivity already developed in `EXPLICIT_LOG_TAIL_THEOREM.md`, or
   the sharper prolate internal gap when available.

Thus the updated chain is

\[
\begin{aligned}
&\text{fixed Hermite exact parity and quartic exterior mass}\\
&\Downarrow\\
&\text{boundary-layer analysis of the full Weil formula}\\
&\Downarrow\\
&QW(g_{+,\lambda}^{\rm in})
  /QW(g_{-,\lambda}^{\rm in})
  =\Theta(\lambda^{-4})\\
&\Downarrow\\
&\color{#555}{\text{remaining: odd-sector lower bound / Schur control}}\\
&\Downarrow\\
&\text{true simple-even Weil ground state.}
\end{aligned}
\]

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*,
  arXiv:2511.22755, especially the full Weil decomposition in Section 3.
- A. Connes, C. Consani, *Zeta zeros and prolate wave operators: Semilocal
  adelic operators*, arXiv:2310.18423, especially the description of the
  radical as the range of `E` and the Hermite/prolate link.
- `FIXED_HERMITE_ANCHOR.md` and `GRADING_BRIDGE_AUDIT.md` in this repository.
