# Eighth-power constraint gaps and the Sylvester no-crossing route

## 1. Purpose

The large-parameter parity problem has two logically distinct tasks:

1. prove a strict ordering at at least one parameter value;
2. prevent the lowest even and odd branches from crossing as the parameter
   varies.

A rank-one Sylvester relation can perform the second task, but only when the
relevant boundary overlaps are nonzero.  A robust way to prove nonvanishing is
to show that each unconstrained ground eigenvalue lies strictly below the
corresponding boundary-constrained minimum.

The pure prolate model contains an unexpectedly large margin for this purpose:
the lowest unconstrained fixed-index defect is smaller than the first
boundary-constrained scale by `lambda^(-8)`, not merely by the
`lambda^(-4)` parity margin.

This note isolates that mechanism and states precisely what remains to be
proved for the actual Weil operator.

---

## 2. Fixed-index prolate ratios

Write

\[
d_n(\lambda)=1-\chi_n(\lambda),
\qquad
c=2\pi\lambda^2.
\tag{1}
\]

For fixed index, the common Fuchs normalization cancels in ratios and

\[
d_n(c)\asymp \frac{2^{3n}}{n!}c^n\,\mathfrak c(c),
\tag{2}
\]

where the factor \(\mathfrak c(c)\) is independent of the fixed index.
Consequently

\[
\frac{d_0}{d_4}
 \sim \frac{3}{512}c^{-4}
 =\frac{3}{8192\pi^4}\lambda^{-8},
\tag{3}
\]

and

\[
\frac{d_2}{d_6}
 \sim \frac{45}{512}c^{-4}
 =\frac{45}{8192\pi^4}\lambda^{-8}.
\tag{4}
\]

The lowest boundary-constrained roots satisfy

\[
\nu_+\sim\frac8{11}d_4,
\qquad
\nu_-\sim\frac8{13}d_6.
\tag{5}
\]

Therefore

\[
\boxed{
\frac{d_0}{\nu_+}
 \sim \frac{33}{65536\pi^4}\lambda^{-8},
}
\tag{6}
\]

\[
\boxed{
\frac{d_2}{\nu_-}
 \sim \frac{585}{65536\pi^4}\lambda^{-8}.
}
\tag{7}
\]

Using only \(\pi>3\), the constants obey the coarse rational bounds

\[
\frac{33}{65536\pi^4}<10^{-5},
\qquad
\frac{585}{65536\pi^4}<\frac1{8000}.
\tag{8}
\]

Thus even the larger odd-sector coefficient is below `1/8000` before the
factor \(\lambda^{-8}\) is applied.

---

## 3. Scalar transfer to an actual quadratic form

Let

- \(e_{\rm low}\) be a lowest unconstrained reference scale;
- \(e_{\rm con}\) be a first boundary-constrained reference scale;
- \(q_{\rm low}\) be an actual unconstrained trial energy;
- \(\nu_{\rm con}\) be an actual constrained lower bound.

Assume

\[
q_{\rm low}\le M e_{\rm low},
\qquad
m e_{\rm con}\le\nu_{\rm con},
\tag{9}
\]

and

\[
\lambda^8e_{\rm low}\le C e_{\rm con}.
\tag{10}
\]

Then

\[
M C<m\lambda^8
\tag{11}
\]

implies

\[
\boxed{q_{\rm low}<\nu_{\rm con}.}
\tag{12}
\]

This multiplication-only certificate is formalized in
`RiemannCvs/ConstraintGapTransfer.lean`.

The eighth-power margin is extremely forgiving.  If the actual form and the
reference form are comparable with any fixed condition number, (11) eventually
holds.  Even a condition number growing slower than \(\lambda^8\) is
admissible.

---

## 4. From strict constraint gaps to no crossing

Suppose a parity-sector eigenvector \(x\) has eigenvalue \(\mu\), while every
vector in the kernel of its boundary functional \(L\) has Rayleigh value at
least \(\nu_{\rm con}>\mu\).  Then \(L(x)\ne0\): otherwise \(x\) itself would
contradict the constrained lower bound.

For the rank-one Sylvester relation

\[
JQ_+-Q_-J=\beta\otimes\eta,
\tag{13}
\]

a common eigenvalue forces a product of one even and one odd boundary overlap
to vanish.  Strict constraint gaps in both sectors make both overlaps nonzero,
so a common parity eigenvalue is impossible.

This logic is already formalized in

- `RiemannCvs/BoundaryGapNoCrossing.lean`;
- `RiemannCvs/SylvesterNoCrossing.lean`;
- `RiemannCvs/ParityOrderContinuation.lean`.

The new eighth-power transfer supplies a quantitative route to the strict-gap
hypotheses.

If the lowest even and odd eigenvalue branches are continuous, one certified
ordering at a single anchor parameter plus global no crossing preserves that
ordering throughout the connected parameter range.

---

## 5. Why this does not yet close the argument

The fixed-index quantities in (3)--(7) belong to the pure prolate model.  To
instantiate (9) for the actual Weil operator one still needs two analytic
bridges:

1. an **unconstrained upper bridge** for a true low-mode trial direction;
2. a **boundary-constrained lower bridge** for the complete constrained
   subspace, including its orthogonal complement.

There is an additional domain distinction that must not be hidden.  The
boundary-zero Hermite radicals used in the exterior-tail argument lie in the
source space on which the map \(\mathcal E\) lands in the Weil radical.  The
lowest unconstrained Hermite/prolate modes \(h_0\) and \(h_2\) do not satisfy
the same two vanishing conditions.  Therefore the radical tail identity cannot
simply be reused for the unconstrained upper bridge without an additional
correction or a different trial construction.

This is the main analytic issue in the no-crossing route.

---

## 6. Updated proof architecture

A calibrated architecture is now

\[
\begin{aligned}
&\text{finite or asymptotic strict parity anchor}\\
&\quad +\quad
\text{actual unconstrained/constrained comparison at scale }\lambda^{-8}\\
&\Downarrow\\
&\text{strict boundary gaps in both sectors}\\
&\Downarrow\\
&\text{nonzero boundary overlaps}\\
&\Downarrow\\
&\text{Sylvester no crossing}\\
&\Downarrow\\
&\text{global preservation of the parity ordering.}
\end{aligned}
\tag{14}
\]

This route could avoid proving a fresh odd-sector Temple lower bound at every
parameter.  It does not remove the need for at least one genuine operator-level
anchor and one rigorous unconstrained/constrained bridge.

---

## 7. Formalization boundary

`RiemannCvs/ConstraintGapTransfer.lean` verifies:

- the generic eighth-power transfer (9)--(12);
- symmetric and asymmetric common-leading error versions;
- simultaneous packaging of the two parity-sector gaps;
- all fixed-index constants in (3)--(8).

It does not formalize:

- Fuchs' fixed-index asymptotic itself;
- prolate-to-Weil form comparison;
- continuity of concrete infinite-dimensional eigenvalue branches;
- the concrete Sylvester identity for the limiting operator;
- a simple-even or Riemann-Hypothesis conclusion.
