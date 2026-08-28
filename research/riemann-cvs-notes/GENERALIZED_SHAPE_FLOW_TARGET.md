# Generalized congruence-plus-boundary shape flow

## 1. Correction to the bare-Lax formulation

Transporting an operator from a moving interval to a fixed coordinate interval
changes both:

- the quadratic-form matrix `A(L)`;
- the mass/Gram matrix `G(L)`.

The relevant eigenproblem is therefore generalized:

\[
A(L)x(L)=\lambda(L)G(L)x(L).
\]

The natural shape derivative has the form

\[
\boxed{
A'=K^*A+AK-B,
\qquad
G'=K^*G+GK,
}
\tag{1}
\]

where `B` is a boundary form.  A bare commutator identity for `A` is not
required and, in a fixed normalized Fourier basis, may be false.

For a generalized eigenvector, self-adjointness gives

\[
\langle Kx,Ax\rangle
=\lambda\langle Kx,Gx\rangle,
\]

\[
\langle x,AKx\rangle
=\lambda\langle x,GKx\rangle.
\]

Thus

\[
\boxed{
\langle x,(A'-\lambda G')x\rangle
=-\langle x,Bx\rangle.
}
\tag{2}
\]

This cancellation is formalized in `GeneralizedBoundaryFlow.lean`.

---

## 2. Compression of a fixed kernel

The cutoff-free CvS form should be viewed before basis normalization as the
compression of one fixed distributional convolution kernel to a growing log
interval.  Prime-power events occur when a new translation length first fits
inside the interval; between events, the set of active shifts is fixed.

For a fixed convolution kernel, differentiating the interval compression has
two parts:

1. the coordinate transport, represented by the congruence terms in (1);
2. endpoint traces, represented by `B`.

Consequently, the correct source-level audit is not to fit the raw derivative
`A'` by a rank-one matrix.  It is to fit

\[
A'-\lambda G'
\]

on generalized eigenvectors, or equivalently to subtract the complete
congruence contribution before testing the boundary rank.

---

## 3. Expected parity reduction

On a centered interval, reflection identifies the two endpoint traces.  A
rank-two boundary form in the full space reduces to one trace direction in
each reflection sector:

\[
L_+(f)=f(b)+f(-b),
\qquad
L_-(f)=f(b)-f(-b).
\]

The hoped-for sector identities are

\[
A_+'-\lambda G_+'
=-a_+(L,\lambda)L_+^*L_+,
\]

\[
A_-'-\lambda G_-'
=-a_-(L,\lambda)L_-^*L_-.
\]

The coefficient may depend affinely on the eigenvalue; such dependence is
normal for compression defects.  Positivity of the coefficient, rather than
constancy, is what is needed.

On the corresponding boundary kernel, the eigenvalue velocity vanishes.  The
unconstrained branch is nonincreasing, so the constrained-to-unconstrained gap
is nondecreasing.

---

## 4. Revised numerical audit

The first exploratory script compared the derivative of the matrix alone with
one fixed boundary vector.  That is not a decisive test of (1).

The corrected audit must:

1. construct the operator in a fixed-coordinate but non-orthonormal basis;
2. retain the exact Gram matrix `G(L)`;
3. finite-difference both `A` and `G` between prime events;
4. compute generalized eigenvectors;
5. test
   \[
   x_i^*(A'-\lambda_iG')x_i
   \]
   against the parity endpoint overlap squared;
6. inspect the off-diagonal residual after solving for the transport generator
   `K`.

A successful diagonal test is already enough for eigenvalue no crossing; a
full matrix identity would be stronger.

---

## 5. Relationship with prime events

At a prime-power event, the exact update is already a negative boundary
rank-one form.  It is invisible on the boundary kernel and cannot shrink the
constraint gap.

If the generalized smooth flow also has nonnegative boundary coefficients,
then the entire cutoff path has a unified interpretation:

\[
\boxed{
\text{isospectral coordinate transport}
+
\text{boundary dissipation}.
}
\]

One strict parity anchor, positive constraint gaps, and the Sylvester
no-common-eigenvalue obstruction would then propagate the ordering globally.

---

## 6. Status

Equation (2) is rigorous abstract algebra.  The concrete decomposition (1) for
the full CvS kernel remains a research target.  The next implementation should
use the unscaled log-interval basis or an explicitly tracked Gram matrix,
rather than infer the shape law from the derivative of the orthonormal Fourier
matrix alone.
