# Smooth-cutoff no crossing through a Lax-plus-boundary flow

## 1. Motivation

The Temple residual audit shows that controlling one optimal prolate trial
vector is not enough unless the full operator residual is linear in the
exponentially small defect.  A no-crossing argument can avoid that requirement.

Prime-power events already have the favorable exact form

\[
Q_{\rm new}=Q_{\rm old}-aL^*L,
\qquad a>0,
\]

and therefore enlarge the boundary-constrained gap.  The natural question is
whether the smooth cutoff evolution between events has the infinitesimal form

\[
\boxed{
\dot Q=[K,Q]-a(u)L_u^*L_u+R_u.
}
\tag{1}
\]

Here:

- `K` is skew-adjoint and represents the changing basis/domain
  identification;
- the commutator is isospectral;
- `L_u` is the endpoint/boundary functional;
- `R_u` is zero or is small relative to the current constraint gap.

If (1) holds with `R=0`, the smooth boundary gap is nondecreasing.  If

\[
|\langle x,R_ux\rangle|
\le
\varepsilon(u)\,
(\nu(u)-\lambda(u))
\]

with integrable `epsilon`, strict positivity is preserved by Gronwall.

The scalar eigenvalue-velocity implications are formalized in
`LaxBoundaryFlow.lean`.

---

## 2. Why the commutator disappears

Let `Qx=lambda x`, with `Q` self-adjoint and `K` skew-adjoint.  Then

\[
\begin{aligned}
\langle x,[K,Q]x\rangle
&=
\langle x,KQx\rangle-
\langle x,QKx\rangle\\
&=
\lambda\langle x,Kx\rangle-
\lambda\langle x,Kx\rangle=0.
\end{aligned}
\]

Thus Hellmann--Feynman gives

\[
\lambda'(u)
=-a(u)|L_u(x_u)|^2+
\langle x_u,R_ux_u\rangle.
\tag{2}
\]

On the transported constrained space `ker L_u`, the rank-one term vanishes.
When the residual is absent, its constrained eigenvalue has zero velocity in
the Lax frame.

Consequently,

\[
\frac d{du}(\nu-\lambda)
=a(u)|L_u(x_u)|^2\ge0.
\tag{3}
\]

A nonzero boundary overlap makes the gap strictly increase.

---

## 3. Why such a decomposition is plausible

Between prime events, the set of translation lengths present in the truncated
Weil kernel is fixed.  Varying the cutoff changes:

1. the compression interval;
2. the normalized Fourier basis used to identify different intervals;
3. endpoint pieces of the compressed translation/convolution kernels.

For a compressed translation-invariant operator, differentiating the unitary
identification produces a commutator.  Differentiating the interval endpoints
produces boundary forms.  This is the standard source of Lax-plus-boundary
shape derivatives.

The discontinuous addition of a new prime-power shift has already been
identified separately as a negative boundary rank-one update.  The hoped-for
identity (1) is therefore compatible with the exact event geometry.

---

## 4. The concrete matrix audit

Let

\[
\tau_L=W_{0,2}(L)-W_R(L)-W_p(L),
\qquad L=\log c,
\]

be the cutoff-free Fourier matrix on an interval containing no new prime-power
logarithm.  The next exact calculation should proceed as follows.

### Step A: differentiate every block

Use the closed formulas already implemented in
`certify_parity_gap.py` to obtain

\[
\partial_LW_{0,2},\qquad
\partial_LW_R,\qquad
\partial_LW_p.
\]

### Step B: remove the basis Lax term

For the normalized basis

\[
e_n^{(L)}(x)=L^{-1/2}e^{2\pi inx/L},
\]

differentiate the basis and form the skew generator `K_L`.  Subtract

\[
[K_L,\tau_L]
\]

from the raw matrix derivative.

### Step C: test the remaining rank

The target is that the remainder is supported by endpoint evaluation vectors,
ideally

\[
\partial_L\tau_L-[K_L,\tau_L]
=-a_L v_Lv_L^*
\]

inside each relevant parity sector, or a sum of finitely many boundary rank-one
forms whose restriction to the exact constraint kernel is controlled.

The first audit should be exact symbolic algebra for each prime translation and
the rank-two pole block, followed by high-precision numerical singular-value
checks for the archimedean block.

---

## 5. Consequence if the exact identity holds

Assume:

1. one finite or asymptotic parameter value has
   \(\lambda_+<\lambda_-\);
2. both sector constraint gaps are positive at that anchor;
3. the smooth flow has (1) with `R=0`;
4. prime events have the already proved negative rank-one form;
5. the rank-one Sylvester relation rules out a common parity eigenvalue when
   both boundary overlaps are nonzero.

Then:

- constraint gaps remain positive globally;
- boundary overlaps never vanish;
- even and odd eigenbranches cannot meet;
- prime events only lower the even branch or leave the ordering unchanged;
- the initial strict ordering persists over the whole connected cutoff range.

This would bypass the square-root-defect Temple residual obstruction and the
need to prove a fresh full odd-complement lower bound at every parameter.

---

## 6. If an exact rank-one identity fails

A useful approximate identity is still enough.  Suppose

\[
\left|
\langle x,R_ux\rangle
\right|
\le
\varepsilon(u)(\nu(u)-\lambda(u))
\]

for both unconstrained and constrained extremizers.  Then

\[
(\nu-\lambda)'
\ge
-\varepsilon(u)(\nu-\lambda).
\]

Hence

\[
\nu(u)-\lambda(u)
\ge
(\nu(u_0)-\lambda(u_0))
\exp\!\left(-\int_{u_0}^u\varepsilon(s)ds\right)>0.
\]

This is considerably weaker than the defect-linear operator residual required
by Temple.  It controls only the scalar boundary gap.

---

## 7. Status

The Lax/no-crossing mechanism is now a precise candidate, not a proved identity
for the concrete CvS flow.  The rank-one prime-event part and the scalar
velocity logic are rigorous.  The source-level derivative audit of the smooth
archimedean and pole blocks remains open.

This audit is now the highest-leverage next computation because a successful
identity would remove the full odd-complement bottleneck rather than merely
estimate it more sharply.
