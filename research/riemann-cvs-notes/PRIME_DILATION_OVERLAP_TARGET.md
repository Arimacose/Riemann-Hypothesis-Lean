# Prime dilation-overlap target — corrected stationary-phase version

> **Status correction (2026-08-28).** The earlier linear-carrier model in this
> note incorrectly suggested that the true radial PSWF dilation phase is
> globally nonstationary.  The actual Liouville phase has one nondegenerate
> stationary point.  The old `O(c^-1)` integration-by-parts target is therefore
> superseded by the stationary-phase target below.

## 1. Actual radial phase

For a fixed-index radial prolate mode, write the Liouville phase as

\[
\xi_a'(x)=\sqrt{\frac{x^2-a}{x^2-1}},\qquad x>1,
\]

where for the fixed modes of interest `0 <= a <= 1/2` once the bandwidth is
large enough.  For two modes with parameters `a,b` and a dilation `r >= 2`,

\[
\Phi_{a,b,r}(x)=\xi_b(rx)-\xi_a(x).
\]

Put

\[
M=r^2,\qquad t=x^2,\qquad s=M(t-1).
\]

After squaring the stationary equation and clearing positive denominators, the
root is governed by

\[
M(M-1)t^2+(1-M^2+M(a-b))t+Mb-a=0.
\]

The Lean module `ProlateCrossDilationStationaryPoint.lean` formalizes the
polynomial geometry.  In particular, the unique exterior root satisfies

\[
\boxed{\frac14<s_*<2,}
\]

so

\[
\frac1{4r^2}<x_*^2-1<\frac2{r^2}.
\]

The same module reduces the curvature estimate to division-free scalar
budgets; the current conservative target is

\[
\boxed{\Phi''(x_*)\ge r^3/20.}
\]

## 2. Correct overlap scale

Dunster's uniform radial PSWF expansion expresses each fixed-index exterior
mode as a Bessel/Hankel oscillatory term plus an `O(c^-1)` envelope remainder.
The main-main overlap is therefore a one-dimensional oscillatory integral with
one uniformly nondegenerate stationary point.

The correct target is

\[
\boxed{
|\langle t_{n,c},D_rt_{k,c}\rangle|
\le C_{n,k}c^{-1/2}r^{-3/2}
\|t_{n,c}\|_2\|t_{k,c}\|_2
+\operatorname{Err}_{n,k}(c,r).
}
\]

The first term is the stationary-phase contribution.  The Dunster envelope
remainder should give a summably weaker contribution; even a relative
`O(c^-1)` remainder with no additional `r` decay is sufficient after the prime
sum.

## 3. Prime summation

The prime-power coefficient is `Lambda(r)/sqrt(r)`.  The main stationary term
therefore contributes

\[
\frac1{\sqrt c}
\sum_{r\ge2}\frac{\Lambda(r)}{r^2},
\]

and

\[
\sum_{r\ge2}\frac{\Lambda(r)}{r^2}
=-\frac{\zeta'(2)}{\zeta(2)}<\infty.
\]

Hence the fixed-mode prime Gram contribution is expected at the scale

\[
\boxed{O(c^{-1/2})}
\]

relative to the exterior defect Gram, not `O(c^-1)`.

This is still negligible compared with the common archimedean conductor scale
`asymp log(lambda)` because `c = 2*pi*lambda^2`.

## 4. Compact scaled family

Set

\[
u=r^{-2},\qquad x=\sqrt{1+us},\qquad \Psi=r\Phi.
\]

Then the scaled phase derivative has a smooth compact-parameter description;
the multiplication-only algebra is recorded in
`ProlateScaledStationaryFamily.lean`.  The relevant parameter set is

\[
0\le u\le1/4,\quad 0\le a,b\le1/2,
\]

with the stationary point confined to `1/4 < s < 2`.

For the moving arithmetic cutoff used in the project,

\[
r\le c/(2\pi),
\]

so the effective oscillatory parameter

\[
\mu=c/r
\]

always satisfies `mu >= 2*pi`.  Thus the remaining main-term proof is a
standard-looking **uniform single-stationary-point theorem on a compact
parameter family**, rather than an endpoint-degeneracy problem.

## 5. What remains analytic

To promote the target to a theorem for the actual PSWF tails, one still needs
to write down, with constants uniform over the fixed set of modes:

1. Dunster's radial Bessel expansion in the project's normalization;
2. an amplitude `C^1`/variation bound on the scaled stationary region;
3. a uniform stationary-phase estimate for the compact family;
4. the `L2` effect of the `O(c^-1)` Bessel-envelope remainder;
5. the final prime-power summation.

The exterior logarithmic-moment estimate is treated separately in
`PSWF_EXTERIOR_LOG_MOMENT_REDUCTION.md` and
`ExteriorLogMomentTransfer.lean`.

## 6. Consequence for the main line

If the corrected estimate is completed, the fixed low prolate tail spaces have

\[
Q_{\rm prime}=O(c^{-1/2})P_{\rm defect},
\]

while the conductor part is

\[
Q_{\rm arch}=(2\log\lambda+O(1))P_{\rm defect}.
\]

This is more than sufficient to preserve the existing `lambda^-4` parity
margin on the fixed-index block.  It does **not** by itself control the entire
odd complement; that remains a separate global coercivity/no-intruder issue.
