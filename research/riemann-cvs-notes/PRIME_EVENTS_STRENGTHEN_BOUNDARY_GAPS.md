# Prime events strengthen the boundary-gap no-crossing mechanism

## 1. Statement

Let `L` be the boundary functional represented by the prime-event vector in a
finite CvS cutoff model.  Crossing a prime-power event changes the quadratic
form by

\[
Q_{\rm new}(x)
=
Q_{\rm old}(x)-a|L(x)|^2,
\qquad a>0.
\]

Let

\[
\lambda=\inf_{\|x\|=1}Q(x)
\]

be the unconstrained lowest value and

\[
\nu=\inf_{\substack{\|x\|=1\\L(x)=0}}Q(x)
\]

the boundary-constrained lowest value.

Then the event has two exact consequences:

1. `nu` is unchanged, because the update vanishes on `ker L`;
2. `lambda` cannot increase.

Therefore

\[
\boxed{
(\nu-\lambda)_{\rm new}
\ge
(\nu-\lambda)_{\rm old}.
}
\]

If the ground state has nonzero boundary overlap, the Hellmann--Feynman event
shift is strictly negative and the boundary gap strictly increases.

The scalar logic is formalized in `BoundaryRankOneGap.lean`.

---

## 2. Parity consequence

The prime-event vector is reflection-even.  Hence every odd-parity vector is
orthogonal to it, and the odd block is invisible to the event.  The event acts
only in the even sector and lowers its unconstrained minimum.

Thus prime events cannot create an even-to-odd crossing in the unfavorable
direction.  They either leave the parity gap unchanged or push the even branch
farther downward.

This is useful because the finite cutoff path contains many discontinuous
prime-power events.  They do not need separate interval crossing checks once
the rank-one identification and parity normalization have been audited.

---

## 3. What remains between prime events

This observation does **not** prove global no crossing.  Between prime events
the cutoff path also contains smooth archimedean, pole, and basis-rescaling
terms.  Their effect on

\[
\nu_+(u)-\lambda_+(u),
\qquad
\nu_-(u)-\lambda_-(u)
\]

must still be controlled.

The updated no-crossing architecture is therefore:

\[
\begin{aligned}
&\text{one strict simple-even anchor}\\
&+\text{ nonvanishing boundary overlaps on smooth intervals}\\
&+\text{ Sylvester obstruction to an even/odd common eigenvalue}\\
&+\text{ prime events that can only strengthen the even boundary gap}\\
&\Longrightarrow
\text{ global parity-order continuation}.
\end{aligned}
\]

---

## 4. Why this matters after the Temple obstruction

The Temple residual audit shows that a raw

\[
O(\sqrt d)
\]

operator residual cannot preserve an exponentially small prolate ground scale.
The no-crossing strategy avoids requiring such a residual at every parameter.
It needs instead:

- one genuine strict ordering anchor;
- positive unconstrained-to-constrained gaps;
- continuity between events;
- exclusion of common parity eigenvalues.

The prime-event monotonicity established here removes all discontinuous events
from the list of dangerous steps.  The unresolved analytic work is now
concentrated in the smooth intervals and in the infinite-dimensional limit.

---

## 5. Current focused target

For a smooth cutoff interval containing no new prime power, derive a bound of
the form

\[
\frac d{du}
\bigl(\nu_+(u)-\lambda_+(u)\bigr)
\ge
-\varepsilon_+(u)
\bigl(\nu_+(u)-\lambda_+(u)\bigr),
\]

and analogously in the odd sector, with an integrable error.  Gronwall would
then preserve strict positivity of both constraint gaps between events.

A stronger outcome would be monotonicity of the smooth gap itself.  The next
source-level task is to differentiate the cutoff-free CvS matrix and isolate
which parts vanish on the boundary kernel.
