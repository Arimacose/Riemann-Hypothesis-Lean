# Sign correction for the exterior PSWF Liouville transform

This note corrects the low-order term in
`PSWF_EXTERIOR_LOG_MOMENT_REDUCTION.md`.

Starting from

\[
\psi_{uu}
+
\coth u\,\psi_u
+
\bigl(c^2\cosh^2u-\chi_n(c)\bigr)\psi
=0
\]

and defining

\[
v(u)=\sqrt{\sinh u}\,\psi(\cosh u),
\]

the standard removal-of-first-derivative formula gives

\[
v''(u)+q_{n,c}(u)v(u)=0,
\]

with

\[
\boxed{
q_{n,c}(u)
=
c^2\cosh^2u-
\chi_n(c)-\frac14+
\frac1{4\sinh^2u}.
}
\]

Indeed, for \(P(u)=\coth u\),

\[
Q_{\rm eff}
=Q-\frac12P'-\frac14P^2,
\]

and

\[
-\frac12P'-\frac14P^2
=
-\frac14+
\frac1{4\sinh^2u}.
\]

The leading exterior relation

\[
q_{n,c}(u)\asymp c^2\cosh^2u
\]

away from the endpoint is unchanged, as are the WKB envelope and logarithmic
moment reduction.  Any rigorous endpoint analysis must use the corrected
formula above.
