# V22 zero-mode correction and repository-version reconciliation

## 1. Why the repository was called V17

`V17ExactParityMainline.lean` was the name of the last locally committed Lean
umbrella that had a complete kernel replay.  The web research conversation had
continued through V18--V22, but its V22 response explicitly left the Lean
replay, corrected Arb certificate, and GitHub synchronization pending.  The
repository therefore described its checked-in artifact, not the latest web
research iteration.  Treating that local label as the overall research version
was too coarse.

This patch keeps the historical V17 umbrella for reproducibility and introduces
`V22ZeroModeMainline.lean` as the corrected repository-side successor.

## 2. The omitted zero-frequency terms

Let

```text
L = log c,
c_k = 2 k + 1/2,
G1(L) = sum_{k >= 0} exp(-c_k L) / c_k,
G2(L) = sum_{k >= 0} exp(-c_k L) / c_k^2.
```

At frequency `n = 0`, the closed form must use

```text
XC(0) = psi'(1/4) / 4 - L G1(L) - G2(L).
```

The archimedean diagonal has the convention

```text
WR(0,0) = background - (2/L) XC(0),
T = W02 - WR - Wp.
```

Hence the corrected cutoff-free matrix is

```text
Delta_L = 2 G1(L) + 2 G2(L) / L > 0,
T_corrected = T_legacy - Delta_L e0 e0^T.
```

The update is a negative rank-one form.  It leaves the zero-coordinate kernel,
including the odd Fourier sector, unchanged and lowers every vector with a
nonzero central Fourier coefficient.

## 3. Source audit

The strict constructor in
`research/riemann-cvs-numerics/certify_parity_gap.py` was already correct from
its first repository commit:

```python
g_s += exp_term / den
if n != 0:
    g_cc += exp_term * w2 / (ck * den)
g_x1 += exp_term * ck / den
g_x2 += exp_term * (ck * ck - w2) / (den * den)
```

Only `g_cc` is conditional.  The `g_x1` and `g_x2` accumulations include
`n = 0`, matching the upstream interval implementation at commit
`5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c`.

The strict pole constant is likewise

```text
J_L = -2 log(U+1) + log(U^2+1) + 2 atan(U) + log 2 - pi/2,
U = exp(L/2),
```

with one `log 2`.  The exploratory smooth-flow script and logarithmic-tail
constant audit had two copies.  The extra copy shifted every absolute matrix
eigenvalue by `-log 2`; it did not change the smooth derivative because the
shift was cutoff-independent.  Both exploratory formulas now use the strict
normalization.

## 4. Independent `c = 13` high-precision replay

Running

```powershell
python research/riemann-cvs-numerics/audit_zero_mode_correction.py `
  --c 13 --dps 120 `
  --json-out work/v22-zero-mode-c13.json
```

reproduces

```text
G1 = 0.55535881299691919579915105924615839881740439163658...
G2 = 1.10966345333530915390918236460023899220396496072207...
XC(0) = 1.76520160473441890277352061893142161395369051083706...
Delta_L = 1.97596937071718375848858750178771622127604888263256...
```

The independently integrated defining archimedean zero entry agrees with the
one-`log 2` closed form to the audit tolerance.  Replacing it by two copies of
`log 2` produces an excess exactly equal to `log 2`.  At `N = 4`, all 81 float
entries emitted by the corrected exploratory builder agree with the midpoints
of the 400-bit strict Arb builder (the local replay produced zero float
difference).

The strict finite certificate is replayed with

```powershell
python research/riemann-cvs-numerics/certify_parity_gap.py `
  --c 13 --N 20 --prec 900 --threshold 1e-38 `
  --json-out work/v22-c13-N20-parity-gap.json
```

and proves for this 41-dimensional cutoff-free Galerkin matrix

```text
0 < lambda_min(even) < 1e-38 < lambda_min(odd),
```

with exactly one full-matrix eigenvalue below the threshold.

## 5. Formalized boundary and remaining frontier

`ZeroModeCorrection.lean` now kernel-checks the finite-sum positivity, the
`XC(0)` sign, the exact diagonal algebra, the negative rank-one quadratic
update, kernel invariance, and strict lowering away from the kernel.

The finite certificate and the formal algebra do not by themselves establish a
continuum RH conclusion.  The active frontier remains a uniform no-crossing
argument connecting the finite/cutoff path to the limiting Weil form, together
with the source-specific PSWF-to-Bessel remainder needed by the exterior
stationary-phase line.
