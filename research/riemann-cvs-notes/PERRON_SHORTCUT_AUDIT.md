# Perron shortcut audit for the CvS parity blocks

## Purpose

A tempting way to prove the nonvanishing boundary overlaps required by the
Sylvester no-crossing argument is to seek a Perron--Frobenius structure for the
lowest even and odd parity blocks.  If, after a fixed diagonal sign gauge, a
parity block were an irreducible symmetric Z-matrix, its lowest eigenvector
would have a prescribed sign pattern and a suitable positive boundary vector
could not be orthogonal to it.

This note records a rigorous finite-matrix pressure test showing that this
shortcut is not available in the naive Fourier parity basis.

---

## 1. Interval-certified sign audit

The script

`research/riemann-cvs-numerics/audit_parity_offdiagonal_signs.py`

uses the same cutoff-free Arb matrix builder as the finite simple-even
certificates.  It forms the exact reflection-even and reflection-odd blocks and
classifies every off-diagonal Arb ball as positive, negative, zero, or
undetermined.

At `c = 13`, `N = 20`, `500` bits, all off-diagonal signs are certified and no
ball straddles zero.  The counts are

- even block: 128 positive, 82 negative;
- odd block: 72 positive, 118 negative.

Thus neither block is a Z-matrix or the negative of a Z-matrix.

---

## 2. No diagonal sign gauge repairs the problem

For a diagonal sign gauge `S = diag(epsilon_i)`, requiring every transformed
off-diagonal entry of `S A S` to be negative imposes

`epsilon_i epsilon_j = -sign(A_ij)`

on every nonzero edge.  The script propagates these constraints through the
complete certified sign graph.

At `c = 13`, `N = 20`, both parity blocks encounter a sign-cycle conflict; in
both cases the first recorded conflict occurs on the edge `(1,2)`.  Hence there
is no diagonal `+/-1` gauge making all off-diagonal entries negative.

The same workflow runs the audit at `c = 5, 13, 29`.

---

## 3. Consequence for the main line

The simple Perron route

`sign-definite off diagonals -> positive ground vector -> nonzero boundary overlap`

must not be used for the actual CvS Fourier parity blocks.

This does **not** rule out more sophisticated positivity-improving
representations in another basis (Suzuki's small-support screw-function model
has such a mechanism), nor does it rule out cyclicity of the boundary vector.
It only eliminates the naive sign-matrix proof in the current basis.

The preferred global route therefore remains

1. Bombieri continuity of the even/odd variational infima;
2. Suzuki's small-support simple-even anchor;
3. a no-crossing theorem;
4. nonvanishing boundary overlaps obtained from strict
   unconstrained/constrained gaps, or from a genuinely different cyclicity
   argument.

The pure prolate model supplies an `lambda^-8` reference margin for the strict
constraint gaps.  Transferring enough of that margin to the actual Weil
operator remains the principal no-crossing task.

---

## 4. Status

The finite sign statements above are interval-certified properties of the
selected Galerkin matrices.  They are used only to falsify a proposed shortcut;
they are not extrapolated to the infinite operator and make no RH claim.
