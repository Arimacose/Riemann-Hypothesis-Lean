import Mathlib

/-!
# Characteristic-product ratio and the boundary-Weyl residue sum

For an `(N+1)`-point simple pole set and a numerator polynomial of degree at
most `N`, Lagrange interpolation gives the exact partial-fraction identity

`P(x) / product_i (x-lambda_i)
  = sum_i r_i / (x-lambda_i)`.

Here

`r_i = P(lambda_i) / product_{j != i} (lambda_i-lambda_j)`.

Specializing `P` to the monic product over `N` odd eigenvalues identifies the
finite characteristic-product ratio with the residue sum certified by the
V23 Arb audit.  Reversing each denominator yields the sign convention used by
`BoundaryWeylCumulative`:

`G(x) = sum_i r_i / (lambda_i-x)
      = - characteristicRatio(x)`.

The separate concrete displacement module explains why the odd characteristic
polynomial is the relevant numerator for the CvS parity blocks.  This file
also supplies the exact adapter from the two matrix characteristic
polynomials to their determinant ratio, without inserting any numerical or
continuum hypothesis.
-/

namespace RiemannCvs.ObliqueWeylDeterminant

open Polynomial
open scoped BigOperators

/-- Residue attached to one simple pole of a polynomial/nodal ratio. -/
noncomputable def interpolationResidue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : ι → ℝ) (numerator : ℝ[X]) (i : ι) : ℝ :=
  Lagrange.nodalWeight Finset.univ poles i * numerator.eval (poles i)

/-- Exact partial-fraction expansion of a polynomial divided by the monic
nodal polynomial over a simple finite pole set. -/
theorem polynomialRatio_eq_residueSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : ι → ℝ) (numerator : ℝ[X]) (x : ℝ)
    (hPoles : Function.Injective poles)
    (hDegree : numerator.degree < (Fintype.card ι : WithBot ℕ))
    (hx : ∀ i, x ≠ poles i) :
    numerator.eval x /
        (Lagrange.nodal Finset.univ poles).eval x =
      ∑ i ∈ Finset.univ,
        interpolationResidue poles numerator i / (x - poles i) := by
  have hInj : Set.InjOn poles (Finset.univ : Finset ι) :=
    hPoles.injOn
  have hDegree' :
      numerator.degree < ((Finset.univ : Finset ι).card : WithBot ℕ) := by
    simpa using hDegree
  have hInterp :
      numerator = Lagrange.interpolate Finset.univ poles
        (fun i => numerator.eval (poles i)) :=
    Lagrange.eq_interpolate hInj hDegree'
  have hEval := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset ι))
    (v := poles)
    (fun i => numerator.eval (poles i))
    (x := x)
    (fun i _hi => hx i)
  rw [← hInterp] at hEval
  have hNodal :
      (Lagrange.nodal (Finset.univ : Finset ι) poles).eval x ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun i _hi => hx i)
  calc
    numerator.eval x /
          (Lagrange.nodal Finset.univ poles).eval x =
        ∑ i ∈ Finset.univ,
          Lagrange.nodalWeight Finset.univ poles i *
            (x - poles i)⁻¹ * numerator.eval (poles i) := by
              apply (div_eq_iff hNodal).2
              rw [hEval]
              ring
    _ = ∑ i ∈ Finset.univ,
          interpolationResidue poles numerator i / (x - poles i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [interpolationResidue, div_eq_mul_inv]
            ring

/-- The total residue of a proper nodal ratio is its numerator coefficient
one degree below the pole polynomial.  This is the leading-coefficient form
of the same Lagrange identity. -/
theorem sum_interpolationResidue_eq_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : ι → ℝ) (numerator : ℝ[X])
    (hPoles : Function.Injective poles)
    (hDegree : numerator.degree < (Fintype.card ι : WithBot ℕ)) :
    ∑ i ∈ Finset.univ, interpolationResidue poles numerator i =
      numerator.coeff (Fintype.card ι - 1) := by
  have hInj : Set.InjOn poles (Finset.univ : Finset ι) :=
    hPoles.injOn
  have hDegree' :
      numerator.degree < ((Finset.univ : Finset ι).card : WithBot ℕ) := by
    simpa using hDegree
  calc
    ∑ i ∈ Finset.univ, interpolationResidue poles numerator i =
        ∑ i ∈ Finset.univ,
          numerator.eval (poles i) /
            ∏ j ∈ Finset.univ.erase i, (poles i - poles j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [interpolationResidue, Lagrange.nodalWeight,
        Finset.prod_inv_distrib, div_eq_mul_inv]
      ring
    _ = numerator.coeff (Fintype.card ι - 1) := by
      simpa only [Finset.card_univ] using
        (Lagrange.coeff_eq_sum hInj hDegree').symm

/-- Monic characteristic numerator built from the odd spectral points. -/
noncomputable def characteristicNumerator
    {ι : Type*} [Fintype ι]
    (zeros : ι → ℝ) : ℝ[X] :=
  Lagrange.nodal Finset.univ zeros

/-- Monic characteristic denominator built from the one-larger even pole
set. -/
noncomputable def characteristicDenominator
    {ι : Type*} [Fintype ι]
    (poles : Option ι → ℝ) : ℝ[X] :=
  Lagrange.nodal Finset.univ poles

/-- Spectral residue used by the finite boundary-Weyl function. -/
noncomputable def characteristicResidue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : Option ι → ℝ) (zeros : ι → ℝ) (i : Option ι) : ℝ :=
  interpolationResidue poles (characteristicNumerator zeros) i

/-- A monic `N`-zero characteristic product divided by a monic `(N+1)`-pole
product is exactly the sum of its simple-pole residues. -/
theorem characteristicRatio_eq_residueSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : Option ι → ℝ) (zeros : ι → ℝ) (x : ℝ)
    (hPoles : Function.Injective poles)
    (hx : ∀ i, x ≠ poles i) :
    (characteristicNumerator zeros).eval x /
        (characteristicDenominator poles).eval x =
      ∑ i ∈ Finset.univ,
        characteristicResidue poles zeros i / (x - poles i) := by
  have hDegree :
      (characteristicNumerator zeros).degree <
        (Fintype.card (Option ι) : WithBot ℕ) := by
    rw [characteristicNumerator, Lagrange.degree_nodal]
    rw [Finset.card_univ, Fintype.card_option]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)
  simpa only [characteristicDenominator, characteristicResidue] using
    polynomialRatio_eq_residueSum poles
      (characteristicNumerator zeros) x hPoles hDegree hx

/-- Because both characteristic products are monic and the pole set has one
more point than the zero set, their spectral residues have total mass one.
This is the exact normalization checked interval-wise by the V23 Arb
certificate. -/
theorem sum_characteristicResidue_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : Option ι → ℝ) (zeros : ι → ℝ)
    (hPoles : Function.Injective poles) :
    ∑ i ∈ Finset.univ, characteristicResidue poles zeros i = 1 := by
  have hDegree :
      (characteristicNumerator zeros).degree <
        (Fintype.card (Option ι) : WithBot ℕ) := by
    rw [characteristicNumerator, Lagrange.degree_nodal]
    rw [Finset.card_univ, Fintype.card_option]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)
  change (∑ i ∈ Finset.univ, interpolationResidue poles
    (characteristicNumerator zeros) i) = 1
  rw [sum_interpolationResidue_eq_coeff poles
    (characteristicNumerator zeros) hPoles hDegree]
  have hNatDegree :
      (characteristicNumerator zeros).natDegree = Fintype.card ι := by
    rw [characteristicNumerator, Lagrange.natDegree_nodal,
      Finset.card_univ]
  have hMonic : (characteristicNumerator zeros).Monic := by
    exact Lagrange.nodal_monic
  rw [Fintype.card_option]
  simp only [Nat.add_sub_cancel]
  rw [← hNatDegree]
  exact hMonic.coeff_natDegree

/-- Boundary-Weyl sign convention: positive denominators to the left of the
first pole introduce one global minus sign relative to the characteristic
ratio. -/
theorem neg_characteristicRatio_eq_boundaryWeylSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (poles : Option ι → ℝ) (zeros : ι → ℝ) (x : ℝ)
    (hPoles : Function.Injective poles)
    (hx : ∀ i, x ≠ poles i) :
    -((characteristicNumerator zeros).eval x /
        (characteristicDenominator poles).eval x) =
      ∑ i ∈ Finset.univ,
        characteristicResidue poles zeros i / (poles i - x) := by
  rw [characteristicRatio_eq_residueSum poles zeros x hPoles hx]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show poles i - x = -(x - poles i) by ring, div_neg]

/-- Matrix-level determinant form of the boundary-Weyl identity.  The two
explicit hypotheses identify the block characteristic polynomials with their
enumerated simple spectral products; `Matrix.eval_charpoly` then turns that
spectral ratio into the actual finite determinant ratio with the same global
sign used by `BoundaryWeylCumulative`. -/
theorem neg_determinantRatio_eq_boundaryWeylSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (evenBlock : Matrix (Option ι) (Option ι) ℝ)
    (oddBlock : Matrix ι ι ℝ)
    (poles : Option ι → ℝ) (zeros : ι → ℝ) (x : ℝ)
    (hEvenCharpoly :
      evenBlock.charpoly = characteristicDenominator poles)
    (hOddCharpoly :
      oddBlock.charpoly = characteristicNumerator zeros)
    (hPoles : Function.Injective poles)
    (hx : ∀ i, x ≠ poles i) :
    -(((Matrix.scalar ι) x - oddBlock).det /
        ((Matrix.scalar (Option ι)) x - evenBlock).det) =
      ∑ i ∈ Finset.univ,
        characteristicResidue poles zeros i / (poles i - x) := by
  rw [← Matrix.eval_charpoly oddBlock x,
    ← Matrix.eval_charpoly evenBlock x,
    hOddCharpoly, hEvenCharpoly]
  exact neg_characteristicRatio_eq_boundaryWeylSum
    poles zeros x hPoles hx

/-- Multiplicative form of the same determinant bridge.  This is the exact
`scale = -1` factorization expected by
`BoundaryWeylCumulative.factorizedNumerator_ne_zero_beforeFirstPole`. -/
theorem determinantFactorization_eq_neg_boundaryWeylSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (evenBlock : Matrix (Option ι) (Option ι) ℝ)
    (oddBlock : Matrix ι ι ℝ)
    (poles : Option ι → ℝ) (zeros : ι → ℝ) (x : ℝ)
    (hEvenCharpoly :
      evenBlock.charpoly = characteristicDenominator poles)
    (hOddCharpoly :
      oddBlock.charpoly = characteristicNumerator zeros)
    (hPoles : Function.Injective poles)
    (hx : ∀ i, x ≠ poles i) :
    ((Matrix.scalar ι) x - oddBlock).det =
      -(∑ i ∈ Finset.univ,
          characteristicResidue poles zeros i / (poles i - x)) *
        ((Matrix.scalar (Option ι)) x - evenBlock).det := by
  have hEvenDet :
      ((Matrix.scalar (Option ι)) x - evenBlock).det ≠ 0 := by
    rw [← Matrix.eval_charpoly evenBlock x, hEvenCharpoly,
      characteristicDenominator]
    exact Lagrange.eval_nodal_not_at_node
      (fun i _hi => hx i)
  have hRatio := neg_determinantRatio_eq_boundaryWeylSum
    evenBlock oddBlock poles zeros x hEvenCharpoly hOddCharpoly
      hPoles hx
  apply (div_eq_iff hEvenDet).mp
  linarith

end RiemannCvs.ObliqueWeylDeterminant
