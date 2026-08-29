import Mathlib

/-!
# Eighth-power boundary-constraint gap transfer

The lowest unconstrained fixed-index prolate defect in each Fourier class is
smaller than the first boundary-constrained scale by four powers of the
bandwidth `c`, hence by eight powers of `lambda` when

`c = 2 * pi * lambda^2`.

This file isolates the finite scalar certificate needed to turn that
`lambda^(-8)` reference separation into a strict gap between an unconstrained
trial energy and a boundary-constrained lower bound.  Such strict gaps provide
the nonzero boundary overlaps required by the rank-one Sylvester no-crossing
argument.

The Fuchs fixed-index asymptotic, convergence of prolate residues, and every
comparison with the concrete Weil form are external analytic inputs.  Only
algebraic constants and order-theoretic transfers are formalized here.
-/

namespace RiemannCvs.ConstraintGapTransfer

/-- Generic eighth-power transfer.  The reference scales satisfy
`lambda^8 * eLow <= C * eConstraint`; the actual unconstrained trial is bounded
above by `M * eLow`, while the boundary-constrained energy is bounded below by
`m * eConstraint`. -/
theorem eighthPowerGapTransfer
    (eLow eConstraint qLow nuConstraint m M C lambda : ℝ)
    (_heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hM : 0 ≤ M)
    (hLambda : 0 < lambda)
    (hqLow : qLow ≤ M * eLow)
    (hConstraint : m * eConstraint ≤ nuConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin : M * C < m * lambda ^ 8) :
    qLow < nuConstraint := by
  have hLambdaEight : 0 < lambda ^ 8 := pow_pos hLambda 8
  have hLowScaled :
      lambda ^ 8 * qLow ≤ lambda ^ 8 * (M * eLow) :=
    mul_le_mul_of_nonneg_left hqLow (le_of_lt hLambdaEight)
  have hRatioScaled :
      M * (lambda ^ 8 * eLow) ≤ M * (C * eConstraint) :=
    mul_le_mul_of_nonneg_left hEighthRatio hM
  have hMarginScaled :
      (M * C) * eConstraint <
        (m * lambda ^ 8) * eConstraint :=
    mul_lt_mul_of_pos_right hMargin heConstraint
  have hConstraintScaled :
      lambda ^ 8 * (m * eConstraint) ≤
        lambda ^ 8 * nuConstraint :=
    mul_le_mul_of_nonneg_left hConstraint (le_of_lt hLambdaEight)
  have hScaled :
      lambda ^ 8 * qLow < lambda ^ 8 * nuConstraint := by
    nlinarith
  exact lt_of_mul_lt_mul_left hScaled (le_of_lt hLambdaEight)

/-- Common leading coefficients with asymmetric errors give the one-sided
bounds needed by `eighthPowerGapTransfer`. -/
theorem commonLeadingEighthPowerGap
    (eLow eConstraint qLow nuConstraint A deltaLow deltaConstraint
      C lambda : ℝ)
    (heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hLeadingUpper : 0 ≤ A + deltaLow)
    (hLambda : 0 < lambda)
    (hqLow : qLow ≤ (A + deltaLow) * eLow)
    (hConstraint :
      (A - deltaConstraint) * eConstraint ≤ nuConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin :
      (A + deltaLow) * C <
        (A - deltaConstraint) * lambda ^ 8) :
    qLow < nuConstraint := by
  exact eighthPowerGapTransfer
    eLow eConstraint qLow nuConstraint
    (A - deltaConstraint) (A + deltaLow) C lambda
    heLow heConstraint hLeadingUpper hLambda
    hqLow hConstraint hEighthRatio hMargin

/-- Symmetric absolute relative-form errors around one scalar coefficient. -/
theorem commonLeadingAbsoluteErrorEighthPowerGap
    (eLow eConstraint qLow nuConstraint A delta C lambda : ℝ)
    (heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hLeadingUpper : 0 ≤ A + delta)
    (hLambda : 0 < lambda)
    (hqLow : |qLow - A * eLow| ≤ delta * eLow)
    (hConstraint :
      |nuConstraint - A * eConstraint| ≤ delta * eConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin :
      (A + delta) * C < (A - delta) * lambda ^ 8) :
    qLow < nuConstraint := by
  have hqLowOneSided : qLow ≤ (A + delta) * eLow := by
    have h := (abs_le.mp hqLow).2
    nlinarith
  have hConstraintOneSided :
      (A - delta) * eConstraint ≤ nuConstraint := by
    have h := (abs_le.mp hConstraint).1
    nlinarith
  exact commonLeadingEighthPowerGap
    eLow eConstraint qLow nuConstraint A delta delta C lambda
    heLow heConstraint hLeadingUpper hLambda
    hqLowOneSided hConstraintOneSided hEighthRatio hMargin

/-- Two parity sectors may be certified independently and then packaged as the
pair of strict boundary-constraint gaps required by a no-crossing theorem. -/
theorem twoSectorEighthPowerGaps
    (eLowPlus eConstraintPlus qPlus nuPlus mPlus MPlus CPlus
      eLowMinus eConstraintMinus qMinus nuMinus mMinus MMinus CMinus
      lambda : ℝ)
    (heLowPlus : 0 ≤ eLowPlus)
    (heConstraintPlus : 0 < eConstraintPlus)
    (hMPlus : 0 ≤ MPlus)
    (heLowMinus : 0 ≤ eLowMinus)
    (heConstraintMinus : 0 < eConstraintMinus)
    (hMMinus : 0 ≤ MMinus)
    (hLambda : 0 < lambda)
    (hqPlus : qPlus ≤ MPlus * eLowPlus)
    (hnuPlus : mPlus * eConstraintPlus ≤ nuPlus)
    (hRatioPlus : lambda ^ 8 * eLowPlus ≤ CPlus * eConstraintPlus)
    (hMarginPlus : MPlus * CPlus < mPlus * lambda ^ 8)
    (hqMinus : qMinus ≤ MMinus * eLowMinus)
    (hnuMinus : mMinus * eConstraintMinus ≤ nuMinus)
    (hRatioMinus : lambda ^ 8 * eLowMinus ≤ CMinus * eConstraintMinus)
    (hMarginMinus : MMinus * CMinus < mMinus * lambda ^ 8) :
    qPlus < nuPlus ∧ qMinus < nuMinus := by
  exact ⟨
    eighthPowerGapTransfer
      eLowPlus eConstraintPlus qPlus nuPlus
      mPlus MPlus CPlus lambda
      heLowPlus heConstraintPlus hMPlus hLambda
      hqPlus hnuPlus hRatioPlus hMarginPlus,
    eighthPowerGapTransfer
      eLowMinus eConstraintMinus qMinus nuMinus
      mMinus MMinus CMinus lambda
      heLowMinus heConstraintMinus hMMinus hLambda
      hqMinus hnuMinus hRatioMinus hMarginMinus
  ⟩

/-! ## Fixed-index coefficient arithmetic -/

/-- Fuchs coefficient ratio `A_0/A_4` for `A_n = 2^(3n)/n!`. -/
theorem defectZeroOverFour :
    (1 : ℝ) / ((2 : ℝ) ^ 12 / 24) = 3 / 512 := by
  norm_num

/-- Fuchs coefficient ratio `A_2/A_6`. -/
theorem defectTwoOverSix :
    ((2 : ℝ) ^ 6 / 2) /
      ((2 : ℝ) ^ 18 / 720) = 45 / 512 := by
  norm_num

/-- After `c = 2*pi*lambda^2`, the `0/4` defect ratio coefficient is
`3/(8192*pi^4)` in units of `lambda^(-8)`. -/
theorem plusLowDefectLambdaCoefficient :
    (3 / 512 : ℝ) / (16 * Real.pi ^ 4) =
      3 / (8192 * Real.pi ^ 4) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- The corresponding `2/6` coefficient. -/
theorem minusLowDefectLambdaCoefficient :
    (45 / 512 : ℝ) / (16 * Real.pi ^ 4) =
      45 / (8192 * Real.pi ^ 4) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- Dividing the `0/4` ratio by the limiting constrained-root weight `8/11`
gives the lowest-unconstrained / lowest-constrained `+1` coefficient. -/
theorem plusConstraintGapCoefficient :
    (3 / (8192 * Real.pi ^ 4) : ℝ) / (8 / 11) =
      33 / (65536 * Real.pi ^ 4) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- Dividing the `2/6` ratio by the limiting constrained-root weight `8/13`
gives the corresponding `-1` coefficient. -/
theorem minusConstraintGapCoefficient :
    (45 / (8192 * Real.pi ^ 4) : ℝ) / (8 / 13) =
      585 / (65536 * Real.pi ^ 4) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- A coarse rational upper bound for the `+1` coefficient, using only
`pi > 3`. -/
theorem plusConstraintGapCoefficient_lt_oneOverHundredThousand :
    33 / (65536 * Real.pi ^ 4) < (1 / 100000 : ℝ) := by
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hdiff : 0 < Real.pi ^ 2 - 9 := sub_pos.mpr hpiSq
  have hsum : 0 < Real.pi ^ 2 + 9 := by positivity
  have hpiFourth : (81 : ℝ) < Real.pi ^ 4 := by
    have hprod : 0 < (Real.pi ^ 2 - 9) * (Real.pi ^ 2 + 9) :=
      mul_pos hdiff hsum
    nlinarith
  have hden : 0 < 65536 * Real.pi ^ 4 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- A coarse rational upper bound for the larger `-1` coefficient. -/
theorem minusConstraintGapCoefficient_lt_oneOverEightThousand :
    585 / (65536 * Real.pi ^ 4) < (1 / 8000 : ℝ) := by
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hdiff : 0 < Real.pi ^ 2 - 9 := sub_pos.mpr hpiSq
  have hsum : 0 < Real.pi ^ 2 + 9 := by positivity
  have hpiFourth : (81 : ℝ) < Real.pi ^ 4 := by
    have hprod : 0 < (Real.pi ^ 2 - 9) * (Real.pi ^ 2 + 9) :=
      mul_pos hdiff hsum
    nlinarith
  have hden : 0 < 65536 * Real.pi ^ 4 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

end RiemannCvs.ConstraintGapTransfer
