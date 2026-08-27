import RiemannCvs.CommonLeadingWeilTransfer

/-!
# From an explicit odd trial vector to a full odd-sector lower bound

The fixed-Hermite boundary-layer calculation compares two actual Weil trial
energies, but a comparison of trial values alone does not order the two sector
ground states.  The missing one-sided step is a Temple or Schur lower bound in
the inversion-odd sector.

This file isolates a deliberately generous scalar certificate.  The intended
inputs are:

* a quartic reference-mass separation
  `lambda^4 * ePlus <= (9/16) * eMinus`;
* a common leading Weil scale `A` for the even and odd trial energies;
* a Temple estimate for the true odd ground value;
* a residual correction no larger than a fixed fraction of `A * eMinus`.

No concrete spectral gap, residual estimate, Weil asymptotic, or
Riemann-hypothesis statement is hidden here.  Every analytic input appears as
an explicit hypothesis.
-/

namespace RiemannCvs.OddTempleParityTransfer

/-- A residual budget turns a Temple lower bound into an additive-loss lower
bound.  This formulation is useful because interval arithmetic can certify the
multiplication-only hypothesis `residualSq <= loss * gap`. -/
theorem templeCorrectionFromResidualBudget
    (mu theta residualSq gap loss : ℝ)
    (hgap : 0 < gap)
    (hTemple : theta - residualSq / gap ≤ mu)
    (hResidual : residualSq ≤ loss * gap) :
    theta - loss ≤ mu := by
  have hquot : residualSq / gap ≤ loss := by
    exact (div_le_iff₀ hgap).2 hResidual
  linarith

/-- A quartic even trial upper bound and a Temple-corrected odd trial lower
bound imply a strict ordering of the even trial value below the full odd-sector
ground value. -/
theorem quarticParityFromTempleLoss
    (ePlus eMinus qPlus thetaMinus muMinus m M loss C lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hM : 0 ≤ M)
    (hLambda : 0 < lambda)
    (hqPlus : qPlus ≤ M * ePlus)
    (hThetaMinus : (m + loss) * eMinus ≤ thetaMinus)
    (hTempleLower : thetaMinus - loss * eMinus ≤ muMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin : M * C < m * lambda ^ 4) :
    qPlus < muMinus := by
  have hOddLower : m * eMinus ≤ muMinus := by
    nlinarith
  exact RiemannCvs.RadicalTailTransfer.quarticMarginParityTransfer
    ePlus eMinus qPlus muMinus m M C lambda
    hePlus heMinus hM hLambda hqPlus hOddLower hQuarticRatio hMargin

/-- Common-leading-coefficient version of
`quarticParityFromTempleLoss`.

`deltaPlus` and `deltaMinus` are one-sided relative-form errors for the two
trial directions.  `templeLoss` is the additional odd-sector loss measured in
units of the odd reference mass. -/
theorem commonLeadingTempleQuarticTransfer
    (ePlus eMinus qPlus thetaMinus muMinus
      A deltaPlus deltaMinus templeLoss C lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hLeadingUpper : 0 ≤ A + deltaPlus)
    (hLambda : 0 < lambda)
    (hqPlus : qPlus ≤ (A + deltaPlus) * ePlus)
    (hThetaMinus : (A - deltaMinus) * eMinus ≤ thetaMinus)
    (hTempleLower : thetaMinus - templeLoss * eMinus ≤ muMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin :
      (A + deltaPlus) * C <
        (A - deltaMinus - templeLoss) * lambda ^ 4) :
    qPlus < muMinus := by
  exact quarticParityFromTempleLoss
    ePlus eMinus qPlus thetaMinus muMinus
    (A - deltaMinus - templeLoss) (A + deltaPlus)
    templeLoss C lambda
    hePlus heMinus hLeadingUpper hLambda hqPlus
    (by nlinarith) hTempleLower hQuarticRatio hMargin

/-- Version in which the Temple loss is supplied by a residual-square and a
certified odd spectral gap. -/
theorem commonLeadingTempleResidualTransfer
    (ePlus eMinus qPlus thetaMinus muMinus
      A deltaPlus deltaMinus templeLoss C lambda residualSq gap : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hLeadingUpper : 0 ≤ A + deltaPlus)
    (hLambda : 0 < lambda)
    (hgap : 0 < gap)
    (hqPlus : qPlus ≤ (A + deltaPlus) * ePlus)
    (hThetaMinus : (A - deltaMinus) * eMinus ≤ thetaMinus)
    (hTemple : thetaMinus - residualSq / gap ≤ muMinus)
    (hResidual : residualSq ≤ (templeLoss * eMinus) * gap)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin :
      (A + deltaPlus) * C <
        (A - deltaMinus - templeLoss) * lambda ^ 4) :
    qPlus < muMinus := by
  have hTempleLower :
      thetaMinus - templeLoss * eMinus ≤ muMinus :=
    templeCorrectionFromResidualBudget
      muMinus thetaMinus residualSq gap (templeLoss * eMinus)
      hgap hTemple hResidual
  exact commonLeadingTempleQuarticTransfer
    ePlus eMinus qPlus thetaMinus muMinus
    A deltaPlus deltaMinus templeLoss C lambda
    hePlus heMinus hLeadingUpper hLambda hqPlus hThetaMinus
    hTempleLower hQuarticRatio hMargin

/-- Concrete fixed-Hermite certificate with very coarse error budgets.

For `lambda >= 2`, the non-asymptotic reference estimate has coefficient
`9/16`.  It is enough that:

* each trial energy is within one quarter of the common leading scale;
* the Temple correction is at most another quarter of the odd leading scale.

Thus the analytic odd-sector lower-bound problem does not require sharp
constants. -/
theorem fixedHermiteGroundParityFromQuarterBudgets
    (ePlus eMinus qPlus thetaMinus muMinus A lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hA : 0 < A)
    (hLambda : 2 ≤ lambda)
    (hqPlus : |qPlus - A * ePlus| ≤ (A / 4) * ePlus)
    (hThetaMinus :
      |thetaMinus - A * eMinus| ≤ (A / 4) * eMinus)
    (hTempleLower : thetaMinus - (A / 4) * eMinus ≤ muMinus)
    (hFixedHermiteRatio :
      lambda ^ 4 * ePlus ≤ (9 / 16 : ℝ) * eMinus) :
    qPlus < muMinus := by
  have hLambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hLambda
  have hLambdaSq : (4 : ℝ) ≤ lambda ^ 2 := by
    nlinarith
  have hLambdaFourth : (16 : ℝ) ≤ lambda ^ 4 := by
    have hsum : 0 ≤ lambda ^ 2 + 4 := by positivity
    have hprod : 0 ≤ (lambda ^ 2 - 4) * (lambda ^ 2 + 4) :=
      mul_nonneg (sub_nonneg.mpr hLambdaSq) hsum
    nlinarith

  have hqPlusUpper : qPlus ≤ (A + A / 4) * ePlus := by
    have h := (abs_le.mp hqPlus).2
    nlinarith
  have hThetaLower : (A - A / 4) * eMinus ≤ thetaMinus := by
    have h := (abs_le.mp hThetaMinus).1
    nlinarith
  have hLeadingUpper : 0 ≤ A + A / 4 := by
    nlinarith
  have hRight :
      (A / 2) * 16 ≤ (A / 2) * lambda ^ 4 :=
    mul_le_mul_of_nonneg_left hLambdaFourth (by positivity)
  have hStrict :
      (A + A / 4) * (9 / 16 : ℝ) < (A / 2) * 16 := by
    nlinarith
  have hMargin :
      (A + A / 4) * (9 / 16 : ℝ) <
        (A - A / 4 - A / 4) * lambda ^ 4 := by
    have h := lt_of_lt_of_le hStrict hRight
    nlinarith

  exact commonLeadingTempleQuarticTransfer
    ePlus eMinus qPlus thetaMinus muMinus
    A (A / 4) (A / 4) (A / 4) (9 / 16) lambda
    hePlus heMinus hLeadingUpper hLambdaPos
    hqPlusUpper hThetaLower hTempleLower
    hFixedHermiteRatio hMargin

/-- The preceding fixed-Hermite result with the Temple correction expressed
directly through residual-square and gap data. -/
theorem fixedHermiteGroundParityFromTempleData
    (ePlus eMinus qPlus thetaMinus muMinus A lambda residualSq gap : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hA : 0 < A)
    (hLambda : 2 ≤ lambda)
    (hgap : 0 < gap)
    (hqPlus : |qPlus - A * ePlus| ≤ (A / 4) * ePlus)
    (hThetaMinus :
      |thetaMinus - A * eMinus| ≤ (A / 4) * eMinus)
    (hTemple : thetaMinus - residualSq / gap ≤ muMinus)
    (hResidual : residualSq ≤ ((A / 4) * eMinus) * gap)
    (hFixedHermiteRatio :
      lambda ^ 4 * ePlus ≤ (9 / 16 : ℝ) * eMinus) :
    qPlus < muMinus := by
  have hTempleLower : thetaMinus - (A / 4) * eMinus ≤ muMinus :=
    templeCorrectionFromResidualBudget
      muMinus thetaMinus residualSq gap ((A / 4) * eMinus)
      hgap hTemple hResidual
  exact fixedHermiteGroundParityFromQuarterBudgets
    ePlus eMinus qPlus thetaMinus muMinus A lambda
    hePlus heMinus hA hLambda hqPlus hThetaMinus
    hTempleLower hFixedHermiteRatio

end RiemannCvs.OddTempleParityTransfer
