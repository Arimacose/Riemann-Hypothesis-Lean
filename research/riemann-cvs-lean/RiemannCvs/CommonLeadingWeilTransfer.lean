import RiemannCvs.RadicalTailTransfer

/-!
# Transfer from a common leading Weil-tail scale

The fixed-Hermite radical vectors provide exact inversion-parity tails whose
reference masses obey a non-asymptotic quartic separation

`lambda^4 * ePlus <= (9/16) * eMinus`.

For the actual Weil form it is therefore unnecessary to prove an asymptotic
isometry.  It is enough that the two tail energies share a common positive
leading coefficient with a bounded relative distortion.  The lemmas below
isolate this deliberately forgiving scalar certificate.

No assertion about the concrete Weil form, Hermite functions, the map `E`, or
large-parameter asymptotics is hidden here.  Those analytic inputs remain
explicit hypotheses.
-/

namespace RiemannCvs.CommonLeadingWeilTransfer

/-- A common leading coefficient with asymmetric error budgets preserves a
quartic reference-energy separation once the remaining scalar margin is
positive. -/
theorem commonLeadingQuarticTransfer
    (ePlus eMinus qPlus qMinus A deltaPlus deltaMinus C lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hLeadingUpper : 0 ≤ A + deltaPlus)
    (hLambda : 0 < lambda)
    (hqPlus : qPlus ≤ (A + deltaPlus) * ePlus)
    (hqMinus : (A - deltaMinus) * eMinus ≤ qMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin :
      (A + deltaPlus) * C < (A - deltaMinus) * lambda ^ 4) :
    qPlus < qMinus := by
  exact RiemannCvs.RadicalTailTransfer.quarticMarginParityTransfer
    ePlus eMinus qPlus qMinus
    (A - deltaMinus) (A + deltaPlus) C lambda
    hePlus heMinus hLeadingUpper hLambda
    hqPlus hqMinus hQuarticRatio hMargin

/-- Absolute relative-form errors around a common scalar coefficient give the
one-sided estimates needed by `commonLeadingQuarticTransfer`. -/
theorem commonLeadingAbsoluteErrorTransfer
    (ePlus eMinus qPlus qMinus A delta C lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hLeadingUpper : 0 ≤ A + delta)
    (hLambda : 0 < lambda)
    (hqPlus : |qPlus - A * ePlus| ≤ delta * ePlus)
    (hqMinus : |qMinus - A * eMinus| ≤ delta * eMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin : (A + delta) * C < (A - delta) * lambda ^ 4) :
    qPlus < qMinus := by
  have hqPlusOneSided : qPlus ≤ (A + delta) * ePlus := by
    have h := (abs_le.mp hqPlus).2
    nlinarith
  have hqMinusOneSided : (A - delta) * eMinus ≤ qMinus := by
    have h := (abs_le.mp hqMinus).1
    nlinarith
  exact commonLeadingQuarticTransfer
    ePlus eMinus qPlus qMinus A delta delta C lambda
    hePlus heMinus hLeadingUpper hLambda
    hqPlusOneSided hqMinusOneSided hQuarticRatio hMargin

/-- The fixed-Hermite mass coefficient `9/16` survives a very coarse fifty
percent relative-form error.

Thus, for `lambda >= 2`, it is enough to place both Weil-tail energies in the
interval

`[(A-delta)e, (A+delta)e]`

with `2*delta <= A`.  No small asymptotic constant is required. -/
theorem fixedHermiteParityFromHalfRelativeError
    (ePlus eMinus qPlus qMinus A delta lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hA : 0 < A)
    (hDeltaNonneg : 0 ≤ delta)
    (hHalfError : 2 * delta ≤ A)
    (hLambda : 2 ≤ lambda)
    (hqPlus : |qPlus - A * ePlus| ≤ delta * ePlus)
    (hqMinus : |qMinus - A * eMinus| ≤ delta * eMinus)
    (hFixedHermiteRatio :
      lambda ^ 4 * ePlus ≤ (9 / 16 : ℝ) * eMinus) :
    qPlus < qMinus := by
  have hLambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hLambda
  have hLambdaSq : (4 : ℝ) ≤ lambda ^ 2 := by
    nlinarith
  have hLambdaFourth : (16 : ℝ) ≤ lambda ^ 4 := by
    have hsum : 0 ≤ lambda ^ 2 + 4 := by positivity
    have hprod :
        0 ≤ (lambda ^ 2 - 4) * (lambda ^ 2 + 4) :=
      mul_nonneg (sub_nonneg.mpr hLambdaSq) hsum
    nlinarith

  have hUpperCoeff : A + delta ≤ 3 * A / 2 := by
    nlinarith
  have hLowerCoeff : A / 2 ≤ A - delta := by
    nlinarith
  have hLeadingUpper : 0 ≤ A + delta := by
    nlinarith

  have hLeft :
      (A + delta) * (9 / 16 : ℝ) ≤ (3 * A / 2) * (9 / 16 : ℝ) :=
    mul_le_mul_of_nonneg_right hUpperCoeff (by norm_num)
  have hRightFirst :
      (A / 2) * 16 ≤ (A / 2) * lambda ^ 4 :=
    mul_le_mul_of_nonneg_left hLambdaFourth (by positivity)
  have hLambdaFourthNonneg : 0 ≤ lambda ^ 4 := by positivity
  have hRightSecond :
      (A / 2) * lambda ^ 4 ≤ (A - delta) * lambda ^ 4 :=
    mul_le_mul_of_nonneg_right hLowerCoeff hLambdaFourthNonneg
  have hMargin :
      (A + delta) * (9 / 16 : ℝ) <
        (A - delta) * lambda ^ 4 := by
    have hStrict :
        (3 * A / 2) * (9 / 16 : ℝ) < (A / 2) * 16 := by
      nlinarith
    exact lt_of_le_of_lt hLeft (lt_of_lt_of_le hStrict
      (hRightFirst.trans hRightSecond))

  exact commonLeadingAbsoluteErrorTransfer
    ePlus eMinus qPlus qMinus A delta (9 / 16) lambda
    hePlus heMinus hLeadingUpper hLambdaPos
    hqPlus hqMinus hFixedHermiteRatio hMargin

/-- A convenient one-quarter-error corollary. -/
theorem fixedHermiteParityFromQuarterRelativeError
    (ePlus eMinus qPlus qMinus A lambda : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hA : 0 < A)
    (hLambda : 2 ≤ lambda)
    (hqPlus : |qPlus - A * ePlus| ≤ (A / 4) * ePlus)
    (hqMinus : |qMinus - A * eMinus| ≤ (A / 4) * eMinus)
    (hFixedHermiteRatio :
      lambda ^ 4 * ePlus ≤ (9 / 16 : ℝ) * eMinus) :
    qPlus < qMinus := by
  exact fixedHermiteParityFromHalfRelativeError
    ePlus eMinus qPlus qMinus A (A / 4) lambda
    hePlus heMinus hA (by positivity) (by nlinarith)
    hLambda hqPlus hqMinus hFixedHermiteRatio

end RiemannCvs.CommonLeadingWeilTransfer
