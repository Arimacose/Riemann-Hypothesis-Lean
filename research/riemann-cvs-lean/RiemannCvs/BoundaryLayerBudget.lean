import RiemannCvs.OddTempleParityTransfer

/-!
# Turning an O(1) boundary-layer remainder into a relative parity budget

The boundary-layer reduction predicts

`q = A * e + O(e)`,  with `A = 2 log lambda`.

Since `A` grows, a uniform absolute coefficient bound `C` eventually becomes a
small relative error.  This file records the finite inequalities needed to feed
such an analytic estimate into the odd-sector Temple certificate.
-/

namespace RiemannCvs.BoundaryLayerBudget

/-- If `4 C <= A`, an `O(C e)` coefficient error is at most one quarter of the
leading energy `A e`. -/
theorem quarterRelativeErrorFromBoundedRemainder
    (e q A C : ℝ)
    (he : 0 ≤ e)
    (hC : 0 ≤ C)
    (hGrowth : 4 * C ≤ A)
    (hRemainder : |q - A * e| ≤ C * e) :
    |q - A * e| ≤ (A / 4) * e := by
  have hCoeff : C ≤ A / 4 := by
    nlinarith
  have hScaled : C * e ≤ (A / 4) * e :=
    mul_le_mul_of_nonneg_right hCoeff he
  exact le_trans hRemainder hScaled

/-- A residual budget with coefficient `C` is also a quarter-Temple budget once
`4 C <= A`. -/
theorem quarterTempleResidualFromBoundedCoefficient
    (e residualSq gap A C : ℝ)
    (he : 0 ≤ e)
    (hgap : 0 ≤ gap)
    (hC : 0 ≤ C)
    (hGrowth : 4 * C ≤ A)
    (hResidual : residualSq ≤ (C * e) * gap) :
    residualSq ≤ ((A / 4) * e) * gap := by
  have hCoeff : C ≤ A / 4 := by
    nlinarith
  have hEnergy : C * e ≤ (A / 4) * e :=
    mul_le_mul_of_nonneg_right hCoeff he
  have hScaled := mul_le_mul_of_nonneg_right hEnergy hgap
  exact le_trans hResidual hScaled

/-- Complete fixed-Hermite ground-parity certificate from uniform bounded
boundary-layer remainders and a Temple residual budget.

The theorem is intentionally finite-scale.  An analytic proof may instantiate
`A = 2 log lambda` and a mode-independent constant `C`; once `4 C <= A`, the
quartic reference margin is strong enough to absorb both form errors and the
Temple correction. -/
theorem fixedHermiteGroundParityFromBoundedRemainders
    (ePlus eMinus qPlus thetaMinus muMinus
      A C lambda residualSq gap : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hA : 0 < A)
    (hC : 0 ≤ C)
    (hGrowth : 4 * C ≤ A)
    (hLambda : 2 ≤ lambda)
    (hgap : 0 < gap)
    (hqPlus : |qPlus - A * ePlus| ≤ C * ePlus)
    (hThetaMinus : |thetaMinus - A * eMinus| ≤ C * eMinus)
    (hTemple : thetaMinus - residualSq / gap ≤ muMinus)
    (hResidual : residualSq ≤ (C * eMinus) * gap)
    (hFixedHermiteRatio :
      lambda ^ 4 * ePlus ≤ (9 / 16 : ℝ) * eMinus) :
    qPlus < muMinus := by
  have hqQuarter := quarterRelativeErrorFromBoundedRemainder
    ePlus qPlus A C hePlus hC hGrowth hqPlus
  have hThetaQuarter := quarterRelativeErrorFromBoundedRemainder
    eMinus thetaMinus A C (le_of_lt heMinus) hC hGrowth hThetaMinus
  have hResidualQuarter := quarterTempleResidualFromBoundedCoefficient
    eMinus residualSq gap A C (le_of_lt heMinus) (le_of_lt hgap)
    hC hGrowth hResidual
  exact RiemannCvs.OddTempleParityTransfer.fixedHermiteGroundParityFromTempleData
    ePlus eMinus qPlus thetaMinus muMinus A lambda residualSq gap
    hePlus heMinus hA hLambda hgap
    hqQuarter hThetaQuarter hTemple hResidualQuarter
    hFixedHermiteRatio

end RiemannCvs.BoundaryLayerBudget
