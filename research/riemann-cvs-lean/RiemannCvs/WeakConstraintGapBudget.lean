import RiemannCvs.ConstraintGapTransfer

/-!
# Weak lower bounds still suffice for the eighth-power no-crossing margin

The pure fixed-index prolate model separates the lowest unconstrained scale
from the first boundary-constrained scale by `lambda^8`.  Consequently, the
actual boundary-constrained lower bridge does not need a uniform positive
condition number.  It may deteriorate by almost eight powers of `lambda` and
still force a strict boundary gap.

This file records concrete division-free consequences.  The analytic estimates
for the actual Weil form remain explicit hypotheses.
-/

namespace RiemannCvs.WeakConstraintGapBudget

/-- A constrained lower bound as weak as `m0 / lambda^7` still beats an
unconstrained upper bound with fixed coefficient `M`, provided the remaining
linear margin `M*C < m0*lambda` holds. -/
theorem seventhPowerLowerBridgeSuffices
    (eLow eConstraint qLow nuConstraint m0 M C lambda : ℝ)
    (heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hM : 0 ≤ M)
    (hLambda : 0 < lambda)
    (hqLow : qLow ≤ M * eLow)
    (hConstraint :
      (m0 / lambda ^ 7) * eConstraint ≤ nuConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin : M * C < m0 * lambda) :
    qLow < nuConstraint := by
  have hLambdaSeven : 0 < lambda ^ 7 := pow_pos hLambda 7
  have hMargin' :
      M * C < (m0 / lambda ^ 7) * lambda ^ 8 := by
    field_simp [ne_of_gt hLambdaSeven]
    nlinarith [pow_succ lambda 7]
  exact RiemannCvs.ConstraintGapTransfer.eighthPowerGapTransfer
    eLow eConstraint qLow nuConstraint
    (m0 / lambda ^ 7) M C lambda
    heLow heConstraint hM hLambda hqLow hConstraint
    hEighthRatio hMargin'

/-- A `lambda^-6` constrained lower bridge leaves a quadratic margin. -/
theorem sixthPowerLowerBridgeSuffices
    (eLow eConstraint qLow nuConstraint m0 M C lambda : ℝ)
    (heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hM : 0 ≤ M)
    (hLambda : 0 < lambda)
    (hqLow : qLow ≤ M * eLow)
    (hConstraint :
      (m0 / lambda ^ 6) * eConstraint ≤ nuConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin : M * C < m0 * lambda ^ 2) :
    qLow < nuConstraint := by
  have hLambdaSix : 0 < lambda ^ 6 := pow_pos hLambda 6
  have hMargin' :
      M * C < (m0 / lambda ^ 6) * lambda ^ 8 := by
    field_simp [ne_of_gt hLambdaSix]
    nlinarith [pow_succ lambda 6, pow_succ lambda 7]
  exact RiemannCvs.ConstraintGapTransfer.eighthPowerGapTransfer
    eLow eConstraint qLow nuConstraint
    (m0 / lambda ^ 6) M C lambda
    heLow heConstraint hM hLambda hqLow hConstraint
    hEighthRatio hMargin'

/-- If the unconstrained upper bridge itself grows linearly in `lambda`, a
`lambda^-6` constrained lower bridge still leaves one power of asymptotic
margin. -/
theorem linearUpperAndSixthPowerLowerSuffice
    (eLow eConstraint qLow nuConstraint m0 M0 C lambda : ℝ)
    (heLow : 0 ≤ eLow)
    (heConstraint : 0 < eConstraint)
    (hM0 : 0 ≤ M0)
    (hLambda : 0 < lambda)
    (hqLow : qLow ≤ (M0 * lambda) * eLow)
    (hConstraint :
      (m0 / lambda ^ 6) * eConstraint ≤ nuConstraint)
    (hEighthRatio : lambda ^ 8 * eLow ≤ C * eConstraint)
    (hMargin : M0 * C < m0 * lambda) :
    qLow < nuConstraint := by
  have hMarginScaled :
      (M0 * lambda) * C < m0 * lambda ^ 2 := by
    have hpos := hLambda
    nlinarith
  exact sixthPowerLowerBridgeSuffices
    eLow eConstraint qLow nuConstraint m0 (M0 * lambda) C lambda
    heLow heConstraint (mul_nonneg hM0 (le_of_lt hLambda)) hLambda
    hqLow hConstraint hEighthRatio hMarginScaled

end RiemannCvs.WeakConstraintGapBudget
