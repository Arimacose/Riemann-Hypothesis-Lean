import RiemannCvs.BlockGapTransfer

/-!
# Stationary-phase coupling versus an eighth-power high-mode gap

The corrected prolate dilation analysis predicts a low/high prime coupling of
size `O(λ³ / log λ)` after normalization by the lowest odd reference energy.
For a conservative scalar certificate we discard the logarithm and assume

`k² ≤ C² λ⁶`.

The first odd constrained high-mode gap is of relative order `G λ⁸`.  Hence the
Schur determinant condition follows once `λ²` dominates the fixed coupling
constant.  This file formalizes that scale comparison and plugs it into the
existing parity-separation theorem.

No stationary-phase estimate, prolate asymptotic, or Weil-form lower bound is
asserted here.  They appear only as explicit hypotheses.
-/

namespace RiemannCvs.StationarySchurNoIntruder

/-- A coupling of order at most `λ³` is absorbed by an eighth-power high-mode
gap once the explicit quadratic threshold is crossed. -/
theorem determinantBudgetFromStationaryScale
    (m G k C lambda : ℝ)
    (hm : 0 < m)
    (hlambda : 1 ≤ lambda)
    (hHighFloor : m ≤ G * lambda ^ 8)
    (hCoupling : k ^ 2 ≤ C ^ 2 * lambda ^ 6)
    (hThreshold : 4 * C ^ 2 ≤ m * G * lambda ^ 2) :
    k ^ 2 ≤ (m / 2) * (G * lambda ^ 8 - m / 2) := by
  have hm0 : 0 ≤ m := le_of_lt hm
  have hlambda6 : 0 ≤ lambda ^ 6 := sq_nonneg (lambda ^ 3)
  have hThresholdScaled :=
    mul_le_mul_of_nonneg_right hThreshold hlambda6
  have hCouplingToQuarter :
      C ^ 2 * lambda ^ 6 ≤
        (m / 2) * ((G * lambda ^ 8) / 2) := by
    nlinarith [hThresholdScaled]
  have hGapHalf :
      (G * lambda ^ 8) / 2 ≤ G * lambda ^ 8 - m / 2 := by
    nlinarith [hHighFloor]
  have hRhs :
      (m / 2) * ((G * lambda ^ 8) / 2) ≤
        (m / 2) * (G * lambda ^ 8 - m / 2) :=
    mul_le_mul_of_nonneg_left hGapHalf (by positivity)
  exact hCoupling.trans (hCouplingToQuarter.trans hRhs)

/-- The stationary-scale coupling cannot create a high-mode intruder below
half of the odd low-block baseline. -/
theorem oddLowerBoundFromStationaryScale
    (q e x y m G k C lambda : ℝ)
    (he : 0 < e)
    (hm : 0 < m)
    (hlambda : 1 ≤ lambda)
    (hHighFloor : m ≤ G * lambda ^ 8)
    (hCoupling : k ^ 2 ≤ C ^ 2 * lambda ^ 6)
    (hThreshold : 4 * C ^ 2 ≤ m * G * lambda ^ 2)
    (hq :
      e * (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 -
        2 * k * x * y) ≤ q) :
    e * (m / 2) * (x ^ 2 + y ^ 2) ≤ q := by
  have hdet := determinantBudgetFromStationaryScale
    m G k C lambda hm hlambda hHighFloor hCoupling hThreshold
  exact RiemannCvs.BlockGapTransfer.lambdaEightBlockLowerBound
    q e x y m G k lambda he hm hdet hq

/-- Complete scalar parity certificate combining the quartic even trial scale,
the eighth-power odd high gap, and the stationary-phase coupling scale. -/
theorem quarticParityFromStationarySchur
    (qPlus qMinus e x y m G k C M0 C0 lambda : ℝ)
    (he : 0 < e)
    (hm : 0 < m)
    (hlambda : 1 ≤ lambda)
    (hnorm : x ^ 2 + y ^ 2 = 1)
    (hOdd :
      e * (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 -
        2 * k * x * y) ≤ qMinus)
    (hHighFloor : m ≤ G * lambda ^ 8)
    (hCoupling : k ^ 2 ≤ C ^ 2 * lambda ^ 6)
    (hThreshold : 4 * C ^ 2 ≤ m * G * lambda ^ 2)
    (hEvenScaled : lambda ^ 4 * qPlus ≤ e * (M0 * C0))
    (hQuarticMargin : 2 * (M0 * C0) < m * lambda ^ 4) :
    qPlus < qMinus := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hdet := determinantBudgetFromStationaryScale
    m G k C lambda hm hlambda hHighFloor hCoupling hThreshold
  exact RiemannCvs.BlockGapTransfer.quarticEvenOddSeparation
    qPlus qMinus e x y m G k M0 C0 lambda
    he hm hlambdaPos hnorm hOdd hdet hEvenScaled hQuarticMargin

/-- A convenient threshold restatement: a fixed stationary coupling constant is
harmless once `λ²` exceeds `4 C² / (m G)`, written without division. -/
theorem thresholdMonotone
    (m G C lambda Lambda : ℝ)
    (hLambda : 0 ≤ Lambda)
    (hlambda : Lambda ≤ lambda)
    (hThresholdAtLambda : 4 * C ^ 2 ≤ m * G * Lambda ^ 2)
    (hmG : 0 ≤ m * G) :
    4 * C ^ 2 ≤ m * G * lambda ^ 2 := by
  have hsquares : Lambda ^ 2 ≤ lambda ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsquares hmG
  exact hThresholdAtLambda.trans hscaled

end RiemannCvs.StationarySchurNoIntruder
