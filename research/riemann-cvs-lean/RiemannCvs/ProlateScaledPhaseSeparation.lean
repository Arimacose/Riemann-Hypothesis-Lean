import RiemannCvs.ProlateScaledStationaryFamily

/-!
# Uniform separation of the scaled radial prolate phase derivative

For `u = r⁻²`, the cross-mode radial dilation phase has a derivative whose
numerator is `scaledSlopeNumerator u a b s`.  On the compact parameter range

`0 ≤ u ≤ 1/4`, `0 ≤ a,b ≤ 1/2`, `s ≥ 0`,

the numerator is uniformly increasing with slope at least `7/16`.  Hence, once
the unique stationary point is known, the phase derivative separates linearly
from zero.  This is the quantitative input needed for an elementary split into
a stationary layer of width `μ⁻¹/2` and two monotone nonstationary regions.

The square-root denominator and the oscillatory-integral argument are not
hidden here.  The final two lemmas accept an explicit positive denominator
bound as a hypothesis.
-/

namespace RiemannCvs.ProlateScaledPhaseSeparation

open RiemannCvs.ProlateScaledStationaryFamily

/-- Exact difference formula for the compact scaled slope numerator. -/
theorem scaledSlopeDifference
    (u a b s₁ s₂ : ℝ) :
    scaledSlopeNumerator u a b s₂ -
        scaledSlopeNumerator u a b s₁ =
      (s₂ - s₁) *
        ((1 - u) ^ 2 + u * (a - b) +
          u * (1 - u) * (s₁ + s₂)) := by
  unfold scaledSlopeNumerator
  ring

/-- Uniform lower bound for the difference coefficient.  The constant `7/16`
is the endpoint value of `(1-u)²-u/2` at `u=1/4`. -/
theorem differenceCoefficientLower
    (u a b s₁ s₂ : ℝ)
    (hu0 : 0 ≤ u)
    (hu4 : u ≤ 1 / 4)
    (ha0 : 0 ≤ a)
    (hb2 : b ≤ 1 / 2)
    (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 ≤ s₂) :
    (7 / 16 : ℝ) ≤
      (1 - u) ^ 2 + u * (a - b) +
        u * (1 - u) * (s₁ + s₂) := by
  have hOneMinus : 0 ≤ 1 - u := by linarith
  have hSum : 0 ≤ s₁ + s₂ := add_nonneg hs₁ hs₂
  have hTail : 0 ≤ u * (1 - u) * (s₁ + s₂) := by positivity
  have hab : -(1 / 2 : ℝ) ≤ a - b := by linarith
  have hUab : -(u / 2) ≤ u * (a - b) := by
    have h := mul_le_mul_of_nonneg_left hab hu0
    nlinarith
  have hEndpoint :
      (7 / 16 : ℝ) ≤ (1 - u) ^ 2 - u / 2 := by
    have hfactor : 0 ≤ (1 / 4 - u) * (9 / 4 - u) := by
      positivity
    nlinarith
  nlinarith

/-- To the right of a stationary root, the numerator grows at least linearly. -/
theorem numeratorLowerRightOfRoot
    (u a b root s : ℝ)
    (hu0 : 0 ≤ u)
    (hu4 : u ≤ 1 / 4)
    (ha0 : 0 ≤ a)
    (hb2 : b ≤ 1 / 2)
    (hroot0 : 0 ≤ root)
    (hs : root ≤ s)
    (hroot : scaledSlopeNumerator u a b root = 0) :
    (7 / 16 : ℝ) * (s - root) ≤
      scaledSlopeNumerator u a b s := by
  have hs0 : 0 ≤ s := le_trans hroot0 hs
  have hcoeff := differenceCoefficientLower
    u a b root s hu0 hu4 ha0 hb2 hroot0 hs0
  have hdelta : 0 ≤ s - root := sub_nonneg.mpr hs
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hdelta
  have hdiff := scaledSlopeDifference u a b root s
  rw [hroot, sub_zero] at hdiff
  nlinarith

/-- To the left of a stationary root, the negative numerator grows at least
linearly with the distance to the root. -/
theorem numeratorLowerLeftOfRoot
    (u a b root s : ℝ)
    (hu0 : 0 ≤ u)
    (hu4 : u ≤ 1 / 4)
    (ha0 : 0 ≤ a)
    (hb2 : b ≤ 1 / 2)
    (hs0 : 0 ≤ s)
    (hs : s ≤ root)
    (hroot : scaledSlopeNumerator u a b root = 0) :
    (7 / 16 : ℝ) * (root - s) ≤
      -scaledSlopeNumerator u a b s := by
  have hroot0 : 0 ≤ root := le_trans hs0 hs
  have hcoeff := differenceCoefficientLower
    u a b s root hu0 hu4 ha0 hb2 hs0 hroot0
  have hdelta : 0 ≤ root - s := sub_nonneg.mpr hs
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hdelta
  have hdiff := scaledSlopeDifference u a b s root
  rw [hroot, zero_sub] at hdiff
  nlinarith

/-- If the positive square-root denominator is at most `66`, the actual scaled
phase derivative is at least `(7/1056)(s-root)` to the right of the root. -/
theorem phaseDerivativeLowerRight
    (numerator phaseDerivative denominator root s : ℝ)
    (hroot : root ≤ s)
    (hnum : (7 / 16 : ℝ) * (s - root) ≤ numerator)
    (hidentity : numerator = phaseDerivative * denominator)
    (hdenPos : 0 < denominator)
    (hdenUpper : denominator ≤ 66) :
    (7 / 1056 : ℝ) * (s - root) ≤ phaseDerivative := by
  have hdelta : 0 ≤ s - root := sub_nonneg.mpr hroot
  have hdenScaled :
      (7 / 1056 : ℝ) * (s - root) * denominator ≤
        (7 / 16 : ℝ) * (s - root) := by
    have h := mul_le_mul_of_nonneg_left hdenUpper
      (mul_nonneg (by norm_num) hdelta)
    nlinarith
  have hproduct :
      (7 / 1056 : ℝ) * (s - root) * denominator ≤
        phaseDerivative * denominator := by
    rw [← hidentity]
    exact hdenScaled.trans hnum
  exact (mul_le_mul_right hdenPos).mp (by
    simpa [mul_assoc] using hproduct)

/-- Symmetric left-side derivative estimate. -/
theorem phaseDerivativeUpperLeft
    (numerator phaseDerivative denominator root s : ℝ)
    (hs : s ≤ root)
    (hnum : (7 / 16 : ℝ) * (root - s) ≤ -numerator)
    (hidentity : numerator = phaseDerivative * denominator)
    (hdenPos : 0 < denominator)
    (hdenUpper : denominator ≤ 66) :
    phaseDerivative ≤ -(7 / 1056 : ℝ) * (root - s) := by
  have hdelta : 0 ≤ root - s := sub_nonneg.mpr hs
  have hdenScaled :
      (7 / 1056 : ℝ) * (root - s) * denominator ≤
        (7 / 16 : ℝ) * (root - s) := by
    have h := mul_le_mul_of_nonneg_left hdenUpper
      (mul_nonneg (by norm_num) hdelta)
    nlinarith
  have hproduct :
      (7 / 1056 : ℝ) * (root - s) * denominator ≤
        (-phaseDerivative) * denominator := by
    have hnegIdentity : -numerator = (-phaseDerivative) * denominator := by
      rw [hidentity]
      ring
    rw [← hnegIdentity]
    exact hdenScaled.trans hnum
  have hcancel := (mul_le_mul_right hdenPos).mp (by
    simpa [mul_assoc] using hproduct)
  linarith

end RiemannCvs.ProlateScaledPhaseSeparation
