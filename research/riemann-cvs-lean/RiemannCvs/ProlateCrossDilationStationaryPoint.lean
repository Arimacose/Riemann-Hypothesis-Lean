import Mathlib

/-!
# Cross-mode stationary geometry for prolate dilation phases

For the radial phase

`ξ_a'(x)^2 = (x² - a) / (x² - 1)`,

the cross-mode dilation phase is `ξ_b(r x) - ξ_a(x)`.  After setting
`M = r²`, `t = x²`, and `s = M(t-1)`, its squared stationary equation
reduces to one quadratic polynomial.  This file formalizes the polynomial
geometry only; PSWF asymptotics and oscillatory-integral estimates remain
external analytic inputs.
-/

namespace RiemannCvs.ProlateCrossDilationStationaryPoint

def crossStationaryPoly (M a b t : ℝ) : ℝ :=
  M * (M - 1) * t ^ 2 +
    (1 - M ^ 2 + M * (a - b)) * t + M * b - a

def scaledStationaryPoly (M a b s : ℝ) : ℝ :=
  M ^ 2 * a + M ^ 2 * s - M ^ 2 +
    M * a * s - M * a - M * b * s +
    M * s ^ 2 - 2 * M * s + M - s ^ 2 + s

theorem crossSlopeNumerator
    (M a b t : ℝ) :
    M * (M * t - b) * (t - 1) -
        (t - a) * (M * t - 1) =
      crossStationaryPoly M a b t := by
  unfold crossStationaryPoly
  ring

theorem scaledSubstitution
    (M a b t : ℝ) :
    scaledStationaryPoly M a b (M * (t - 1)) =
      M * crossStationaryPoly M a b t := by
  unfold scaledStationaryPoly crossStationaryPoly
  ring

theorem scaledDifference
    (M a b s₁ s₂ : ℝ) :
    scaledStationaryPoly M a b s₂ -
        scaledStationaryPoly M a b s₁ =
      (s₂ - s₁) *
        ((M - 1) ^ 2 + M * (a - b) +
          (M - 1) * (s₁ + s₂)) := by
  unfold scaledStationaryPoly
  ring

theorem scaledDifferenceFactorPositive
    (M a b s₁ s₂ : ℝ)
    (hM : 4 ≤ M)
    (ha : 0 ≤ a)
    (hb : b ≤ 1 / 2)
    (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 ≤ s₂) :
    0 < (M - 1) ^ 2 + M * (a - b) +
      (M - 1) * (s₁ + s₂) := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 0 ≤ M - 1 := by linarith
  have hMb : M * b ≤ M / 2 := by
    have h := mul_le_mul_of_nonneg_left hb hM0
    nlinarith
  have hMa : 0 ≤ M * a := mul_nonneg hM0 ha
  have hs : 0 ≤ s₁ + s₂ := add_nonneg hs₁ hs₂
  have htail : 0 ≤ (M - 1) * (s₁ + s₂) := mul_nonneg hM1 hs
  have hbase : 0 < (M - 1) ^ 2 - M / 2 := by
    nlinarith [sq_nonneg (M - 4)]
  nlinarith

theorem scaledAtQuarterNegative
    (M a b : ℝ)
    (hM : 4 ≤ M)
    (_ha0 : 0 ≤ a)
    (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b) :
    scaledStationaryPoly M a b (1 / 4) < 0 := by
  have hM0 : 0 ≤ M := by linarith
  have hcoef : 0 ≤ 16 * M ^ 2 - 12 * M := by
    nlinarith [sq_nonneg (M - 4)]
  have haScaled := mul_le_mul_of_nonneg_left ha1 hcoef
  have hbTerm : -4 * M * b ≤ 0 := by
    nlinarith [mul_nonneg hM0 hb0]
  have hidentity :
      16 * scaledStationaryPoly M a b (1 / 4) =
        (16 * M ^ 2 - 12 * M) * a -
          12 * M ^ 2 - 4 * M * b + 9 * M + 3 := by
    unfold scaledStationaryPoly
    ring
  have hupper :
      16 * scaledStationaryPoly M a b (1 / 4) ≤
        -4 * M ^ 2 + 3 * M + 3 := by
    rw [hidentity]
    nlinarith
  have hnegative : -4 * M ^ 2 + 3 * M + 3 < 0 := by
    nlinarith [sq_nonneg (M - 4)]
  nlinarith

theorem scaledAtTwoPositive
    (M a b : ℝ)
    (hM : 4 ≤ M)
    (ha0 : 0 ≤ a)
    (hb1 : b ≤ 1 / 2) :
    0 < scaledStationaryPoly M a b 2 := by
  have hM0 : 0 ≤ M := by linarith
  have htwoM : 0 ≤ 2 * M := by nlinarith
  have hbScaled : 2 * M * b ≤ M := by
    have h := mul_le_mul_of_nonneg_left hb1 htwoM
    nlinarith
  have hidentity :
      scaledStationaryPoly M a b 2 =
        M ^ 2 * a + M ^ 2 + M * a -
          2 * M * b + M - 2 := by
    unfold scaledStationaryPoly
    ring
  rw [hidentity]
  nlinarith [sq_nonneg (M - 4), mul_nonneg hM0 ha0]

theorem scaledRootLayer
    (M a b s : ℝ)
    (hM : 4 ≤ M)
    (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2)
    (hs : 0 ≤ s)
    (hroot : scaledStationaryPoly M a b s = 0) :
    1 / 4 < s ∧ s < 2 := by
  have hquarter := scaledAtQuarterNegative M a b hM ha0 ha1 hb0
  have htwo := scaledAtTwoPositive M a b hM ha0 hb1
  constructor
  · by_contra hnot
    have hsle : s ≤ 1 / 4 := le_of_not_gt hnot
    have hfactor := scaledDifferenceFactorPositive
      M a b s (1 / 4) hM ha0 hb1 hs (by norm_num)
    have hnonneg :
        0 ≤ ((1 / 4 : ℝ) - s) *
          ((M - 1) ^ 2 + M * (a - b) +
            (M - 1) * (s + 1 / 4)) :=
      mul_nonneg (sub_nonneg.mpr hsle) (le_of_lt hfactor)
    have hdiff := scaledDifference M a b s (1 / 4)
    rw [hroot, sub_zero] at hdiff
    nlinarith
  · by_contra hnot
    have hge : 2 ≤ s := le_of_not_gt hnot
    have hfactor := scaledDifferenceFactorPositive
      M a b 2 s hM ha0 hb1 (by norm_num) hs
    have hnonneg :
        0 ≤ (s - 2) *
          ((M - 1) ^ 2 + M * (a - b) +
            (M - 1) * (2 + s)) :=
      mul_nonneg (sub_nonneg.mpr hge) (le_of_lt hfactor)
    have hdiff := scaledDifference M a b 2 s
    rw [hroot, zero_sub] at hdiff
    nlinarith

theorem uniqueScaledRoot
    (M a b s₁ s₂ : ℝ)
    (hM : 4 ≤ M)
    (ha : 0 ≤ a)
    (hb : b ≤ 1 / 2)
    (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 ≤ s₂)
    (hroot₁ : scaledStationaryPoly M a b s₁ = 0)
    (hroot₂ : scaledStationaryPoly M a b s₂ = 0) :
    s₁ = s₂ := by
  have hfactor := scaledDifferenceFactorPositive
    M a b s₁ s₂ hM ha hb hs₁ hs₂
  have hdiff := scaledDifference M a b s₁ s₂
  rw [hroot₁, hroot₂, sub_self] at hdiff
  have hprod :
      (s₂ - s₁) *
        ((M - 1) ^ 2 + M * (a - b) +
          (M - 1) * (s₁ + s₂)) = 0 := by
    simpa using hdiff.symm
  have hzero : s₂ - s₁ = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hfactor)
  linarith

def scaledDerivative (M a b s : ℝ) : ℝ :=
  (M - 1) ^ 2 + M * (a - b) + 2 * (M - 1) * s

theorem scaledDerivativeLower
    (M a b s : ℝ)
    (hM : 4 ≤ M)
    (ha : 0 ≤ a)
    (hb : b ≤ 1 / 2)
    (hs : 0 ≤ s) :
    M ^ 2 / 4 ≤ scaledDerivative M a b s := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 0 ≤ M - 1 := by linarith
  have hMb : M * b ≤ M / 2 := by
    have h := mul_le_mul_of_nonneg_left hb hM0
    nlinarith
  have hMa : 0 ≤ M * a := mul_nonneg hM0 ha
  have htail : 0 ≤ 2 * (M - 1) * s := by positivity
  have hpoly : 0 ≤ (M - 4) * (3 * M + 2) := by positivity
  unfold scaledDerivative
  nlinarith

theorem scaledDenominatorBudget
    (M s : ℝ)
    (hM : 4 ≤ M)
    (_hs0 : 0 ≤ s)
    (hs2 : s ≤ 2) :
    s * (M + s - 1) ≤ (5 / 2 : ℝ) * M := by
  have hfactor : 0 ≤ M + s - 1 := by linarith
  have hfirst : s * (M + s - 1) ≤ 2 * (M + s - 1) :=
    mul_le_mul_of_nonneg_right hs2 hfactor
  have hsecond : 2 * (M + s - 1) ≤ 2 * (M + 1) := by
    nlinarith
  have hthird : 2 * (M + 1) ≤ (5 / 2 : ℝ) * M := by
    linarith
  exact hfirst.trans (hsecond.trans hthird)

theorem curvatureScaleFromBudgets
    (r curvature denominator xOverP derivative : ℝ)
    (hr3 : r ^ 3 ≤ 8 * xOverP * derivative)
    (hcurv0 : 0 ≤ curvature)
    (hdenom : 2 * denominator ≤ 5)
    (hidentity : curvature * denominator = xOverP * derivative) :
    r ^ 3 ≤ 20 * curvature := by
  have hscaled := mul_le_mul_of_nonneg_left hdenom hcurv0
  nlinarith

end RiemannCvs.ProlateCrossDilationStationaryPoint
