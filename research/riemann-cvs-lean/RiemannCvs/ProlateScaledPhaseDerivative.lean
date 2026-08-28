import RiemannCvs.ProlateScaledDenominator
import RiemannCvs.ProlateScaledPhaseSeparation

/-!
# Concrete scaled radial phase derivative

This file joins the machine-checked slope numerator and denominator estimates.
On the compact stationary box it proves a fully explicit linear separation

`|Psi'(s)| >= (7/1088) |s-root|`

on either side of the unique stationary point.  The constant uses the certified
denominator bound `68`.

The subsequent oscillatory integration-by-parts argument remains ordinary
analysis rather than a Lean theorem in this module.
-/

namespace RiemannCvs.ProlateScaledPhaseDerivative

open RiemannCvs.ProlateScaledStationaryFamily
open RiemannCvs.ProlateScaledDenominator
open RiemannCvs.ProlateScaledPhaseSeparation

noncomputable def scaledPhaseDerivative (u a b s : ℝ) : ℝ :=
  (Real.sqrt (ratioA u b s) - Real.sqrt (ratioB u a s)) /
    (2 * Real.sqrt (1 + u * s))

/-- Rationalizing the square-root difference recovers exactly the compact slope
numerator. -/
theorem derivative_times_denominator
    (u a b s : ℝ)
    (hs : 0 < s)
    (hx : 0 < 1 + u * s)
    (hq : 0 < 1 + u * (s - 1))
    (hA : 0 ≤ ratioA u b s)
    (hB : 0 ≤ ratioB u a s) :
    scaledPhaseDerivative u a b s *
        phaseDenominator u a b s =
      scaledSlopeNumerator u a b s := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hqne : 1 + u * (s - 1) ≠ 0 := ne_of_gt hq
  have hsqrtX : Real.sqrt (1 + u * s) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hx)
  have hsqA : (Real.sqrt (ratioA u b s)) ^ 2 = ratioA u b s :=
    Real.sq_sqrt hA
  have hsqB : (Real.sqrt (ratioB u a s)) ^ 2 = ratioB u a s :=
    Real.sq_sqrt hB
  unfold scaledPhaseDerivative phaseDenominator
  have hdiff :
      (Real.sqrt (ratioA u b s) - Real.sqrt (ratioB u a s)) *
          (Real.sqrt (ratioA u b s) + Real.sqrt (ratioB u a s)) =
        ratioA u b s - ratioB u a s := by
    nlinarith
  rw [div_mul_eq_mul_div, mul_assoc, hdiff]
  field_simp [hsqrtX]
  unfold ratioA ratioB scaledSlopeNumerator
  field_simp [hsne, hqne]
  ring

section Box

variable (u a b root s : ℝ)
variable (hu0 : 0 ≤ u) (hu4 : u ≤ 1 / 4)
variable (ha0 : 0 ≤ a) (ha2 : a ≤ 1 / 2)
variable (hb0 : 0 ≤ b) (hb2 : b ≤ 1 / 2)
variable (hroot8 : 1 / 8 ≤ root) (hroot3 : root ≤ 3)
variable (hs8 : 1 / 8 ≤ s) (hs3 : s ≤ 3)
variable (hroot : scaledSlopeNumerator u a b root = 0)

private theorem q_pos (z : ℝ) (hz8 : 1 / 8 ≤ z) :
    0 < 1 + u * (z - 1) := by
  have huz : 0 ≤ u * z :=
    mul_nonneg hu0 (le_trans (by norm_num) hz8)
  nlinarith

private theorem x_pos (z : ℝ) (hz8 : 1 / 8 ≤ z) :
    0 < 1 + u * z := by
  have huz : 0 ≤ u * z :=
    mul_nonneg hu0 (le_trans (by norm_num) hz8)
  linarith

/-- Concrete right-side derivative separation on the stationary box. -/
theorem derivativeLowerRight
    (horder : root ≤ s) :
    (7 / 1088 : ℝ) * (s - root) ≤
      scaledPhaseDerivative u a b s := by
  have hnum := numeratorLowerRightOfRoot
    u a b root s hu0 hu4 ha0 hb2
    (le_trans (by norm_num) hroot8) horder hroot
  have hA := ProlateScaledDenominator.ratioA_nonneg
    u b s hu0 hu4 hb0 hb2 hs8
  have hB := ProlateScaledDenominator.ratioB_nonneg
    u a s hu0 ha2 hs8
  have hidentity := derivative_times_denominator
    u a b s (lt_of_lt_of_le (by norm_num) hs8)
    (x_pos u s hu0 hs8) (q_pos u s hu0 hu4 hs8) hA hB
  have hdenPos := phaseDenominator_pos
    u a b s hu0 hu4 ha0 ha2 hb0 hb2 hs8 hs3
  have hdenUpper := phaseDenominator_le_sixtyEight
    u a b s hu0 hu4 ha0 ha2 hb0 hb2 hs8 hs3
  have hdelta : 0 ≤ s - root := sub_nonneg.mpr horder
  have hdenScaled :
      (7 / 1088 : ℝ) * (s - root) * phaseDenominator u a b s ≤
        (7 / 16 : ℝ) * (s - root) := by
    have h := mul_le_mul_of_nonneg_left hdenUpper
      (mul_nonneg (by norm_num) hdelta)
    nlinarith
  have hproduct :
      (7 / 1088 : ℝ) * (s - root) * phaseDenominator u a b s ≤
        scaledPhaseDerivative u a b s * phaseDenominator u a b s := by
    rw [hidentity]
    exact hdenScaled.trans hnum
  exact (mul_le_mul_right hdenPos).mp (by
    simpa [mul_assoc] using hproduct)

/-- Concrete left-side derivative separation on the stationary box. -/
theorem derivativeUpperLeft
    (horder : s ≤ root) :
    scaledPhaseDerivative u a b s ≤
      -(7 / 1088 : ℝ) * (root - s) := by
  have hnum := numeratorLowerLeftOfRoot
    u a b root s hu0 hu4 ha0 hb2
    (le_trans (by norm_num) hs8) horder hroot
  have hA := ProlateScaledDenominator.ratioA_nonneg
    u b s hu0 hu4 hb0 hb2 hs8
  have hB := ProlateScaledDenominator.ratioB_nonneg
    u a s hu0 ha2 hs8
  have hidentity := derivative_times_denominator
    u a b s (lt_of_lt_of_le (by norm_num) hs8)
    (x_pos u s hu0 hs8) (q_pos u s hu0 hu4 hs8) hA hB
  have hdenPos := phaseDenominator_pos
    u a b s hu0 hu4 ha0 ha2 hb0 hb2 hs8 hs3
  have hdenUpper := phaseDenominator_le_sixtyEight
    u a b s hu0 hu4 ha0 ha2 hb0 hb2 hs8 hs3
  have hdelta : 0 ≤ root - s := sub_nonneg.mpr horder
  have hdenScaled :
      (7 / 1088 : ℝ) * (root - s) * phaseDenominator u a b s ≤
        (7 / 16 : ℝ) * (root - s) := by
    have h := mul_le_mul_of_nonneg_left hdenUpper
      (mul_nonneg (by norm_num) hdelta)
    nlinarith
  have hproduct :
      (7 / 1088 : ℝ) * (root - s) * phaseDenominator u a b s ≤
        (-scaledPhaseDerivative u a b s) * phaseDenominator u a b s := by
    have hnegIdentity :
        -scaledSlopeNumerator u a b s =
          (-scaledPhaseDerivative u a b s) * phaseDenominator u a b s := by
      rw [← hidentity]
      ring
    rw [← hnegIdentity]
    exact hdenScaled.trans hnum
  have hcancel := (mul_le_mul_right hdenPos).mp (by
    simpa [mul_assoc] using hproduct)
  linarith

end Box

end RiemannCvs.ProlateScaledPhaseDerivative
