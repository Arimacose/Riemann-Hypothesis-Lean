import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The right-half-plane sector factor for the digamma remainder

DLMF 5.11(ii) bounds the complex remainder in the digamma expansion by the
first neglected term times `sec (arg z / 2) ^ 3`.  This module discharges the
entire sector-geometry part on `0 < re z`: the argument lies in
`[-π/2, π/2]`, hence the factor is at most `2 * sqrt 2`.  Consequently the
DLMF coefficient `1 / 12` becomes the exact `sqrt 2 / 6` constant consumed by
the Archimedean diagonal route.  The remaining input is now only the analytic
first-neglected-term estimate itself.
-/

namespace RiemannCvs.DigammaQuadraticRemainder

lemma cos_half_arg_lower (w : ℂ) (hw : 0 < w.re) :
    Real.sqrt 2 / 2 ≤ Real.cos (w.arg / 2) := by
  have hArg : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.2 hw.le
  have hHalf : |w.arg / 2| ≤ Real.pi / 4 := by
    rw [abs_div]
    norm_num
    linarith
  have hQuarterNonneg : 0 ≤ Real.pi / 4 := by positivity
  have hQuarterLePi : Real.pi / 4 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hCos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (w.arg / 2)) hQuarterLePi hHalf
  rw [Real.cos_pi_div_four] at hCos
  simpa using hCos

lemma inv_cos_half_arg_le_sqrt_two (w : ℂ) (hw : 0 < w.re) :
    (Real.cos (w.arg / 2))⁻¹ ≤ Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hCos := cos_half_arg_lower w hw
  have hBase : 0 < Real.sqrt 2 / 2 := by positivity
  have hInv := one_div_le_one_div_of_le hBase hCos
  have hRecip : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
    field_simp [ne_of_gt hs]
    nlinarith
  rw [hRecip] at hInv
  simpa [one_div] using hInv

lemma sec_half_arg_cubed_le (w : ℂ) (hw : 0 < w.re) :
    (Real.cos (w.arg / 2))⁻¹ ^ 3 ≤ 2 * Real.sqrt 2 := by
  have hInv := inv_cos_half_arg_le_sqrt_two w hw
  have hCosPos : 0 < Real.cos (w.arg / 2) :=
    (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)).trans_le
      (cos_half_arg_lower w hw)
  have hPow : (Real.cos (w.arg / 2))⁻¹ ^ 3 ≤ (Real.sqrt 2) ^ 3 := by
    gcongr
  have hsSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  calc
    (Real.cos (w.arg / 2))⁻¹ ^ 3 ≤ (Real.sqrt 2) ^ 3 := hPow
    _ = 2 * Real.sqrt 2 := by
      rw [show Real.sqrt (2 : ℝ) ^ 3 =
          Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsSq]

/-- The DLMF first-neglected-term estimate implies the exact global constant
used by the cutoff-13 diagonal route once its sector factor is discharged. -/
theorem quadratic_remainder_bound_of_first_neglected_term
    (hFirst : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2) :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2 := by
  intro w hw
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hSector := sec_half_arg_cubed_le w hw
  have hCoeff :
      (1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3 ≤
        Real.sqrt 2 / 6 := by
    nlinarith
  exact (hFirst w hw).trans
    (div_le_div_of_nonneg_right hCoeff (sq_nonneg ‖w‖))

end RiemannCvs.DigammaQuadraticRemainder
