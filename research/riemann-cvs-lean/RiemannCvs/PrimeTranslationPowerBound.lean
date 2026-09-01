import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Sixth-power norm extraction for the prime-translation operator

The cutoff-13 path certificate controls the sixth power of a self-adjoint
translation operator.  This module proves the exact C-star algebra step that
turns that certificate into an operator-norm bound.  In particular, no
unproved appeal to spectral calculus remains in the `power = 6` reduction.
-/

namespace RiemannCvs.PrimeTranslationPowerBound

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Nontrivial A]

theorem norm_pow_three {T : A} (hT : IsSelfAdjoint T) :
    ‖T ^ 3‖ = ‖T‖ ^ 3 := by
  by_cases hZero : T = 0
  · simp [hZero]
  have hNormPos : 0 < ‖T‖ := norm_pos_iff.mpr hZero
  have hUpper : ‖T ^ 3‖ ≤ ‖T‖ ^ 3 := norm_pow_le T 3
  have hFour : ‖T ^ 4‖ = ‖T‖ ^ 4 := by
    simpa using hT.norm_pow_two_pow 2
  have hLower : ‖T‖ ^ 4 ≤ ‖T ^ 3‖ * ‖T‖ := by
    calc
      ‖T‖ ^ 4 = ‖T ^ 4‖ := hFour.symm
      _ = ‖T ^ 3 * T‖ := by rw [pow_succ]
      _ ≤ ‖T ^ 3‖ * ‖T‖ := norm_mul_le _ _
  nlinarith

theorem norm_pow_six {T : A} (hT : IsSelfAdjoint T) :
    ‖T ^ 6‖ = ‖T‖ ^ 6 := by
  calc
    ‖T ^ 6‖ = ‖(T ^ 3) * (T ^ 3)‖ := by
      congr 1
      rw [← pow_add]
    _ = ‖T ^ 3‖ ^ 2 := (hT.pow 3).norm_mul_self
    _ = ‖T‖ ^ 6 := by rw [norm_pow_three hT]; ring

theorem norm_lt_of_norm_pow_six_lt
    {T : A} (hT : IsSelfAdjoint T) {B : ℝ} (hB : 0 ≤ B)
    (hPower : ‖T ^ 6‖ < B ^ 6) :
    ‖T‖ < B := by
  rw [norm_pow_six hT] at hPower
  by_contra h
  have hLe : B ≤ ‖T‖ := le_of_not_gt h
  have hPowLe : B ^ 6 ≤ ‖T‖ ^ 6 := pow_le_pow_left₀ hB hLe 6
  exact (not_lt_of_ge hPowLe) hPower

/-- The exact rational target used by the cutoff-13 prime path certificate. -/
theorem norm_lt_tenThird_of_norm_pow_six_lt
    {T : A} (hT : IsSelfAdjoint T)
    (hPower : ‖T ^ 6‖ < (10 / 3 : ℝ) ^ 6) :
    ‖T‖ < (10 / 3 : ℝ) := by
  exact norm_lt_of_norm_pow_six_lt hT (by norm_num) hPower

end RiemannCvs.PrimeTranslationPowerBound
