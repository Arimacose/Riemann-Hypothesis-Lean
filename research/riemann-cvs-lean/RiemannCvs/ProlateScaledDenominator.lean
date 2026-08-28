import Mathlib

/-!
# A uniform denominator bound for the scaled radial phase derivative

After rationalizing the two square roots in the compact radial phase, the
slope numerator is divided by

`2 sqrt(1+u s) s (1+u(s-1)) (sqrt A + sqrt B)`.

On the stationary box used in the V17 argument this file proves the explicit
upper bound `68`.  The slightly weaker constant, rather than a hand-optimized
`66`, keeps the proof elementary and fully machine-checkable.
-/

namespace RiemannCvs.ProlateScaledDenominator

noncomputable def ratioA (u b s : ℝ) : ℝ :=
  (1 + u * (s - b)) / (1 + u * (s - 1))

noncomputable def ratioB (u a s : ℝ) : ℝ :=
  (1 - a + u * s) / s

noncomputable def phaseDenominator (u a b s : ℝ) : ℝ :=
  2 * Real.sqrt (1 + u * s) * s * (1 + u * (s - 1)) *
    (Real.sqrt (ratioA u b s) + Real.sqrt (ratioB u a s))

section Box

variable (u a b s : ℝ)
variable (hu0 : 0 ≤ u) (hu4 : u ≤ 1 / 4)
variable (ha0 : 0 ≤ a) (ha2 : a ≤ 1 / 2)
variable (hb0 : 0 ≤ b) (hb2 : b ≤ 1 / 2)
variable (hs8 : 1 / 8 ≤ s) (hs3 : s ≤ 3)

private theorem s_pos : 0 < s := by linarith

private theorem us_nonneg : 0 ≤ u * s :=
  mul_nonneg hu0 (le_trans (by norm_num) hs8)

private theorem us_upper : u * s ≤ 3 / 4 := by
  exact mul_le_mul hu4 hs3 (le_trans (by norm_num) hs8) (by norm_num)

private theorem q_lower : 3 / 4 ≤ 1 + u * (s - 1) := by
  have hus := us_nonneg u s hu0 hs8
  nlinarith

private theorem q_upper : 1 + u * (s - 1) ≤ 3 / 2 := by
  have hsMinus : s - 1 ≤ 2 := by linarith
  have hmul : u * (s - 1) ≤ u * 2 :=
    mul_le_mul_of_nonneg_left hsMinus hu0
  nlinarith

private theorem sqrt_x_upper : Real.sqrt (1 + u * s) ≤ 4 / 3 := by
  have hrad : 0 ≤ 1 + u * s := by
    have := us_nonneg u s hu0 hs8
    linarith
  have hsq := Real.sq_sqrt hrad
  have hupper := us_upper u s hu0 hu4 hs8 hs3
  have hsqrt0 := Real.sqrt_nonneg (1 + u * s)
  nlinarith

private theorem ratioA_nonneg : 0 ≤ ratioA u b s := by
  have hq : 0 < 1 + u * (s - 1) :=
    lt_of_lt_of_le (by norm_num) (q_lower u s hu0 hs8)
  have hub : u * b ≤ 1 / 8 := by
    exact mul_le_mul hu4 hb2 hb0 (by norm_num)
  have hus := us_nonneg u s hu0 hs8
  have hnum : 0 ≤ 1 + u * (s - b) := by
    ring_nf
    nlinarith
  exact div_nonneg hnum (le_of_lt hq)

private theorem ratioA_upper : ratioA u b s ≤ 7 / 3 := by
  have hq : 0 < 1 + u * (s - 1) :=
    lt_of_lt_of_le (by norm_num) (q_lower u s hu0 hs8)
  have husUpper := us_upper u s hu0 hu4 hs8 hs3
  have hub : 0 ≤ u * b := mul_nonneg hu0 hb0
  have hnum : 1 + u * (s - b) ≤ 7 / 4 := by
    ring_nf
    nlinarith
  unfold ratioA
  apply (div_le_iff₀ hq).2
  have hqLower := q_lower u s hu0 hs8
  nlinarith

private theorem sqrt_ratioA_upper : Real.sqrt (ratioA u b s) ≤ 8 / 5 := by
  have hnonneg := ratioA_nonneg u b s hu0 hu4 hb0 hb2 hs8
  have hsq := Real.sq_sqrt hnonneg
  have hupper := ratioA_upper u b s hu0 hu4 hb0 hs8 hs3
  have hsqrt0 := Real.sqrt_nonneg (ratioA u b s)
  nlinarith

private theorem ratioB_nonneg : 0 ≤ ratioB u a s := by
  have hspos := s_pos s hs8
  have hus := us_nonneg u s hu0 hs8
  have hnum : 0 ≤ 1 - a + u * s := by linarith
  exact div_nonneg hnum (le_of_lt hspos)

private theorem ratioB_upper : ratioB u a s ≤ 14 := by
  have hspos := s_pos s hs8
  have husUpper := us_upper u s hu0 hu4 hs8 hs3
  have hnum : 1 - a + u * s ≤ 7 / 4 := by nlinarith
  unfold ratioB
  apply (div_le_iff₀ hspos).2
  nlinarith

private theorem sqrt_ratioB_upper : Real.sqrt (ratioB u a s) ≤ 4 := by
  have hnonneg := ratioB_nonneg u a s hu0 ha2 hs8
  have hsq := Real.sq_sqrt hnonneg
  have hupper := ratioB_upper u a s hu0 hu4 ha0 hs8 hs3
  have hsqrt0 := Real.sqrt_nonneg (ratioB u a s)
  nlinarith

/-- The rationalized square-root denominator is positive on the stationary
box. -/
theorem phaseDenominator_pos :
    0 < phaseDenominator u a b s := by
  have hspos := s_pos s hs8
  have hq : 0 < 1 + u * (s - 1) :=
    lt_of_lt_of_le (by norm_num) (q_lower u s hu0 hs8)
  have hA : 0 < Real.sqrt (ratioA u b s) := by
    have hqpos := hq
    have hub : u * b ≤ 1 / 8 := by
      exact mul_le_mul hu4 hb2 hb0 (by norm_num)
    have hus := us_nonneg u s hu0 hs8
    have hnum : 0 < 1 + u * (s - b) := by
      ring_nf
      nlinarith
    have hratio : 0 < ratioA u b s := by
      unfold ratioA
      exact div_pos hnum hqpos
    exact Real.sqrt_pos.2 hratio
  have hX : 0 < Real.sqrt (1 + u * s) := by
    apply Real.sqrt_pos.2
    have := us_nonneg u s hu0 hs8
    linarith
  unfold phaseDenominator
  positivity

/-- Fully explicit machine-checked denominator upper bound. -/
theorem phaseDenominator_le_sixtyEight :
    phaseDenominator u a b s ≤ 68 := by
  have hx0 : 0 ≤ Real.sqrt (1 + u * s) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := le_of_lt (s_pos s hs8)
  have hq0 : 0 ≤ 1 + u * (s - 1) :=
    le_trans (by norm_num) (q_lower u s hu0 hs8)
  have hA0 : 0 ≤ Real.sqrt (ratioA u b s) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt (ratioB u a s) := Real.sqrt_nonneg _
  have hx := sqrt_x_upper u s hu0 hu4 hs8 hs3
  have hq := q_upper u s hu0 hu4 hs3
  have hA := sqrt_ratioA_upper u b s hu0 hu4 hb0 hb2 hs8 hs3
  have hB := sqrt_ratioB_upper u a s hu0 hu4 ha0 ha2 hs8 hs3
  have h1 :
      2 * Real.sqrt (1 + u * s) ≤ 8 / 3 := by nlinarith
  have h2 :
      2 * Real.sqrt (1 + u * s) * s ≤ 8 := by
    exact mul_le_mul h1 hs3 hs0 (by positivity)
  have h3 :
      2 * Real.sqrt (1 + u * s) * s * (1 + u * (s - 1)) ≤ 12 := by
    exact mul_le_mul h2 hq hq0 (by positivity)
  have hsum :
      Real.sqrt (ratioA u b s) + Real.sqrt (ratioB u a s) ≤ 28 / 5 := by
    nlinarith
  have h4 :
      2 * Real.sqrt (1 + u * s) * s * (1 + u * (s - 1)) *
          (Real.sqrt (ratioA u b s) + Real.sqrt (ratioB u a s)) ≤
        12 * (28 / 5) := by
    exact mul_le_mul h3 hsum (add_nonneg hA0 hB0) (by positivity)
  unfold phaseDenominator
  nlinarith

end Box

end RiemannCvs.ProlateScaledDenominator
