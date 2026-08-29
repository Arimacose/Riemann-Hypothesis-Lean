import Mathlib

/-!
# Uniform outer-region slope bounds for radial prolate dilation phases

Write the radial phase slopes in the endpoint-scaled variable

`x² = 1 + s / r²`.

Then

`xi_a'(x)² = 1 + (1-a) r² / s`,

and

`xi_b'(r x)² = 1 + (1-b) / (r²+s-1)`.

For `r ≥ 2` and `0 ≤ a,b ≤ 1/2`, the dilation-phase derivative

`r xi_b'(r x) - xi_a'(x)`

is uniformly negative on `0 < s ≤ 1/8` and uniformly positive on `s ≥ 3`.
Thus all stationary behavior is confined to the compact middle box used by
`ProlateScaledPhaseDerivative`.
-/

namespace RiemannCvs.ProlateDilationOuterPhase

noncomputable def innerSlope (r a s : ℝ) : ℝ :=
  Real.sqrt (1 + (1 - a) * r ^ 2 / s)

noncomputable def dilatedSlope (r b s : ℝ) : ℝ :=
  Real.sqrt (1 + (1 - b) / (r ^ 2 + s - 1))

noncomputable def dilationPhaseSlope (r a b s : ℝ) : ℝ :=
  r * dilatedSlope r b s - innerSlope r a s

/-- On the endpoint region the inner radial slope is at least `2r`. -/
theorem two_mul_r_le_innerSlope
    (r a s : ℝ)
    (hr : 2 ≤ r)
    (ha : a ≤ 1 / 2)
    (hs0 : 0 < s)
    (hs8 : s ≤ 1 / 8) :
    2 * r ≤ innerSlope r a s := by
  have hr0 : 0 ≤ r := by linarith
  have hs0' : 0 ≤ s := le_of_lt hs0
  have hOneMinus : 1 / 2 ≤ 1 - a := by linarith
  have hratio : 4 * r ^ 2 ≤ (1 - a) * r ^ 2 / s := by
    apply (le_div_iff₀ hs0).2
    have hsScaled : 4 * r ^ 2 * s ≤ (1 / 2) * r ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hs8
        (show 0 ≤ (4 : ℝ) * r ^ 2 by positivity)
      nlinarith
    have hcoef := mul_le_mul_of_nonneg_right hOneMinus (sq_nonneg r)
    nlinarith
  have hrad : 0 ≤ 1 + (1 - a) * r ^ 2 / s := by
    nlinarith [sq_nonneg r]
  have hsq := Real.sq_sqrt hrad
  have hsqrt0 := Real.sqrt_nonneg (1 + (1 - a) * r ^ 2 / s)
  unfold innerSlope
  nlinarith

/-- On the endpoint region the dilated radial slope is at most `3/2`. -/
theorem dilatedSlope_le_threeHalves
    (r b s : ℝ)
    (hr : 2 ≤ r)
    (hb0 : 0 ≤ b)
    (hs0 : 0 ≤ s) :
    dilatedSlope r b s ≤ 3 / 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hden : 0 < r ^ 2 + s - 1 := by
    nlinarith [sq_nonneg (r - 2)]
  have hnum : 1 - b ≤ 1 := by linarith
  have hden3 : 3 ≤ r ^ 2 + s - 1 := by
    nlinarith [sq_nonneg (r - 2)]
  have hratio : (1 - b) / (r ^ 2 + s - 1) ≤ 1 / 3 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold dilatedSlope
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith

/-- The dilation phase is strictly decreasing before the compact stationary
box. -/
theorem endpointSlopeUpper
    (r a b s : ℝ)
    (hr : 2 ≤ r)
    (ha : a ≤ 1 / 2)
    (hb0 : 0 ≤ b)
    (hs0 : 0 < s)
    (hs8 : s ≤ 1 / 8) :
    dilationPhaseSlope r a b s ≤ -(r / 2) := by
  have hinner := two_mul_r_le_innerSlope r a s hr ha hs0 hs8
  have hdilated := dilatedSlope_le_threeHalves r b s hr hb0 (le_of_lt hs0)
  have hr0 : 0 ≤ r := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hdilated hr0
  unfold dilationPhaseSlope
  nlinarith

/-- On the far exterior region the inner radial slope is at most `4r/5`. -/
theorem innerSlope_le_fourFifths
    (r a s : ℝ)
    (hr : 2 ≤ r)
    (ha0 : 0 ≤ a)
    (hs3 : 3 ≤ s) :
    innerSlope r a s ≤ (4 / 5) * r := by
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs3
  have hOneMinus : 1 - a ≤ 1 := by linarith
  have hratio : (1 - a) * r ^ 2 / s ≤ r ^ 2 / 3 := by
    apply (div_le_iff₀ hs0).2
    have hsNonneg : 0 ≤ s := le_of_lt hs0
    have hcoef := mul_le_mul_of_nonneg_right hOneMinus (sq_nonneg r)
    have hthree := mul_le_mul_of_nonneg_left hs3 (sq_nonneg r)
    nlinarith
  have htarget : 1 + r ^ 2 / 3 ≤ (16 / 25) * r ^ 2 := by
    nlinarith [sq_nonneg (r - 2)]
  unfold innerSlope
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith

/-- The dilated radial slope is always at least one on the relevant parameter
range. -/
theorem one_le_dilatedSlope
    (r b s : ℝ)
    (hr : 2 ≤ r)
    (hb : b ≤ 1)
    (hs0 : 0 ≤ s) :
    1 ≤ dilatedSlope r b s := by
  have hden : 0 < r ^ 2 + s - 1 := by
    nlinarith [sq_nonneg (r - 2)]
  have hnum : 0 ≤ 1 - b := by linarith
  have hratio : 0 ≤ (1 - b) / (r ^ 2 + s - 1) :=
    div_nonneg hnum (le_of_lt hden)
  have hrad : 0 ≤ 1 + (1 - b) / (r ^ 2 + s - 1) := by linarith
  have hsq := Real.sq_sqrt hrad
  have hsqrt0 := Real.sqrt_nonneg (1 + (1 - b) / (r ^ 2 + s - 1))
  unfold dilatedSlope
  nlinarith

/-- The dilation phase is uniformly increasing after the compact stationary
box. -/
theorem farSlopeLower
    (r a b s : ℝ)
    (hr : 2 ≤ r)
    (ha0 : 0 ≤ a)
    (hb : b ≤ 1)
    (hs3 : 3 ≤ s) :
    r / 5 ≤ dilationPhaseSlope r a b s := by
  have hinner := innerSlope_le_fourFifths r a s hr ha0 hs3
  have hdilated := one_le_dilatedSlope r b s hr hb (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hdilated hr0
  unfold dilationPhaseSlope
  nlinarith

end RiemannCvs.ProlateDilationOuterPhase
