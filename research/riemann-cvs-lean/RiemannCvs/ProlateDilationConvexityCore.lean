import Mathlib

/-!
# A global convexity core for radial prolate dilation phases

For `M = r² ≥ 4` and `t = x² ≥ 1`, the polynomial inequality below is
a parameter-free sufficient condition for strict convexity of every cross-mode
radial phase

`ξ_b(r x) - ξ_a(x)`

with `0 ≤ a,b ≤ 1/2`.

The square-root differentiation and the analytic implication for the PSWF phase
are documented in the accompanying research note.  This file formalizes the
exact polynomial positivity and the parameter-box comparison.
-/

namespace RiemannCvs.ProlateDilationConvexityCore

/-- The parameter-free polynomial inequality behind global phase convexity. -/
theorem uniformCorePositive
    (M t : ℝ)
    (hM : 4 ≤ M)
    (ht : 1 ≤ t) :
    4 * M ^ 3 * t * (t - 1) ^ 3 <
      (M * t - 1 / 2) * (M * t - 1) ^ 3 := by
  let h : ℝ := M - 4
  let u : ℝ := t - 1
  have hh : 0 ≤ h := by
    dsimp [h]
    linarith
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hidentity :
      (M * t - 1 / 2) * (M * t - 1) ^ 3 -
          4 * M ^ 3 * t * (t - 1) ^ 3 =
        h ^ 4 * (u + 1) ^ 4 +
        (h ^ 3 / 2) *
          (24 * u ^ 4 + 113 * u ^ 3 + 171 * u ^ 2 + 107 * u + 25) +
        (h ^ 2 / 2) *
          (96 * u ^ 4 + 588 * u ^ 3 + 909 * u ^ 2 + 534 * u + 117) +
        (h / 2) *
          (128 * u ^ 4 + 1328 * u ^ 3 + 2136 * u ^ 2 + 1179 * u + 243) +
        (1 / 2) * (1088 * u ^ 3 + 1872 * u ^ 2 + 972 * u + 189) := by
    dsimp [h, u]
    ring
  have hpos :
      0 <
        h ^ 4 * (u + 1) ^ 4 +
        (h ^ 3 / 2) *
          (24 * u ^ 4 + 113 * u ^ 3 + 171 * u ^ 2 + 107 * u + 25) +
        (h ^ 2 / 2) *
          (96 * u ^ 4 + 588 * u ^ 3 + 909 * u ^ 2 + 534 * u + 117) +
        (h / 2) *
          (128 * u ^ 4 + 1328 * u ^ 3 + 2136 * u ^ 2 + 1179 * u + 243) +
        (1 / 2) * (1088 * u ^ 3 + 1872 * u ^ 2 + 972 * u + 189) := by
    positivity
  rw [hidentity]
  exact hpos

/-- The actual parameter-dependent squared curvature comparison follows from
the universal core inequality. -/
theorem radialCurvatureSquareDominance
    (M a b t : ℝ)
    (hM : 4 ≤ M)
    (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2)
    (ht : 1 ≤ t) :
    M ^ 3 * (1 - b) ^ 2 * (t - a) * (t - 1) ^ 3 <
      (1 - a) ^ 2 * (M * t - b) * (M * t - 1) ^ 3 := by
  have hM0 : 0 ≤ M := by linarith
  have ht0 : 0 ≤ t := by linarith
  have htm1 : 0 ≤ t - 1 := by linarith
  have hMt : 0 ≤ M * t := mul_nonneg hM0 ht0
  have hMt1 : 0 ≤ M * t - 1 := by nlinarith
  have htail : 0 ≤ (t - 1) ^ 3 := positivity
  have hMtail : 0 ≤ M ^ 3 * (t - 1) ^ 3 := positivity
  have hMtTail : 0 ≤ (M * t - 1) ^ 3 := positivity
  have hba : 0 ≤ 1 - b := by linarith
  have hbaSq : (1 - b) ^ 2 ≤ 1 := by nlinarith
  have hta0 : 0 ≤ t - a := by linarith
  have hta : t - a ≤ t := by linarith
  have hsmallProduct : (1 - b) ^ 2 * (t - a) ≤ t := by
    have h :=
      mul_le_mul hbaSq hta hta0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hleft :
      M ^ 3 * (1 - b) ^ 2 * (t - a) * (t - 1) ^ 3 ≤
        M ^ 3 * t * (t - 1) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hsmallProduct hMtail
    nlinarith
  have haBase : (1 / 4 : ℝ) ≤ (1 - a) ^ 2 := by
    nlinarith [sq_nonneg (a - 1 / 2)]
  have hMb : M * t - 1 / 2 ≤ M * t - b := by linarith
  have hMb0 : 0 ≤ M * t - b := by nlinarith
  have hfirstProduct :
      (1 / 4 : ℝ) * (M * t - 1 / 2) ≤
        (1 - a) ^ 2 * (M * t - b) := by
    exact mul_le_mul haBase hMb (by nlinarith) (by positivity)
  have hright :
      (1 / 4 : ℝ) * (M * t - 1 / 2) * (M * t - 1) ^ 3 ≤
        (1 - a) ^ 2 * (M * t - b) * (M * t - 1) ^ 3 := by
    exact mul_le_mul_of_nonneg_right hfirstProduct hMtTail
  have hcore := uniformCorePositive M t hM ht
  have hcoreQuarter :
      M ^ 3 * t * (t - 1) ^ 3 <
        (1 / 4 : ℝ) * (M * t - 1 / 2) * (M * t - 1) ^ 3 := by
    nlinarith
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hcoreQuarter hright)

/-- A nonnegative square comparison can be converted to an unsquared strict
order without importing any analytic structure. -/
theorem nonnegativeLtOfSquareLt
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hsq : x ^ 2 < y ^ 2) :
    x < y := by
  nlinarith [sq_nonneg (x - y)]

end RiemannCvs.ProlateDilationConvexityCore
