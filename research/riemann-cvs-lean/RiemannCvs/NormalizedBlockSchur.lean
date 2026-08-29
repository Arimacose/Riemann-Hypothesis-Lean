import Mathlib
import RiemannCvs.SchurQuadraticForm

/-!
# Normalized two-block Schur lower bounds

A subtlety in passing from a low-block Schur estimate to a lower bound for the
whole normalized vector is that a vector may lie entirely in the high block.
Keeping half of the high coercivity term resolves this: completing the square
with the other half costs `2 * epsilon² / gap`, while the retained half supplies
`gap / 2` on the high component.

The scalar certificates are used by the finite Arb block experiment.  The final
theorem below also packages the same argument for an actual bilinear form on a
low/high vector decomposition.  The operator norm and complement-gap estimates
remain external inputs.
-/

namespace RiemannCvs.NormalizedBlockSchur

/-- General two-block lower certificate at arbitrary vector scale. -/
theorem blockLowerBound
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hTargetLow : target ≤ lowLevel - 2 * epsilon ^ 2 / gap)
    (hTargetHigh : target ≤ gap / 2)
    (hTotal : total = low + 2 * cross + high) :
    target * (s ^ 2 + t ^ 2) ≤ total := by
  have hHalfGap : 0 < gap / 2 := by linarith
  have hSquare :=
    RiemannCvs.SchurQuadraticForm.squareCompletion
      (gap / 2) epsilon s t hHalfGap
  have hDivision :
      epsilon ^ 2 / (gap / 2) = 2 * epsilon ^ 2 / gap := by
    field_simp [ne_of_gt hGap]
  rw [hDivision] at hSquare
  have hTargetLowScaled :=
    mul_le_mul_of_nonneg_right hTargetLow (sq_nonneg s)
  have hTargetHighScaled :=
    mul_le_mul_of_nonneg_right hTargetHigh (sq_nonneg t)
  rw [hTotal]
  nlinarith

/-- General normalized two-block lower certificate. -/
theorem normalizedBlockLowerBound
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hTargetLow : target ≤ lowLevel - 2 * epsilon ^ 2 / gap)
    (hTargetHigh : target ≤ gap / 2)
    (hTotal : total = low + 2 * cross + high) :
    target ≤ total := by
  have h := blockLowerBound
    target low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hTargetLow hTargetHigh hTotal
  rw [hNorm] at h
  simpa only [mul_one] using h

/-- The familiar explicit lower bound, provided it is no larger than the
retained high-block floor `gap / 2`. -/
theorem normalizedBlockSchurBound
    (low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hFloor : lowLevel - 2 * epsilon ^ 2 / gap ≤ gap / 2)
    (hTotal : total = low + 2 * cross + high) :
    lowLevel - 2 * epsilon ^ 2 / gap ≤ total := by
  exact normalizedBlockLowerBound
    (lowLevel - 2 * epsilon ^ 2 / gap)
    low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hNorm le_rfl hFloor hTotal

/-- Division-free sufficient condition for a target lower bound at arbitrary
vector scale. -/
theorem blockTargetOfProductBudgets
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hLowBudget : gap * (lowLevel - target) ≥ 2 * epsilon ^ 2)
    (hHighBudget : 2 * target ≤ gap)
    (hTotal : total = low + 2 * cross + high) :
    target * (s ^ 2 + t ^ 2) ≤ total := by
  have hTargetLow : target ≤ lowLevel - 2 * epsilon ^ 2 / gap := by
    have hDiv : 2 * epsilon ^ 2 / gap ≤ lowLevel - target := by
      exact (div_le_iff₀ hGap).2 (by nlinarith [hLowBudget])
    nlinarith
  have hTargetHigh : target ≤ gap / 2 := by nlinarith
  exact blockLowerBound
    target low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hTargetLow hTargetHigh hTotal

/-- Division-free sufficient condition for a normalized target lower bound. -/
theorem normalizedBlockTargetOfProductBudgets
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hLowBudget : gap * (lowLevel - target) ≥ 2 * epsilon ^ 2)
    (hHighBudget : 2 * target ≤ gap)
    (hTotal : total = low + 2 * cross + high) :
    target ≤ total := by
  have h := blockTargetOfProductBudgets
    target low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hLowBudget hHighBudget hTotal
  rw [hNorm] at h
  simpa only [mul_one] using h

section BilinearForm

variable {V : Type*}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Direct low/high Schur certificate for a bilinear quadratic form.

The hypotheses expose exactly the analytic inputs needed on the actual
decomposition: a low-block floor, a coercive high complement, a low/high
coupling estimate, symmetry of the cross term, and Pythagorean norm splitting.
The conclusion is homogeneous and therefore applies to every (not necessarily
normalized) vector `u + v`. -/
theorem bilinearBlockTargetOfProductBudgets
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u v : V)
    (target lowLevel gap epsilon : ℝ)
    (hGap : 0 < gap)
    (hSymm : B v u = B u v)
    (hNormAdd : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2)
    (hLow : lowLevel * ‖u‖ ^ 2 ≤ B u u)
    (hHigh : gap * ‖v‖ ^ 2 ≤ B v v)
    (hCross : -epsilon * ‖u‖ * ‖v‖ ≤ B u v)
    (hLowBudget : gap * (lowLevel - target) ≥ 2 * epsilon ^ 2)
    (hHighBudget : 2 * target ≤ gap) :
    target * ‖u + v‖ ^ 2 ≤ B (u + v) (u + v) := by
  have hTotal :
      B (u + v) (u + v) = B u u + 2 * B u v + B v v := by
    simp only [map_add, LinearMap.add_apply]
    rw [hSymm]
    ring
  have h := blockTargetOfProductBudgets
    target (B u u) (B v v) (B u v)
      lowLevel gap epsilon ‖u‖ ‖v‖ (B (u + v) (u + v))
    hGap hLow hHigh hCross hLowBudget hHighBudget hTotal
  rw [← hNormAdd] at h
  exact h

end BilinearForm

section OrthogonalBilinearForm

open scoped InnerProductSpace

variable {V : Type*}
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Orthogonal low/high specialization.  An orthogonal projection supplies
`hOrth`; no separate scalar normalization identity is needed. -/
theorem bilinearBlockTargetOfOrthogonalBudgets
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u v : V)
    (target lowLevel gap epsilon : ℝ)
    (hGap : 0 < gap)
    (hSymm : B v u = B u v)
    (hOrth : ⟪u, v⟫_ℝ = 0)
    (hLow : lowLevel * ‖u‖ ^ 2 ≤ B u u)
    (hHigh : gap * ‖v‖ ^ 2 ≤ B v v)
    (hCross : -epsilon * ‖u‖ * ‖v‖ ≤ B u v)
    (hLowBudget : gap * (lowLevel - target) ≥ 2 * epsilon ^ 2)
    (hHighBudget : 2 * target ≤ gap) :
    target * ‖u + v‖ ^ 2 ≤ B (u + v) (u + v) := by
  have hNormAdd : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := norm_add_sq_real u v
    rw [hOrth] at h
    norm_num at h
    exact h
  exact bilinearBlockTargetOfProductBudgets
    B u v target lowLevel gap epsilon
    hGap hSymm hNormAdd hLow hHigh hCross hLowBudget hHighBudget

end OrthogonalBilinearForm

end RiemannCvs.NormalizedBlockSchur
