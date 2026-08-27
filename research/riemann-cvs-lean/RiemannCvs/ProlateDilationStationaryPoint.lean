import Mathlib

/-!
# Stationary geometry of prolate dilation phases

For the radial prolate phase

`ξ'(x)^2 = (x² - a) / (x² - 1)`,  with `0 ≤ a < 1`,

the same-carrier dilation phase is `ξ(m x) - ξ(x)`.  Contrary to the
linear-phase model, its derivative has one stationary point on `(1,∞)`.

This file formalizes the polynomial algebra governing that stationary point.
It does not formalize the square-root differentiation, the radial PSWF
asymptotic, or a stationary-phase integral estimate.  Those analytic inputs
remain explicit research obligations.
-/

namespace RiemannCvs.ProlateDilationStationaryPoint

/-- Dunster's separation parameter `lambda` and the concentration-operator
parameter `chi` are related by `chi = lambda + gamma²`. -/
theorem pswfCoefficientShift
    (lambda gamma chi x : ℝ)
    (hchi : chi = lambda + gamma ^ 2) :
    lambda + gamma ^ 2 * (1 - x ^ 2) = chi - gamma ^ 2 * x ^ 2 := by
  rw [hchi]
  ring

/-- Polynomial obtained after squaring the stationary equation and clearing
positive denominators.  Here `M = m²`, `a = sigma²`, and `t = x²`. -/
def stationaryPoly (M a t : ℝ) : ℝ :=
  M * t ^ 2 - (M + 1) * t + a

/-- Exact factorization of the cleared squared-slope equation. -/
theorem squaredSlopeCrossFactor
    (M a t : ℝ) :
    M * (M * t - a) * (t - 1) -
        (t - a) * (M * t - 1) =
      (M - 1) * stationaryPoly M a t := by
  unfold stationaryPoly
  ring

/-- If the dilation is nontrivial, the cleared stationary equation is
 equivalent to vanishing of `stationaryPoly`. -/
theorem squaredSlopeCross_iff
    (M a t : ℝ)
    (hM : M ≠ 1) :
    M * (M * t - a) * (t - 1) =
        (t - a) * (M * t - 1) ↔
      stationaryPoly M a t = 0 := by
  constructor
  · intro hcross
    have hfactor := squaredSlopeCrossFactor M a t
    have hzero : (M - 1) * stationaryPoly M a t = 0 := by
      linarith
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hM)
  · intro hroot
    have hfactor := squaredSlopeCrossFactor M a t
    rw [hroot, mul_zero] at hfactor
    linarith

/-- Completing the square gives the explicit quadratic-root discriminant. -/
theorem completedSquareIdentity
    (M a t : ℝ) :
    (2 * M * t - (M + 1)) ^ 2 -
        ((M + 1) ^ 2 - 4 * M * a) =
      4 * M * stationaryPoly M a t := by
  unfold stationaryPoly
  ring

/-- At a stationary root, the quadratic equation can be rewritten in the
particularly useful form `M t (t - 1) = t - a`. -/
theorem rootBalance
    (M a t : ℝ)
    (hroot : stationaryPoly M a t = 0) :
    M * t * (t - 1) = t - a := by
  unfold stationaryPoly at hroot
  nlinarith

/-- The exterior stationary root is strictly above the singular endpoint. -/
theorem rootStrictlyAboveOne
    (M a t : ℝ)
    (ha : a < 1)
    (ht : 1 ≤ t)
    (hroot : stationaryPoly M a t = 0) :
    1 < t := by
  have hne : t ≠ 1 := by
    intro htone
    subst t
    unfold stationaryPoly at hroot
    nlinarith
  exact lt_of_le_of_ne ht (Ne.symm hne)

/-- The exterior root lies in a width-`1/M` layer in the squared coordinate.
This multiplication-only form avoids division and is interval-friendly. -/
theorem rootWidthBudget
    (M a t : ℝ)
    (hM : 0 < M)
    (ha : 0 ≤ a)
    (ht : 1 ≤ t)
    (hroot : stationaryPoly M a t = 0) :
    M * (t - 1) ≤ 1 := by
  have hbalance := rootBalance M a t hroot
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have henergy : M * t * (t - 1) ≤ t := by
    rw [hbalance]
    linarith
  by_contra hnot
  have hgt : 1 < M * (t - 1) := lt_of_not_ge hnot
  have hscaled := mul_lt_mul_of_pos_left hgt htpos
  nlinarith

/-- The quadratic has at most one root in `[1,∞)` when `M > 1`. -/
theorem uniqueRootAboveOne
    (M a t₁ t₂ : ℝ)
    (hM : 1 < M)
    (ht₁ : 1 ≤ t₁)
    (ht₂ : 1 ≤ t₂)
    (hroot₁ : stationaryPoly M a t₁ = 0)
    (hroot₂ : stationaryPoly M a t₂ = 0) :
    t₁ = t₂ := by
  have hproduct :
      (t₁ - t₂) * (M * (t₁ + t₂) - (M + 1)) = 0 := by
    unfold stationaryPoly at hroot₁ hroot₂
    nlinarith
  have hfactorPos : 0 < M * (t₁ + t₂) - (M + 1) := by
    nlinarith
  have hdiff : t₁ - t₂ = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hfactorPos)
  linarith

/-- Algebraic numerator controlling the curvature at the stationary root. -/
theorem curvatureDifferenceFactor
    (M t : ℝ) :
    (M * t - 1) ^ 2 - M ^ 2 * (t - 1) ^ 2 =
      (M - 1) * (2 * M * t - M - 1) := by
  ring

/-- The curvature numerator is strictly positive on the exterior branch. -/
theorem curvatureDifferencePositive
    (M t : ℝ)
    (hM : 1 < M)
    (ht : 1 ≤ t) :
    0 < (M * t - 1) ^ 2 - M ^ 2 * (t - 1) ^ 2 := by
  rw [curvatureDifferenceFactor]
  have hleft : 0 < M - 1 := by linarith
  have hright : 0 < 2 * M * t - M - 1 := by nlinarith
  exact mul_pos hleft hright

end RiemannCvs.ProlateDilationStationaryPoint
