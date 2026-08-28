import Mathlib

/-!
# Compact scaled family for radial prolate dilation phases

This file records the division-free algebra behind the scaled phase derivative.
The analytic square roots are not differentiated here.
-/

namespace RiemannCvs.ProlateScaledStationaryFamily

def scaledSlopeNumerator (u a b s : ℝ) : ℝ :=
  s * (1 + u * (s - b)) -
    (1 - a + u * s) * (1 + u * (s - 1))

theorem scaledSlopeNumeratorExpanded
    (u a b s : ℝ) :
    scaledSlopeNumerator u a b s =
      a * s * u - a * u + a - b * s * u -
      s ^ 2 * u ^ 2 + s ^ 2 * u + s * u ^ 2 -
      2 * s * u + s + u - 1 := by
  unfold scaledSlopeNumerator
  ring

theorem limitingSlopeNumerator
    (a b s : ℝ) :
    scaledSlopeNumerator 0 a b s = s + a - 1 := by
  unfold scaledSlopeNumerator
  ring

/-- Relation between the compact parameter `u = 1/M` and the scaled
stationary polynomial. -/
theorem scaledSlopePolynomialRelation
    (M u a b s Q : ℝ)
    (hQ :
      Q =
        M ^ 2 * a + M ^ 2 * s - M ^ 2 +
        M * a * s - M * a - M * b * s +
        M * s ^ 2 - 2 * M * s + M - s ^ 2 + s) :
    M ^ 2 * scaledSlopeNumerator u a b s - Q =
      -(M * u - 1) *
        (-M * a * s + M * a + M * b * s +
          M * s ^ 2 * u - M * s ^ 2 - M * s * u +
          2 * M * s - M + s ^ 2 - s) := by
  rw [hQ]
  unfold scaledSlopeNumerator
  ring

theorem scaledSlopePolynomialAtReciprocal
    (M u a b s Q : ℝ)
    (hMu : M * u = 1)
    (hQ :
      Q =
        M ^ 2 * a + M ^ 2 * s - M ^ 2 +
        M * a * s - M * a - M * b * s +
        M * s ^ 2 - 2 * M * s + M - s ^ 2 + s) :
    M ^ 2 * scaledSlopeNumerator u a b s = Q := by
  have h := scaledSlopePolynomialRelation M u a b s Q hQ
  rw [hMu, sub_self, zero_mul, neg_zero] at h
  linarith

end RiemannCvs.ProlateScaledStationaryFamily
