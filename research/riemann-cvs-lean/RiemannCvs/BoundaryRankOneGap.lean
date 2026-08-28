import Mathlib

/-!
# Boundary-constrained gaps under a negative rank-one update

A prime-power event in the finite CvS cutoff path has the form

`Q_new = Q_old - a * L^* L`,  with `a ≥ 0`,

where `L` is the boundary functional represented by the event vector.  The
update vanishes identically on `ker L`; it can only lower the unconstrained
minimum.  Consequently it can only enlarge the gap between the boundary-
constrained minimum and the true minimum.

This file formalizes the scalar and pointwise consequences.  It does not assert
that every smooth part of the CvS path is rank one, nor does it prove a global
no-crossing result.
-/

namespace RiemannCvs.BoundaryRankOneGap

/-- The rank-one update is invisible on the boundary kernel. -/
theorem updateVanishesOnBoundaryKernel
    (qOld qNew boundary : α → ℝ)
    (a : ℝ) (x : α)
    (hUpdate : qNew x = qOld x - a * (boundary x) ^ 2)
    (hBoundary : boundary x = 0) :
    qNew x = qOld x := by
  rw [hUpdate, hBoundary]
  ring

/-- A negative rank-one update lowers every pointwise quadratic value. -/
theorem negativeRankOneLowersValue
    (qOld qNew boundary : α → ℝ)
    (a : ℝ) (x : α)
    (ha : 0 ≤ a)
    (hUpdate : qNew x = qOld x - a * (boundary x) ^ 2) :
    qNew x ≤ qOld x := by
  rw [hUpdate]
  have hsquare : 0 ≤ (boundary x) ^ 2 := sq_nonneg _
  nlinarith

/-- Scalar min--max consequence: if the constrained value is unchanged while
the unconstrained minimum decreases, the boundary gap cannot shrink. -/
theorem constrainedGapMonotone
    (lambdaOld lambdaNew nuOld nuNew : ℝ)
    (hGround : lambdaNew ≤ lambdaOld)
    (hConstrained : nuNew = nuOld) :
    nuOld - lambdaOld ≤ nuNew - lambdaNew := by
  rw [hConstrained]
  linarith

/-- Strict positivity of a pre-event boundary gap persists through the event. -/
theorem positiveGapPersists
    (lambdaOld lambdaNew nu : ℝ)
    (hGround : lambdaNew ≤ lambdaOld)
    (hGap : lambdaOld < nu) :
    lambdaNew < nu := by
  exact lt_of_le_of_lt hGround hGap

/-- If the update actually lowers the ground value, then the constrained gap
strictly increases. -/
theorem constrainedGapStrictlyIncreases
    (lambdaOld lambdaNew nuOld nuNew : ℝ)
    (hGround : lambdaNew < lambdaOld)
    (hConstrained : nuNew = nuOld) :
    nuOld - lambdaOld < nuNew - lambdaNew := by
  rw [hConstrained]
  linarith

/-- Hellmann--Feynman event velocity in scalar form.  A nonzero boundary
overlap makes the event strictly downward. -/
theorem strictDecreaseFromBoundaryOverlap
    (velocity a overlap : ℝ)
    (ha : 0 < a)
    (hoverlap : overlap ≠ 0)
    (hVelocity : velocity = -(a * overlap ^ 2)) :
    velocity < 0 := by
  have hsquare : 0 < overlap ^ 2 := sq_pos_of_ne_zero hoverlap
  rw [hVelocity]
  nlinarith

/-- Odd-parity vectors are unaffected when the prime-event vector is even and
their boundary overlap therefore vanishes. -/
theorem parityOrthogonalEventIsInvisible
    (qOld qNew : α → ℝ)
    (a overlap : ℝ) (x : α)
    (hUpdate : qNew x = qOld x - a * overlap ^ 2)
    (hOrthogonal : overlap = 0) :
    qNew x = qOld x := by
  rw [hUpdate, hOrthogonal]
  ring

end RiemannCvs.BoundaryRankOneGap
