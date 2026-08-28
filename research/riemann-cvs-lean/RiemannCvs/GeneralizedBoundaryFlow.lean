import Mathlib

/-!
# Generalized eigenvalue velocities under a congruence-plus-boundary flow

For an operator on a moving interval, transporting to fixed coordinates changes
both the quadratic-form matrix `A` and the mass/Gram matrix `G`.  The natural
shape derivative is a congruence flow

`A' = K^* A + A K - boundary`,
`G' = K^* G + G K`,

rather than a bare commutator for `A` alone.  On a generalized eigenvector
`A x = lambda G x`, all congruence terms cancel in
`<x,(A' - lambda G')x>`, leaving only the boundary form.

This file formalizes that cancellation at the scalar bilinear level.  It does
not assert the concrete CvS shape-derivative identity.
-/

namespace RiemannCvs.GeneralizedBoundaryFlow

/-- Cancellation of the two congruence terms against the derivative of the
mass form. -/
theorem congruenceCancellation
    (aKxX aXKx gKxX gXKx lambda : ℝ)
    (hleft : aKxX = lambda * gKxX)
    (hright : aXKx = lambda * gXKx) :
    (aKxX + aXKx) - lambda * (gKxX + gXKx) = 0 := by
  rw [hleft, hright]
  ring

/-- Hellmann--Feynman numerator for one negative boundary square. -/
theorem generalizedVelocityNumerator
    (aPrime gPrime congruenceA congruenceG
      boundaryCoeff overlap lambda numerator : ℝ)
    (hCongruence : congruenceA - lambda * congruenceG = 0)
    (hAPrime : aPrime = congruenceA - boundaryCoeff * overlap ^ 2)
    (hGPrime : gPrime = congruenceG)
    (hNumerator : numerator = aPrime - lambda * gPrime) :
    numerator = -(boundaryCoeff * overlap ^ 2) := by
  rw [hNumerator, hAPrime, hGPrime]
  nlinarith

/-- Several boundary traces lead to the sum of their signed squares. -/
theorem generalizedFiniteRankVelocity
    (aPrime gPrime congruenceA congruenceG lambda numerator
      b0 b1 b2 : ℝ)
    (hCongruence : congruenceA - lambda * congruenceG = 0)
    (hAPrime : aPrime = congruenceA - b0 - b1 - b2)
    (hGPrime : gPrime = congruenceG)
    (hNumerator : numerator = aPrime - lambda * gPrime) :
    numerator = -(b0 + b1 + b2) := by
  rw [hNumerator, hAPrime, hGPrime]
  nlinarith

/-- Division by a positive generalized norm gives the eigenvalue velocity. -/
theorem generalizedEigenvalueVelocity
    (velocity numerator mass boundaryCoeff overlap : ℝ)
    (hmass : 0 < mass)
    (hNumerator : numerator = -(boundaryCoeff * overlap ^ 2))
    (hVelocity : velocity * mass = numerator) :
    velocity * mass = -(boundaryCoeff * overlap ^ 2) := by
  rw [hVelocity, hNumerator]

/-- A nonnegative boundary coefficient makes the generalized eigenvalue
nonincreasing. -/
theorem generalizedEigenvalueNonincreasing
    (velocity mass boundaryCoeff overlap : ℝ)
    (hmass : 0 < mass)
    (hboundary : 0 ≤ boundaryCoeff)
    (hVelocity : velocity * mass = -(boundaryCoeff * overlap ^ 2)) :
    velocity ≤ 0 := by
  have hsquare : 0 ≤ overlap ^ 2 := sq_nonneg _
  have hrhs : -(boundaryCoeff * overlap ^ 2) ≤ 0 := by
    nlinarith [mul_nonneg hboundary hsquare]
  have hscaled : velocity * mass ≤ 0 := by
    rw [hVelocity]
    exact hrhs
  exact (mul_nonpos_iff_of_pos_right hmass).mp hscaled

/-- On the boundary kernel the shape derivative is purely congruential, hence
the generalized eigenvalue velocity is zero. -/
theorem boundaryKernelStationary
    (velocity mass boundaryCoeff overlap : ℝ)
    (hmass : 0 < mass)
    (hoverlap : overlap = 0)
    (hVelocity : velocity * mass = -(boundaryCoeff * overlap ^ 2)) :
    velocity = 0 := by
  rw [hoverlap, sq_zero, mul_zero, neg_zero] at hVelocity
  exact (mul_eq_zero.mp hVelocity).resolve_right (ne_of_gt hmass)

/-- If the constrained generalized eigenbranch is stationary while the
unconstrained branch is nonincreasing, their gap is nondecreasing. -/
theorem generalizedGapNondecreasing
    (groundVelocity constrainedVelocity gapVelocity : ℝ)
    (hground : groundVelocity ≤ 0)
    (hconstrained : constrainedVelocity = 0)
    (hgap : gapVelocity = constrainedVelocity - groundVelocity) :
    0 ≤ gapVelocity := by
  rw [hgap, hconstrained]
  linarith

/-- Approximate congruence identity: an error controlled relative to the gap
still yields the scalar differential inequality needed for Gronwall. -/
theorem approximateGeneralizedGap
    (groundVelocity constrainedVelocity gapVelocity
      boundaryGain constrainedError groundError epsilon gap : ℝ)
    (hboundary : 0 ≤ boundaryGain)
    (hconstrainedError : -epsilon * gap / 2 ≤ constrainedError)
    (hgroundError : groundError ≤ epsilon * gap / 2)
    (hground : groundVelocity = -boundaryGain + groundError)
    (hconstrained : constrainedVelocity = constrainedError)
    (hgap : gapVelocity = constrainedVelocity - groundVelocity) :
    -epsilon * gap ≤ gapVelocity := by
  rw [hgap, hground, hconstrained]
  nlinarith

end RiemannCvs.GeneralizedBoundaryFlow
