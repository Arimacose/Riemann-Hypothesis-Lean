import Mathlib

/-!
# Eigenvalue velocities for a Lax flow with boundary dissipation

The desired smooth-cutoff identity has the schematic form

`Q' = [K,Q] - a * L^* L`,

where the commutator is an isospectral change of coordinates and the final
term is a negative boundary rank-one form.  On a normalized eigenvector of a
self-adjoint `Q`, the commutator expectation vanishes.  On `ker L`, the entire
boundary term vanishes.

This file formalizes the scalar consequences after the analytic/operator
identity has been supplied.  It does not assert that the concrete CvS cutoff
flow has this form.
-/

namespace RiemannCvs.LaxBoundaryFlow

/-- The expectation of a commutator vanishes on an eigenvector once the two
adjointness identities needed for the calculation are supplied. -/
theorem commutatorExpectationVanishes
    (qkx kqx xkx lambda : ℝ)
    (hKQ : kqx = lambda * xkx)
    (hQK : qkx = lambda * xkx) :
    kqx - qkx = 0 := by
  rw [hKQ, hQK]
  ring

/-- Hellmann--Feynman velocity for a Lax-plus-boundary flow. -/
theorem eigenvalueVelocity
    (velocity commutator a overlap : ℝ)
    (hcommutator : commutator = 0)
    (hvelocity : velocity = commutator - a * overlap ^ 2) :
    velocity = -(a * overlap ^ 2) := by
  rw [hvelocity, hcommutator]
  ring

/-- A positive boundary coefficient makes every eigenbranch nonincreasing. -/
theorem eigenvalueNonincreasing
    (velocity commutator a overlap : ℝ)
    (ha : 0 ≤ a)
    (hcommutator : commutator = 0)
    (hvelocity : velocity = commutator - a * overlap ^ 2) :
    velocity ≤ 0 := by
  rw [eigenvalueVelocity velocity commutator a overlap
    hcommutator hvelocity]
  have hsquare : 0 ≤ overlap ^ 2 := sq_nonneg _
  nlinarith

/-- A vector in the boundary kernel has zero instantaneous velocity under the
same flow. -/
theorem boundaryKernelVelocityZero
    (velocity commutator a overlap : ℝ)
    (hoverlap : overlap = 0)
    (hcommutator : commutator = 0)
    (hvelocity : velocity = commutator - a * overlap ^ 2) :
    velocity = 0 := by
  rw [hvelocity, hcommutator, hoverlap]
  ring

/-- If a constrained branch is stationary and the unconstrained branch is
nonincreasing, their difference is nondecreasing. -/
theorem gapVelocityNonnegative
    (lambdaVelocity constrainedVelocity gapVelocity : ℝ)
    (hlambda : lambdaVelocity ≤ 0)
    (hconstrained : constrainedVelocity = 0)
    (hgap : gapVelocity = constrainedVelocity - lambdaVelocity) :
    0 ≤ gapVelocity := by
  rw [hgap, hconstrained]
  linarith

/-- Strict boundary overlap gives a strictly increasing constraint gap. -/
theorem gapVelocityPositive
    (lambdaVelocity constrainedVelocity gapVelocity
      commutator a overlap : ℝ)
    (ha : 0 < a)
    (hoverlap : overlap ≠ 0)
    (hcommutator : commutator = 0)
    (hlambda :
      lambdaVelocity = commutator - a * overlap ^ 2)
    (hconstrained : constrainedVelocity = 0)
    (hgap : gapVelocity = constrainedVelocity - lambdaVelocity) :
    0 < gapVelocity := by
  have hsquare : 0 < overlap ^ 2 := sq_pos_of_ne_zero hoverlap
  have hlambdaNeg : lambdaVelocity < 0 := by
    rw [hlambda, hcommutator]
    nlinarith
  rw [hgap, hconstrained]
  linarith

/-- Approximate version: an error bounded by `epsilon * gap` leads to the
standard Gronwall-type differential inequality. -/
theorem approximateGapVelocity
    (lambdaVelocity constrainedVelocity gapVelocity
      boundaryGain error epsilon gap : ℝ)
    (hboundary : 0 ≤ boundaryGain)
    (herror : -epsilon * gap ≤ error)
    (hlambda : lambdaVelocity = -boundaryGain)
    (hconstrained : constrainedVelocity = error)
    (hgap : gapVelocity = constrainedVelocity - lambdaVelocity) :
    -epsilon * gap ≤ gapVelocity := by
  rw [hgap, hconstrained, hlambda]
  nlinarith

end RiemannCvs.LaxBoundaryFlow
