import Mathlib

/-!
# Parity ordering across rank-one prime events

In the finite CvS path, the singular velocity change at a prime-power event is
an even rank-one negative perturbation.  The odd sector is unchanged at the
event, while every even Rayleigh value can only decrease.

This file records the scalar and variational consequences needed to glue
continuous no-crossing intervals across the discrete prime events.  It does not
assert the concrete CvS event formula; that analytic/algebraic identification
remains an external input.
-/

namespace RiemannCvs.PrimeEventParityMonotonicity

/-- Subtracting a nonnegative rank-one contribution lowers a Rayleigh value. -/
theorem rankOneEventLowersRayleigh
    (before after amplitude overlap : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hafter : after = before - amplitude * overlap ^ 2) :
    after ≤ before := by
  rw [hafter]
  have hsquare : 0 ≤ overlap ^ 2 := sq_nonneg overlap
  have hproduct : 0 ≤ amplitude * overlap ^ 2 :=
    mul_nonneg hamplitude hsquare
  linarith

/-- A strict even-below-odd ordering survives a negative rank-one event in the
even sector when the odd value is unchanged. -/
theorem strictParityOrderSurvivesEvent
    (evenBefore evenAfter oddBefore oddAfter : ℝ)
    (horder : evenBefore < oddBefore)
    (heven : evenAfter ≤ evenBefore)
    (hodd : oddAfter = oddBefore) :
    evenAfter < oddAfter := by
  rw [hodd]
  exact lt_of_le_of_lt heven horder

/-- Quantitative margin version.  The parity gap cannot decrease at such an
event. -/
theorem parityGapNondecreasingAtEvent
    (evenBefore evenAfter oddBefore oddAfter : ℝ)
    (heven : evenAfter ≤ evenBefore)
    (hodd : oddAfter = oddBefore) :
    oddBefore - evenBefore ≤ oddAfter - evenAfter := by
  rw [hodd]
  linarith

/-- Direct specialization to the Hellmann--Feynman rank-one event formula. -/
theorem strictParityOrderSurvivesRankOneFormula
    (evenBefore evenAfter oddBefore oddAfter amplitude overlap : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (horder : evenBefore < oddBefore)
    (hevent : evenAfter = evenBefore - amplitude * overlap ^ 2)
    (hodd : oddAfter = oddBefore) :
    evenAfter < oddAfter := by
  have heven := rankOneEventLowersRayleigh
    evenBefore evenAfter amplitude overlap hamplitude hevent
  exact strictParityOrderSurvivesEvent
    evenBefore evenAfter oddBefore oddAfter horder heven hodd

/-- A finite chain of order-preserving events can be collapsed to its endpoint.
The theorem is deliberately scalar; continuous intervals are handled by
`ParityOrderContinuation`. -/
theorem strictOrderAfterTwoEvents
    (e0 e1 e2 o0 o1 o2 : ℝ)
    (h0 : e0 < o0)
    (he01 : e1 ≤ e0)
    (he12 : e2 ≤ e1)
    (ho01 : o1 = o0)
    (ho12 : o2 = o1) :
    e2 < o2 := by
  have h1 := strictParityOrderSurvivesEvent e0 e1 o0 o1 h0 he01 ho01
  exact strictParityOrderSurvivesEvent e1 e2 o1 o2 h1 he12 ho12

end RiemannCvs.PrimeEventParityMonotonicity
