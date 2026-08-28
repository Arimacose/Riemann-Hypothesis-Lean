import RiemannCvs.ParityOrderContinuation
import RiemannCvs.PrimeEventParityMonotonicity

/-!
# Piecewise continuation across a prime event

Between prime-power events, continuous parity eigenvalue branches preserve a
strict order whenever the Sylvester obstruction rules out equality.  At an
event, the singular rank-one perturbation lowers the even branch and leaves the
odd branch unchanged.  The theorems below glue these two mechanisms.

No concrete continuity theorem, eigenvalue-branch construction, Sylvester
identity, or CvS event formula is hidden here; each remains an explicit
hypothesis.
-/

namespace RiemannCvs.PiecewiseParityContinuation

open Set
open RiemannCvs.ParityOrderContinuation
open RiemannCvs.PrimeEventParityMonotonicity

/-- A strict parity order propagates through one continuous interval, one
order-preserving prime event, and a second continuous interval. -/
theorem orderAcrossOnePrimeEvent
    (evenLeft oddLeft evenRight oddRight : ℝ → ℝ)
    (a b c : ℝ)
    (hab : a ≤ b)
    (hbc : b ≤ c)
    (hEvenLeft : ContinuousOn evenLeft (Icc a b))
    (hOddLeft : ContinuousOn oddLeft (Icc a b))
    (hNoCrossLeft : ∀ x ∈ Icc a b, evenLeft x ≠ oddLeft x)
    (hStart : evenLeft a < oddLeft a)
    (hEventEven : evenRight b ≤ evenLeft b)
    (hEventOdd : oddRight b = oddLeft b)
    (hEvenRight : ContinuousOn evenRight (Icc b c))
    (hOddRight : ContinuousOn oddRight (Icc b c))
    (hNoCrossRight : ∀ x ∈ Icc b c, evenRight x ≠ oddRight x) :
    (∀ x ∈ Icc a b, evenLeft x < oddLeft x) ∧
      (∀ x ∈ Icc b c, evenRight x < oddRight x) := by
  have hLeft := strictOrderPersistsOnIcc
    evenLeft oddLeft a b hab hEvenLeft hOddLeft hStart hNoCrossLeft
  have hbLeft : evenLeft b < oddLeft b :=
    hLeft b ⟨hab, le_rfl⟩
  have hbRight : evenRight b < oddRight b :=
    strictParityOrderSurvivesEvent
      (evenLeft b) (evenRight b) (oddLeft b) (oddRight b)
      hbLeft hEventEven hEventOdd
  have hRight := strictOrderPersistsOnIcc
    evenRight oddRight b c hbc hEvenRight hOddRight
    hbRight hNoCrossRight
  exact ⟨hLeft, hRight⟩

/-- Direct specialization when the event is supplied by the negative rank-one
Hellmann--Feynman formula. -/
theorem orderAcrossRankOnePrimeEvent
    (evenLeft oddLeft evenRight oddRight : ℝ → ℝ)
    (a b c amplitude overlap : ℝ)
    (hab : a ≤ b)
    (hbc : b ≤ c)
    (hEvenLeft : ContinuousOn evenLeft (Icc a b))
    (hOddLeft : ContinuousOn oddLeft (Icc a b))
    (hNoCrossLeft : ∀ x ∈ Icc a b, evenLeft x ≠ oddLeft x)
    (hStart : evenLeft a < oddLeft a)
    (hAmplitude : 0 ≤ amplitude)
    (hEventFormula :
      evenRight b = evenLeft b - amplitude * overlap ^ 2)
    (hEventOdd : oddRight b = oddLeft b)
    (hEvenRight : ContinuousOn evenRight (Icc b c))
    (hOddRight : ContinuousOn oddRight (Icc b c))
    (hNoCrossRight : ∀ x ∈ Icc b c, evenRight x ≠ oddRight x) :
    (∀ x ∈ Icc a b, evenLeft x < oddLeft x) ∧
      (∀ x ∈ Icc b c, evenRight x < oddRight x) := by
  have hEventEven := rankOneEventLowersRayleigh
    (evenLeft b) (evenRight b) amplitude overlap
    hAmplitude hEventFormula
  exact orderAcrossOnePrimeEvent
    evenLeft oddLeft evenRight oddRight a b c
    hab hbc hEvenLeft hOddLeft hNoCrossLeft hStart
    hEventEven hEventOdd hEvenRight hOddRight hNoCrossRight

/-- A quantitative parity margin is nondecreasing at the event, so any lower
margin certified immediately before the event is inherited immediately after
it. -/
theorem marginAcrossPrimeEvent
    (evenLeft oddLeft evenRight oddRight margin : ℝ)
    (hMargin : margin ≤ oddLeft - evenLeft)
    (hEven : evenRight ≤ evenLeft)
    (hOdd : oddRight = oddLeft) :
    margin ≤ oddRight - evenRight := by
  exact hMargin.trans
    (parityGapNondecreasingAtEvent
      evenLeft evenRight oddLeft oddRight hEven hOdd)

end RiemannCvs.PiecewiseParityContinuation
