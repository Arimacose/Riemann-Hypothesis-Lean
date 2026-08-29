import Mathlib

/-!
# Weighted stationary-phase budgets for the prime block

The analytic PSWF input is a restricted dilation-overlap estimate of the form

`|overlap i| ≤ scale * decay i * normProduct`.

For the radial stationary-phase calculation one takes

`scale = c⁻¹ᐟ²`, `decay(q) = q⁻³ᐟ²`, and
`weight(q) = Λ(q) / √q`, so that `weight(q) * decay(q) = Λ(q) / q²`.

This file formalizes only the finite weighted-sum and perturbative bookkeeping.
The oscillatory-integral estimate and the von Mangoldt series evaluation remain
analytic inputs.
-/

namespace RiemannCvs.PrimeStationaryBudget

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A restricted stationary-phase estimate is stable under a finite
nonnegative weighted sum. -/
theorem weightedStationaryOverlapBound
    (weight decay overlap : ι → ℝ)
    (scale normProduct : ℝ)
    (hWeight : ∀ i, 0 ≤ weight i)
    (_hDecay : ∀ i, 0 ≤ decay i)
    (_hScale : 0 ≤ scale)
    (_hNorm : 0 ≤ normProduct)
    (hOverlap :
      ∀ i, |overlap i| ≤ scale * decay i * normProduct) :
    |∑ i, weight i * overlap i| ≤
      scale * (∑ i, weight i * decay i) * normProduct := by
  calc
    |∑ i, weight i * overlap i|
        ≤ ∑ i, |weight i * overlap i| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weight i * |overlap i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hWeight i)]
    _ ≤ ∑ i, weight i * (scale * decay i * normProduct) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hOverlap i) (hWeight i)
    _ = scale * (∑ i, weight i * decay i) * normProduct := by
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- If the weighted decay sum is bounded by a scalar series cap, then the
whole restricted prime block has the corresponding bound. -/
theorem weightedStationaryOverlapWithSeriesCap
    (weight decay overlap : ι → ℝ)
    (scale normProduct seriesCap : ℝ)
    (hWeight : ∀ i, 0 ≤ weight i)
    (hDecay : ∀ i, 0 ≤ decay i)
    (hScale : 0 ≤ scale)
    (hNorm : 0 ≤ normProduct)
    (hOverlap :
      ∀ i, |overlap i| ≤ scale * decay i * normProduct)
    (hSeries : ∑ i, weight i * decay i ≤ seriesCap) :
    |∑ i, weight i * overlap i| ≤
      scale * seriesCap * normProduct := by
  have hbase := weightedStationaryOverlapBound
    weight decay overlap scale normProduct
    hWeight hDecay hScale hNorm hOverlap
  have hsumNonneg :
      0 ≤ ∑ i, weight i * decay i := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hWeight i) (hDecay i)
  have hscaled := mul_le_mul_of_nonneg_left hSeries hScale
  have hscaledNorm := mul_le_mul_of_nonneg_right hscaled hNorm
  exact le_trans hbase (by simpa [mul_assoc] using hscaledNorm)

/-- Main stationary contribution and envelope remainder can be combined before
comparison with the logarithmic conductor scale. -/
theorem combineMainAndEnvelopeRemainder
    (main remainder total mainScale remainderScale normSq : ℝ)
    (hMain : |main| ≤ mainScale * normSq)
    (hRemainder : |remainder| ≤ remainderScale * normSq)
    (hTotal : total = main + remainder) :
    |total| ≤ (mainScale + remainderScale) * normSq := by
  rw [hTotal]
  calc
    |main + remainder| ≤ |main| + |remainder| := abs_add_le _ _
    _ ≤ mainScale * normSq + remainderScale * normSq :=
      add_le_add hMain hRemainder
    _ = (mainScale + remainderScale) * normSq := by ring

/-- A lower-order prime perturbation preserves a fixed fraction of a positive
conductor coefficient. -/
theorem conductorDominatesPrimePerturbation
    (conductor prime total logScale errorScale normSq eta : ℝ)
    (hNorm : 0 ≤ normSq)
    (hConductor : logScale * normSq ≤ conductor)
    (hPrime : |prime| ≤ errorScale * normSq)
    (hTotal : total = conductor + prime)
    (_hEta0 : 0 ≤ eta)
    (hMargin : errorScale ≤ eta * logScale) :
    (1 - eta) * logScale * normSq ≤ total := by
  have hPrimeLower : -(errorScale * normSq) ≤ prime := by
    exact (abs_le.mp hPrime).1
  have hError :
      errorScale * normSq ≤ eta * logScale * normSq := by
    exact mul_le_mul_of_nonneg_right hMargin hNorm
  rw [hTotal]
  nlinarith

end RiemannCvs.PrimeStationaryBudget
