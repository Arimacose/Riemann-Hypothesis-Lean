import Mathlib

/-!
# Normalizing the exact-parity prolate conductor estimate

The exact Fourier symmetrization has squared norm `N = 2 + 2 sigma`.  Both its
exterior mass and every quadratic-form value on the exterior tail are divided
by the same positive number `N`.  Thus a conductor estimate in units of the
unnormalized prolate defect passes to the normalized exact-parity vector with
no distortion.
-/

namespace RiemannCvs.NormalizedSymmetrizedConductor

/-- Two-sided form comparability is unchanged by a common positive
normalization. -/
theorem normalizeTwoSidedFormBound
    (energy defect normSq lower upper : ℝ)
    (hNorm : 0 < normSq)
    (hLower : lower * defect ≤ energy)
    (hUpper : energy ≤ upper * defect) :
    lower * (defect / normSq) ≤ energy / normSq ∧
      energy / normSq ≤ upper * (defect / normSq) := by
  constructor
  · exact (div_le_div_iff_of_pos_right hNorm).2 (by
      simpa [mul_div_assoc] using hLower)
  · exact (div_le_div_iff_of_pos_right hNorm).2 (by
      simpa [mul_div_assoc] using hUpper)

/-- Specialization to the exact Fourier-symmetrization norm
`2 + 2 sigma`. -/
theorem normalizeSymmetrizedTailBound
    (energy defect sigma lower upper : ℝ)
    (hSigma : -1 < sigma)
    (hLower : lower * defect ≤ energy)
    (hUpper : energy ≤ upper * defect) :
    lower * (defect / (2 + 2 * sigma)) ≤
        energy / (2 + 2 * sigma) ∧
      energy / (2 + 2 * sigma) ≤
        upper * (defect / (2 + 2 * sigma)) := by
  have hNorm : 0 < 2 + 2 * sigma := by nlinarith
  exact normalizeTwoSidedFormBound
    energy defect (2 + 2 * sigma) lower upper
    hNorm hLower hUpper

/-- If the normalized exact-parity defect is named `exactDefect`, the same
bounds can be rewritten directly in that scale. -/
theorem normalizedExactParityConductorBound
    (energy defect exactDefect sigma lower upper : ℝ)
    (hSigma : -1 < sigma)
    (hExactDefect : exactDefect = defect / (2 + 2 * sigma))
    (hLower : lower * defect ≤ energy)
    (hUpper : energy ≤ upper * defect) :
    lower * exactDefect ≤ energy / (2 + 2 * sigma) ∧
      energy / (2 + 2 * sigma) ≤ upper * exactDefect := by
  rw [hExactDefect]
  exact normalizeSymmetrizedTailBound
    energy defect sigma lower upper hSigma hLower hUpper

/-- The common normalization also preserves a quartic parity comparison. -/
theorem normalizedQuarticRatio
    (dPlus dMinus nPlus nMinus ePlus eMinus C lambda : ℝ)
    (hnPlus : 0 < nPlus)
    (hnMinus : 0 < nMinus)
    (hePlus : ePlus = dPlus / nPlus)
    (heMinus : eMinus = dMinus / nMinus)
    (hRatio : lambda ^ 4 * dPlus * nMinus ≤ C * dMinus * nPlus) :
    lambda ^ 4 * ePlus ≤ C * eMinus := by
  rw [hePlus, heMinus]
  apply (div_le_div_iff₀ hnPlus hnMinus).2
  nlinarith

end RiemannCvs.NormalizedSymmetrizedConductor
