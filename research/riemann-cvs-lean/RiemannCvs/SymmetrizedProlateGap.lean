import Mathlib

/-!
# Coarse gap bounds after exact Fourier symmetrization

For a compressed Fourier singular value `sigma in [0,1]`, the usual squared
concentration defect is `D = 1 - sigma^2`, whereas the normalized defect of the
exact Fourier symmetrization is `e = (1 - sigma)/2`.

The elementary bounds `D/4 <= e <= D/2` show that a large fixed-index prolate
hierarchy survives exact parity symmetrization.  In particular, a high defect
at least four times a low defect leaves a symmetrized gap at least one eighth of
the high squared defect.
-/

namespace RiemannCvs.SymmetrizedProlateGap

/-- Two-sided comparison between the usual prolate defect and the normalized
exact-parity defect. -/
theorem normalizedDefectBounds
    (sigma : ℝ)
    (hNonneg : 0 ≤ sigma)
    (hLeOne : sigma ≤ 1) :
    (1 - sigma ^ 2) / 4 ≤ (1 - sigma) / 2 ∧
      (1 - sigma) / 2 ≤ (1 - sigma ^ 2) / 2 := by
  have hOneMinus : 0 ≤ 1 - sigma := sub_nonneg.mpr hLeOne
  have hOnePlus : 0 ≤ 1 + sigma := by nlinarith
  have hProduct :
      0 ≤ (1 - sigma) * (1 + sigma) :=
    mul_nonneg hOneMinus hOnePlus
  constructor <;> nlinarith

/-- A factor-four hierarchy of squared defects leaves a quantitative gap after
exact Fourier symmetrization. -/
theorem normalizedHighGap
    (sigmaLow sigmaHigh : ℝ)
    (hLowNonneg : 0 ≤ sigmaLow)
    (hLowLeOne : sigmaLow ≤ 1)
    (hHighNonneg : 0 ≤ sigmaHigh)
    (hHighLeOne : sigmaHigh ≤ 1)
    (hHierarchy :
      4 * (1 - sigmaLow ^ 2) ≤ 1 - sigmaHigh ^ 2) :
    (1 - sigmaHigh ^ 2) / 8 ≤
      (1 - sigmaHigh) / 2 - (1 - sigmaLow) / 2 := by
  obtain ⟨_, hLowUpper⟩ :=
    normalizedDefectBounds sigmaLow hLowNonneg hLowLeOne
  obtain ⟨hHighLower, _⟩ :=
    normalizedDefectBounds sigmaHigh hHighNonneg hHighLeOne
  nlinarith

/-- The residue multiplier introduced by exact symmetrization never increases a
nonnegative squared boundary residue. -/
theorem symmetrizedResidueLe
    (sigma r : ℝ)
    (_hSigmaNonneg : 0 ≤ sigma)
    (hSigmaLeOne : sigma ≤ 1)
    (hR : 0 ≤ r) :
    ((1 + sigma) / 2) * r ≤ r := by
  have hFactor : (1 + sigma) / 2 ≤ 1 := by
    nlinarith
  calc
    ((1 + sigma) / 2) * r ≤ 1 * r :=
      mul_le_mul_of_nonneg_right hFactor hR
    _ = r := one_mul r

/-- The same residue multiplier retains at least one half of a nonnegative
boundary residue. -/
theorem halfResidueLeSymmetrized
    (sigma r : ℝ)
    (hSigmaNonneg : 0 ≤ sigma)
    (hR : 0 ≤ r) :
    r / 2 ≤ ((1 + sigma) / 2) * r := by
  have hFactor : (1 / 2 : ℝ) ≤ (1 + sigma) / 2 := by
    nlinarith
  calc
    r / 2 = (1 / 2 : ℝ) * r := by ring
    _ ≤ ((1 + sigma) / 2) * r :=
      mul_le_mul_of_nonneg_right hFactor hR

end RiemannCvs.SymmetrizedProlateGap
