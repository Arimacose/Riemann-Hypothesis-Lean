import Mathlib

/-!
# Scalar transfer for a normalized exterior logarithmic moment

The analytic PSWF proof supplies an upper weighted-moment bound and a lower
mass bound in terms of one common radial normalization scale.
-/

namespace RiemannCvs.ExteriorLogMomentTransfer

theorem weightedMomentOfCommonScale
    (weighted mass scale upper lower : ℝ)
    (hupper : 0 ≤ upper)
    (hlower : 0 < lower)
    (hweighted : weighted ≤ upper * scale)
    (hmass : lower * scale ≤ mass) :
    lower * weighted ≤ upper * mass := by
  have hweightedScaled :=
    mul_le_mul_of_nonneg_left hweighted (le_of_lt hlower)
  have hmassScaled := mul_le_mul_of_nonneg_left hmass hupper
  nlinarith

theorem normalizedWeightedMomentBound
    (weighted mass scale upper lower : ℝ)
    (hmassPos : 0 < mass)
    (hupper : 0 ≤ upper)
    (hlower : 0 < lower)
    (hweighted : weighted ≤ upper * scale)
    (hmass : lower * scale ≤ mass) :
    weighted / mass ≤ upper / lower := by
  have hcross := weightedMomentOfCommonScale
    weighted mass scale upper lower hupper hlower hweighted hmass
  exact (div_le_div_iff₀ hmassPos hlower).2 <| by
    simpa [mul_comm] using hcross

theorem dilationLogMomentIdentity
    (logScale mass residual total : ℝ)
    (htotal : total = logScale * mass + residual) :
    total - logScale * mass = residual := by
  linarith

/-- If dilation separates the physical logarithmic moment into its support
floor and a nonnegative relative moment, an upper residual budget gives both
physical-moment bounds in conductor-ready form. -/
theorem dilationLogMomentBounds
    (physical residual mass logScale residualBound : ℝ)
    (hResidualNonneg : 0 ≤ residual)
    (hResidualUpper : residual ≤ residualBound * mass)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + residualBound) * mass := by
  constructor
  · rw [hIdentity]
    linarith
  · rw [hIdentity]
    calc
      logScale * mass + residual ≤
          logScale * mass + residualBound * mass :=
        add_le_add (le_refl _) hResidualUpper
      _ = (logScale + residualBound) * mass := by ring

/-- The analytic WKB input may use one unnormalized amplitude scale.  Dividing
its weighted upper bound by the corresponding mass lower bound and then
applying the exact dilation identity yields the physical logarithmic-moment
bounds needed by the prolate conductor estimate. -/
theorem dilationLogMomentBoundsOfCommonScale
    (physical residual mass scale logScale upper lower : ℝ)
    (hmassPos : 0 < mass)
    (hResidualNonneg : 0 ≤ residual)
    (hupper : 0 ≤ upper)
    (hlower : 0 < lower)
    (hResidual : residual ≤ upper * scale)
    (hMass : lower * scale ≤ mass)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + upper / lower) * mass := by
  have hNormalized : residual / mass ≤ upper / lower :=
    normalizedWeightedMomentBound residual mass scale upper lower
      hmassPos hupper hlower hResidual hMass
  have hResidualUpper : residual ≤ (upper / lower) * mass :=
    (div_le_iff₀ hmassPos).1 hNormalized
  exact dilationLogMomentBounds physical residual mass logScale
    (upper / lower) hResidualNonneg hResidualUpper hIdentity

end RiemannCvs.ExteriorLogMomentTransfer
