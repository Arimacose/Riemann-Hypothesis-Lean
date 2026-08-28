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

end RiemannCvs.ExteriorLogMomentTransfer
