import Mathlib

/-!
# Exact conductor identities for a prolate leakage tail

Let `p` be a retained unit vector and suppose its full Fourier transform has
compressed-eigenvector decomposition

`Fourier p = (epsilon * sigma) p + t`,

where `t` is the exterior leakage, `epsilon^2 = 1`, and Fourier squares to the
identity on `p`.  Then

`Fourier t = (1 - sigma^2) p - (epsilon * sigma) t`.

For a multiplication form whose retained and exterior supports are orthogonal,
this gives an exact decomposition of the logarithmic conductor energy.  The
identity is useful because it reduces the archimedean Weil estimate to weighted
logarithmic moments of the retained mode and its exterior leakage.

No concrete Fourier transform, cutoff projection, logarithmic multiplier, or
prolate asymptotic is asserted in this file.
-/

namespace RiemannCvs.ProlateConductorIdentity

section FourierTail

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- Exact Fourier transform of the exterior leakage. -/
theorem fourier_tail_identity
    (fourier : V →ₗ[ℝ] V)
    (epsilon sigma : ℝ)
    (p t : V)
    (hFourierSq : fourier (fourier p) = p)
    (hDecomp : fourier p = (epsilon * sigma) • p + t)
    (hSign : epsilon ^ 2 = 1) :
    fourier t =
      (1 - sigma ^ 2) • p - (epsilon * sigma) • t := by
  have h := congrArg fourier hDecomp
  rw [map_add, map_smul, hFourierSq] at h
  rw [hDecomp] at h
  module at h ⊢
  exact h

/-- The same identity with the concentration defect named explicitly. -/
theorem fourier_tail_identity_with_defect
    (fourier : V →ₗ[ℝ] V)
    (epsilon sigma defect : ℝ)
    (p t : V)
    (hFourierSq : fourier (fourier p) = p)
    (hDecomp : fourier p = (epsilon * sigma) • p + t)
    (hSign : epsilon ^ 2 = 1)
    (hDefect : defect = 1 - sigma ^ 2) :
    fourier t = defect • p - (epsilon * sigma) • t := by
  rw [hDefect]
  exact fourier_tail_identity
    fourier epsilon sigma p t hFourierSq hDecomp hSign

end FourierTail

section Bilinear

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- A multiplication-type bilinear form is diagonal on a retained/exterior
support decomposition.  Expanding the exact Fourier-tail identity then gives
the transformed multiplication energy. -/
theorem transformedMultiplicationEnergy
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p t : V)
    (epsilon sigma defect : ℝ)
    (hSign : epsilon ^ 2 = 1)
    (hCrossPT : B p t = 0)
    (hCrossTP : B t p = 0) :
    B (defect • p - (epsilon * sigma) • t)
        (defect • p - (epsilon * sigma) • t) =
      defect ^ 2 * B p p + sigma ^ 2 * B t t := by
  simp only [map_sub, map_smul, LinearMap.map_sub,
    LinearMap.map_smul, hCrossPT, hCrossTP]
  module
  nlinarith

/-- Exact conductor identity.  Here `B t t` is the physical logarithmic
multiplication energy and `B (Fourier t) (Fourier t)` is the Fourier-side
logarithmic energy. -/
theorem conductorEnergyIdentity
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p t fourierTail : V)
    (epsilon sigma defect : ℝ)
    (hSign : epsilon ^ 2 = 1)
    (hFourierTail :
      fourierTail = defect • p - (epsilon * sigma) • t)
    (hCrossPT : B p t = 0)
    (hCrossTP : B t p = 0) :
    B t t + B fourierTail fourierTail =
      (1 + sigma ^ 2) * B t t + defect ^ 2 * B p p := by
  rw [hFourierTail,
    transformedMultiplicationEnergy B p t epsilon sigma defect
      hSign hCrossPT hCrossTP]
  ring

/-- Substitution of the concentration identity `defect = 1 - sigma^2`. -/
theorem conductorEnergyIdentityOfConcentrationDefect
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (p t fourierTail : V)
    (epsilon sigma defect : ℝ)
    (hSign : epsilon ^ 2 = 1)
    (hDefect : defect = 1 - sigma ^ 2)
    (hFourierTail :
      fourierTail = defect • p - (epsilon * sigma) • t)
    (hCrossPT : B p t = 0)
    (hCrossTP : B t p = 0) :
    B t t + B fourierTail fourierTail =
      (2 - defect) * B t t + defect ^ 2 * B p p := by
  have h := conductorEnergyIdentity
    B p t fourierTail epsilon sigma defect
    hSign hFourierTail hCrossPT hCrossTP
  rw [hDefect] at h ⊢
  nlinarith

end Bilinear

section Bounds

/-- A lower logarithmic moment bound for the tail and a lower bound for the
retained logarithmic moment give a lower conductor estimate. -/
theorem conductorLowerBound
    (conductor tailMoment retainedMoment defect L C : ℝ)
    (hDefectNonneg : 0 ≤ defect)
    (hDefectLeOne : defect ≤ 1)
    (hTail : L * defect ≤ tailMoment)
    (hRetained : -(C * defect) ≤ defect * retainedMoment)
    (hIdentity :
      conductor =
        (2 - defect) * tailMoment + defect ^ 2 * retainedMoment) :
    ((2 - defect) * L - C * defect) * defect ≤ conductor := by
  have hCoeff : 0 ≤ 2 - defect := by linarith
  have hTailScaled := mul_le_mul_of_nonneg_left hTail hCoeff
  rw [hIdentity]
  nlinarith

/-- Matching upper estimate from an upper tail logarithmic moment and an
absolute retained-moment budget. -/
theorem conductorUpperBound
    (conductor tailMoment retainedMoment defect U C : ℝ)
    (hDefectNonneg : 0 ≤ defect)
    (hDefectLeOne : defect ≤ 1)
    (hTail : tailMoment ≤ U * defect)
    (hRetained : defect * retainedMoment ≤ C * defect)
    (hIdentity :
      conductor =
        (2 - defect) * tailMoment + defect ^ 2 * retainedMoment) :
    conductor ≤ ((2 - defect) * U + C * defect) * defect := by
  have hCoeff : 0 ≤ 2 - defect := by linarith
  have hTailScaled := mul_le_mul_of_nonneg_left hTail hCoeff
  rw [hIdentity]
  nlinarith

/-- A coarse fixed-condition-number conclusion.  If the tail logarithmic
moment lies between `L * defect` and `K * L * defect`, and the retained term is
small compared with `L`, then the conductor is uniformly comparable with
`L * defect`. -/
theorem conductorComparableToLogScale
    (conductor tailMoment retainedMoment defect L K : ℝ)
    (hDefectNonneg : 0 ≤ defect)
    (hDefectLeHalf : defect ≤ 1 / 2)
    (hL : 0 < L)
    (hK : 1 ≤ K)
    (hTailLower : L * defect ≤ tailMoment)
    (hTailUpper : tailMoment ≤ K * L * defect)
    (hRetainedLower : -(L * defect) ≤ defect * retainedMoment)
    (hRetainedUpper : defect * retainedMoment ≤ L * defect)
    (hIdentity :
      conductor =
        (2 - defect) * tailMoment + defect ^ 2 * retainedMoment) :
    L * defect ≤ conductor ∧
      conductor ≤ (2 * K + 1 / 2) * L * defect := by
  have hLower := conductorLowerBound
    conductor tailMoment retainedMoment defect L L
    hDefectNonneg (by linarith) hTailLower hRetainedLower hIdentity
  have hUpper := conductorUpperBound
    conductor tailMoment retainedMoment defect (K * L) L
    hDefectNonneg (by linarith) hTailUpper hRetainedUpper hIdentity
  constructor <;> nlinarith

end Bounds

end RiemannCvs.ProlateConductorIdentity
