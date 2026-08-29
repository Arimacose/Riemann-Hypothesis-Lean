import Mathlib

/-!
# Secular data after exact Fourier symmetrization

For a compressed Fourier singular value `sigma`, exact Fourier
symmetrization changes the normalized exterior defect from
`1 - sigma^2` to `(1 - sigma) / 2` and changes a squared boundary residue
`r` to `((1 + sigma) / 2) * r`.

The identities below show that these changes preserve the fixed-index prolate
quartic hierarchy.  They also quantify the perturbation of the two-pole secular
weight.  No prolate asymptotic or concrete boundary functional is asserted.
-/

namespace RiemannCvs.SymmetrizedProlateSecular

/-- Exact normalized exterior defect of an exact Fourier symmetrization. -/
theorem normalizedDefectIdentity
    (sigma : ℝ)
    (hSigma : sigma ≠ -1) :
    (1 - sigma ^ 2) / (2 + 2 * sigma) =
      (1 - sigma) / 2 := by
  have hden : 2 + 2 * sigma ≠ 0 := by
    intro h
    apply hSigma
    nlinarith
  have hOnePlus : 1 + sigma ≠ 0 := by
    intro h
    apply hSigma
    linarith
  rw [show 1 - sigma ^ 2 = (1 - sigma) * (1 + sigma) by ring]
  rw [show 2 + 2 * sigma = 2 * (1 + sigma) by ring]
  field_simp [hOnePlus]

/-- If the unnormalized symmetrized boundary value is `(1 + sigma) b` and the
squared norm is `2(1 + sigma)`, then the normalized squared residue is
`((1 + sigma)/2) b^2`. -/
theorem normalizedBoundaryResidueIdentity
    (sigma b : ℝ)
    (hSigma : sigma ≠ -1) :
    ((1 + sigma) ^ 2 * b ^ 2) / (2 + 2 * sigma) =
      ((1 + sigma) / 2) * b ^ 2 := by
  have hden : 2 + 2 * sigma ≠ 0 := by
    intro h
    apply hSigma
    nlinarith
  field_simp [hden]

/-- Exact comparison between the ratio of symmetrized defects and the ratio of
the usual squared concentration defects. -/
theorem normalizedDefectRatioIdentity
    (sigmaPlus sigmaMinus : ℝ)
    (hPlus : 1 + sigmaPlus ≠ 0)
    (hMinusDefect : 1 - sigmaMinus ^ 2 ≠ 0) :
    (1 - sigmaPlus) / (1 - sigmaMinus) =
      ((1 - sigmaPlus ^ 2) / (1 - sigmaMinus ^ 2)) *
        ((1 + sigmaMinus) / (1 + sigmaPlus)) := by
  have hMinus : 1 - sigmaMinus ≠ 0 := by
    intro h
    apply hMinusDefect
    have hs : sigmaMinus = 1 := by linarith
    rw [hs]
    norm_num
  field_simp [hPlus, hMinus, hMinusDefect]
  ring

/-- Even without using `sigma -> 1`, exact symmetrization loses at most a factor
of two in a quartic comparison when both singular values lie in `[0,1]`.

This coarse result is already sufficient for the large `lambda` parity margin;
the exact fixed-index asymptotic loses no factor. -/
theorem quarticBoundForNormalizedSymmetrizedDefects
    (sigmaPlus sigmaMinus lambda C : ℝ)
    (hPlusNonneg : 0 ≤ sigmaPlus)
    (hPlusLeOne : sigmaPlus ≤ 1)
    (hMinusNonneg : 0 ≤ sigmaMinus)
    (hMinusLeOne : sigmaMinus ≤ 1)
    (hC : 0 ≤ C)
    (hSquaredDefects :
      lambda ^ 4 * (1 - sigmaPlus ^ 2) ≤
        C * (1 - sigmaMinus ^ 2)) :
    lambda ^ 4 * ((1 - sigmaPlus) / 2) ≤
      (2 * C) * ((1 - sigmaMinus) / 2) := by
  have hLambdaFourth : 0 ≤ lambda ^ 4 := by positivity
  have hPlusFactor :
      1 - sigmaPlus ≤ 1 - sigmaPlus ^ 2 := by
    have hprod : 0 ≤ sigmaPlus * (1 - sigmaPlus) :=
      mul_nonneg hPlusNonneg (sub_nonneg.mpr hPlusLeOne)
    nlinarith
  have hMinusFactor :
      1 - sigmaMinus ^ 2 ≤ 2 * (1 - sigmaMinus) := by
    have hprod : 0 ≤ (1 - sigmaMinus) * (1 + sigmaMinus) :=
      mul_nonneg (sub_nonneg.mpr hMinusLeOne) (by nlinarith)
    nlinarith
  have hPlusScaled :=
    mul_le_mul_of_nonneg_left hPlusFactor hLambdaFourth
  have hMinusScaled :=
    mul_le_mul_of_nonneg_left hMinusFactor hC
  nlinarith

/-- Exact perturbation formula for a two-pole secular weight.

The original weight is `r0/(r0+r1)`.  Multiplying the two residues by `a0` and
`a1` changes it by the displayed rank-one rational correction.  For exact
symmetrization, `ai = (1 + sigma_i)/2`, so the perturbation vanishes as the two
fixed-index singular values both tend to one. -/
theorem twoPoleWeightPerturbation
    (r0 r1 a0 a1 : ℝ)
    (hOld : r0 + r1 ≠ 0)
    (hNew : a0 * r0 + a1 * r1 ≠ 0) :
    (a0 * r0) / (a0 * r0 + a1 * r1) - r0 / (r0 + r1) =
      (r0 * r1 * (a0 - a1)) /
        ((a0 * r0 + a1 * r1) * (r0 + r1)) := by
  field_simp [hOld, hNew]
  ring

/-- Specialization of `twoPoleWeightPerturbation` to exact Fourier
symmetrization factors. -/
theorem symmetrizedTwoPoleWeightPerturbation
    (r0 r1 sigma0 sigma1 : ℝ)
    (hOld : r0 + r1 ≠ 0)
    (hNew :
      ((1 + sigma0) / 2) * r0 +
        ((1 + sigma1) / 2) * r1 ≠ 0) :
    (((1 + sigma0) / 2) * r0) /
          (((1 + sigma0) / 2) * r0 +
            ((1 + sigma1) / 2) * r1) -
        r0 / (r0 + r1) =
      (r0 * r1 *
          (((1 + sigma0) / 2) - ((1 + sigma1) / 2))) /
        (((((1 + sigma0) / 2) * r0 +
            ((1 + sigma1) / 2) * r1)) * (r0 + r1)) := by
  exact twoPoleWeightPerturbation
    r0 r1 ((1 + sigma0) / 2) ((1 + sigma1) / 2)
    hOld hNew

/-- Exact normalized two-mode boundary-zero energy for diagonal defects
`d0,d1` and squared boundary residues `rho0,rho1`. -/
theorem twoModeBoundaryEnergyIdentity
    (d0 d1 rho0 rho1 : ℝ)
    (hDen : rho0 + rho1 ≠ 0) :
    (rho1 * d0 + rho0 * d1) / (rho0 + rho1) =
      d0 + (rho0 / (rho0 + rho1)) * (d1 - d0) := by
  field_simp [hDen]
  ring

end RiemannCvs.SymmetrizedProlateSecular
