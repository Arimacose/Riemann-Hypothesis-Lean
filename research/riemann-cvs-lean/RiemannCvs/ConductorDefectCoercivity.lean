import Mathlib

/-!
# Defect-weighted coercivity of the logarithmic conductor

For a combination of same-Fourier-sign prolate leakage modes, the exact
Fourier-tail identity splits the transformed logarithmic multiplication energy
into an exterior part with weight `sigma_i^2 d_i` and a retained residual part
with weight `d_i^2`, where `d_i = 1 - sigma_i^2`.

If logarithmic multiplication is bounded below by `L` on the exterior support
and by `-C` on the relevant retained subspace, then the conductor is bounded
below by

`(2 L - (L + C) delta) * sum_i d_i |a_i|^2`

whenever every active defect is at most `delta`.

This file formalizes the scalar reduction.  The support inequalities,
orthogonality, and identification of a concrete prolate family remain analytic
inputs.
-/

namespace RiemannCvs.ConductorDefectCoercivity

/-- Pointwise coefficient estimate behind the finite-family conductor lower
bound. -/
theorem oneModeDefectCoefficient
    (d L C delta : ℝ)
    (hd : 0 ≤ d)
    (hdDelta : d ≤ delta) :
    (2 * L - (L + C) * delta) * d ≤
      L * d + L * (1 - d) * d - C * d ^ 2 := by
  nlinarith

/-- Summed scalar form for three fixed-index modes. -/
theorem threeModeConductorLower
    (q d0 d1 d2 a0 a1 a2 L C delta : ℝ)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hd0Delta : d0 ≤ delta)
    (hd1Delta : d1 ≤ delta)
    (hd2Delta : d2 ≤ delta)
    (hq :
      L * (d0 * a0 ^ 2 + d1 * a1 ^ 2 + d2 * a2 ^ 2) +
        L * ((1 - d0) * d0 * a0 ^ 2 +
          (1 - d1) * d1 * a1 ^ 2 +
          (1 - d2) * d2 * a2 ^ 2) -
        C * (d0 ^ 2 * a0 ^ 2 +
          d1 ^ 2 * a1 ^ 2 + d2 ^ 2 * a2 ^ 2) ≤ q) :
    (2 * L - (L + C) * delta) *
        (d0 * a0 ^ 2 + d1 * a1 ^ 2 + d2 * a2 ^ 2) ≤ q := by
  have h0 := oneModeDefectCoefficient d0 L C delta hd0 hd0Delta
  have h1 := oneModeDefectCoefficient d1 L C delta hd1 hd1Delta
  have h2 := oneModeDefectCoefficient d2 L C delta hd2 hd2Delta
  have ha0 : 0 ≤ a0 ^ 2 := sq_nonneg a0
  have ha1 : 0 ≤ a1 ^ 2 := sq_nonneg a1
  have ha2 : 0 ≤ a2 ^ 2 := sq_nonneg a2
  have h0s := mul_le_mul_of_nonneg_right h0 ha0
  have h1s := mul_le_mul_of_nonneg_right h1 ha1
  have h2s := mul_le_mul_of_nonneg_right h2 ha2
  nlinarith

/-- A convenient positive-margin specialization.  If the retained logarithmic
lower-bound constant is at most `K L` and the active defects are small enough,
the conductor retains at least one full unit of `L` times the defect energy. -/
theorem threeModeConductorAtLeastLogDefect
    (q d0 d1 d2 a0 a1 a2 L C K delta : ℝ)
    (hL : 0 < L)
    (hK : 0 ≤ K)
    (hC : C ≤ K * L)
    (hDelta : (1 + K) * delta ≤ 1)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hd0Delta : d0 ≤ delta)
    (hd1Delta : d1 ≤ delta)
    (hd2Delta : d2 ≤ delta)
    (hq :
      L * (d0 * a0 ^ 2 + d1 * a1 ^ 2 + d2 * a2 ^ 2) +
        L * ((1 - d0) * d0 * a0 ^ 2 +
          (1 - d1) * d1 * a1 ^ 2 +
          (1 - d2) * d2 * a2 ^ 2) -
        C * (d0 ^ 2 * a0 ^ 2 +
          d1 ^ 2 * a1 ^ 2 + d2 ^ 2 * a2 ^ 2) ≤ q) :
    L * (d0 * a0 ^ 2 + d1 * a1 ^ 2 + d2 * a2 ^ 2) ≤ q := by
  have hbase := threeModeConductorLower
    q d0 d1 d2 a0 a1 a2 L C delta
    hd0 hd1 hd2 hd0Delta hd1Delta hd2Delta hq
  have hCoefficient : L ≤ 2 * L - (L + C) * delta := by
    have hDeltaNonneg : 0 ≤ delta := le_trans hd0 hd0Delta
    have hLC : L + C ≤ (1 + K) * L := by
      nlinarith
    have hScaled := mul_le_mul_of_nonneg_right hLC hDeltaNonneg
    nlinarith
  have hEnergyNonneg :
      0 ≤ d0 * a0 ^ 2 + d1 * a1 ^ 2 + d2 * a2 ^ 2 := by
    positivity
  have hScale :=
    mul_le_mul_of_nonneg_right hCoefficient hEnergyNonneg
  exact le_trans hScale hbase

/-- Adding a lower-order perturbation bounded below by
`-R * defectEnergy` preserves positive coercivity whenever `R < L`. -/
theorem addPerturbationToConductorLower
    (conductor perturbation total defectEnergy L R : ℝ)
    (hDefect : 0 ≤ defectEnergy)
    (hConductor : L * defectEnergy ≤ conductor)
    (hPerturbation : -(R * defectEnergy) ≤ perturbation)
    (hTotal : total = conductor + perturbation) :
    (L - R) * defectEnergy ≤ total := by
  rw [hTotal]
  nlinarith

end RiemannCvs.ConductorDefectCoercivity
