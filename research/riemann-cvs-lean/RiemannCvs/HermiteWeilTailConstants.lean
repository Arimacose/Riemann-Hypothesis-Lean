import Mathlib

/-!
# Fixed-Hermite Weil-tail leading constants

The analytic boundary-layer calculation predicts that the complete exterior
masses, and consequently the corresponding common-scale Weil trial energies,
have the leading ratio

`(195 / (88 * pi^2)) * lambda^(-4)`.

This file verifies only the exact algebraic constant identities and coarse
inequalities.  It does not formalize the Hermite tail asymptotic, the map `E`,
the Weil explicit formula, or any large-parameter limit.
-/

namespace RiemannCvs.HermiteWeilTailConstants

/-- Source normalization `13/11`, raw prefactor ratio squared `30`, and the
leading polynomial ratio squared `1/(16*pi^2)` combine to the fixed-Hermite
exterior-tail coefficient `195/(88*pi^2)`. -/
theorem normalizedHermiteLeadingRatio :
    (13 / 11 : ℝ) * (30 / (16 * Real.pi ^ 2)) =
      195 / (88 * Real.pi ^ 2) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- The fixed-Hermite leading mass coefficient is exactly sixteen times the
boundary-constrained prolate coefficient.  The equality compares constants
only; the two constructions are analytically different. -/
theorem hermiteCoefficient_eq_sixteen_mul_prolateCoefficient :
    195 / (88 * Real.pi ^ 2) =
      16 * (195 / (1408 * Real.pi ^ 2)) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- A useful rationally certified upper bound. -/
theorem hermiteCoefficient_lt_oneQuarter :
    195 / (88 * Real.pi ^ 2) < (1 / 4 : ℝ) := by
  have hden : 0 < 88 * Real.pi ^ 2 := by positivity
  apply (div_lt_iff₀ hden).2
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  nlinarith

/-- The sharp asymptotic coefficient lies well inside the elementary
non-asymptotic `9/16` budget used by the robust transfer theorem. -/
theorem hermiteCoefficient_lt_nineSixteenths :
    195 / (88 * Real.pi ^ 2) < (9 / 16 : ℝ) := by
  have hquarter := hermiteCoefficient_lt_oneQuarter
  nlinarith

end RiemannCvs.HermiteWeilTailConstants
