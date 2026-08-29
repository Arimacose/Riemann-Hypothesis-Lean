import Mathlib

/-!
# Scalar and hyperbolic-envelope transfer for an exterior logarithmic moment

The analytic PSWF proof supplies an upper weighted-moment bound and a lower
mass bound in terms of one common radial normalization scale.

The second half of this file makes the radial integration step explicit.  A
nonnegative density bounded by a multiple of `1 / cosh u` has both mass and
`log (cosh u)` moment at most twice that multiple.  This is the elementary
integral estimate needed after inserting a uniform radial Bessel envelope.

The final bridge records the exact one-sided normalization used by the DLMF
signal-analysis convention: a globally normalized parity mode with retained
mass `concentration` has total exterior defect `1 - concentration`, hence each
exterior half-line has mass `(1 - concentration) / 2`.  This removes a formerly
free mass-normalization hypothesis from the fixed-index PSWF application.
-/

namespace RiemannCvs.ExteriorLogMomentTransfer

open Real Set MeasureTheory

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

section HyperbolicEnvelope

/-- The elementary exponential envelope for the hyperbolic secant. -/
theorem sech_le_two_exp_neg (u : ℝ) :
    1 / cosh u ≤ 2 * exp (-u) := by
  have hcosh : exp u / 2 ≤ cosh u := by
    rw [cosh_eq]
    nlinarith [exp_pos (-u)]
  have hrecip := one_div_le_one_div_of_le
    (div_pos (exp_pos u) (by norm_num : (0 : ℝ) < 2)) hcosh
  calc
    1 / cosh u ≤ 1 / (exp u / 2) := hrecip
    _ = 2 * exp (-u) := by
      rw [exp_neg]
      field_simp

/-- On the positive radial half-line, the logarithmic coordinate weight is at
most the coordinate itself. -/
theorem log_cosh_le_self {u : ℝ} (hu : 0 ≤ u) :
    log (cosh u) ≤ u := by
  have hneg : -u ≤ u := by linarith
  have hexp : exp (-u) ≤ exp u := exp_le_exp.mpr hneg
  have hcosh : cosh u ≤ exp u := by
    rw [cosh_eq]
    linarith
  calc
    log (cosh u) ≤ log (exp u) := log_le_log (cosh_pos u) hcosh
    _ = u := log_exp u

theorem log_cosh_nonneg (u : ℝ) : 0 ≤ log (cosh u) :=
  log_nonneg (one_le_cosh u)

theorem integral_two_exp_neg_Ioi_zero :
    (∫ u : ℝ in Ioi 0, 2 * exp (-u)) = 2 := by
  rw [integral_const_mul, integral_exp_neg_Ioi_zero]
  norm_num

theorem integrableOn_two_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ => 2 * exp (-u)) (Ioi 0) := by
  exact (integrableOn_exp_neg_Ioi 0).const_mul 2

theorem integrableOn_u_mul_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
  convert h using 1
  all_goals norm_num [Real.rpow_one, mul_comm]

theorem integral_u_mul_exp_neg_Ioi_zero :
    (∫ u : ℝ in Ioi 0, u * exp (-u)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [Real.rpow_one, mul_comm]

theorem integrableOn_two_u_mul_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ => 2 * (u * exp (-u))) (Ioi 0) := by
  exact integrableOn_u_mul_exp_neg_Ioi_zero.const_mul 2

theorem integral_two_u_mul_exp_neg_Ioi_zero :
    (∫ u : ℝ in Ioi 0, 2 * (u * exp (-u))) = 2 := by
  rw [integral_const_mul, integral_u_mul_exp_neg_Ioi_zero]
  norm_num

theorem integrableOn_sech_Ioi_zero :
    IntegrableOn (fun u : ℝ => 1 / cosh u) (Ioi 0) := by
  have hContinuous : Continuous (fun u : ℝ => 1 / cosh u) :=
    continuous_const.div₀ continuous_cosh (fun u => (cosh_pos u).ne')
  refine integrableOn_two_exp_neg_Ioi_zero.mono'
    hContinuous.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (cosh_pos u))]
  exact sech_le_two_exp_neg u

theorem integral_sech_Ioi_zero_le_two :
    (∫ u : ℝ in Ioi 0, 1 / cosh u) ≤ 2 := by
  calc
    (∫ u : ℝ in Ioi 0, 1 / cosh u) ≤
        ∫ u : ℝ in Ioi 0, 2 * exp (-u) :=
      setIntegral_mono_on integrableOn_sech_Ioi_zero
        integrableOn_two_exp_neg_Ioi_zero measurableSet_Ioi
        (fun u _ => sech_le_two_exp_neg u)
    _ = 2 := integral_two_exp_neg_Ioi_zero

theorem u_div_cosh_le_two_u_exp_neg {u : ℝ} (hu : 0 ≤ u) :
    u / cosh u ≤ 2 * (u * exp (-u)) := by
  have h := mul_le_mul_of_nonneg_left (sech_le_two_exp_neg u) hu
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem integrableOn_u_div_cosh_Ioi_zero :
    IntegrableOn (fun u : ℝ => u / cosh u) (Ioi 0) := by
  have hContinuous : Continuous (fun u : ℝ => u / cosh u) :=
    continuous_id.div₀ continuous_cosh (fun u => (cosh_pos u).ne')
  refine integrableOn_two_u_mul_exp_neg_Ioi_zero.mono'
    hContinuous.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hu.le (cosh_pos u).le)]
  exact u_div_cosh_le_two_u_exp_neg hu.le

theorem integral_u_div_cosh_Ioi_zero_le_two :
    (∫ u : ℝ in Ioi 0, u / cosh u) ≤ 2 := by
  calc
    (∫ u : ℝ in Ioi 0, u / cosh u) ≤
        ∫ u : ℝ in Ioi 0, 2 * (u * exp (-u)) :=
      setIntegral_mono_on integrableOn_u_div_cosh_Ioi_zero
        integrableOn_two_u_mul_exp_neg_Ioi_zero measurableSet_Ioi
        (fun u hu => u_div_cosh_le_two_u_exp_neg hu.le)
    _ = 2 := integral_two_u_mul_exp_neg_Ioi_zero

/-- A nonnegative exterior density dominated by a multiple of `sech` has both
finite mass and finite first moment, with the same explicit constant. -/
theorem exteriorEnvelopeMassAndFirstMomentBounds
    (density : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale)
    (hmeas : AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hdensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (henvelope : ∀ u ∈ Ioi (0 : ℝ), density u ≤ scale / cosh u) :
    IntegrableOn density (Ioi 0) ∧
      IntegrableOn (fun u => u * density u) (Ioi 0) ∧
      (∫ u in Ioi 0, density u) ≤ 2 * scale ∧
      (∫ u in Ioi 0, u * density u) ≤ 2 * scale := by
  have hScaledSech : IntegrableOn
      (fun u : ℝ => scale * (1 / cosh u)) (Ioi 0) :=
    integrableOn_sech_Ioi_zero.const_mul scale
  have hDensity : IntegrableOn density (Ioi 0) := by
    refine hScaledSech.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hdensityNonneg u hu)]
    simpa [div_eq_mul_inv] using henvelope u hu
  have hScaledFirst : IntegrableOn
      (fun u : ℝ => scale * (u / cosh u)) (Ioi 0) :=
    integrableOn_u_div_cosh_Ioi_zero.const_mul scale
  have hWeightedMeas : AEStronglyMeasurable
      (fun u : ℝ => u * density u) (volume.restrict (Ioi 0)) :=
    continuous_id.aestronglyMeasurable.mul hmeas
  have hFirst : IntegrableOn (fun u : ℝ => u * density u) (Ioi 0) := by
    refine hScaledFirst.mono' hWeightedMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hu.le (hdensityNonneg u hu))]
    calc
      u * density u ≤ u * (scale / cosh u) :=
        mul_le_mul_of_nonneg_left (henvelope u hu) hu.le
      _ = scale * (u / cosh u) := by ring
  have hMass : (∫ u in Ioi 0, density u) ≤ 2 * scale := by
    calc
      (∫ u in Ioi 0, density u) ≤
          ∫ u in Ioi 0, scale * (1 / cosh u) :=
        setIntegral_mono_on hDensity hScaledSech measurableSet_Ioi
          (fun u hu => by simpa [div_eq_mul_inv] using henvelope u hu)
      _ = scale * (∫ u in Ioi 0, 1 / cosh u) := by
        rw [integral_const_mul]
      _ ≤ scale * 2 :=
        mul_le_mul_of_nonneg_left integral_sech_Ioi_zero_le_two hscale
      _ = 2 * scale := by ring
  have hFirstBound : (∫ u in Ioi 0, u * density u) ≤ 2 * scale := by
    calc
      (∫ u in Ioi 0, u * density u) ≤
          ∫ u in Ioi 0, scale * (u / cosh u) :=
        setIntegral_mono_on hFirst hScaledFirst measurableSet_Ioi
          (fun u hu => by
            calc
              u * density u ≤ u * (scale / cosh u) :=
                mul_le_mul_of_nonneg_left (henvelope u hu) hu.le
              _ = scale * (u / cosh u) := by ring)
      _ = scale * (∫ u in Ioi 0, u / cosh u) := by
        rw [integral_const_mul]
      _ ≤ scale * 2 :=
        mul_le_mul_of_nonneg_left integral_u_div_cosh_Ioi_zero_le_two hscale
      _ = 2 * scale := by ring
  exact ⟨hDensity, hFirst, hMass, hFirstBound⟩

/-- The logarithmic radial weight `log (cosh u)` is controlled by the same
first-moment envelope because `0 ≤ log (cosh u) ≤ u` on `Ioi 0`. -/
theorem exteriorEnvelopeLogMomentBound
    (density : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale)
    (hmeas : AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hdensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (henvelope : ∀ u ∈ Ioi (0 : ℝ), density u ≤ scale / cosh u) :
    IntegrableOn (fun u => log (cosh u) * density u) (Ioi 0) ∧
      (∫ u in Ioi 0, log (cosh u) * density u) ≤ 2 * scale := by
  obtain ⟨_, hFirst, _, hFirstBound⟩ :=
    exteriorEnvelopeMassAndFirstMomentBounds density scale hscale hmeas
      hdensityNonneg henvelope
  have hLogContinuous : Continuous (fun u : ℝ => log (cosh u)) :=
    continuous_cosh.log (fun u => (cosh_pos u).ne')
  have hLogMeas : AEStronglyMeasurable
      (fun u : ℝ => log (cosh u) * density u)
      (volume.restrict (Ioi 0)) :=
    hLogContinuous.aestronglyMeasurable.mul hmeas
  have hLog : IntegrableOn
      (fun u : ℝ => log (cosh u) * density u) (Ioi 0) := by
    refine hFirst.mono' hLogMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (log_cosh_nonneg u) (hdensityNonneg u hu))]
    exact mul_le_mul_of_nonneg_right (log_cosh_le_self hu.le)
      (hdensityNonneg u hu)
  constructor
  · exact hLog
  · exact (setIntegral_mono_on hLog hFirst measurableSet_Ioi
      (fun u hu => mul_le_mul_of_nonneg_right (log_cosh_le_self hu.le)
        (hdensityNonneg u hu))).trans hFirstBound

/-- A pointwise hyperbolic envelope plus one matching mass lower bound supplies
the complete pair of physical logarithmic-moment bounds. -/
theorem dilationLogMomentBoundsOfSechEnvelope
    (density : ℝ → ℝ)
    (physical residual mass amplitude logScale upper lower : ℝ)
    (hmassPos : 0 < mass)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hupper : 0 ≤ upper)
    (hlower : 0 < lower)
    (hmeas : AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hdensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (henvelope :
      ∀ u ∈ Ioi (0 : ℝ), density u ≤ (upper * amplitude) / cosh u)
    (hMass : lower * amplitude ≤ mass)
    (hResidual : residual =
      ∫ u in Ioi 0, log (cosh u) * density u)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + (2 * upper) / lower) * mass := by
  have hScale : 0 ≤ upper * amplitude := mul_nonneg hupper hAmplitudeNonneg
  obtain ⟨_, hLogUpper⟩ := exteriorEnvelopeLogMomentBound density
    (upper * amplitude) hScale hmeas hdensityNonneg henvelope
  have hResidualNonneg : 0 ≤ residual := by
    rw [hResidual]
    exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (log_cosh_nonneg u) (hdensityNonneg u hu)
  have hResidualUpper : residual ≤ (2 * upper) * amplitude := by
    rw [hResidual]
    calc
      (∫ u in Ioi 0, log (cosh u) * density u) ≤
          2 * (upper * amplitude) := hLogUpper
      _ = (2 * upper) * amplitude := by ring
  exact dilationLogMomentBoundsOfCommonScale
    physical residual mass amplitude logScale (2 * upper) lower
    hmassPos hResidualNonneg (mul_nonneg (by norm_num) hupper) hlower
    hResidualUpper hMass hIdentity

/-- In the globally normalized signal-analysis convention, orthogonal mass
decomposition and parity split the concentration defect equally between the
two exterior half-lines.  This is the scalar content of DLMF 30.15.7--30.15.8
after identifying `concentration` with the retained mass. -/
theorem oneSidedExteriorMassOfConcentration
    (globalMass retainedMass exteriorMass oneSidedMass concentration defect : ℝ)
    (hGlobal : globalMass = 1)
    (hRetained : retainedMass = concentration)
    (hDecomposition : globalMass = retainedMass + exteriorMass)
    (hParity : exteriorMass = 2 * oneSidedMass)
    (hDefect : defect = 1 - concentration) :
    oneSidedMass = defect / 2 := by
  linarith

/-- Concentration-normalized version of
`dilationLogMomentBoundsOfSechEnvelope`.

For a parity PSWF normalized to global mass one, the positive exterior radial
mass is exactly `defect / 2`.  Therefore a `sech` envelope measured directly in
units of the total concentration defect yields an explicit residual constant
`4 * upper`; no additional lower-normalization parameter remains. -/
theorem dilationLogMomentBoundsOfConcentrationDefectEnvelope
    (density : ℝ → ℝ)
    (physical residual mass defect logScale upper : ℝ)
    (hDefectPos : 0 < defect)
    (hupper : 0 ≤ upper)
    (hMass : mass = defect / 2)
    (hmeas : AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hdensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (henvelope :
      ∀ u ∈ Ioi (0 : ℝ), density u ≤ (upper * defect) / cosh u)
    (hResidual : residual =
      ∫ u in Ioi 0, log (cosh u) * density u)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + 4 * upper) * mass := by
  have hMassPos : 0 < mass := by
    rw [hMass]
    positivity
  have hMassLower : (1 / 2 : ℝ) * defect ≤ mass := by
    rw [hMass]
    ring_nf
    exact le_rfl
  have h := dilationLogMomentBoundsOfSechEnvelope
    density physical residual mass defect logScale upper (1 / 2 : ℝ)
    hMassPos (le_of_lt hDefectPos) hupper (by norm_num) hmeas
    hdensityNonneg henvelope hMassLower hResidual hIdentity
  convert h using 1
  ring_nf

end HyperbolicEnvelope

end RiemannCvs.ExteriorLogMomentTransfer
