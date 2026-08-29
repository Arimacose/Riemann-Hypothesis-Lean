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

section OscillatoryAverage

/-- Exact weighted `cos²` decomposition used by the fixed-interval Bessel
mean-square argument.  The analytic integration-by-parts step only has to
bound the second, oscillatory integral. -/
theorem weightedCosSqIntegralIdentity
    (weight phase : ℝ → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hWeight : IntegrableOn weight s)
    (hOscillatory :
      IntegrableOn (fun x => weight x * cos (2 * phase x)) s) :
    (∫ x in s, weight x * cos (phase x) ^ 2) =
      (1 / 2 : ℝ) *
        ((∫ x in s, weight x) +
          ∫ x in s, weight x * cos (2 * phase x)) := by
  calc
    (∫ x in s, weight x * cos (phase x) ^ 2) =
        ∫ x in s,
          (1 / 2 : ℝ) *
            (weight x + weight x * cos (2 * phase x)) := by
      apply setIntegral_congr_fun hs
      intro x _
      change weight x * cos (phase x) ^ 2 =
        (1 / 2 : ℝ) * (weight x + weight x * cos (2 * phase x))
      rw [Real.cos_two_mul]
      ring
    _ = (1 / 2 : ℝ) *
        (∫ x in s, weight x + weight x * cos (2 * phase x)) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ((∫ x in s, weight x) +
          ∫ x in s, weight x * cos (2 * phase x)) := by
      rw [integral_add hWeight hOscillatory]

/-- If integration by parts shows that the weighted double-frequency term is
not more negative than half of the nonoscillatory weight mass, then the
weighted `cos²` average retains at least one quarter of that mass. -/
theorem weightedCosSqIntegralLower
    (weight phase : ℝ → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hWeight : IntegrableOn weight s)
    (hOscillatory :
      IntegrableOn (fun x => weight x * cos (2 * phase x)) s)
    (hOscillatoryLower :
      -((1 / 2 : ℝ) * (∫ x in s, weight x)) ≤
        ∫ x in s, weight x * cos (2 * phase x)) :
    (1 / 4 : ℝ) * (∫ x in s, weight x) ≤
      ∫ x in s, weight x * cos (phase x) ^ 2 := by
  rw [weightedCosSqIntegralIdentity weight phase s hs hWeight hOscillatory]
  linarith

/-- Interval-integral version of `weightedCosSqIntegralIdentity`, suited to the
fixed compact interval on which the Dunster approximation is instantiated. -/
theorem weightedCosSqIntervalIntegralIdentity
    (weight phase : ℝ → ℝ) (a b : ℝ)
    (hWeight : IntervalIntegrable weight volume a b)
    (hOscillatory :
      IntervalIntegrable (fun x => weight x * cos (2 * phase x)) volume a b) :
    (∫ x in a..b, weight x * cos (phase x) ^ 2) =
      (1 / 2 : ℝ) *
        ((∫ x in a..b, weight x) +
          ∫ x in a..b, weight x * cos (2 * phase x)) := by
  calc
    (∫ x in a..b, weight x * cos (phase x) ^ 2) =
        ∫ x in a..b,
          (1 / 2 : ℝ) *
            (weight x + weight x * cos (2 * phase x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      change weight x * cos (phase x) ^ 2 =
        (1 / 2 : ℝ) * (weight x + weight x * cos (2 * phase x))
      rw [Real.cos_two_mul]
      ring
    _ = (1 / 2 : ℝ) *
        (∫ x in a..b, weight x + weight x * cos (2 * phase x)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ((∫ x in a..b, weight x) +
          ∫ x in a..b, weight x * cos (2 * phase x)) := by
      rw [intervalIntegral.integral_add hWeight hOscillatory]

/-- If the double-frequency interval integral is no more negative than half of
the nonoscillatory interval mass, the weighted `cos²` integral keeps one
quarter of that mass. -/
theorem weightedCosSqIntervalIntegralLower
    (weight phase : ℝ → ℝ) (a b : ℝ)
    (hWeight : IntervalIntegrable weight volume a b)
    (hOscillatory :
      IntervalIntegrable (fun x => weight x * cos (2 * phase x)) volume a b)
    (hOscillatoryLower :
      -((1 / 2 : ℝ) * (∫ x in a..b, weight x)) ≤
        ∫ x in a..b, weight x * cos (2 * phase x)) :
    (1 / 4 : ℝ) * (∫ x in a..b, weight x) ≤
      ∫ x in a..b, weight x * cos (phase x) ^ 2 := by
  rw [weightedCosSqIntervalIntegralIdentity weight phase a b hWeight hOscillatory]
  linarith

/-- Integration by parts for a weighted linear-frequency cosine.  This is the
form obtained from the fixed-interval Bessel phase after the monotone change of
variables `y = ξ(x)`. -/
theorem linearPhaseIntegrationByPartsIdentity
    (weight weight' : ℝ → ℝ) (a b frequency offset : ℝ)
    (hWeightDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt weight (weight' x) x)
    (hWeightPrimeIntegrable : IntervalIntegrable weight' volume a b) :
    frequency * (∫ x in a..b, weight x * cos (frequency * x + offset)) =
      weight b * sin (frequency * b + offset) -
        weight a * sin (frequency * a + offset) -
        ∫ x in a..b, weight' x * sin (frequency * x + offset) := by
  have hSinDeriv :
      ∀ x ∈ uIcc a b,
        HasDerivAt (fun y : ℝ => sin (frequency * y + offset))
          (frequency * cos (frequency * x + offset)) x := by
    intro x _
    simpa only [id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id x).const_mul frequency).add_const offset).sin
  have hSinPrimeIntegrable :
      IntervalIntegrable
        (fun x : ℝ => frequency * cos (frequency * x + offset))
        volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hWeightDeriv hSinDeriv hWeightPrimeIntegrable hSinPrimeIntegrable
  calc
    frequency * (∫ x in a..b, weight x * cos (frequency * x + offset)) =
        ∫ x in a..b, frequency *
          (weight x * cos (frequency * x + offset)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b, weight x *
        (frequency * cos (frequency * x + offset)) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = weight b * sin (frequency * b + offset) -
        weight a * sin (frequency * a + offset) -
        ∫ x in a..b, weight' x * sin (frequency * x + offset) := hIBP

/-- Endpoint-plus-variation bound obtained from
`linearPhaseIntegrationByPartsIdentity`. -/
theorem linearPhaseOscillatoryIntegralBound
    (weight weight' : ℝ → ℝ) (a b frequency offset variation : ℝ)
    (hFrequency : 0 < frequency)
    (hWeightDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt weight (weight' x) x)
    (hWeightPrimeIntegrable : IntervalIntegrable weight' volume a b)
    (hVariation :
      |∫ x in a..b, weight' x * sin (frequency * x + offset)| ≤ variation) :
    |∫ x in a..b, weight x * cos (frequency * x + offset)| ≤
      (|weight b| + |weight a| + variation) / frequency := by
  have hIdentity := linearPhaseIntegrationByPartsIdentity
    weight weight' a b frequency offset hWeightDeriv hWeightPrimeIntegrable
  have hEndpointB :
      |weight b * sin (frequency * b + offset)| ≤ |weight b| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (abs_sin_le_one (frequency * b + offset)) (abs_nonneg (weight b))
  have hEndpointA :
      |weight a * sin (frequency * a + offset)| ≤ |weight a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (abs_sin_le_one (frequency * a + offset)) (abs_nonneg (weight a))
  have hTriangle :
      |weight b * sin (frequency * b + offset) -
          weight a * sin (frequency * a + offset) -
          ∫ x in a..b, weight' x * sin (frequency * x + offset)| ≤
        |weight b * sin (frequency * b + offset)| +
          |weight a * sin (frequency * a + offset)| +
          |∫ x in a..b, weight' x * sin (frequency * x + offset)| := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    calc
      |weight b * sin (frequency * b + offset) +
          -(weight a * sin (frequency * a + offset)) +
          -(∫ x in a..b, weight' x * sin (frequency * x + offset))| ≤
          |weight b * sin (frequency * b + offset) +
            -(weight a * sin (frequency * a + offset))| +
            |-(∫ x in a..b, weight' x * sin (frequency * x + offset))| :=
        abs_add_le _ _
      _ ≤
          (|weight b * sin (frequency * b + offset)| +
            |-(weight a * sin (frequency * a + offset))|) +
            |-(∫ x in a..b, weight' x * sin (frequency * x + offset))| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = |weight b * sin (frequency * b + offset)| +
          |weight a * sin (frequency * a + offset)| +
          |∫ x in a..b, weight' x * sin (frequency * x + offset)| := by
        rw [abs_neg, abs_neg]
  have hScaled :
      frequency * |∫ x in a..b, weight x * cos (frequency * x + offset)| ≤
        |weight b| + |weight a| + variation := by
    calc
      frequency * |∫ x in a..b, weight x * cos (frequency * x + offset)| =
          |frequency * (∫ x in a..b,
            weight x * cos (frequency * x + offset))| := by
        rw [abs_mul, abs_of_pos hFrequency]
      _ = |weight b * sin (frequency * b + offset) -
          weight a * sin (frequency * a + offset) -
          ∫ x in a..b, weight' x * sin (frequency * x + offset)| := by
        rw [hIdentity]
      _ ≤ |weight b * sin (frequency * b + offset)| +
          |weight a * sin (frequency * a + offset)| +
          |∫ x in a..b, weight' x * sin (frequency * x + offset)| := hTriangle
      _ ≤ |weight b| + |weight a| + variation := by linarith
  exact (le_div_iff₀ hFrequency).2 (by simpa [mul_comm] using hScaled)

/-- A directly usable integration-by-parts bound in terms of the total
variation `∫ |weight'|`. -/
theorem linearPhaseOscillatoryIntegralBoundByVariation
    (weight weight' : ℝ → ℝ) (a b frequency offset : ℝ)
    (hab : a ≤ b)
    (hFrequency : 0 < frequency)
    (hWeightDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt weight (weight' x) x)
    (hWeightPrimeIntegrable : IntervalIntegrable weight' volume a b) :
    |∫ x in a..b, weight x * cos (frequency * x + offset)| ≤
      (|weight b| + |weight a| + ∫ x in a..b, |weight' x|) /
        frequency := by
  have hSinContinuous :
      ContinuousOn (fun x : ℝ => sin (frequency * x + offset)) (uIcc a b) := by
    fun_prop
  have hProductIntegrable :
      IntervalIntegrable
        (fun x : ℝ => weight' x * sin (frequency * x + offset))
        volume a b :=
    hWeightPrimeIntegrable.mul_continuousOn hSinContinuous
  have hVariation :
      |∫ x in a..b, weight' x * sin (frequency * x + offset)| ≤
        ∫ x in a..b, |weight' x| := by
    calc
      |∫ x in a..b, weight' x * sin (frequency * x + offset)| ≤
          ∫ x in a..b, |weight' x * sin (frequency * x + offset)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, |weight' x| := by
        apply intervalIntegral.integral_mono_on hab
          hProductIntegrable.norm hWeightPrimeIntegrable.norm
        intro x _
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (abs_sin_le_one (frequency * x + offset)) (abs_nonneg (weight' x))
  exact linearPhaseOscillatoryIntegralBound
    weight weight' a b frequency offset (∫ x in a..b, |weight' x|)
    hFrequency hWeightDeriv hWeightPrimeIntegrable hVariation

/-- A complete fixed-interval weighted mean-square lower bound.  Endpoint and
total-variation control at the doubled phase frequency are sufficient to keep
one quarter of the nonoscillatory weight mass. -/
theorem linearPhaseWeightedCosSqLowerOfVariation
    (weight weight' : ℝ → ℝ) (a b frequency offset : ℝ)
    (hab : a ≤ b)
    (hFrequency : 0 < frequency)
    (hWeight : IntervalIntegrable weight volume a b)
    (hWeightDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt weight (weight' x) x)
    (hWeightPrimeIntegrable : IntervalIntegrable weight' volume a b)
    (hOscillatoryBudget :
      (|weight b| + |weight a| + ∫ x in a..b, |weight' x|) / frequency ≤
        (1 / 2 : ℝ) * (∫ x in a..b, weight x)) :
    (1 / 4 : ℝ) * (∫ x in a..b, weight x) ≤
      ∫ x in a..b,
        weight x * cos ((frequency * x + offset) / 2) ^ 2 := by
  have hPhaseContinuous :
      ContinuousOn (fun x : ℝ => cos (frequency * x + offset)) (uIcc a b) := by
    fun_prop
  have hOscBase :
      IntervalIntegrable (fun x : ℝ => weight x * cos (frequency * x + offset))
        volume a b :=
    hWeight.mul_continuousOn hPhaseContinuous
  have hOsc :
      IntervalIntegrable
        (fun x : ℝ => weight x * cos (2 * ((frequency * x + offset) / 2)))
        volume a b := by
    convert hOscBase using 1
    funext x
    congr 1
    ring_nf
  have hAbs := linearPhaseOscillatoryIntegralBoundByVariation
    weight weight' a b frequency offset hab hFrequency hWeightDeriv
      hWeightPrimeIntegrable
  have hAbsHalf :
      |∫ x in a..b, weight x * cos (frequency * x + offset)| ≤
        (1 / 2 : ℝ) * (∫ x in a..b, weight x) :=
    hAbs.trans hOscillatoryBudget
  have hLowerBase :
      -((1 / 2 : ℝ) * (∫ x in a..b, weight x)) ≤
        ∫ x in a..b, weight x * cos (frequency * x + offset) :=
    neg_le_of_abs_le hAbsHalf
  have hLower :
      -((1 / 2 : ℝ) * (∫ x in a..b, weight x)) ≤
        ∫ x in a..b,
          weight x * cos (2 * ((frequency * x + offset) / 2)) := by
    convert hLowerBase using 1
    apply intervalIntegral.integral_congr
    intro x _
    ring_nf
  exact weightedCosSqIntervalIntegralLower weight
    (fun x => (frequency * x + offset) / 2) a b hWeight hOsc hLower

/-- Quotient-rule derivative for the reduced oscillatory weight
`W = weight / phasePrime`. -/
theorem reducedWeightDerivative
    (weight weight' phasePrime phaseSecond : ℝ → ℝ) (x : ℝ)
    (hWeight : HasDerivAt weight (weight' x) x)
    (hPhasePrime : HasDerivAt phasePrime (phaseSecond x) x)
    (hPhasePrimeNe : phasePrime x ≠ 0) :
    HasDerivAt (fun y => weight y / phasePrime y)
      ((weight' x * phasePrime x - weight x * phaseSecond x) /
        phasePrime x ^ 2) x := by
  have h := hWeight.div hPhasePrime hPhasePrimeNe
  change HasDerivAt (fun y => weight y / phasePrime y)
    ((weight' x * phasePrime x - weight x * phaseSecond x) /
      phasePrime x ^ 2) x at h
  exact h

/-- The quotient definition of the reduced weight gives the factorization
needed by nonlinear-phase integration by parts whenever the phase slope is
nonzero. -/
theorem reducedWeightFactorization
    (weight phasePrime : ℝ → ℝ) (x : ℝ)
    (hPhasePrimeNe : phasePrime x ≠ 0) :
    weight x = (weight x / phasePrime x) * phasePrime x := by
  field_simp

/-- Integration by parts for a nonlinear phase without a measure-theoretic
change of variables.  The reduced weight satisfies `weight = reducedWeight ·
phase'`; this is the direct form needed for Dunster's phase `ξ`. -/
theorem nonlinearPhaseIntegrationByPartsIdentity
    (weight phase phase' reducedWeight reducedWeight' : ℝ → ℝ)
    (a b frequency offset : ℝ)
    (hPhaseDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt phase (phase' x) x)
    (hReducedDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt reducedWeight (reducedWeight' x) x)
    (hReducedPrimeIntegrable :
      IntervalIntegrable reducedWeight' volume a b)
    (hSinPrimeIntegrable :
      IntervalIntegrable
        (fun x => frequency * phase' x * cos (frequency * phase x + offset))
        volume a b)
    (hWeightFactor :
      ∀ x ∈ uIcc a b, weight x = reducedWeight x * phase' x) :
    frequency *
        (∫ x in a..b, weight x * cos (frequency * phase x + offset)) =
      reducedWeight b * sin (frequency * phase b + offset) -
        reducedWeight a * sin (frequency * phase a + offset) -
        ∫ x in a..b,
          reducedWeight' x * sin (frequency * phase x + offset) := by
  have hSinDeriv :
      ∀ x ∈ uIcc a b,
        HasDerivAt (fun y : ℝ => sin (frequency * phase y + offset))
          (frequency * phase' x * cos (frequency * phase x + offset)) x := by
    intro x hx
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      ((((hPhaseDeriv x hx).const_mul frequency).add_const offset).sin)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hReducedDeriv hSinDeriv hReducedPrimeIntegrable hSinPrimeIntegrable
  calc
    frequency *
        (∫ x in a..b, weight x * cos (frequency * phase x + offset)) =
        ∫ x in a..b,
          frequency * (weight x * cos (frequency * phase x + offset)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b,
        reducedWeight x *
          (frequency * phase' x * cos (frequency * phase x + offset)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change frequency * (weight x * cos (frequency * phase x + offset)) =
        reducedWeight x *
          (frequency * phase' x * cos (frequency * phase x + offset))
      rw [hWeightFactor x hx]
      ring
    _ = reducedWeight b * sin (frequency * phase b + offset) -
        reducedWeight a * sin (frequency * phase a + offset) -
        ∫ x in a..b,
          reducedWeight' x * sin (frequency * phase x + offset) := hIBP

/-- Endpoint-plus-total-variation control for a nonlinear phase.  It applies to
the reduced weight `W = weight / phase'` once the factorization hypothesis is
verified on the compact interval. -/
theorem nonlinearPhaseOscillatoryIntegralBoundByVariation
    (weight phase phase' reducedWeight reducedWeight' : ℝ → ℝ)
    (a b frequency offset : ℝ)
    (hab : a ≤ b)
    (hFrequency : 0 < frequency)
    (hPhaseDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt phase (phase' x) x)
    (hPhasePrimeIntegrable : IntervalIntegrable phase' volume a b)
    (hReducedDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt reducedWeight (reducedWeight' x) x)
    (hReducedPrimeIntegrable :
      IntervalIntegrable reducedWeight' volume a b)
    (hWeightFactor :
      ∀ x ∈ uIcc a b, weight x = reducedWeight x * phase' x) :
    |∫ x in a..b, weight x * cos (frequency * phase x + offset)| ≤
      (|reducedWeight b| + |reducedWeight a| +
          ∫ x in a..b, |reducedWeight' x|) /
        frequency := by
  have hPhaseContinuous : ContinuousOn phase (uIcc a b) := by
    intro x hx
    exact (hPhaseDeriv x hx).continuousAt.continuousWithinAt
  have hCosContinuous :
      ContinuousOn (fun x : ℝ => cos (frequency * phase x + offset))
        (uIcc a b) := by
    fun_prop
  have hSinContinuous :
      ContinuousOn (fun x : ℝ => sin (frequency * phase x + offset))
        (uIcc a b) := by
    fun_prop
  have hSinPrimeIntegrable :
      IntervalIntegrable
        (fun x => frequency * phase' x * cos (frequency * phase x + offset))
        volume a b := by
    have hProduct := hPhasePrimeIntegrable.mul_continuousOn hCosContinuous
    simpa only [mul_assoc] using hProduct.const_mul frequency
  have hIdentity := nonlinearPhaseIntegrationByPartsIdentity
    weight phase phase' reducedWeight reducedWeight' a b frequency offset
      hPhaseDeriv hReducedDeriv hReducedPrimeIntegrable hSinPrimeIntegrable
      hWeightFactor
  have hProductIntegrable :
      IntervalIntegrable
        (fun x : ℝ => reducedWeight' x * sin (frequency * phase x + offset))
        volume a b :=
    hReducedPrimeIntegrable.mul_continuousOn hSinContinuous
  have hVariation :
      |∫ x in a..b,
          reducedWeight' x * sin (frequency * phase x + offset)| ≤
        ∫ x in a..b, |reducedWeight' x| := by
    calc
      |∫ x in a..b,
          reducedWeight' x * sin (frequency * phase x + offset)| ≤
          ∫ x in a..b,
            |reducedWeight' x * sin (frequency * phase x + offset)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, |reducedWeight' x| := by
        apply intervalIntegral.integral_mono_on hab
          hProductIntegrable.norm hReducedPrimeIntegrable.norm
        intro x _
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (abs_sin_le_one (frequency * phase x + offset))
          (abs_nonneg (reducedWeight' x))
  have hEndpointB :
      |reducedWeight b * sin (frequency * phase b + offset)| ≤
        |reducedWeight b| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (abs_sin_le_one (frequency * phase b + offset))
      (abs_nonneg (reducedWeight b))
  have hEndpointA :
      |reducedWeight a * sin (frequency * phase a + offset)| ≤
        |reducedWeight a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (abs_sin_le_one (frequency * phase a + offset))
      (abs_nonneg (reducedWeight a))
  have hTriangle :
      |reducedWeight b * sin (frequency * phase b + offset) -
          reducedWeight a * sin (frequency * phase a + offset) -
          ∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset)| ≤
        |reducedWeight b * sin (frequency * phase b + offset)| +
          |reducedWeight a * sin (frequency * phase a + offset)| +
          |∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset)| := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    calc
      |reducedWeight b * sin (frequency * phase b + offset) +
          -(reducedWeight a * sin (frequency * phase a + offset)) +
          -(∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset))| ≤
          |reducedWeight b * sin (frequency * phase b + offset) +
            -(reducedWeight a * sin (frequency * phase a + offset))| +
            |-(∫ x in a..b,
              reducedWeight' x * sin (frequency * phase x + offset))| :=
        abs_add_le _ _
      _ ≤
          (|reducedWeight b * sin (frequency * phase b + offset)| +
            |-(reducedWeight a * sin (frequency * phase a + offset))|) +
            |-(∫ x in a..b,
              reducedWeight' x * sin (frequency * phase x + offset))| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = |reducedWeight b * sin (frequency * phase b + offset)| +
          |reducedWeight a * sin (frequency * phase a + offset)| +
          |∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset)| := by
        rw [abs_neg, abs_neg]
  have hScaled :
      frequency *
          |∫ x in a..b, weight x * cos (frequency * phase x + offset)| ≤
        |reducedWeight b| + |reducedWeight a| +
          ∫ x in a..b, |reducedWeight' x| := by
    calc
      frequency *
          |∫ x in a..b, weight x * cos (frequency * phase x + offset)| =
          |frequency *
            (∫ x in a..b, weight x * cos (frequency * phase x + offset))| := by
        rw [abs_mul, abs_of_pos hFrequency]
      _ = |reducedWeight b * sin (frequency * phase b + offset) -
          reducedWeight a * sin (frequency * phase a + offset) -
          ∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset)| := by
        rw [hIdentity]
      _ ≤ |reducedWeight b * sin (frequency * phase b + offset)| +
          |reducedWeight a * sin (frequency * phase a + offset)| +
          |∫ x in a..b,
            reducedWeight' x * sin (frequency * phase x + offset)| := hTriangle
      _ ≤ |reducedWeight b| + |reducedWeight a| +
          ∫ x in a..b, |reducedWeight' x| := by linarith
  exact (le_div_iff₀ hFrequency).2 (by simpa [mul_comm] using hScaled)

/-- Complete weighted `cos²` lower bound for a nonlinear phase.  If the
reduced-weight endpoint and total-variation budget is at most half of the
nonoscillatory weight mass, one quarter of that mass survives. -/
theorem nonlinearPhaseWeightedCosSqLowerOfVariation
    (weight phase phase' reducedWeight reducedWeight' : ℝ → ℝ)
    (a b frequency offset : ℝ)
    (hab : a ≤ b)
    (hFrequency : 0 < frequency)
    (hWeight : IntervalIntegrable weight volume a b)
    (hPhaseDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt phase (phase' x) x)
    (hPhasePrimeIntegrable : IntervalIntegrable phase' volume a b)
    (hReducedDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt reducedWeight (reducedWeight' x) x)
    (hReducedPrimeIntegrable :
      IntervalIntegrable reducedWeight' volume a b)
    (hWeightFactor :
      ∀ x ∈ uIcc a b, weight x = reducedWeight x * phase' x)
    (hOscillatoryBudget :
      (|reducedWeight b| + |reducedWeight a| +
          ∫ x in a..b, |reducedWeight' x|) /
          frequency ≤
        (1 / 2 : ℝ) * (∫ x in a..b, weight x)) :
    (1 / 4 : ℝ) * (∫ x in a..b, weight x) ≤
      ∫ x in a..b,
        weight x * cos ((frequency * phase x + offset) / 2) ^ 2 := by
  have hPhaseContinuous : ContinuousOn phase (uIcc a b) := by
    intro x hx
    exact (hPhaseDeriv x hx).continuousAt.continuousWithinAt
  have hOscContinuous :
      ContinuousOn (fun x : ℝ => cos (frequency * phase x + offset))
        (uIcc a b) := by
    fun_prop
  have hOscBase :
      IntervalIntegrable
        (fun x : ℝ => weight x * cos (frequency * phase x + offset))
        volume a b :=
    hWeight.mul_continuousOn hOscContinuous
  have hOsc :
      IntervalIntegrable
        (fun x : ℝ =>
          weight x * cos (2 * ((frequency * phase x + offset) / 2)))
        volume a b := by
    convert hOscBase using 1
    funext x
    congr 1
    ring_nf
  have hAbs := nonlinearPhaseOscillatoryIntegralBoundByVariation
    weight phase phase' reducedWeight reducedWeight' a b frequency offset
      hab hFrequency hPhaseDeriv hPhasePrimeIntegrable hReducedDeriv
      hReducedPrimeIntegrable hWeightFactor
  have hAbsHalf :
      |∫ x in a..b, weight x * cos (frequency * phase x + offset)| ≤
        (1 / 2 : ℝ) * (∫ x in a..b, weight x) :=
    hAbs.trans hOscillatoryBudget
  have hLowerBase :
      -((1 / 2 : ℝ) * (∫ x in a..b, weight x)) ≤
        ∫ x in a..b, weight x * cos (frequency * phase x + offset) :=
    neg_le_of_abs_le hAbsHalf
  have hLower :
      -((1 / 2 : ℝ) * (∫ x in a..b, weight x)) ≤
        ∫ x in a..b,
          weight x * cos (2 * ((frequency * phase x + offset) / 2)) := by
    convert hLowerBase using 1
    apply intervalIntegral.integral_congr
    intro x _
    ring_nf
  exact weightedCosSqIntervalIntegralLower weight
    (fun x => (frequency * phase x + offset) / 2) a b hWeight hOsc hLower

/-- A uniform pointwise derivative bound controls total variation on `[2,3]`. -/
theorem intervalVariationBoundOnTwoThree
    (derivative : ℝ → ℝ) (bound : ℝ)
    (hDerivativeIntegrable : IntervalIntegrable derivative volume 2 3)
    (hBound : ∀ x ∈ uIcc (2 : ℝ) 3, |derivative x| ≤ bound) :
    (∫ x in (2 : ℝ)..3, |derivative x|) ≤ bound := by
  calc
    (∫ x in (2 : ℝ)..3, |derivative x|) ≤
        ∫ _x in (2 : ℝ)..3, bound := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        hDerivativeIntegrable.norm intervalIntegrable_const
      intro x hx
      have hx' : x ∈ uIcc (2 : ℝ) 3 := by
        simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
      simpa [Real.norm_eq_abs] using hBound x hx'
    _ = bound := by norm_num

/-- Nonlinear-phase weighted mean-square lower bound from uniform endpoint,
variation, and mass constants. -/
theorem nonlinearPhaseWeightedCosSqLowerOfUniformBudget
    (weight phase phase' reducedWeight reducedWeight' : ℝ → ℝ)
    (a b frequency offset endpointBound variationBound massLower : ℝ)
    (hab : a ≤ b)
    (hFrequency : 0 < frequency)
    (hWeight : IntervalIntegrable weight volume a b)
    (hPhaseDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt phase (phase' x) x)
    (hPhasePrimeIntegrable : IntervalIntegrable phase' volume a b)
    (hReducedDeriv :
      ∀ x ∈ uIcc a b, HasDerivAt reducedWeight (reducedWeight' x) x)
    (hReducedPrimeIntegrable :
      IntervalIntegrable reducedWeight' volume a b)
    (hWeightFactor :
      ∀ x ∈ uIcc a b, weight x = reducedWeight x * phase' x)
    (hEndpointA : |reducedWeight a| ≤ endpointBound)
    (hEndpointB : |reducedWeight b| ≤ endpointBound)
    (hVariation :
      (∫ x in a..b, |reducedWeight' x|) ≤ variationBound)
    (hMassLower : massLower ≤ ∫ x in a..b, weight x)
    (hThreshold :
      2 * (2 * endpointBound + variationBound) ≤ frequency * massLower) :
    (1 / 4 : ℝ) * (∫ x in a..b, weight x) ≤
      ∫ x in a..b,
        weight x * cos ((frequency * phase x + offset) / 2) ^ 2 := by
  have hNumerator :
      |reducedWeight b| + |reducedWeight a| +
          (∫ x in a..b, |reducedWeight' x|) ≤
        2 * endpointBound + variationBound := by
    linarith
  have hTwiceNumerator :
      2 * (|reducedWeight b| + |reducedWeight a| +
          (∫ x in a..b, |reducedWeight' x|)) ≤
        frequency * (∫ x in a..b, weight x) := by
    calc
      2 * (|reducedWeight b| + |reducedWeight a| +
          (∫ x in a..b, |reducedWeight' x|)) ≤
          2 * (2 * endpointBound + variationBound) := by linarith
      _ ≤ frequency * massLower := hThreshold
      _ ≤ frequency * (∫ x in a..b, weight x) :=
        mul_le_mul_of_nonneg_left hMassLower (le_of_lt hFrequency)
  have hOscillatoryBudget :
      (|reducedWeight b| + |reducedWeight a| +
          ∫ x in a..b, |reducedWeight' x|) /
          frequency ≤
        (1 / 2 : ℝ) * (∫ x in a..b, weight x) := by
    apply (div_le_iff₀ hFrequency).2
    nlinarith
  exact nonlinearPhaseWeightedCosSqLowerOfVariation
    weight phase phase' reducedWeight reducedWeight' a b frequency offset
      hab hFrequency hWeight hPhaseDeriv hPhasePrimeIntegrable hReducedDeriv
      hReducedPrimeIntegrable hWeightFactor hOscillatoryBudget

/-- Scalar `L²`-approximation budget.  If the reference mass is controlled by
twice the actual mass plus twice the error mass, a reference lower bound and an
error upper bound leave the displayed positive part of the reference scale in
the actual mass. -/
theorem massLowerOfReferenceAndErrorBudget
    (actualMass referenceMass errorMass amplitude lower error : ℝ)
    (hReferenceLower : lower * amplitude ≤ referenceMass)
    (hReferenceSplit : referenceMass ≤ 2 * actualMass + 2 * errorMass)
    (hErrorUpper : errorMass ≤ error * amplitude) :
    ((lower - 2 * error) / 2) * amplitude ≤ actualMass := by
  nlinarith

/-- Convenient positive-margin form of
`massLowerOfReferenceAndErrorBudget`: an error coefficient at most one quarter
of the reference coefficient leaves at least one quarter of the reference
scale in the actual mass. -/
theorem massLowerOfReferenceAndQuarterError
    (actualMass referenceMass errorMass amplitude lower error : ℝ)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hReferenceLower : lower * amplitude ≤ referenceMass)
    (hReferenceSplit : referenceMass ≤ 2 * actualMass + 2 * errorMass)
    (hErrorUpper : errorMass ≤ error * amplitude)
    (hQuarter : 4 * error ≤ lower) :
    (lower / 4) * amplitude ≤ actualMass := by
  have hBudget := massLowerOfReferenceAndErrorBudget
    actualMass referenceMass errorMass amplitude lower error
    hReferenceLower hReferenceSplit hErrorUpper
  have hCoefficient : lower / 4 ≤ (lower - 2 * error) / 2 := by
    linarith
  exact (mul_le_mul_of_nonneg_right hCoefficient hAmplitudeNonneg).trans hBudget

end OscillatoryAverage

section ProlateFixedIntervalWeight

/-- Algebraic radicand in the `m = 0` fixed-interval weight extracted from
Dunster (3.1), (3.5) and the leading Bessel amplitude. -/
def prolateFixedWeightRadicand (a x : ℝ) : ℝ :=
  (x ^ 2 - 1) * (x ^ 2 - a)

/-- The Dunster fixed-interval oscillatory weight, with the global factor
`2 / π` left in the radial amplitude scale. -/
noncomputable def prolateFixedWeight (a x : ℝ) : ℝ :=
  1 / sqrt (prolateFixedWeightRadicand a x)

/-- Crude uniform radicand bounds on `a ∈ [0, 1/2]`, `x ∈ [2,3]`. -/
theorem prolateFixedWeightRadicandBounds
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    9 ≤ prolateFixedWeightRadicand a x ∧
      prolateFixedWeightRadicand a x ≤ 81 := by
  have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith
  have hxSquareUpper : x ^ 2 ≤ 9 := by nlinarith
  have hFirstLower : 3 ≤ x ^ 2 - 1 := by linarith
  have hFirstUpper : x ^ 2 - 1 ≤ 8 := by linarith
  have hSecondLower : 3 ≤ x ^ 2 - a := by linarith
  have hSecondUpper : x ^ 2 - a ≤ 9 := by linarith
  have hProductLower :
      3 * 3 ≤ (x ^ 2 - 1) * (x ^ 2 - a) :=
    mul_le_mul hFirstLower hSecondLower (by norm_num) (by linarith)
  have hProductUpper :
      (x ^ 2 - 1) * (x ^ 2 - a) ≤ 8 * 9 :=
    mul_le_mul hFirstUpper hSecondUpper (by linarith) (by norm_num)
  unfold prolateFixedWeightRadicand
  constructor <;> nlinarith

/-- Explicit positive upper and lower bounds for the fixed-interval weight. -/
theorem prolateFixedWeightBounds
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    (1 / 9 : ℝ) ≤ prolateFixedWeight a x ∧
      prolateFixedWeight a x ≤ 1 / 3 := by
  have hRadicand := prolateFixedWeightRadicandBounds
    a x haNonneg haUpper hxLower hxUpper
  have hRadicandNonneg : 0 ≤ prolateFixedWeightRadicand a x := by
    linarith [hRadicand.1]
  have hSqrtSquare := Real.sq_sqrt hRadicandNonneg
  have hSqrtNonneg := Real.sqrt_nonneg (prolateFixedWeightRadicand a x)
  have hSqrtLower : 3 ≤ sqrt (prolateFixedWeightRadicand a x) := by
    nlinarith [hRadicand.1]
  have hSqrtUpper : sqrt (prolateFixedWeightRadicand a x) ≤ 9 := by
    nlinarith [hRadicand.2]
  have hSqrtPos : 0 < sqrt (prolateFixedWeightRadicand a x) := by
    linarith
  unfold prolateFixedWeight
  constructor
  · simpa using one_div_le_one_div_of_le hSqrtPos hSqrtUpper
  · simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hSqrtLower

/-- The fixed-interval weight is continuous because its radicand stays uniformly
away from zero. -/
theorem prolateFixedWeightContinuousOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    ContinuousOn (prolateFixedWeight a) (uIcc (2 : ℝ) 3) := by
  have hRadicandContinuous : Continuous (prolateFixedWeightRadicand a) := by
    unfold prolateFixedWeightRadicand
    fun_prop
  have hSqrtContinuous :
      Continuous (fun x => sqrt (prolateFixedWeightRadicand a x)) :=
    continuous_sqrt.comp hRadicandContinuous
  unfold prolateFixedWeight
  apply continuousOn_const.div hSqrtContinuous.continuousOn
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  have hBounds := prolateFixedWeightBounds a x haNonneg haUpper hx'.1 hx'.2
  have hLower :
      (1 / 9 : ℝ) ≤ 1 / sqrt (prolateFixedWeightRadicand a x) := by
    simpa [prolateFixedWeight] using hBounds.1
  have hPos : 0 < 1 / sqrt (prolateFixedWeightRadicand a x) :=
    lt_of_lt_of_le (by norm_num) hLower
  exact ne_of_gt (one_div_pos.mp hPos)

/-- Interval integrability of the explicit Dunster weight. -/
theorem prolateFixedWeightIntervalIntegrableOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    IntervalIntegrable (prolateFixedWeight a) volume 2 3 :=
  (prolateFixedWeightContinuousOnTwoThree a haNonneg haUpper).intervalIntegrable

/-- The unit-length interval `[2,3]` carries at least `1/9` of the unscaled
Dunster oscillatory weight. -/
theorem prolateFixedWeightMassLowerOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    (1 / 9 : ℝ) ≤ ∫ x in (2 : ℝ)..3, prolateFixedWeight a x := by
  have hWeightIntegrable :=
    prolateFixedWeightIntervalIntegrableOnTwoThree a haNonneg haUpper
  calc
    (1 / 9 : ℝ) = ∫ _x in (2 : ℝ)..3, (1 / 9 : ℝ) := by norm_num
    _ ≤ ∫ x in (2 : ℝ)..3, prolateFixedWeight a x := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        intervalIntegrable_const hWeightIntegrable
      intro x hx
      exact (prolateFixedWeightBounds a x haNonneg haUpper hx.1 hx.2).1

/-- Explicit derivative of the unscaled Dunster fixed-interval weight. -/
noncomputable def prolateFixedWeightDerivative (a x : ℝ) : ℝ :=
  -(x * (2 * x ^ 2 - a - 1)) /
    sqrt (prolateFixedWeightRadicand a x) ^ 3

lemma prolateFixedWeightRadicand_hasDerivAt (a x : ℝ) :
    HasDerivAt (prolateFixedWeightRadicand a)
      (2 * x * (2 * x ^ 2 - a - 1)) x := by
  have hFirst : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    exact ((hasDerivAt_pow 2 x).sub_const 1).congr_deriv (by norm_num)
  have hSecond : HasDerivAt (fun y : ℝ => y ^ 2 - a) (2 * x) x := by
    exact ((hasDerivAt_pow 2 x).sub_const a).congr_deriv (by norm_num)
  change HasDerivAt (fun y : ℝ => (y ^ 2 - 1) * (y ^ 2 - a))
    (2 * x * (2 * x ^ 2 - a - 1)) x
  have hCoeff :
      2 * x * (2 * x ^ 2 - a - 1) =
        2 * x * (x ^ 2 - a) + (x ^ 2 - 1) * (2 * x) := by
    ring
  rw [hCoeff]
  exact hFirst.mul hSecond

lemma prolateFixedWeight_hasDerivAt
    (a x : ℝ)
    (hRadicandPos : 0 < prolateFixedWeightRadicand a x) :
    HasDerivAt (prolateFixedWeight a)
      (prolateFixedWeightDerivative a x) x := by
  have hRad := prolateFixedWeightRadicand_hasDerivAt a x
  have hSqrt := hRad.sqrt (ne_of_gt hRadicandPos)
  have hSqrtNe : sqrt (prolateFixedWeightRadicand a x) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hRadicandPos
  have hOne : HasDerivAt (fun _y : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hDiv := hOne.div hSqrt hSqrtNe
  have hCoeff :
      (0 * sqrt (prolateFixedWeightRadicand a x) -
          1 * (2 * x * (2 * x ^ 2 - a - 1) /
            (2 * sqrt (prolateFixedWeightRadicand a x)))) /
          sqrt (prolateFixedWeightRadicand a x) ^ 2 =
        prolateFixedWeightDerivative a x := by
    unfold prolateFixedWeightDerivative
    field_simp
    ring
  rw [hCoeff] at hDiv
  change HasDerivAt (fun y => 1 / sqrt (prolateFixedWeightRadicand a y))
    (prolateFixedWeightDerivative a x) x at hDiv
  change HasDerivAt (fun y => 1 / sqrt (prolateFixedWeightRadicand a y))
    (prolateFixedWeightDerivative a x) x
  exact hDiv

lemma prolateFixedWeightDerivative_abs_le_two
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    |prolateFixedWeightDerivative a x| ≤ 2 := by
  have hRadicand := prolateFixedWeightRadicandBounds
    a x haNonneg haUpper hxLower hxUpper
  have hRadicandNonneg : 0 ≤ prolateFixedWeightRadicand a x := by
    linarith [hRadicand.1]
  have hSqrtNonneg : 0 ≤ sqrt (prolateFixedWeightRadicand a x) :=
    Real.sqrt_nonneg _
  have hSqrtSquare := Real.sq_sqrt hRadicandNonneg
  have hSqrtLower : 3 ≤ sqrt (prolateFixedWeightRadicand a x) := by
    nlinarith [hRadicand.1]
  have hDenLower :
      27 ≤ sqrt (prolateFixedWeightRadicand a x) ^ 3 := by
    nlinarith [sq_nonneg (sqrt (prolateFixedWeightRadicand a x) - 3)]
  have hDenPos : 0 < sqrt (prolateFixedWeightRadicand a x) ^ 3 := by
    linarith
  have hxNonneg : 0 ≤ x := by linarith
  have hFactorNonneg : 0 ≤ 2 * x ^ 2 - a - 1 := by
    have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith
    linarith
  have hFactorUpper : 2 * x ^ 2 - a - 1 ≤ 17 := by
    have hxSquareUpper : x ^ 2 ≤ 9 := by nlinarith
    linarith
  have hNumeratorUpper : x * (2 * x ^ 2 - a - 1) ≤ 51 := by
    have hRaw := mul_le_mul hxUpper hFactorUpper hFactorNonneg
      (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at hRaw
    exact hRaw
  unfold prolateFixedWeightDerivative
  rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hxNonneg,
    abs_of_nonneg hFactorNonneg, abs_of_nonneg (pow_nonneg hSqrtNonneg 3)]
  apply (div_le_iff₀ hDenPos).2
  nlinarith

noncomputable def prolateFixedPhaseSlope (a x : ℝ) : ℝ :=
  sqrt ((x ^ 2 - a) / (x ^ 2 - 1))

noncomputable def prolateFixedPhaseSecond (a x : ℝ) : ℝ :=
  x * (a - 1) /
    (prolateFixedPhaseSlope a x * (x ^ 2 - 1) ^ 2)

lemma prolateFixedPhaseSlope_hasDerivAt
    (a x : ℝ)
    (_haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (_hxUpper : x ≤ 3) :
    HasDerivAt (prolateFixedPhaseSlope a)
      (prolateFixedPhaseSecond a x) x := by
  have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith
  have hDenPos : 0 < x ^ 2 - 1 := by nlinarith
  have hNumPos : 0 < x ^ 2 - a := by linarith
  have hRatioPos : 0 < (x ^ 2 - a) / (x ^ 2 - 1) :=
    div_pos hNumPos hDenPos
  have hNum : HasDerivAt (fun y : ℝ => y ^ 2 - a) (2 * x) x :=
    ((hasDerivAt_pow 2 x).sub_const a).congr_deriv (by norm_num)
  have hDen : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x :=
    ((hasDerivAt_pow 2 x).sub_const 1).congr_deriv (by norm_num)
  have hRatio := hNum.div hDen (ne_of_gt hDenPos)
  change HasDerivAt (fun y : ℝ => (y ^ 2 - a) / (y ^ 2 - 1))
    (((2 * x) * (x ^ 2 - 1) - (x ^ 2 - a) * (2 * x)) /
      (x ^ 2 - 1) ^ 2) x at hRatio
  have hSqrt := hRatio.sqrt (ne_of_gt hRatioPos)
  have hCoeff :
      (((2 * x) * (x ^ 2 - 1) - (x ^ 2 - a) * (2 * x)) /
          (x ^ 2 - 1) ^ 2) /
          (2 * sqrt ((x ^ 2 - a) / (x ^ 2 - 1))) =
        prolateFixedPhaseSecond a x := by
    unfold prolateFixedPhaseSecond prolateFixedPhaseSlope
    field_simp
    ring
  rw [hCoeff] at hSqrt
  change HasDerivAt
    (fun y : ℝ => sqrt ((y ^ 2 - a) / (y ^ 2 - 1)))
    (prolateFixedPhaseSecond a x) x
  exact hSqrt

lemma prolateFixedPhaseSlope_bounds
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (_hxUpper : x ≤ 3) :
    1 ≤ prolateFixedPhaseSlope a x ∧
      prolateFixedPhaseSlope a x ≤ 2 := by
  have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith
  have hDenPos : 0 < x ^ 2 - 1 := by nlinarith
  have hNumPos : 0 < x ^ 2 - a := by linarith
  have hRatioNonneg : 0 ≤ (x ^ 2 - a) / (x ^ 2 - 1) :=
    le_of_lt (div_pos hNumPos hDenPos)
  have hSlopeNonneg : 0 ≤ prolateFixedPhaseSlope a x := by
    exact Real.sqrt_nonneg _
  have hSlopeSquare :
      (x ^ 2 - 1) * prolateFixedPhaseSlope a x ^ 2 = x ^ 2 - a := by
    unfold prolateFixedPhaseSlope
    rw [Real.sq_sqrt hRatioNonneg]
    field_simp
  constructor
  · by_contra hnot
    have hSlopeLt : prolateFixedPhaseSlope a x < 1 := lt_of_not_ge hnot
    have hSlopeSquareLt : prolateFixedPhaseSlope a x ^ 2 < 1 := by
      nlinarith
    have hScaledLt := mul_lt_mul_of_pos_left hSlopeSquareLt hDenPos
    nlinarith
  · by_contra hnot
    have hSlopeGt : 2 < prolateFixedPhaseSlope a x := lt_of_not_ge hnot
    have hSlopeSquareGt : 4 < prolateFixedPhaseSlope a x ^ 2 := by
      nlinarith
    have hScaledGt := mul_lt_mul_of_pos_left hSlopeSquareGt hDenPos
    nlinarith

lemma prolateFixedPhaseSecond_abs_le_one_third
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    |prolateFixedPhaseSecond a x| ≤ 1 / 3 := by
  have hSlopeBounds := prolateFixedPhaseSlope_bounds
    a x haNonneg haUpper hxLower hxUpper
  have hxNonneg : 0 ≤ x := by linarith
  have hGapNonneg : 0 ≤ 1 - a := by linarith
  have hGapUpper : 1 - a ≤ 1 := by linarith
  have hBaseLower : 3 ≤ x ^ 2 - 1 := by nlinarith
  have hBaseNonneg : 0 ≤ x ^ 2 - 1 := by linarith
  have hSquareLower : 9 ≤ (x ^ 2 - 1) ^ 2 := by nlinarith
  have hDenLower :
      9 ≤ prolateFixedPhaseSlope a x * (x ^ 2 - 1) ^ 2 := by
    have h := mul_le_mul hSlopeBounds.1 hSquareLower
      (by norm_num : (0 : ℝ) ≤ 9)
      (by linarith [hSlopeBounds.1] : 0 ≤ prolateFixedPhaseSlope a x)
    norm_num at h
    exact h
  have hDenPos :
      0 < prolateFixedPhaseSlope a x * (x ^ 2 - 1) ^ 2 := by
    linarith
  have hNumeratorUpper : x * (1 - a) ≤ 3 := by
    have h := mul_le_mul hxUpper hGapUpper hGapNonneg
      (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    exact h
  unfold prolateFixedPhaseSecond
  rw [abs_div, abs_mul, abs_of_nonneg hxNonneg,
    abs_of_nonpos (by linarith : a - 1 ≤ 0),
    abs_of_pos hDenPos]
  apply (div_le_iff₀ hDenPos).2
  nlinarith

noncomputable def prolateFixedReducedWeight (a x : ℝ) : ℝ :=
  prolateFixedWeight a x / prolateFixedPhaseSlope a x

noncomputable def prolateFixedReducedWeightDerivative (a x : ℝ) : ℝ :=
  (prolateFixedWeightDerivative a x * prolateFixedPhaseSlope a x -
      prolateFixedWeight a x * prolateFixedPhaseSecond a x) /
    prolateFixedPhaseSlope a x ^ 2

lemma prolateFixedReducedWeight_hasDerivAt
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    HasDerivAt (prolateFixedReducedWeight a)
      (prolateFixedReducedWeightDerivative a x) x := by
  have hRadicand := prolateFixedWeightRadicandBounds
    a x haNonneg haUpper hxLower hxUpper
  have hWeight := prolateFixedWeight_hasDerivAt a x (by linarith [hRadicand.1])
  have hSlope := prolateFixedPhaseSlope_hasDerivAt
    a x haNonneg haUpper hxLower hxUpper
  have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
    linarith [(prolateFixedPhaseSlope_bounds
      a x haNonneg haUpper hxLower hxUpper).1]
  have h := reducedWeightDerivative
    (prolateFixedWeight a) (prolateFixedWeightDerivative a)
    (prolateFixedPhaseSlope a) (prolateFixedPhaseSecond a) x
    hWeight hSlope (ne_of_gt hSlopePos)
  change HasDerivAt
    (fun y => prolateFixedWeight a y / prolateFixedPhaseSlope a y)
    (prolateFixedReducedWeightDerivative a x) x
  exact h

lemma prolateFixedReducedWeight_abs_le_one_third
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    |prolateFixedReducedWeight a x| ≤ 1 / 3 := by
  have hWeightBounds := prolateFixedWeightBounds
    a x haNonneg haUpper hxLower hxUpper
  have hSlopeBounds := prolateFixedPhaseSlope_bounds
    a x haNonneg haUpper hxLower hxUpper
  have hWeightNonneg : 0 ≤ prolateFixedWeight a x := by
    linarith [hWeightBounds.1]
  have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
    linarith [hSlopeBounds.1]
  unfold prolateFixedReducedWeight
  rw [abs_div, abs_of_nonneg hWeightNonneg, abs_of_pos hSlopePos]
  apply (div_le_iff₀ hSlopePos).2
  nlinarith

lemma prolateFixedReducedWeightDerivative_abs_le_three
    (a x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    |prolateFixedReducedWeightDerivative a x| ≤ 3 := by
  have hWeightBounds := prolateFixedWeightBounds
    a x haNonneg haUpper hxLower hxUpper
  have hWeightNonneg : 0 ≤ prolateFixedWeight a x := by
    linarith [hWeightBounds.1]
  have hWeightAbs : |prolateFixedWeight a x| ≤ 1 / 3 := by
    rw [abs_of_nonneg hWeightNonneg]
    exact hWeightBounds.2
  have hWeightDerivative := prolateFixedWeightDerivative_abs_le_two
    a x haNonneg haUpper hxLower hxUpper
  have hSlopeBounds := prolateFixedPhaseSlope_bounds
    a x haNonneg haUpper hxLower hxUpper
  have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
    linarith [hSlopeBounds.1]
  have hSlopeAbs : |prolateFixedPhaseSlope a x| =
      prolateFixedPhaseSlope a x := abs_of_pos hSlopePos
  have hSecond := prolateFixedPhaseSecond_abs_le_one_third
    a x haNonneg haUpper hxLower hxUpper
  have hFirstTerm :
      |prolateFixedWeightDerivative a x /
          prolateFixedPhaseSlope a x| ≤ 2 := by
    rw [abs_div, hSlopeAbs]
    apply (div_le_iff₀ hSlopePos).2
    nlinarith
  have hSlopeSquarePos : 0 < prolateFixedPhaseSlope a x ^ 2 :=
    sq_pos_of_pos hSlopePos
  have hSlopeSquareLower : 1 ≤ prolateFixedPhaseSlope a x ^ 2 := by
    nlinarith [hSlopeBounds.1]
  have hProductAbs :
      |prolateFixedWeight a x * prolateFixedPhaseSecond a x| ≤ 1 / 9 := by
    rw [abs_mul]
    have h := mul_le_mul hWeightAbs hSecond (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    norm_num at h ⊢
    exact h
  have hSecondTerm :
      |prolateFixedWeight a x * prolateFixedPhaseSecond a x /
          prolateFixedPhaseSlope a x ^ 2| ≤ 1 / 9 := by
    rw [abs_div, abs_of_pos hSlopeSquarePos]
    apply (div_le_iff₀ hSlopeSquarePos).2
    nlinarith
  have hRewrite :
      prolateFixedReducedWeightDerivative a x =
        prolateFixedWeightDerivative a x / prolateFixedPhaseSlope a x -
          prolateFixedWeight a x * prolateFixedPhaseSecond a x /
            prolateFixedPhaseSlope a x ^ 2 := by
    unfold prolateFixedReducedWeightDerivative
    field_simp
  rw [hRewrite]
  calc
    |prolateFixedWeightDerivative a x / prolateFixedPhaseSlope a x -
        prolateFixedWeight a x * prolateFixedPhaseSecond a x /
          prolateFixedPhaseSlope a x ^ 2| ≤
        |prolateFixedWeightDerivative a x / prolateFixedPhaseSlope a x| +
          |prolateFixedWeight a x * prolateFixedPhaseSecond a x /
            prolateFixedPhaseSlope a x ^ 2| := abs_sub _ _
    _ ≤ 3 := by linarith

lemma prolateFixedPhaseSlopeContinuousOnTwoThree
    (a : ℝ) :
    ContinuousOn (prolateFixedPhaseSlope a) (uIcc (2 : ℝ) 3) := by
  have hNum : Continuous (fun x : ℝ => x ^ 2 - a) := by fun_prop
  have hDen : Continuous (fun x : ℝ => x ^ 2 - 1) := by fun_prop
  have hRatio :
      ContinuousOn (fun x : ℝ => (x ^ 2 - a) / (x ^ 2 - 1))
        (uIcc (2 : ℝ) 3) := by
    apply hNum.continuousOn.div hDen.continuousOn
    intro x hx
    have hx' : x ∈ Icc (2 : ℝ) 3 := by
      simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith [hx'.1]
    nlinarith
  unfold prolateFixedPhaseSlope
  exact hRatio.sqrt

lemma prolateFixedWeightDerivativeContinuousOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    ContinuousOn (prolateFixedWeightDerivative a) (uIcc (2 : ℝ) 3) := by
  have hNumerator :
      Continuous (fun x : ℝ => -(x * (2 * x ^ 2 - a - 1))) := by
    fun_prop
  have hRadicandContinuous : Continuous (prolateFixedWeightRadicand a) := by
    unfold prolateFixedWeightRadicand
    fun_prop
  have hDenominator :
      Continuous (fun x : ℝ => sqrt (prolateFixedWeightRadicand a x) ^ 3) := by
    fun_prop
  unfold prolateFixedWeightDerivative
  apply hNumerator.continuousOn.div hDenominator.continuousOn
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  have hRadicand := prolateFixedWeightRadicandBounds
    a x haNonneg haUpper hx'.1 hx'.2
  have hSqrtPos : 0 < sqrt (prolateFixedWeightRadicand a x) := by
    have hSqrtNonneg := Real.sqrt_nonneg (prolateFixedWeightRadicand a x)
    have hSqrtSquare := Real.sq_sqrt (by linarith [hRadicand.1] :
      0 ≤ prolateFixedWeightRadicand a x)
    nlinarith [hRadicand.1]
  exact pow_ne_zero 3 (ne_of_gt hSqrtPos)

lemma prolateFixedPhaseSecondContinuousOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    ContinuousOn (prolateFixedPhaseSecond a) (uIcc (2 : ℝ) 3) := by
  have hNumerator : Continuous (fun x : ℝ => x * (a - 1)) := by fun_prop
  have hSlope := prolateFixedPhaseSlopeContinuousOnTwoThree a
  have hPolynomial : Continuous (fun x : ℝ => (x ^ 2 - 1) ^ 2) := by fun_prop
  unfold prolateFixedPhaseSecond
  apply hNumerator.continuousOn.div (hSlope.mul hPolynomial.continuousOn)
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
    linarith [(prolateFixedPhaseSlope_bounds
      a x haNonneg haUpper hx'.1 hx'.2).1]
  have hBasePos : 0 < x ^ 2 - 1 := by nlinarith [hx'.1]
  exact mul_ne_zero (ne_of_gt hSlopePos) (pow_ne_zero 2 (ne_of_gt hBasePos))

lemma prolateFixedReducedWeightDerivativeContinuousOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    ContinuousOn (prolateFixedReducedWeightDerivative a)
      (uIcc (2 : ℝ) 3) := by
  have hWeight := prolateFixedWeightContinuousOnTwoThree a haNonneg haUpper
  have hWeightDerivative :=
    prolateFixedWeightDerivativeContinuousOnTwoThree a haNonneg haUpper
  have hSlope := prolateFixedPhaseSlopeContinuousOnTwoThree a
  have hSecond :=
    prolateFixedPhaseSecondContinuousOnTwoThree a haNonneg haUpper
  unfold prolateFixedReducedWeightDerivative
  apply (hWeightDerivative.mul hSlope).sub (hWeight.mul hSecond) |>.div
    (hSlope.pow 2)
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
    linarith [(prolateFixedPhaseSlope_bounds
      a x haNonneg haUpper hx'.1 hx'.2).1]
  exact pow_ne_zero 2 (ne_of_gt hSlopePos)

lemma prolateFixedPhaseSlopeIntervalIntegrableOnTwoThree
    (a : ℝ) :
    IntervalIntegrable (prolateFixedPhaseSlope a) volume 2 3 :=
  (prolateFixedPhaseSlopeContinuousOnTwoThree a).intervalIntegrable

lemma prolateFixedReducedWeightDerivativeIntervalIntegrableOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    IntervalIntegrable (prolateFixedReducedWeightDerivative a) volume 2 3 :=
  (prolateFixedReducedWeightDerivativeContinuousOnTwoThree
    a haNonneg haUpper).intervalIntegrable

/-- The explicit Dunster leading term keeps a uniform amount of weighted
`cos²` mass on `[2,3]` once the radial frequency is at least `33`. -/
theorem prolateFixedIntervalWeightedCosSqLower
    (a c offset : ℝ)
    (phase : ℝ → ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hPhaseDeriv :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        HasDerivAt phase (prolateFixedPhaseSlope a x) x) :
    (1 / 36 : ℝ) ≤
      ∫ x in (2 : ℝ)..3,
        prolateFixedWeight a x * cos (c * phase x + offset) ^ 2 := by
  have hFrequency : 0 < 2 * c := by linarith
  have hWeight :=
    prolateFixedWeightIntervalIntegrableOnTwoThree a haNonneg haUpper
  have hSlopeIntegrable :=
    prolateFixedPhaseSlopeIntervalIntegrableOnTwoThree a
  have hReducedDerivativeIntegrable :=
    prolateFixedReducedWeightDerivativeIntervalIntegrableOnTwoThree
      a haNonneg haUpper
  have hReducedDeriv :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        HasDerivAt (prolateFixedReducedWeight a)
          (prolateFixedReducedWeightDerivative a x) x := by
    intro x hx
    have hx' : x ∈ Icc (2 : ℝ) 3 := by
      simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    exact prolateFixedReducedWeight_hasDerivAt
      a x haNonneg haUpper hx'.1 hx'.2
  have hFactor :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        prolateFixedWeight a x =
          prolateFixedReducedWeight a x * prolateFixedPhaseSlope a x := by
    intro x hx
    have hx' : x ∈ Icc (2 : ℝ) 3 := by
      simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    have hSlopePos : 0 < prolateFixedPhaseSlope a x := by
      linarith [(prolateFixedPhaseSlope_bounds
        a x haNonneg haUpper hx'.1 hx'.2).1]
    unfold prolateFixedReducedWeight
    exact reducedWeightFactorization
      (prolateFixedWeight a) (prolateFixedPhaseSlope a) x
      (ne_of_gt hSlopePos)
  have hEndpointA :
      |prolateFixedReducedWeight a 2| ≤ (1 / 3 : ℝ) :=
    prolateFixedReducedWeight_abs_le_one_third
      a 2 haNonneg haUpper (by norm_num) (by norm_num)
  have hEndpointB :
      |prolateFixedReducedWeight a 3| ≤ (1 / 3 : ℝ) :=
    prolateFixedReducedWeight_abs_le_one_third
      a 3 haNonneg haUpper (by norm_num) (by norm_num)
  have hVariation :
      (∫ x in (2 : ℝ)..3,
        |prolateFixedReducedWeightDerivative a x|) ≤ 3 := by
    apply intervalVariationBoundOnTwoThree
      (prolateFixedReducedWeightDerivative a) 3
      hReducedDerivativeIntegrable
    intro x hx
    have hx' : x ∈ Icc (2 : ℝ) 3 := by
      simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    exact prolateFixedReducedWeightDerivative_abs_le_three
      a x haNonneg haUpper hx'.1 hx'.2
  have hMass := prolateFixedWeightMassLowerOnTwoThree
    a haNonneg haUpper
  have hThreshold :
      2 * (2 * (1 / 3 : ℝ) + 3) ≤ (2 * c) * (1 / 9 : ℝ) := by
    linarith
  have hLower := nonlinearPhaseWeightedCosSqLowerOfUniformBudget
    (prolateFixedWeight a) phase (prolateFixedPhaseSlope a)
    (prolateFixedReducedWeight a) (prolateFixedReducedWeightDerivative a)
    2 3 (2 * c) (2 * offset) (1 / 3) 3 (1 / 9)
    (by norm_num) hFrequency hWeight hPhaseDeriv hSlopeIntegrable
    hReducedDeriv hReducedDerivativeIntegrable hFactor hEndpointA hEndpointB
    hVariation hMass hThreshold
  calc
    (1 / 36 : ℝ) ≤
        (1 / 4 : ℝ) * (∫ x in (2 : ℝ)..3, prolateFixedWeight a x) := by
      linarith
    _ ≤ ∫ x in (2 : ℝ)..3,
        prolateFixedWeight a x *
          cos (((2 * c) * phase x + 2 * offset) / 2) ^ 2 := hLower
    _ = ∫ x in (2 : ℝ)..3,
        prolateFixedWeight a x * cos (c * phase x + offset) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      ring_nf

/-- The same explicit pointwise estimate gives a matching crude upper mass
bound on the unit interval. -/
lemma prolateFixedWeightMassUpperOnTwoThree
    (a : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    (∫ x in (2 : ℝ)..3, prolateFixedWeight a x) ≤ 1 / 3 := by
  have hWeightIntegrable :=
    prolateFixedWeightIntervalIntegrableOnTwoThree a haNonneg haUpper
  calc
    (∫ x in (2 : ℝ)..3, prolateFixedWeight a x) ≤
        ∫ _x in (2 : ℝ)..3, (1 / 3 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        hWeightIntegrable intervalIntegrable_const
      intro x hx
      exact (prolateFixedWeightBounds a x haNonneg haUpper hx.1 hx.2).2
    _ = 1 / 3 := by norm_num

/-- Two independent `1 / c` errors add with the explicit squared coefficient
`2 * (K₁² + K₂²) / c²`.  This is the scalar interface between Dunster's
uniform remainder and the separate Bessel-to-cosine asymptotic remainder. -/
lemma sq_add_le_two_invFrequencyErrorBudget
    (error₁ error₂ c amplitude weight K₁ K₂ : ℝ)
    (hError₁ : error₁ ^ 2 ≤ (K₁ ^ 2 / c ^ 2) * amplitude * weight)
    (hError₂ : error₂ ^ 2 ≤ (K₂ ^ 2 / c ^ 2) * amplitude * weight) :
    (error₁ + error₂) ^ 2 ≤
      (2 * (K₁ ^ 2 + K₂ ^ 2) / c ^ 2) * amplitude * weight := by
  calc
    (error₁ + error₂) ^ 2 ≤ 2 * error₁ ^ 2 + 2 * error₂ ^ 2 := by
      nlinarith [sq_nonneg (error₁ - error₂)]
    _ ≤ 2 * ((K₁ ^ 2 / c ^ 2) * amplitude * weight) +
        2 * ((K₂ ^ 2 / c ^ 2) * amplitude * weight) :=
      add_le_add (mul_le_mul_of_nonneg_left hError₁ (by norm_num))
        (mul_le_mul_of_nonneg_left hError₂ (by norm_num))
    _ = (2 * (K₁ ^ 2 + K₂ ^ 2) / c ^ 2) * amplitude * weight := by
      ring

/-- Integrating `(actual + error)² ≤ 2 actual² + 2 error²` supplies the scalar
reference-splitting hypothesis used by the remainder budget. -/
lemma intervalSqReferenceSplit
    (actual reference error : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (hActualSq : IntervalIntegrable (fun x => actual x ^ 2) volume a b)
    (hReferenceSq : IntervalIntegrable (fun x => reference x ^ 2) volume a b)
    (hErrorSq : IntervalIntegrable (fun x => error x ^ 2) volume a b)
    (hDecomp : ∀ x ∈ Icc a b, reference x = actual x + error x) :
    (∫ x in a..b, reference x ^ 2) ≤
      2 * (∫ x in a..b, actual x ^ 2) +
        2 * (∫ x in a..b, error x ^ 2) := by
  have hRight :
      IntervalIntegrable (fun x => 2 * actual x ^ 2 + 2 * error x ^ 2)
        volume a b :=
    (hActualSq.const_mul 2).add (hErrorSq.const_mul 2)
  calc
    (∫ x in a..b, reference x ^ 2) ≤
        ∫ x in a..b, (2 * actual x ^ 2 + 2 * error x ^ 2) := by
      apply intervalIntegral.integral_mono_on hab hReferenceSq hRight
      intro x hx
      rw [hDecomp x hx]
      nlinarith [sq_nonneg (actual x - error x)]
    _ = 2 * (∫ x in a..b, actual x ^ 2) +
        2 * (∫ x in a..b, error x ^ 2) := by
      rw [intervalIntegral.integral_add
          (hActualSq.const_mul 2) (hErrorSq.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- A pointwise squared error measured against the explicit Dunster weight has
total mass at most one third of its coefficient-amplitude scale. -/
lemma prolateFixedIntervalErrorMassUpper
    (error : ℝ → ℝ)
    (a coefficient amplitude : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hErrorSqIntegrable :
      IntervalIntegrable (fun x => error x ^ 2) volume 2 3)
    (hErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        error x ^ 2 ≤ coefficient * amplitude * prolateFixedWeight a x) :
    (∫ x in (2 : ℝ)..3, error x ^ 2) ≤
      (coefficient / 3) * amplitude := by
  have hWeightIntegrable :=
    prolateFixedWeightIntervalIntegrableOnTwoThree a haNonneg haUpper
  have hScaledIntegrable :
      IntervalIntegrable
        (fun x => coefficient * amplitude * prolateFixedWeight a x)
        volume 2 3 :=
    hWeightIntegrable.const_mul (coefficient * amplitude)
  have hMassUpper :=
    prolateFixedWeightMassUpperOnTwoThree a haNonneg haUpper
  calc
    (∫ x in (2 : ℝ)..3, error x ^ 2) ≤
        ∫ x in (2 : ℝ)..3,
          coefficient * amplitude * prolateFixedWeight a x := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        hErrorSqIntegrable hScaledIntegrable hErrorPointwise
    _ = (coefficient * amplitude) *
        (∫ x in (2 : ℝ)..3, prolateFixedWeight a x) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (coefficient * amplitude) * (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hMassUpper
        (mul_nonneg hCoefficientNonneg hAmplitudeNonneg)
    _ = (coefficient / 3) * amplitude := by ring

/-- A pointwise Dunster/Bessel approximation error with coefficient at most
`1 / 48` preserves an explicit fraction of the fixed-interval leading mass. -/
theorem prolateFixedIntervalActualMassLowerOfErrorBudget
    (actual reference error phase : ℝ → ℝ)
    (a c offset amplitude coefficient : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientThreshold : 48 * coefficient ≤ 1)
    (hPhaseDeriv :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        HasDerivAt phase (prolateFixedPhaseSlope a x) x)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hErrorSqIntegrable :
      IntervalIntegrable (fun x => error x ^ 2) volume 2 3)
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x * cos (c * phase x + offset) ^ 2))
    (hDecomp :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = actual x + error x)
    (hErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        error x ^ 2 ≤
          coefficient * amplitude * prolateFixedWeight a x) :
    (1 / 144 : ℝ) * amplitude ≤
      ∫ x in (2 : ℝ)..3, actual x ^ 2 := by
  have hLeading := prolateFixedIntervalWeightedCosSqLower
    a c offset phase haNonneg haUpper hc hPhaseDeriv
  have hReferenceIdentity :
      (∫ x in (2 : ℝ)..3, reference x ^ 2) =
        amplitude *
          (∫ x in (2 : ℝ)..3,
            prolateFixedWeight a x * cos (c * phase x + offset) ^ 2) := by
    calc
      (∫ x in (2 : ℝ)..3, reference x ^ 2) =
          ∫ x in (2 : ℝ)..3,
            amplitude *
              (prolateFixedWeight a x * cos (c * phase x + offset) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hReferencePointwise x hx
      _ = amplitude *
          (∫ x in (2 : ℝ)..3,
            prolateFixedWeight a x * cos (c * phase x + offset) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
  have hReferenceLower :
      (1 / 36 : ℝ) * amplitude ≤
        ∫ x in (2 : ℝ)..3, reference x ^ 2 := by
    calc
      (1 / 36 : ℝ) * amplitude = amplitude * (1 / 36 : ℝ) := by ring
      _ ≤ amplitude *
          (∫ x in (2 : ℝ)..3,
            prolateFixedWeight a x * cos (c * phase x + offset) ^ 2) :=
        mul_le_mul_of_nonneg_left hLeading hAmplitudeNonneg
      _ = ∫ x in (2 : ℝ)..3, reference x ^ 2 := hReferenceIdentity.symm
  have hReferenceSplit := intervalSqReferenceSplit
    actual reference error 2 3 (by norm_num) hActualSqIntegrable
    hReferenceSqIntegrable hErrorSqIntegrable hDecomp
  have hErrorUpper := prolateFixedIntervalErrorMassUpper
    error a coefficient amplitude haNonneg haUpper hCoefficientNonneg
    hAmplitudeNonneg hErrorSqIntegrable hErrorPointwise
  have hQuarter : 4 * (coefficient / 3) ≤ (1 / 36 : ℝ) := by
    linarith
  have hFinal := massLowerOfReferenceAndQuarterError
    (∫ x in (2 : ℝ)..3, actual x ^ 2)
    (∫ x in (2 : ℝ)..3, reference x ^ 2)
    (∫ x in (2 : ℝ)..3, error x ^ 2)
    amplitude (1 / 36) (coefficient / 3) hAmplitudeNonneg
    hReferenceLower hReferenceSplit hErrorUpper hQuarter
  norm_num at hFinal ⊢
  exact hFinal

/-- Fixed-index form of the preceding budget: a pointwise relative error
`K / c` is absorbable as soon as `48 K² ≤ c²`. -/
theorem prolateFixedIntervalActualMassLowerOfInvFrequencyError
    (actual reference error phase : ℝ → ℝ)
    (a c offset amplitude K : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold : 48 * K ^ 2 ≤ c ^ 2)
    (hPhaseDeriv :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        HasDerivAt phase (prolateFixedPhaseSlope a x) x)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hErrorSqIntegrable :
      IntervalIntegrable (fun x => error x ^ 2) volume 2 3)
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x * cos (c * phase x + offset) ^ 2))
    (hDecomp :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = actual x + error x)
    (hErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        error x ^ 2 ≤
          (K ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x) :
    (1 / 144 : ℝ) * amplitude ≤
      ∫ x in (2 : ℝ)..3, actual x ^ 2 := by
  have hcPos : 0 < c := by linarith
  have hcSquarePos : 0 < c ^ 2 := sq_pos_of_pos hcPos
  have hCoefficientNonneg : 0 ≤ K ^ 2 / c ^ 2 :=
    div_nonneg (sq_nonneg K) (sq_nonneg c)
  have hCoefficientThreshold : 48 * (K ^ 2 / c ^ 2) ≤ 1 := by
    rw [show 48 * (K ^ 2 / c ^ 2) = (48 * K ^ 2) / c ^ 2 by ring]
    exact (div_le_iff₀ hcSquarePos).2 (by simpa using hFrequencyThreshold)
  exact prolateFixedIntervalActualMassLowerOfErrorBudget
    actual reference error phase a c offset amplitude (K ^ 2 / c ^ 2)
    haNonneg haUpper hc hAmplitudeNonneg hCoefficientNonneg
    hCoefficientThreshold hPhaseDeriv hActualSqIntegrable
    hReferenceSqIntegrable hErrorSqIntegrable hReferencePointwise hDecomp
    hErrorPointwise

/-- Fixed-interval phase primitive, normalized to vanish at `x = 2`.  Dunster's
phase differs from this primitive by an additive constant on `[2,3]`. -/
noncomputable def prolateFixedPhase (a x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, prolateFixedPhaseSlope a t

lemma prolateFixedPhaseSlopeContinuousAt
    (a x : ℝ)
    (hDenominator : x ^ 2 - 1 ≠ 0) :
    ContinuousAt (prolateFixedPhaseSlope a) x := by
  have hNumerator : ContinuousAt (fun y : ℝ => y ^ 2 - a) x := by
    fun_prop
  have hDenominatorContinuous :
      ContinuousAt (fun y : ℝ => y ^ 2 - 1) x := by
    fun_prop
  unfold prolateFixedPhaseSlope
  exact (hNumerator.div hDenominatorContinuous hDenominator).sqrt

lemma prolateFixedPhase_hasDerivAt
    (a x : ℝ)
    (hxLower : 2 ≤ x)
    (hxUpper : x ≤ 3) :
    HasDerivAt (prolateFixedPhase a) (prolateFixedPhaseSlope a x) x := by
  have hxMember : x ∈ uIcc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using
      (show x ∈ Icc (2 : ℝ) 3 from ⟨hxLower, hxUpper⟩)
  have hTwoMember : (2 : ℝ) ∈ uIcc (2 : ℝ) 3 := by
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
    exact ⟨le_rfl, by norm_num⟩
  have hIntegrable :
      IntervalIntegrable (prolateFixedPhaseSlope a) volume 2 x :=
    (prolateFixedPhaseSlopeIntervalIntegrableOnTwoThree a).mono_set
      (Set.uIcc_subset_uIcc hTwoMember hxMember)
  have hxSquareLower : 4 ≤ x ^ 2 := by nlinarith
  have hDenominator : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hContinuousAt :=
    prolateFixedPhaseSlopeContinuousAt a x hDenominator
  have hStronglyMeasurable :
      StronglyMeasurable (prolateFixedPhaseSlope a) := by
    unfold prolateFixedPhaseSlope
    exact (by fun_prop :
      Measurable (fun y : ℝ => sqrt ((y ^ 2 - a) / (y ^ 2 - 1)))).stronglyMeasurable
  unfold prolateFixedPhase
  exact intervalIntegral.integral_hasDerivAt_right hIntegrable
    hStronglyMeasurable.stronglyMeasurableAtFilter hContinuousAt

/-- The internally normalized phase primitive is continuous on `[2,3]`. -/
theorem prolateFixedPhaseContinuousOnTwoThree (a : ℝ) :
    ContinuousOn (prolateFixedPhase a) (uIcc (2 : ℝ) 3) := by
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  exact (prolateFixedPhase_hasDerivAt
    a x hx'.1 hx'.2).continuousAt.continuousWithinAt

/-- Any source phase with the explicit Dunster slope differs from the
normalized primitive by its value at the left endpoint. -/
theorem sourcePhase_eq_prolateFixedPhase_add_base
    (sourcePhase : ℝ → ℝ) (a : ℝ)
    (hSourceDeriv :
      ∀ x ∈ Icc (2 : ℝ) 3,
        HasDerivAt sourcePhase (prolateFixedPhaseSlope a x) x) :
    ∀ x ∈ Icc (2 : ℝ) 3,
      sourcePhase x = prolateFixedPhase a x + sourcePhase 2 := by
  have hSourceContinuous : ContinuousOn sourcePhase (Icc (2 : ℝ) 3) := by
    intro x hx
    exact (hSourceDeriv x hx).continuousAt.continuousWithinAt
  have hFixedContinuous :
      ContinuousOn (fun x => prolateFixedPhase a x + sourcePhase 2)
        (Icc (2 : ℝ) 3) := by
    intro x hx
    exact ((prolateFixedPhase_hasDerivAt a x hx.1 hx.2).add_const
      (sourcePhase 2)).continuousAt.continuousWithinAt
  exact eq_of_has_deriv_right_eq
    (a := (2 : ℝ)) (b := 3)
    (f := sourcePhase)
    (g := fun x => prolateFixedPhase a x + sourcePhase 2)
    (f' := prolateFixedPhaseSlope a)
    (fun x hx =>
      (hSourceDeriv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
    (fun x hx =>
      ((prolateFixedPhase_hasDerivAt a x hx.1 hx.2.le).add_const
        (sourcePhase 2)).hasDerivWithinAt)
    hSourceContinuous hFixedContinuous (by simp [prolateFixedPhase])

/-- The source-phase oscillation is the normalized primitive with one explicit
additive offset. -/
theorem sourcePhaseCosine_eq_prolateFixedPhaseCosine
    (sourcePhase : ℝ → ℝ) (a c sourceOffset x : ℝ)
    (hSourceDeriv :
      ∀ y ∈ Icc (2 : ℝ) 3,
        HasDerivAt sourcePhase (prolateFixedPhaseSlope a y) y)
    (hx : x ∈ Icc (2 : ℝ) 3) :
    cos (c * sourcePhase x + sourceOffset) =
      cos (c * prolateFixedPhase a x +
        (c * sourcePhase 2 + sourceOffset)) := by
  rw [sourcePhase_eq_prolateFixedPhase_add_base sourcePhase a
    hSourceDeriv x hx]
  congr 1
  ring

/-- Canonical fixed-interval cosine reference whose square has exactly the
Dunster weight-amplitude normalization used by the mass theorem. -/
noncomputable def prolateFixedCosineReference
    (a c offset amplitude x : ℝ) : ℝ :=
  sqrt (amplitude * prolateFixedWeight a x) *
    cos (c * prolateFixedPhase a x + offset)

lemma prolateFixedCosineReference_sq
    (a c offset amplitude x : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hx : x ∈ uIcc (2 : ℝ) 3) :
    prolateFixedCosineReference a c offset amplitude x ^ 2 =
      amplitude *
        (prolateFixedWeight a x *
          cos (c * prolateFixedPhase a x + offset) ^ 2) := by
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  have hWeightNonneg : 0 ≤ prolateFixedWeight a x := by
    linarith [(prolateFixedWeightBounds
      a x haNonneg haUpper hx'.1 hx'.2).1]
  unfold prolateFixedCosineReference
  rw [mul_pow, sq_sqrt (mul_nonneg hAmplitudeNonneg hWeightNonneg)]
  ring

lemma prolateFixedCosineReferenceContinuousOnTwoThree
    (a c offset amplitude : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    ContinuousOn (prolateFixedCosineReference a c offset amplitude)
      (uIcc (2 : ℝ) 3) := by
  have hWeight := prolateFixedWeightContinuousOnTwoThree a haNonneg haUpper
  have hPhase := prolateFixedPhaseContinuousOnTwoThree a
  have hAmplitudeWeight :
      ContinuousOn (fun x => amplitude * prolateFixedWeight a x)
        (uIcc (2 : ℝ) 3) :=
    continuousOn_const.mul hWeight
  have hOscillation :
      ContinuousOn (fun x => cos (c * prolateFixedPhase a x + offset))
        (uIcc (2 : ℝ) 3) :=
    Real.continuous_cos.comp_continuousOn
      ((continuousOn_const.mul hPhase).add continuousOn_const)
  exact hAmplitudeWeight.sqrt.mul hOscillation

lemma prolateFixedCosineReferenceSqIntervalIntegrable
    (a c offset amplitude : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2) :
    IntervalIntegrable
      (fun x => prolateFixedCosineReference a c offset amplitude x ^ 2)
      volume 2 3 :=
  ((prolateFixedCosineReferenceContinuousOnTwoThree
    a c offset amplitude haNonneg haUpper).pow 2).intervalIntegrable

/-- An explicit `a ≤ parameterK / c` source estimate enters the fixed parameter
rectangle once `2 * parameterK ≤ c`. -/
lemma prolateParameter_le_half_of_invFrequency
    (a c parameterK : ℝ)
    (hcPos : 0 < c)
    (haInvFrequency : a ≤ parameterK / c)
    (hParameterThreshold : 2 * parameterK ≤ c) :
    a ≤ 1 / 2 := by
  apply haInvFrequency.trans
  exact (div_le_iff₀ hcPos).2 (by linarith)

/-- Closed phase-primitive version of the leading fixed-interval lower bound. -/
theorem prolateFixedPhaseWeightedCosSqLower
    (a c offset : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c) :
    (1 / 36 : ℝ) ≤
      ∫ x in (2 : ℝ)..3,
        prolateFixedWeight a x *
          cos (c * prolateFixedPhase a x + offset) ^ 2 := by
  apply prolateFixedIntervalWeightedCosSqLower
    a c offset (prolateFixedPhase a) haNonneg haUpper hc
  intro x hx
  have hx' : x ∈ Icc (2 : ℝ) 3 := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
  exact prolateFixedPhase_hasDerivAt a x hx'.1 hx'.2

/-- Closed phase-primitive version of the fixed-index `K / c` error budget. -/
theorem prolateFixedPhaseActualMassLowerOfInvFrequencyError
    (actual reference error : ℝ → ℝ)
    (a c offset amplitude K : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold : 48 * K ^ 2 ≤ c ^ 2)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hErrorSqIntegrable :
      IntervalIntegrable (fun x => error x ^ 2) volume 2 3)
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x *
              cos (c * prolateFixedPhase a x + offset) ^ 2))
    (hDecomp :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = actual x + error x)
    (hErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        error x ^ 2 ≤
          (K ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x) :
    (1 / 144 : ℝ) * amplitude ≤
      ∫ x in (2 : ℝ)..3, actual x ^ 2 := by
  apply prolateFixedIntervalActualMassLowerOfInvFrequencyError
    actual reference error (prolateFixedPhase a) a c offset amplitude K
    haNonneg haUpper hc hAmplitudeNonneg hFrequencyThreshold
    (fun x hx => by
      have hx' : x ∈ Icc (2 : ℝ) 3 := by
        simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
      exact prolateFixedPhase_hasDerivAt a x hx'.1 hx'.2)
    hActualSqIntegrable hReferenceSqIntegrable hErrorSqIntegrable
    hReferencePointwise hDecomp hErrorPointwise

/-- Source-shaped form of the fixed-interval lower bound: a Dunster remainder
and a Bessel-to-cosine remainder may be proved separately.  Their sum is
absorbed once `96 * (K_d² + K_b²) ≤ c²`; Lean constructs the combined error,
its interval integrability, and the required decomposition internally. -/
theorem prolateFixedPhaseActualMassLowerOfSeparatedErrors
    (actual intermediate reference dunsterError besselError : ℝ → ℝ)
    (a c offset amplitude dunsterK besselK : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold :
      96 * (dunsterK ^ 2 + besselK ^ 2) ≤ c ^ 2)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hDunsterErrorContinuous :
      ContinuousOn dunsterError (uIcc (2 : ℝ) 3))
    (hBesselErrorContinuous :
      ContinuousOn besselError (uIcc (2 : ℝ) 3))
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x *
              cos (c * prolateFixedPhase a x + offset) ^ 2))
    (hDunsterStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        intermediate x = actual x + dunsterError x)
    (hBesselStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = intermediate x + besselError x)
    (hDunsterErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        dunsterError x ^ 2 ≤
          (dunsterK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hBesselErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        besselError x ^ 2 ≤
          (besselK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x) :
    (1 / 144 : ℝ) * amplitude ≤
      ∫ x in (2 : ℝ)..3, actual x ^ 2 := by
  let coefficient : ℝ :=
    2 * (dunsterK ^ 2 + besselK ^ 2) / c ^ 2
  have hcPos : 0 < c := by linarith
  have hcSquarePos : 0 < c ^ 2 := sq_pos_of_pos hcPos
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact div_nonneg
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (sq_nonneg c)
  have hCoefficientThreshold : 48 * coefficient ≤ 1 := by
    dsimp [coefficient]
    rw [show
      48 * (2 * (dunsterK ^ 2 + besselK ^ 2) / c ^ 2) =
        (96 * (dunsterK ^ 2 + besselK ^ 2)) / c ^ 2 by ring]
    exact (div_le_iff₀ hcSquarePos).2 (by simpa using hFrequencyThreshold)
  have hCombinedErrorSqIntegrable :
      IntervalIntegrable
        (fun x => (dunsterError x + besselError x) ^ 2) volume 2 3 :=
    ((hDunsterErrorContinuous.add hBesselErrorContinuous).pow 2).intervalIntegrable
  apply prolateFixedIntervalActualMassLowerOfErrorBudget
    actual reference (fun x => dunsterError x + besselError x)
    (prolateFixedPhase a) a c offset amplitude coefficient
    haNonneg haUpper hc hAmplitudeNonneg hCoefficientNonneg
    hCoefficientThreshold
  · intro x hx
    have hx' : x ∈ Icc (2 : ℝ) 3 := by
      simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    exact prolateFixedPhase_hasDerivAt a x hx'.1 hx'.2
  · exact hActualSqIntegrable
  · exact hReferenceSqIntegrable
  · exact hCombinedErrorSqIntegrable
  · exact hReferencePointwise
  · intro x hx
    rw [hBesselStep x hx, hDunsterStep x hx]
    ring
  · intro x hx
    exact sq_add_le_two_invFrequencyErrorBudget
      (dunsterError x) (besselError x) c amplitude
      (prolateFixedWeight a x) dunsterK besselK
      (hDunsterErrorPointwise x hx) (hBesselErrorPointwise x hx)

/-- Canonical-reference version of the separated Dunster/Bessel mass lower
bound.  The reference square, its integrability, and `a ≤ 1/2` are discharged
internally from the inverse-frequency parameter estimate. -/
theorem prolateFixedPhaseActualMassLowerOfCanonicalReference
    (actual intermediate dunsterError besselError : ℝ → ℝ)
    (a c offset amplitude parameterK dunsterK besselK : ℝ)
    (haNonneg : 0 ≤ a)
    (haInvFrequency : a ≤ parameterK / c)
    (hParameterThreshold : 2 * parameterK ≤ c)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold :
      96 * (dunsterK ^ 2 + besselK ^ 2) ≤ c ^ 2)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hDunsterErrorContinuous :
      ContinuousOn dunsterError (uIcc (2 : ℝ) 3))
    (hBesselErrorContinuous :
      ContinuousOn besselError (uIcc (2 : ℝ) 3))
    (hDunsterStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        intermediate x = actual x + dunsterError x)
    (hBesselStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        prolateFixedCosineReference a c offset amplitude x =
          intermediate x + besselError x)
    (hDunsterErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        dunsterError x ^ 2 ≤
          (dunsterK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hBesselErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        besselError x ^ 2 ≤
          (besselK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x) :
    (1 / 144 : ℝ) * amplitude ≤
      ∫ x in (2 : ℝ)..3, actual x ^ 2 := by
  have hcPos : 0 < c := by linarith
  have haUpper := prolateParameter_le_half_of_invFrequency
    a c parameterK hcPos haInvFrequency hParameterThreshold
  exact prolateFixedPhaseActualMassLowerOfSeparatedErrors
    actual intermediate (prolateFixedCosineReference a c offset amplitude)
    dunsterError besselError a c offset amplitude dunsterK besselK
    haNonneg haUpper hc hAmplitudeNonneg hFrequencyThreshold
    hActualSqIntegrable
    (prolateFixedCosineReferenceSqIntervalIntegrable
      a c offset amplitude haNonneg haUpper)
    hDunsterErrorContinuous hBesselErrorContinuous
    (fun x hx => prolateFixedCosineReference_sq
      a c offset amplitude x haNonneg haUpper hAmplitudeNonneg hx)
    hDunsterStep hBesselStep hDunsterErrorPointwise hBesselErrorPointwise

end ProlateFixedIntervalWeight

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

/-- Conductor-ready composition of the fixed-interval Dunster approximation
with the exterior hyperbolic envelope.  The explicit `1 / 144` retained scale
turns the envelope coefficient `upper` into the residual constant
`288 * upper`. -/
theorem dilationLogMomentBoundsOfProlateFixedPhaseApproximation
    (density actual reference error : ℝ → ℝ)
    (a c offset amplitude K physical residual mass logScale upper : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold : 48 * K ^ 2 ≤ c ^ 2)
    (hMassPos : 0 < mass)
    (hUpperNonneg : 0 ≤ upper)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hErrorSqIntegrable :
      IntervalIntegrable (fun x => error x ^ 2) volume 2 3)
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x *
              cos (c * prolateFixedPhase a x + offset) ^ 2))
    (hDecomp :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = actual x + error x)
    (hErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        error x ^ 2 ≤
          (K ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hFixedMassToExterior :
      (∫ x in (2 : ℝ)..3, actual x ^ 2) ≤ mass)
    (hDensityMeasurable :
      AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hDensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (hEnvelope :
      ∀ u ∈ Ioi (0 : ℝ),
        density u ≤ (upper * amplitude) / cosh u)
    (hResidual :
      residual = ∫ u in Ioi 0, log (cosh u) * density u)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + 288 * upper) * mass := by
  have hFixedLower :=
    prolateFixedPhaseActualMassLowerOfInvFrequencyError
      actual reference error a c offset amplitude K haNonneg haUpper hc
      hAmplitudeNonneg hFrequencyThreshold hActualSqIntegrable
      hReferenceSqIntegrable hErrorSqIntegrable hReferencePointwise hDecomp
      hErrorPointwise
  have hMassLower : (1 / 144 : ℝ) * amplitude ≤ mass :=
    hFixedLower.trans hFixedMassToExterior
  have hBounds := dilationLogMomentBoundsOfSechEnvelope
    density physical residual mass amplitude logScale upper (1 / 144 : ℝ)
    hMassPos hAmplitudeNonneg hUpperNonneg (by norm_num)
    hDensityMeasurable hDensityNonneg hEnvelope hMassLower hResidual hIdentity
  have hCoefficient : (2 * upper) / (1 / 144 : ℝ) = 288 * upper := by
    norm_num [div_eq_mul_inv]
    ring
  constructor
  · exact hBounds.1
  · rw [hCoefficient] at hBounds
    exact hBounds.2

/-- Conductor-ready source adapter with Dunster and Bessel errors kept as
separate functions.  The threshold `96 * (K_d² + K_b²) ≤ c²` closes their
combined fixed-interval budget before applying the exterior `sech` envelope. -/
theorem dilationLogMomentBoundsOfSeparatedDunsterBesselErrors
    (density actual intermediate reference dunsterError besselError : ℝ → ℝ)
    (a c offset amplitude dunsterK besselK
      physical residual mass logScale upper : ℝ)
    (haNonneg : 0 ≤ a)
    (haUpper : a ≤ 1 / 2)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold :
      96 * (dunsterK ^ 2 + besselK ^ 2) ≤ c ^ 2)
    (hMassPos : 0 < mass)
    (hUpperNonneg : 0 ≤ upper)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hReferenceSqIntegrable :
      IntervalIntegrable (fun x => reference x ^ 2) volume 2 3)
    (hDunsterErrorContinuous :
      ContinuousOn dunsterError (uIcc (2 : ℝ) 3))
    (hBesselErrorContinuous :
      ContinuousOn besselError (uIcc (2 : ℝ) 3))
    (hReferencePointwise :
      ∀ x ∈ uIcc (2 : ℝ) 3,
        reference x ^ 2 =
          amplitude *
            (prolateFixedWeight a x *
              cos (c * prolateFixedPhase a x + offset) ^ 2))
    (hDunsterStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        intermediate x = actual x + dunsterError x)
    (hBesselStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        reference x = intermediate x + besselError x)
    (hDunsterErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        dunsterError x ^ 2 ≤
          (dunsterK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hBesselErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        besselError x ^ 2 ≤
          (besselK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hFixedMassToExterior :
      (∫ x in (2 : ℝ)..3, actual x ^ 2) ≤ mass)
    (hDensityMeasurable :
      AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hDensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (hEnvelope :
      ∀ u ∈ Ioi (0 : ℝ),
        density u ≤ (upper * amplitude) / cosh u)
    (hResidual :
      residual = ∫ u in Ioi 0, log (cosh u) * density u)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + 288 * upper) * mass := by
  have hFixedLower :=
    prolateFixedPhaseActualMassLowerOfSeparatedErrors
      actual intermediate reference dunsterError besselError
      a c offset amplitude dunsterK besselK haNonneg haUpper hc
      hAmplitudeNonneg hFrequencyThreshold hActualSqIntegrable
      hReferenceSqIntegrable hDunsterErrorContinuous
      hBesselErrorContinuous hReferencePointwise hDunsterStep hBesselStep
      hDunsterErrorPointwise hBesselErrorPointwise
  have hMassLower : (1 / 144 : ℝ) * amplitude ≤ mass :=
    hFixedLower.trans hFixedMassToExterior
  have hBounds := dilationLogMomentBoundsOfSechEnvelope
    density physical residual mass amplitude logScale upper (1 / 144 : ℝ)
    hMassPos hAmplitudeNonneg hUpperNonneg (by norm_num)
    hDensityMeasurable hDensityNonneg hEnvelope hMassLower hResidual hIdentity
  have hCoefficient : (2 * upper) / (1 / 144 : ℝ) = 288 * upper := by
    norm_num [div_eq_mul_inv]
    ring
  constructor
  · exact hBounds.1
  · rw [hCoefficient] at hBounds
    exact hBounds.2

/-- Conductor-ready source adapter with the canonical cosine reference and the
inverse-frequency parameter bound built in.  The source layer only supplies
the actual/intermediate decompositions and the two pointwise error estimates. -/
theorem dilationLogMomentBoundsOfCanonicalReferenceAndSeparatedErrors
    (density actual intermediate dunsterError besselError : ℝ → ℝ)
    (a c offset amplitude parameterK dunsterK besselK
      physical residual mass logScale upper : ℝ)
    (haNonneg : 0 ≤ a)
    (haInvFrequency : a ≤ parameterK / c)
    (hParameterThreshold : 2 * parameterK ≤ c)
    (hc : 33 ≤ c)
    (hAmplitudeNonneg : 0 ≤ amplitude)
    (hFrequencyThreshold :
      96 * (dunsterK ^ 2 + besselK ^ 2) ≤ c ^ 2)
    (hMassPos : 0 < mass)
    (hUpperNonneg : 0 ≤ upper)
    (hActualSqIntegrable :
      IntervalIntegrable (fun x => actual x ^ 2) volume 2 3)
    (hDunsterErrorContinuous :
      ContinuousOn dunsterError (uIcc (2 : ℝ) 3))
    (hBesselErrorContinuous :
      ContinuousOn besselError (uIcc (2 : ℝ) 3))
    (hDunsterStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        intermediate x = actual x + dunsterError x)
    (hBesselStep :
      ∀ x ∈ Icc (2 : ℝ) 3,
        prolateFixedCosineReference a c offset amplitude x =
          intermediate x + besselError x)
    (hDunsterErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        dunsterError x ^ 2 ≤
          (dunsterK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hBesselErrorPointwise :
      ∀ x ∈ Icc (2 : ℝ) 3,
        besselError x ^ 2 ≤
          (besselK ^ 2 / c ^ 2) * amplitude * prolateFixedWeight a x)
    (hFixedMassToExterior :
      (∫ x in (2 : ℝ)..3, actual x ^ 2) ≤ mass)
    (hDensityMeasurable :
      AEStronglyMeasurable density (volume.restrict (Ioi 0)))
    (hDensityNonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ density u)
    (hEnvelope :
      ∀ u ∈ Ioi (0 : ℝ),
        density u ≤ (upper * amplitude) / cosh u)
    (hResidual :
      residual = ∫ u in Ioi 0, log (cosh u) * density u)
    (hIdentity : physical = logScale * mass + residual) :
    logScale * mass ≤ physical ∧
      physical ≤ (logScale + 288 * upper) * mass := by
  have hcPos : 0 < c := by linarith
  have haUpper := prolateParameter_le_half_of_invFrequency
    a c parameterK hcPos haInvFrequency hParameterThreshold
  exact dilationLogMomentBoundsOfSeparatedDunsterBesselErrors
    density actual intermediate
    (prolateFixedCosineReference a c offset amplitude)
    dunsterError besselError a c offset amplitude dunsterK besselK
    physical residual mass logScale upper haNonneg haUpper hc
    hAmplitudeNonneg hFrequencyThreshold hMassPos hUpperNonneg
    hActualSqIntegrable
    (prolateFixedCosineReferenceSqIntervalIntegrable
      a c offset amplitude haNonneg haUpper)
    hDunsterErrorContinuous hBesselErrorContinuous
    (fun x hx => prolateFixedCosineReference_sq
      a c offset amplitude x haNonneg haUpper hAmplitudeNonneg hx)
    hDunsterStep hBesselStep hDunsterErrorPointwise hBesselErrorPointwise
    hFixedMassToExterior hDensityMeasurable hDensityNonneg hEnvelope
    hResidual hIdentity

end HyperbolicEnvelope

end RiemannCvs.ExteriorLogMomentTransfer
