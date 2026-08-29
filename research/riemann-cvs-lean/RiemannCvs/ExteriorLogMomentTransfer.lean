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
