import RiemannCvs.DigammaQuadraticRemainder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor

/-!
# Euler--Maclaurin kernels behind the digamma remainder

The first-neglected-term estimate for the digamma expansion can be obtained
from an order-two Euler--Maclaurin remainder.  This file closes the elementary
and measure-theoretic part of that route:

* the exact half-angle lower bound
  `cos (arg w / 2) * (norm w + t) <= norm (w + t)`;
* the induced inverse-cubic kernel bound;
* `|B₂({t})| <= 1/6` and the nonnegative periodic tent weight
  `{t} * (1 - {t})`;
* the exact envelope mass
  `integral_0^infinity (norm w + t)^(-3) dt = 1 / (2 * norm w ^ 2)`;
* abstract domination theorems which preserve the DLMF coefficient `1/12`.

The final theorem isolates two scalar analytic inputs: the literal
Euler--Maclaurin representation of `Complex.digamma`, and the corresponding
positive-real mass bound.  All complex-sector geometry is proved here.
-/

namespace RiemannCvs.DigammaEulerMaclaurin

open Filter MeasureTheory Set Topology
open RiemannCvs.DigammaQuadraticRemainder

/-- The order-two Bernoulli polynomial evaluated at the fractional part. -/
noncomputable def periodicBernoulliTwo (t : ℝ) : ℝ :=
  Int.fract t ^ 2 - Int.fract t + 1 / 6

/-- The nonnegative periodic weight occurring after integrating the first
Euler--Maclaurin remainder once more. -/
noncomputable def periodicTentWeight (t : ℝ) : ℝ :=
  Int.fract t * (1 - Int.fract t)

/-- The sharp absolute bound needed for the first Euler--Maclaurin
remainder. -/
lemma abs_periodicBernoulliTwo_le (t : ℝ) :
    |periodicBernoulliTwo t| ≤ 1 / 6 := by
  have h0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t ≤ 1 := (Int.fract_lt_one t).le
  apply abs_le.2
  constructor
  · dsimp [periodicBernoulliTwo]
    nlinarith [sq_nonneg (Int.fract t - 1 / 2)]
  · dsimp [periodicBernoulliTwo]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h0 (sub_nonpos.mpr h1)]

lemma periodicTentWeight_eq (t : ℝ) :
    periodicTentWeight t = 1 / 6 - periodicBernoulliTwo t := by
  simp [periodicTentWeight, periodicBernoulliTwo]
  ring

lemma periodicTentWeight_nonneg (t : ℝ) : 0 ≤ periodicTentWeight t := by
  exact mul_nonneg (Int.fract_nonneg t)
    (sub_nonneg.mpr (Int.fract_lt_one t).le)

lemma periodicTentWeight_le_one_fourth (t : ℝ) :
    periodicTentWeight t ≤ 1 / 4 := by
  dsimp [periodicTentWeight]
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

lemma measurable_periodicTentWeight : Measurable periodicTentWeight := by
  exact measurable_id.fract.mul (measurable_const.sub measurable_id.fract)

/-- Adding a nonnegative real number to a complex number loses at most the
half-angle cosine compared with adding the two norms.  Squaring reduces the
claim to
`(1 - cos (arg w)) * (norm w - t)^2 >= 0`. -/
lemma norm_add_nonneg_real_ge_cos_half_arg
    (w : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    Real.cos (w.arg / 2) * (‖w‖ + t) ≤ ‖w + (t : ℂ)‖ := by
  have hArgLower : -Real.pi ≤ w.arg := (Complex.neg_pi_lt_arg w).le
  have hArgUpper : w.arg ≤ Real.pi := Complex.arg_le_pi w
  have hHalf := Real.cos_half hArgLower hArgUpper
  have hRad : 0 ≤ (1 + Real.cos w.arg) / 2 := by
    nlinarith [Real.neg_one_le_cos w.arg]
  have hCosHalfSq : Real.cos (w.arg / 2) ^ 2 =
      (1 + Real.cos w.arg) / 2 := by
    rw [hHalf, Real.sq_sqrt hRad]
  have hCosHalfNonneg : 0 ≤ Real.cos (w.arg / 2) := by
    rw [hHalf]
    positivity
  have hRe : ‖w‖ * Real.cos w.arg = w.re :=
    Complex.norm_mul_cos_arg w
  have hNormAddSq : ‖w + (t : ℂ)‖ ^ 2 =
      ‖w‖ ^ 2 + t ^ 2 + 2 * t * w.re := by
    rw [Complex.sq_norm, Complex.normSq_apply,
      Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  apply (sq_le_sq₀
      (mul_nonneg hCosHalfNonneg (add_nonneg (norm_nonneg w) ht))
      (norm_nonneg _)).mp
  rw [hNormAddSq, mul_pow, hCosHalfSq]
  have hFactor : 0 ≤ (1 - Real.cos w.arg) * (‖w‖ - t) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (Real.cos_le_one w.arg)) (sq_nonneg _)
  nlinarith

/-- Inverse-cubic form of `norm_add_nonneg_real_ge_cos_half_arg`. -/
lemma norm_inv_cube_add_nonneg_real_le
    (w : ℂ) (hw : 0 < w.re) (t : ℝ) (ht : 0 ≤ t) :
    ‖(w + (t : ℂ))⁻¹ ^ 3‖ ≤
      (Real.cos (w.arg / 2))⁻¹ ^ 3 / (‖w‖ + t) ^ 3 := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hNormW : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hCos : 0 < Real.cos (w.arg / 2) := by
    exact lt_of_lt_of_le
      (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num))
      (cos_half_arg_lower w hw)
  have hSum : 0 < ‖w‖ + t := add_pos_of_pos_of_nonneg hNormW ht
  have hGeom := norm_add_nonneg_real_ge_cos_half_arg w t ht
  have hProd : 0 < Real.cos (w.arg / 2) * (‖w‖ + t) :=
    mul_pos hCos hSum
  have hPow := pow_le_pow_left₀ (le_of_lt hProd) hGeom 3
  have hInv := one_div_le_one_div_of_le (pow_pos hProd 3) hPow
  rw [norm_pow, norm_inv, inv_pow]
  calc
    (‖w + (t : ℂ)‖ ^ 3)⁻¹ = 1 / ‖w + (t : ℂ)‖ ^ 3 := by
      simp [one_div]
    _ ≤ 1 / (Real.cos (w.arg / 2) * (‖w‖ + t)) ^ 3 := hInv
    _ = (Real.cos (w.arg / 2))⁻¹ ^ 3 / (‖w‖ + t) ^ 3 := by
      field_simp [ne_of_gt hCos, ne_of_gt hSum]

/-- The shifted real `(-3)`-power envelope is integrable on the positive
half-line. -/
lemma integrableOn_one_div_cube_add_Ioi_zero (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => 1 / (r + t) ^ 3) (Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt
    (a := (-3 : ℝ)) (c := 0) (m := r) (by norm_num) (by simpa using hr)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change (t + r) ^ (-3 : ℝ) = 1 / (r + t) ^ 3
  rw [add_comm t r, show (-3 : ℝ) = -(3 : ℝ) by norm_num,
    Real.rpow_neg hrt]
  simp [one_div]

/-- Antiderivative evaluation for the shifted real `(-3)`-power. -/
private lemma integral_add_rpow_neg_three_Ioi_zero (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, (t + r) ^ (-3 : ℝ) = 1 / (2 * r ^ 2) := by
  have hInt : IntegrableOn (fun t : ℝ => (t + r) ^ (-3 : ℝ)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by simpa using hr)
  have hDeriv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + r) ^ (-2 : ℝ) / (-2 : ℝ))
        ((x + r) ^ (-3 : ℝ)) x := by
    intro x hx
    convert! (((hasDerivAt_id x).add_const r).rpow_const _).div_const
      (-2 : ℝ) using 1
    · norm_num
    · left
      simp only [id_eq]
      linarith [mem_Ici.mp hx]
  have hLim : Tendsto
      (fun t : ℝ => (t + r) ^ (-2 : ℝ) / (-2 : ℝ))
      atTop (𝓝 (0 / (-2 : ℝ))) := by
    exact ((tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp
      (tendsto_atTop_add_const_right _ r tendsto_id)).div_const _
  have hEval := integral_Ioi_of_hasDerivAt_of_tendsto' hDeriv hInt hLim
  rw [hEval]
  simp only [zero_div, zero_sub]
  norm_num only [zero_add]
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (le_of_lt hr)]
  field_simp
  all_goals exact (Real.rpow_natCast r 2).symm

/-- Exact mass of the inverse-cubic envelope. -/
lemma integral_one_div_cube_add_Ioi_zero (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, 1 / (r + t) ^ 3 = 1 / (2 * r ^ 2) := by
  rw [← integral_add_rpow_neg_three_Ioi_zero r hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change 1 / (r + t) ^ 3 = (t + r) ^ (-3 : ℝ)
  rw [add_comm t r, show (-3 : ℝ) = -(3 : ℝ) by norm_num,
    Real.rpow_neg hrt]
  simp [one_div]

/-- The exact integral of the uniform `1/6` inverse-cubic envelope. -/
lemma integral_first_neglected_envelope (w : ℂ) (hw : 0 < w.re) :
    ∫ t : ℝ in Ioi 0,
        ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
          (1 / (‖w‖ + t) ^ 3) =
      ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  rw [integral_const_mul,
    integral_one_div_cube_add_Ioi_zero ‖w‖ (norm_pos_iff.2 hw0)]
  ring

/-- The uniform `1/6` envelope is integrable on the positive half-line. -/
lemma integrableOn_first_neglected_envelope (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
          (1 / (‖w‖ + t) ^ 3))
      (Ioi 0) := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  exact (integrableOn_one_div_cube_add_Ioi_zero ‖w‖
    (norm_pos_iff.2 hw0)).const_mul _

/-- Any integrand dominated by the uniform Bernoulli-two/inverse-cubic
envelope has the displayed `1/12` bound. -/
theorem norm_setIntegral_le_bernoulliTwo_envelope
    (w : ℂ) (hw : 0 < w.re) (f : ℝ → ℂ)
    (hPointwise : ∀ t ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤
        ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
          (1 / (‖w‖ + t) ^ 3)) :
    ‖∫ t : ℝ in Ioi 0, f t‖ ≤
      ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 := by
  calc
    ‖∫ t : ℝ in Ioi 0, f t‖ ≤
        ∫ t : ℝ in Ioi 0,
          ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
            (1 / (‖w‖ + t) ^ 3) := by
      apply norm_integral_le_of_norm_le
        (integrableOn_first_neglected_envelope w hw)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hPointwise t ht
    _ = ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 :=
      integral_first_neglected_envelope w hw

/-- The literal periodic-Bernoulli kernel is pointwise dominated by the
uniform `1/6` envelope. -/
lemma norm_periodicBernoulliTwo_mul_inv_cube_le
    (w : ℂ) (hw : 0 < w.re) (t : ℝ) (ht : 0 ≤ t) :
    ‖(periodicBernoulliTwo t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
      ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
        (1 / (‖w‖ + t) ^ 3) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hB := abs_periodicBernoulliTwo_le t
  have hK := norm_inv_cube_add_nonneg_real_le w hw t ht
  have hEnvelopeNonneg : 0 ≤ 1 / (‖w‖ + t) ^ 3 := by positivity
  calc
    |periodicBernoulliTwo t| * ‖(w + (t : ℂ))⁻¹ ^ 3‖ ≤
        (1 / 6 : ℝ) * ‖(w + (t : ℂ))⁻¹ ^ 3‖ := by gcongr
    _ ≤ (1 / 6 : ℝ) *
        ((Real.cos (w.arg / 2))⁻¹ ^ 3 / (‖w‖ + t) ^ 3) := by gcongr
    _ = ((1 / 6 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) *
        (1 / (‖w‖ + t) ^ 3) := by ring

/-- The periodic-Bernoulli integral is bounded by the uniform envelope. -/
theorem periodicBernoulliTwo_integral_le
    (w : ℂ) (hw : 0 < w.re) :
    ‖∫ t : ℝ in Ioi 0,
        (periodicBernoulliTwo t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
      ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 := by
  apply norm_setIntegral_le_bernoulliTwo_envelope w hw
  intro t ht
  exact norm_periodicBernoulliTwo_mul_inv_cube_le w hw t (mem_Ioi.mp ht).le

/-- The periodic tent-weight kernel is integrable for every positive real
shift. -/
lemma integrableOn_periodicTentWeight_div_cube (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun t : ℝ => periodicTentWeight t * (1 / (r + t) ^ 3))
      (Ioi 0) := by
  have hMajorant :=
    (integrableOn_one_div_cube_add_Ioi_zero r hr).const_mul (1 / 4 : ℝ)
  apply hMajorant.mono'
  · exact (measurable_periodicTentWeight.mul
      (measurable_const.div
        ((measurable_const.add measurable_id).pow_const 3))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hDen : 0 ≤ 1 / (r + t) ^ 3 := by
      have : 0 < r + t := by linarith [mem_Ioi.mp ht]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (periodicTentWeight_nonneg t) hDen)]
    exact mul_le_mul_of_nonneg_right (periodicTentWeight_le_one_fourth t) hDen

/-- Pointwise sector comparison for the correct nonnegative
Euler--Maclaurin tent weight. -/
lemma norm_periodicTentWeight_mul_inv_cube_le
    (w : ℂ) (hw : 0 < w.re) (t : ℝ) (ht : 0 ≤ t) :
    ‖(periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
      (Real.cos (w.arg / 2))⁻¹ ^ 3 *
        (periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (periodicTentWeight_nonneg t)]
  have hK := norm_inv_cube_add_nonneg_real_le w hw t ht
  have hWeight := periodicTentWeight_nonneg t
  calc
    periodicTentWeight t * ‖(w + (t : ℂ))⁻¹ ^ 3‖ ≤
        periodicTentWeight t *
          ((Real.cos (w.arg / 2))⁻¹ ^ 3 / (‖w‖ + t) ^ 3) := by
      gcongr
    _ = (Real.cos (w.arg / 2))⁻¹ ^ 3 *
        (periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) := by ring

/-- Complex tent-kernel domination by its positive-real mass. -/
theorem norm_periodicTentWeight_integral_le_real_mass
    (w : ℂ) (hw : 0 < w.re) :
    ‖∫ t : ℝ in Ioi 0,
        (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
      (Real.cos (w.arg / 2))⁻¹ ^ 3 *
        (∫ t : ℝ in Ioi 0,
          periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hMassInt := integrableOn_periodicTentWeight_div_cube
    ‖w‖ (norm_pos_iff.2 hw0)
  have hCos : 0 < Real.cos (w.arg / 2) := by
    exact lt_of_lt_of_le
      (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num))
      (cos_half_arg_lower w hw)
  have hSectorNonneg : 0 ≤ (Real.cos (w.arg / 2))⁻¹ ^ 3 := by
    positivity
  calc
    ‖∫ t : ℝ in Ioi 0,
        (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
        ∫ t : ℝ in Ioi 0,
          (Real.cos (w.arg / 2))⁻¹ ^ 3 *
            (periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) := by
      apply norm_integral_le_of_norm_le (hMassInt.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_periodicTentWeight_mul_inv_cube_le
        w hw t (mem_Ioi.mp ht).le
    _ = (Real.cos (w.arg / 2))⁻¹ ^ 3 *
        (∫ t : ℝ in Ioi 0,
          periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) := by
      rw [integral_const_mul]

/-- The exact first-neglected-term estimate follows from the literal
Euler--Maclaurin tent-kernel representation together with its positive-real
mass bound.  These are now the only two analytic inputs in this route. -/
theorem first_neglected_term_of_eulerMaclaurin_tent
    (hRepresentation : ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Ioi 0,
          (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3))
    (hRealMass : ∀ r : ℝ, 0 < r →
      ∫ t : ℝ in Ioi 0,
          periodicTentWeight t * (1 / (r + t) ^ 3) ≤
        1 / (12 * r ^ 2)) :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 := by
  intro w hw
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hMass := hRealMass ‖w‖ (norm_pos_iff.2 hw0)
  have hCos : 0 < Real.cos (w.arg / 2) := by
    exact lt_of_lt_of_le
      (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num))
      (cos_half_arg_lower w hw)
  have hSectorNonneg : 0 ≤ (Real.cos (w.arg / 2))⁻¹ ^ 3 := by
    positivity
  rw [hRepresentation w hw, norm_neg]
  calc
    ‖∫ t : ℝ in Ioi 0,
        (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3‖ ≤
        (Real.cos (w.arg / 2))⁻¹ ^ 3 *
          (∫ t : ℝ in Ioi 0,
            periodicTentWeight t * (1 / (‖w‖ + t) ^ 3)) :=
      norm_periodicTentWeight_integral_le_real_mass w hw
    _ ≤ (Real.cos (w.arg / 2))⁻¹ ^ 3 *
        (1 / (12 * ‖w‖ ^ 2)) := by
      gcongr
    _ = ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) /
        ‖w‖ ^ 2 := by ring

/-- The Euler--Maclaurin tent route immediately supplies the exact global
quadratic remainder constant consumed by the cutoff-13 diagonal. -/
theorem quadratic_remainder_bound_of_eulerMaclaurin_tent
    (hRepresentation : ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Ioi 0,
          (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3))
    (hRealMass : ∀ r : ℝ, 0 < r →
      ∫ t : ℝ in Ioi 0,
          periodicTentWeight t * (1 / (r + t) ^ 3) ≤
        1 / (12 * r ^ 2)) :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2 :=
  quadratic_remainder_bound_of_first_neglected_term
    (first_neglected_term_of_eulerMaclaurin_tent hRepresentation hRealMass)

end RiemannCvs.DigammaEulerMaclaurin
