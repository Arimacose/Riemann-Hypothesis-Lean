import RiemannCvs.DigammaQuadraticRemainder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Order.Floor

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

/-- Inverse-cubic form of
    `norm_add_nonneg_real_ge_cos_half_arg`. -/
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

/-! ## Closing the positive-real tent mass -/

/-- A twice-vanishing potential whose second derivative is the centered tent
weight `x * (1 - x) - 1/6`. -/
private noncomputable def tentPotential (x : ℝ) : ℝ :=
  -(x ^ 2 * (1 - x) ^ 2) / 12

private noncomputable def tentSlope (x : ℝ) : ℝ :=
  -(x * (1 - x) * (1 - 2 * x)) / 6

private noncomputable def tentCentered (x : ℝ) : ℝ :=
  x * (1 - x) - 1 / 6

private lemma hasDerivAt_tentPotential (x : ℝ) :
    HasDerivAt tentPotential (tentSlope x) x := by
  unfold tentPotential tentSlope
  convert (((hasDerivAt_id x).pow 2).mul
    (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).pow 2)).neg.div_const 12 using 1
  all_goals norm_num [id_eq, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
  all_goals first | ring | rfl

private lemma hasDerivAt_tentSlope (x : ℝ) :
    HasDerivAt tentSlope (tentCentered x) x := by
  unfold tentSlope tentCentered
  convert (((hasDerivAt_id x).mul
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x))).mul
      ((hasDerivAt_const x 1).sub
        ((hasDerivAt_const x 2).mul (hasDerivAt_id x)))).neg.div_const 6 using 1
  all_goals norm_num [id_eq, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
  all_goals first | ring | rfl

private lemma tentPotential_nonpos (x : ℝ) : tentPotential x ≤ 0 := by
  unfold tentPotential
  have h : 0 ≤ x ^ 2 * (1 - x) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (by norm_num)

private lemma tentPotential_zero :
    tentPotential 0 = 0 ∧ tentPotential 1 = 0 := by
  simp [tentPotential]

private lemma tentSlope_zero : tentSlope 0 = 0 ∧ tentSlope 1 = 0 := by
  simp [tentSlope]

private lemma continuous_tentPotential : Continuous tentPotential :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_tentPotential x).continuousAt

private lemma continuous_tentSlope : Continuous tentSlope :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_tentSlope x).continuousAt

private lemma continuous_tentCentered : Continuous tentCentered := by
  unfold tentCentered
  fun_prop

/-- Twice integrating by parts turns the centered tent error into
`integral tentPotential * f''`, which is nonpositive for convex `f`. -/
private lemma integral_mul_tentCentered_nonpos
    (f f' f'' : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hf'Int : IntervalIntegrable f' volume 0 1)
    (hf''Int : IntervalIntegrable f'' volume 0 1)
    (hf''Nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f'' x) :
    ∫ x in (0 : ℝ)..1, f x * tentCentered x ≤ 0 := by
  have hCenteredInt : IntervalIntegrable tentCentered volume 0 1 :=
    continuous_tentCentered.intervalIntegrable 0 1
  have hSlopeInt : IntervalIntegrable tentSlope volume 0 1 :=
    continuous_tentSlope.intervalIntegrable 0 1
  have hPotentialCont : ContinuousOn tentPotential (uIcc (0 : ℝ) 1) :=
    continuous_tentPotential.continuousOn
  have hfU : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf
  have hf'U : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt f' (f'' x) x := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf'
  have hOne := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) hfU
      (fun x _ => hasDerivAt_tentSlope x) hf'Int hCenteredInt
  have hTwo := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) hf'U
      (fun x _ => hasDerivAt_tentPotential x) hf''Int hSlopeInt
  have hProdInt :
      IntervalIntegrable (fun x => f'' x * tentPotential x) volume 0 1 :=
    hf''Int.mul_continuousOn hPotentialCont
  have hProdNonpos :
      ∫ x in (0 : ℝ)..1, f'' x * tentPotential x ≤ 0 := by
    have h := intervalIntegral.integral_mono_on
      (show (0 : ℝ) ≤ 1 by norm_num) hProdInt
      (continuous_const.intervalIntegrable 0 1) (fun x hx =>
        mul_nonpos_of_nonneg_of_nonpos
          (hf''Nonneg x hx) (tentPotential_nonpos x))
    simpa using h
  rw [tentSlope_zero.1, tentSlope_zero.2] at hOne
  rw [tentPotential_zero.1, tentPotential_zero.2] at hTwo
  simp only [mul_zero, sub_self, zero_sub] at hOne hTwo
  rw [hOne, hTwo]
  linarith

private lemma hasDerivAt_invCube (R x : ℝ) (h : R + x ≠ 0) :
    HasDerivAt (fun y : ℝ => (R + y) ^ (-3 : ℝ))
      (-3 * (R + x) ^ (-4 : ℝ)) x := by
  have hRaw := ((hasDerivAt_const x R).add (hasDerivAt_id x)).rpow_const
    (p := (-3 : ℝ)) (Or.inl h)
  simpa only [Pi.add_apply, id_eq, zero_add, one_mul,
    show (-3 : ℝ) - 1 = -4 by norm_num] using hRaw

private lemma hasDerivAt_invCubeDeriv (R x : ℝ) (h : R + x ≠ 0) :
    HasDerivAt (fun y : ℝ => -3 * (R + y) ^ (-4 : ℝ))
      (12 * (R + x) ^ (-5 : ℝ)) x := by
  have hPow := ((hasDerivAt_const x R).add (hasDerivAt_id x)).rpow_const
    (p := (-4 : ℝ)) (Or.inl h)
  have hPow' : HasDerivAt (fun y : ℝ => (R + y) ^ (-4 : ℝ))
      (-4 * (R + x) ^ (-5 : ℝ)) x := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul,
      show (-4 : ℝ) - 1 = -5 by norm_num] using hPow
  convert HasDerivAt.const_mul (-3 : ℝ) hPow' using 1
  all_goals first | ring | rfl

private lemma hasDerivAt_invCubeSecond (R x : ℝ) (h : R + x ≠ 0) :
    HasDerivAt (fun y : ℝ => 12 * (R + y) ^ (-5 : ℝ))
      (-60 * (R + x) ^ (-6 : ℝ)) x := by
  have hPow := ((hasDerivAt_const x R).add (hasDerivAt_id x)).rpow_const
    (p := (-5 : ℝ)) (Or.inl h)
  have hPow' : HasDerivAt (fun y : ℝ => (R + y) ^ (-5 : ℝ))
      (-5 * (R + x) ^ (-6 : ℝ)) x := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul,
      show (-5 : ℝ) - 1 = -6 by norm_num] using hPow
  convert HasDerivAt.const_mul (12 : ℝ) hPow' using 1
  all_goals first | ring | rfl

/-- On one unit cell the tent-weighted convex kernel is at most its uniform
`1/6` average. -/
private lemma integral_tent_invCube_le_average (R : ℝ) (hR : 0 < R) :
    ∫ x in (0 : ℝ)..1, (x * (1 - x)) * (R + x) ^ (-3 : ℝ) ≤
      (1 / 6 : ℝ) * ∫ x in (0 : ℝ)..1, (R + x) ^ (-3 : ℝ) := by
  let f : ℝ → ℝ := fun x => (R + x) ^ (-3 : ℝ)
  let f' : ℝ → ℝ := fun x => -3 * (R + x) ^ (-4 : ℝ)
  let f'' : ℝ → ℝ := fun x => 12 * (R + x) ^ (-5 : ℝ)
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < R + x := by
    intro x hx
    linarith [hx.1]
  have hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x := by
    intro x hx
    exact hasDerivAt_invCube R x (ne_of_gt (hpos x hx))
  have hf' : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' x) x := by
    intro x hx
    exact hasDerivAt_invCubeDeriv R x (ne_of_gt (hpos x hx))
  have hf'Int : IntervalIntegrable f' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (hf' x (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)).continuousAt.continuousWithinAt
  have hf''Cont : ContinuousOn f'' (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact (hasDerivAt_invCubeSecond R x
      (ne_of_gt (hpos x hx'))).continuousAt.continuousWithinAt
  have hf''Int : IntervalIntegrable f'' volume 0 1 :=
    hf''Cont.intervalIntegrable
  have hf''Nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f'' x := by
    intro x hx
    dsimp [f'']
    have hp : 0 < R + x := hpos x hx
    positivity
  have hCore := integral_mul_tentCentered_nonpos
    f f' f'' hf hf' hf'Int hf''Int hf''Nonneg
  have hfCont : ContinuousOn f (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact (hf x hx').continuousAt.continuousWithinAt
  have hLeftInt : IntervalIntegrable
      (fun x : ℝ => (x * (1 - x)) * f x) volume 0 1 := by
    exact (by fun_prop : Continuous fun x : ℝ =>
      x * (1 - x)).continuousOn.intervalIntegrable.mul_continuousOn hfCont
  have hConstInt :
      IntervalIntegrable (fun x : ℝ => (1 / 6 : ℝ) * f x) volume 0 1 :=
    hfCont.intervalIntegrable.const_mul _
  have hEq :
      (∫ x in (0 : ℝ)..1, f x * tentCentered x) =
        (∫ x in (0 : ℝ)..1, (x * (1 - x)) * f x) -
          (1 / 6 : ℝ) * (∫ x in (0 : ℝ)..1, f x) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hLeftInt hConstInt]
    apply intervalIntegral.integral_congr
    intro x hx
    simp [tentCentered]
    ring
  rw [hEq] at hCore
  dsimp [f] at hCore ⊢
  linarith

private lemma periodicTentWeight_add_nat (x : ℝ) (n : ℕ) :
    periodicTentWeight (x + n) = periodicTentWeight x := by
  simp [periodicTentWeight]

private lemma periodicTentWeight_eq_on_unitInterval {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    periodicTentWeight x = x * (1 - x) := by
  rcases eq_or_lt_of_le hx.2 with rfl | hx1
  · simp [periodicTentWeight]
  · rw [periodicTentWeight, Int.fract_eq_self.2 ⟨hx.1, hx1⟩]

private lemma interval_periodicTentWeight_invCube_le_average
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∫ t in (n : ℝ)..(n + 1 : ℝ),
        periodicTentWeight t * (r + t) ^ (-3 : ℝ) ≤
      (1 / 6 : ℝ) * ∫ t in (n : ℝ)..(n + 1 : ℝ),
        (r + t) ^ (-3 : ℝ) := by
  have hR : 0 < r + (n : ℝ) := by positivity
  have hCell := integral_tent_invCube_le_average (r + (n : ℝ)) hR
  have hLeft :
      (∫ t in (n : ℝ)..(n + 1 : ℝ),
        periodicTentWeight t * (r + t) ^ (-3 : ℝ)) =
      ∫ x in (0 : ℝ)..1,
        (x * (1 - x)) * (r + (n : ℝ) + x) ^ (-3 : ℝ) := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          periodicTentWeight (x + n) * (r + (x + n)) ^ (-3 : ℝ) := by
        simpa [add_comm] using
          (intervalIntegral.integral_comp_add_right
            (a := (0 : ℝ)) (b := 1)
            (fun t : ℝ => periodicTentWeight t *
              (r + t) ^ (-3 : ℝ)) (n : ℝ)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        change periodicTentWeight (x + (n : ℝ)) *
            (r + (x + (n : ℝ))) ^ (-3 : ℝ) =
          (x * (1 - x)) * (r + (n : ℝ) + x) ^ (-3 : ℝ)
        rw [periodicTentWeight_add_nat,
          periodicTentWeight_eq_on_unitInterval (by
            simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)]
        congr 2
        ring
  have hRight :
      (∫ t in (n : ℝ)..(n + 1 : ℝ), (r + t) ^ (-3 : ℝ)) =
      ∫ x in (0 : ℝ)..1, (r + (n : ℝ) + x) ^ (-3 : ℝ) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (r + (x + n)) ^ (-3 : ℝ) := by
        simpa [add_comm] using
          (intervalIntegral.integral_comp_add_right
            (a := (0 : ℝ)) (b := 1)
            (fun t : ℝ => (r + t) ^ (-3 : ℝ)) (n : ℝ)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (r + (x + (n : ℝ))) ^ (-3 : ℝ) =
          (r + (n : ℝ) + x) ^ (-3 : ℝ)
        rw [show r + (x + (n : ℝ)) = r + (n : ℝ) + x by ring]
  rw [hLeft, hRight]
  exact hCell

private lemma continuous_periodicTentWeight : Continuous periodicTentWeight := by
  have hPoly : ContinuousOn (fun x : ℝ => x * (1 - x)) (Icc 0 1) :=
    (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn
  have hComp := hPoly.comp_fract'' (by norm_num)
  change Continuous (fun x : ℝ => Int.fract x * (1 - Int.fract x))
  simpa [Function.comp_def] using hComp

private lemma intervalIntegrable_periodicTentWeight_invCube
    (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) :
    IntervalIntegrable
      (fun t : ℝ => periodicTentWeight t * (r + t) ^ (-3 : ℝ))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact continuous_periodicTentWeight.continuousOn.mul (by
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hab] at hx
      exact ha.trans hx.1
    exact (hasDerivAt_invCube r x
      (ne_of_gt (by linarith))).continuousAt.continuousWithinAt)

private lemma intervalIntegrable_invCube
    (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) :
    IntervalIntegrable (fun t : ℝ => (r + t) ^ (-3 : ℝ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans hx.1
  exact (hasDerivAt_invCube r x
    (ne_of_gt (by linarith))).continuousAt.continuousWithinAt

private lemma finite_interval_periodicTentWeight_invCube_le_average
    (r : ℝ) (hr : 0 < r) : ∀ N : ℕ,
    ∫ t in (0 : ℝ)..(N : ℝ),
        periodicTentWeight t * (r + t) ^ (-3 : ℝ) ≤
      (1 / 6 : ℝ) * ∫ t in (0 : ℝ)..(N : ℝ),
        (r + t) ^ (-3 : ℝ)
  | 0 => by simp
  | N + 1 => by
      have hPrev :=
        finite_interval_periodicTentWeight_invCube_le_average r hr N
      have hCell := interval_periodicTentWeight_invCube_le_average r hr N
      have hgPrev := intervalIntegrable_periodicTentWeight_invCube r hr
        0 (N : ℝ) (by positivity) (by norm_num)
      have hgCell := intervalIntegrable_periodicTentWeight_invCube r hr
        (N : ℝ) (N + 1 : ℝ) (by norm_num) (by positivity)
      have hfPrev := intervalIntegrable_invCube r hr
        0 (N : ℝ) (by positivity) (by norm_num)
      have hfCell := intervalIntegrable_invCube r hr
        (N : ℝ) (N + 1 : ℝ) (by norm_num) (by positivity)
      calc
        (∫ t in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            periodicTentWeight t * (r + t) ^ (-3 : ℝ)) =
            (∫ t in (0 : ℝ)..(N : ℝ),
              periodicTentWeight t * (r + t) ^ (-3 : ℝ)) +
            (∫ t in (N : ℝ)..(N + 1 : ℝ),
              periodicTentWeight t * (r + t) ^ (-3 : ℝ)) := by
              norm_num only [Nat.cast_add, Nat.cast_one]
              exact (intervalIntegral.integral_add_adjacent_intervals
                hgPrev hgCell).symm
        _ ≤ (1 / 6 : ℝ) * (∫ t in (0 : ℝ)..(N : ℝ),
              (r + t) ^ (-3 : ℝ)) +
            (1 / 6 : ℝ) * (∫ t in (N : ℝ)..(N + 1 : ℝ),
              (r + t) ^ (-3 : ℝ)) := add_le_add hPrev hCell
        _ = (1 / 6 : ℝ) * ∫ t in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
              (r + t) ^ (-3 : ℝ) := by
              norm_num only [Nat.cast_add, Nat.cast_one]
              rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
                hfPrev hfCell]

private lemma integrableOn_periodicTentWeight_mul_rpow_neg_three
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun t : ℝ => periodicTentWeight t * (r + t) ^ (-3 : ℝ))
      (Ioi 0) := by
  have h := integrableOn_periodicTentWeight_div_cube r hr
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change periodicTentWeight t * (1 / (r + t) ^ 3) =
    periodicTentWeight t * (r + t) ^ (-3 : ℝ)
  rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hrt]
  simp [one_div]

private lemma integrableOn_rpow_neg_three_add_Ioi_zero
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (r + t) ^ (-3 : ℝ)) (Ioi 0) := by
  have h := integrableOn_one_div_cube_add_Ioi_zero r hr
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change 1 / (r + t) ^ 3 = (r + t) ^ (-3 : ℝ)
  rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hrt]
  simp [one_div]

private lemma integral_periodicTentWeight_rpow_le_average
    (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, periodicTentWeight t * (r + t) ^ (-3 : ℝ) ≤
      (1 / 6 : ℝ) * ∫ t : ℝ in Ioi 0, (r + t) ^ (-3 : ℝ) := by
  have hG := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_periodicTentWeight_mul_rpow_neg_three r hr)
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hF0 := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_rpow_neg_three_add_Ioi_zero r hr)
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hF := hF0.const_mul (1 / 6 : ℝ)
  exact le_of_tendsto_of_tendsto hG hF
    (Eventually.of_forall
      (finite_interval_periodicTentWeight_invCube_le_average r hr))

private lemma integral_rpow_neg_three_add_Ioi_zero
    (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, (r + t) ^ (-3 : ℝ) = 1 / (2 * r ^ 2) := by
  rw [← integral_one_div_cube_add_Ioi_zero r hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change (r + t) ^ (-3 : ℝ) = 1 / (r + t) ^ 3
  rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hrt]
  simp [one_div]

/-- The positive-real mass required by the complex tent-kernel comparison is
fully closed.  Unit-cell convexity gives the factor `1/6`, and the inverse
cube has total mass `1/(2 r^2)`. -/
theorem periodicTentWeight_real_mass_bound (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0,
        periodicTentWeight t * (1 / (r + t) ^ 3) ≤
      1 / (12 * r ^ 2) := by
  have h := integral_periodicTentWeight_rpow_le_average r hr
  rw [integral_rpow_neg_three_add_Ioi_zero r hr] at h
  have hEq :
      (∫ t : ℝ in Ioi 0,
        periodicTentWeight t * (1 / (r + t) ^ 3)) =
      ∫ t : ℝ in Ioi 0,
        periodicTentWeight t * (r + t) ^ (-3 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
    change periodicTentWeight t * (1 / (r + t) ^ 3) =
      periodicTentWeight t * (r + t) ^ (-3 : ℝ)
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hrt]
    simp [one_div]
  rw [hEq]
  calc
    (∫ t : ℝ in Ioi 0,
        periodicTentWeight t * (r + t) ^ (-3 : ℝ)) ≤
        (1 / 6 : ℝ) * (1 / (2 * r ^ 2)) := h
    _ = 1 / (12 * r ^ 2) := by ring

/-! ## Exact Euler--Maclaurin representation -/

private noncomputable def unitPrimitive (x : ℝ) : ℝ → ℝ :=
  -(fun t : ℝ => Real.log (x + t)) -
    (fun _ : ℝ => 2 * x + 1) / (fun t : ℝ => x + t) +
    (fun _ : ℝ => x * (x + 1) / 2) / (fun t : ℝ => x + t) ^ 2

private lemma hasDerivAt_unitPrimitive (x : ℝ) (hx : 0 < x)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (unitPrimitive x)
      (t * (1 - t) / (x + t) ^ 3) t := by
  have hne : x + t ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun u : ℝ => x + u) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).const_add x
  have hlog : HasDerivAt (fun u : ℝ => Real.log (x + u))
      (1 / (x + t)) t := by
    simpa [one_div] using hden.log hne
  have hq1raw := (hasDerivAt_const t (2 * x + 1)).div hden hne
  have hq1 : HasDerivAt
      ((fun _ : ℝ => 2 * x + 1) / (fun u : ℝ => x + u))
      (-(2 * x + 1) / (x + t) ^ 2) t :=
    hq1raw.congr_deriv (by ring)
  have hpow := hden.pow 2
  have hpne : (x + t) ^ 2 ≠ 0 := pow_ne_zero _ hne
  have hq2raw :=
    (hasDerivAt_const t (x * (x + 1) / 2)).div hpow hpne
  have hq2 : HasDerivAt
      ((fun _ : ℝ => x * (x + 1) / 2) / (fun u : ℝ => x + u) ^ 2)
      (-(x * (x + 1)) / (x + t) ^ 3) t := by
    apply hq2raw.congr_deriv
    dsimp only [Pi.pow_apply]
    field_simp [hne]
    ring
  unfold unitPrimitive
  apply ((hlog.neg.sub hq1).add hq2).congr_deriv
  field_simp [hne]
  ring

private lemma unit_integral (x : ℝ) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..1, t * (1 - t) / (x + t) ^ 3) =
      Real.log x - Real.log (x + 1) + 1 / (2 * x) + 1 / (2 * (x + 1)) := by
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (unitPrimitive x)
        (t * (1 - t) / (x + t) ^ 3) t := by
    intro t ht
    exact hasDerivAt_unitPrimitive x hx t (by
      rw [uIcc_of_le (by norm_num)] at ht
      exact ht.1)
  have hint : IntervalIntegrable
      (fun t : ℝ => t * (1 - t) / (x + t) ^ 3) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
      ((continuous_id.mul (continuous_const.sub continuous_id)).continuousOn)
      ((continuous_const.add continuous_id).pow 3).continuousOn
    intro t ht
    change (x + t) ^ 3 ≠ 0
    apply pow_ne_zero
    rw [uIcc_of_le (by norm_num)] at ht
    exact ne_of_gt (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  simp only [unitPrimitive, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.div_apply, Pi.pow_apply]
  field_simp [ne_of_gt hx, ne_of_gt (by linarith : 0 < x + 1)]
  ring


private noncomputable def realTentKernel (x : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    periodicTentWeight t * (1 / (x + t) ^ 3)


private lemma realTentKernel_tail_translation (x : ℝ) :
    realTentKernel (x + 1) =
      ∫ t : ℝ in Ioi 1,
        periodicTentWeight t * (1 / (x + t) ^ 3) := by
  have hmp := (measurePreserving_add_right volume (1 : ℝ)).restrict_preimage_emb
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding (Ioi (1 : ℝ))
  have htrans := hmp.integral_comp
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding
    (fun t : ℝ => periodicTentWeight t * (1 / (x + t) ^ 3))
  rw [preimage_add_const_Ioi] at htrans
  norm_num at htrans
  unfold realTentKernel
  calc
    (∫ t : ℝ in Ioi 0,
      periodicTentWeight t * (1 / (x + 1 + t) ^ 3)) =
        ∫ t : ℝ in Ioi 0,
          periodicTentWeight (t + 1) * (1 / (x + (t + 1)) ^ 3) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change periodicTentWeight t * (1 / (x + 1 + t) ^ 3) =
        periodicTentWeight (t + 1) * (1 / (x + (t + 1)) ^ 3)
      rw [show periodicTentWeight (t + 1) = periodicTentWeight t by
        simpa using periodicTentWeight_add_nat t 1]
      congr 3
      ring
    _ = _ := by simpa [one_div] using htrans

private lemma realTentKernel_add_one (x : ℝ) (hx : 0 < x) :
    realTentKernel (x + 1) = realTentKernel x -
      (Real.log x - Real.log (x + 1) +
        1 / (2 * x) + 1 / (2 * (x + 1))) := by
  let f : ℝ → ℝ := fun t =>
    periodicTentWeight t * (1 / (x + t) ^ 3)
  have hInt : IntegrableOn f (Ioi 0) := by
    exact integrableOn_periodicTentWeight_div_cube x hx
  have hIoc : IntegrableOn f (Ioc (0 : ℝ) 1) :=
    hInt.mono_set (by intro t ht; exact ht.1)
  have hIoi : IntegrableOn f (Ioi (1 : ℝ)) :=
    hInt.mono_set (Ioi_subset_Ioi (by norm_num))
  have hDis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [disjoint_left]
    intro t ht
    exact not_lt_of_ge ht.2
  have hSplit := setIntegral_union₀ hDis.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hIoc hIoi
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hSplit
  have hUnitInterval :
      (∫ t in (0 : ℝ)..1, f t) =
        Real.log x - Real.log (x + 1) +
          1 / (2 * x) + 1 / (2 * (x + 1)) := by
    calc
      (∫ t in (0 : ℝ)..1, f t) =
          ∫ t in (0 : ℝ)..1, t * (1 - t) / (x + t) ^ 3 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        rw [show f t = periodicTentWeight t * (1 / (x + t) ^ 3) by rfl,
          periodicTentWeight_eq_on_unitInterval ht]
        ring
      _ = _ := unit_integral x hx
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hUnitInterval
  rw [realTentKernel_tail_translation x]
  unfold realTentKernel
  change (∫ t : ℝ in Ioi 1, f t) =
    (∫ t : ℝ in Ioi 0, f t) - _
  rw [hSplit, hUnitInterval]
  ring

private noncomputable def realDigammaTent (x : ℝ) : ℝ :=
  Real.log x - 1 / (2 * x) - realTentKernel x

private lemma realDigammaTent_add_one (x : ℝ) (hx : 0 < x) :
    realDigammaTent (x + 1) = realDigammaTent x + 1 / x := by
  rw [realDigammaTent, realDigammaTent, realTentKernel_add_one x hx]
  ring

private lemma deriv_Complex_Gamma_ofReal (x : ℝ) (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma (x : ℂ) (by
      intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (by
      intro m hm
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have hCReal := hC.hasDerivAt.comp_ofReal
  have hRCast := hR.hasDerivAt.ofReal_comp
  have hCReal' : HasDerivAt (fun y : ℝ => (Real.Gamma y : ℂ))
      (deriv Complex.Gamma (x : ℂ)) x := by
    simpa only [Complex.Gamma_ofReal] using hCReal
  exact hCReal'.unique hRCast

private lemma digamma_ofReal_eq_deriv_logGamma (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) =
      ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply,
    deriv_Complex_Gamma_ofReal x hx, Complex.Gamma_ofReal]
  rw [Function.comp_def, deriv.log
    (Real.differentiableAt_Gamma (by
      intro m hm
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)) (Real.Gamma_pos_of_pos hx).ne']
  exact (Complex.ofReal_div _ _).symm

private noncomputable def logGammaReal : ℝ → ℝ :=
  Real.log ∘ Real.Gamma

private lemma logGammaReal_add_one (x : ℝ) (hx : 0 < x) :
    logGammaReal (x + 1) = logGammaReal x + Real.log x := by
  change Real.log (Real.Gamma (x + 1)) =
    Real.log (Real.Gamma x) + Real.log x
  rw [Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  rw [add_comm]

private lemma differentiableAt_logGammaReal (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ logGammaReal x := by
  exact (Real.differentiableAt_Gamma (by
    intro m hm
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)).log (Real.Gamma_pos_of_pos hx).ne'

private lemma log_y_sub_one_le_deriv_logGammaReal (y : ℝ) (hy : 1 < y) :
    Real.log (y - 1) ≤ deriv logGammaReal y := by
  have hc : ConvexOn ℝ (Ioi 0) logGammaReal :=
    Real.convexOn_log_Gamma
  have hslope : slope logGammaReal (y - 1) y = Real.log (y - 1) := by
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one,
      show y = (y - 1) + 1 by ring,
      logGammaReal_add_one (y - 1) (by linarith)]
    ring
  rw [← hslope]
  exact hc.slope_le_deriv
    (mem_Ioi.mpr (by linarith : 0 < y - 1))
    (mem_Ioi.mpr (by linarith : 0 < y))
    (by linarith) (differentiableAt_logGammaReal y (by linarith))

private lemma deriv_logGammaReal_le_log (y : ℝ) (hy : 0 < y) :
    deriv logGammaReal y ≤ Real.log y := by
  have hc : ConvexOn ℝ (Ioi 0) logGammaReal :=
    Real.convexOn_log_Gamma
  refine (hc.deriv_le_slope
    (mem_Ioi.mpr hy)
    (mem_Ioi.mpr (by linarith : 0 < y + 1))
    (by linarith) (differentiableAt_logGammaReal y hy)).trans (le_of_eq ?_)
  rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one,
    logGammaReal_add_one y hy, add_sub_cancel_left]

private lemma neg_inv_le_log_sub_log (y : ℝ) (hy : 1 < y) :
    -1 / (y - 1) ≤ Real.log (y - 1) - Real.log y := by
  have hy0 : y ≠ 0 := ne_of_gt (by linarith)
  have hym0 : y - 1 ≠ 0 := ne_of_gt (by linarith)
  have hratio : 0 < y / (y - 1) := div_pos (by linarith) (by linarith)
  have h := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hy0 hym0] at h
  have hratEq : y / (y - 1) - 1 = 1 / (y - 1) := by
    field_simp [hym0]
    ring
  rw [hratEq] at h
  calc
    -1 / (y - 1) = -(1 / (y - 1)) := by ring
    _ ≤ -(Real.log y - Real.log (y - 1)) := neg_le_neg h
    _ = Real.log (y - 1) - Real.log y := by ring

private lemma tendsto_deriv_logGammaReal_sub_log_natTranslate
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      deriv logGammaReal (x + (n : ℝ)) - Real.log (x + (n : ℝ)))
      atTop (𝓝 0) := by
  have hBase : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hDen : Tendsto (fun n : ℕ => x + (n : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hBase)
  have hLower : Tendsto (fun n : ℕ => -1 / (x + (n : ℝ) - 1))
      atTop (𝓝 0) := hDen.const_div_atTop (-1)
  have hUpper : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  refine hLower.squeeze' hUpper ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hy : 1 < x + (n : ℝ) := by
      have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
      linarith
    calc
      -1 / (x + (n : ℝ) - 1) ≤
          Real.log (x + (n : ℝ) - 1) - Real.log (x + (n : ℝ)) :=
        neg_inv_le_log_sub_log (x + (n : ℝ)) hy
      _ ≤ deriv logGammaReal (x + (n : ℝ)) -
          Real.log (x + (n : ℝ)) := by
        linarith [log_y_sub_one_le_deriv_logGammaReal
          (x + (n : ℝ)) hy]
  · filter_upwards with n
    linarith [deriv_logGammaReal_le_log (x + (n : ℝ)) (by positivity)]

private lemma realTentKernel_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ realTentKernel x := by
  unfold realTentKernel
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have hxt : 0 < x + t := by linarith [mem_Ioi.mp ht]
  exact mul_nonneg (periodicTentWeight_nonneg t) (by positivity)

private lemma tendsto_realTentKernel_natTranslate (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => realTentKernel (x + (n : ℝ)))
      atTop (𝓝 0) := by
  have hY : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hInv : Tendsto (fun n : ℕ => 1 / (x + (n : ℝ)))
      atTop (𝓝 0) := hY.const_div_atTop 1
  have hMajorRaw := (hInv.pow 2).const_mul (1 / 12 : ℝ)
  have hMajor : Tendsto
      (fun n : ℕ => (1 / 12 : ℝ) / (x + (n : ℝ)) ^ 2)
      atTop (𝓝 0) := by
    convert hMajorRaw using 1
    · funext n
      have hyn : x + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
      field_simp [hyn]
    · ring
  refine squeeze_zero' (g := fun n : ℕ =>
      (1 / 12 : ℝ) / (x + (n : ℝ)) ^ 2) ?_ ?_ hMajor
  · exact Eventually.of_forall fun n =>
      realTentKernel_nonneg (x + (n : ℝ)) (by positivity)
  · exact Eventually.of_forall fun n => by
      have h := periodicTentWeight_real_mass_bound
        (x + (n : ℝ)) (by positivity)
      change realTentKernel (x + (n : ℝ)) ≤
        (1 / 12 : ℝ) / (x + (n : ℝ)) ^ 2
      unfold realTentKernel
      calc
        (∫ t : ℝ in Ioi 0,
            periodicTentWeight t * (1 / (x + (n : ℝ) + t) ^ 3)) ≤
            1 / (12 * (x + (n : ℝ)) ^ 2) := h
        _ = (1 / 12 : ℝ) / (x + (n : ℝ)) ^ 2 := by
          have hyn : x + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
          field_simp [hyn]

private lemma tendsto_realDigammaTent_sub_log_natTranslate
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      realDigammaTent (x + (n : ℝ)) - Real.log (x + (n : ℝ)))
      atTop (𝓝 0) := by
  have hY : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hTwoY : Tendsto (fun n : ℕ => 2 * (x + (n : ℝ))) atTop atTop :=
    hY.const_mul_atTop (by norm_num)
  have hHalf : Tendsto (fun n : ℕ => 1 / (2 * (x + (n : ℝ))))
      atTop (𝓝 0) := hTwoY.const_div_atTop 1
  have hKernel := tendsto_realTentKernel_natTranslate x hx
  have hCombined := hHalf.neg.sub hKernel
  convert hCombined using 1
  · funext n
    simp only [realDigammaTent]
    ring
  · ring

private lemma deriv_logGammaReal_add_one (x : ℝ) (hx : 0 < x) :
    deriv logGammaReal (x + 1) = deriv logGammaReal x + 1 / x := by
  have hEq :
      (fun y : ℝ => logGammaReal (y + 1)) =ᶠ[𝓝 x]
        (fun y : ℝ => logGammaReal y + Real.log y) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact logGammaReal_add_one y hy
  have hDer := hEq.deriv_eq
  rw [deriv_comp_add_const, deriv_fun_add
    (differentiableAt_logGammaReal x hx)
    (Real.hasDerivAt_log hx.ne').differentiableAt,
    Real.deriv_log] at hDer
  simpa [one_div] using hDer

private lemma digammaTent_difference_natTranslate (x : ℝ) (hx : 0 < x) :
    ∀ n : ℕ,
      deriv logGammaReal (x + (n : ℝ)) -
          realDigammaTent (x + (n : ℝ)) =
        deriv logGammaReal x - realDigammaTent x
  | 0 => by norm_num
  | n + 1 => by
      rw [Nat.cast_add, Nat.cast_one,
        show x + ((n : ℝ) + 1) = (x + (n : ℝ)) + 1 by ring,
        deriv_logGammaReal_add_one (x + (n : ℝ)) (by positivity),
        realDigammaTent_add_one (x + (n : ℝ)) (by positivity)]
      calc
        deriv logGammaReal (x + (n : ℝ)) + 1 / (x + (n : ℝ)) -
            (realDigammaTent (x + (n : ℝ)) + 1 / (x + (n : ℝ))) =
          deriv logGammaReal (x + (n : ℝ)) -
            realDigammaTent (x + (n : ℝ)) := by ring
        _ = _ := digammaTent_difference_natTranslate x hx n

private lemma deriv_logGammaReal_eq_realDigammaTent (x : ℝ) (hx : 0 < x) :
    deriv logGammaReal x = realDigammaTent x := by
  have hDig := tendsto_deriv_logGammaReal_sub_log_natTranslate x hx
  have hTent := tendsto_realDigammaTent_sub_log_natTranslate x hx
  have hDiff : Tendsto (fun n : ℕ =>
      deriv logGammaReal (x + (n : ℝ)) -
        realDigammaTent (x + (n : ℝ))) atTop (𝓝 0) := by
    convert hDig.sub hTent using 1 <;> ring
  have hConst : Tendsto (fun _ : ℕ =>
      deriv logGammaReal x - realDigammaTent x) atTop
      (𝓝 (deriv logGammaReal x - realDigammaTent x)) := tendsto_const_nhds
  have hConstZero : Tendsto (fun _ : ℕ =>
      deriv logGammaReal x - realDigammaTent x) atTop (𝓝 0) := by
    apply hDiff.congr'
    exact Eventually.of_forall fun n =>
      digammaTent_difference_natTranslate x hx n
  have hZero := tendsto_nhds_unique hConst hConstZero
  linarith

private lemma complexTentKernel_ofReal (x : ℝ) :
    (∫ t : ℝ in Ioi 0,
      (periodicTentWeight t : ℂ) *
        ((x : ℂ) + (t : ℂ))⁻¹ ^ 3) =
      (realTentKernel x : ℂ) := by
  unfold realTentKernel
  calc
    (∫ t : ℝ in Ioi 0,
      (periodicTentWeight t : ℂ) *
        ((x : ℂ) + (t : ℂ))⁻¹ ^ 3) =
        ∫ t : ℝ in Ioi 0,
          ((periodicTentWeight t * (1 / (x + t) ^ 3) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      push_cast
      simp [one_div]
    _ = _ := integral_ofReal

private lemma digamma_tent_representation_ofReal (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) -
        (Complex.log (x : ℂ) - 1 / (2 * (x : ℂ))) =
      -(∫ t : ℝ in Ioi 0,
        (periodicTentWeight t : ℂ) *
          ((x : ℂ) + (t : ℂ))⁻¹ ^ 3) := by
  rw [digamma_ofReal_eq_deriv_logGamma x hx]
  have hDer : deriv (Real.log ∘ Real.Gamma) x = realDigammaTent x := by
    simpa only [logGammaReal] using
      deriv_logGammaReal_eq_realDigammaTent x hx
  rw [hDer, complexTentKernel_ofReal x]
  unfold realDigammaTent
  rw [← Complex.ofReal_log hx.le]
  push_cast
  ring

private noncomputable def complexTentKernel (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3

private lemma integrableOn_complexTentKernel_integrand
    (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ =>
      (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3) (Ioi 0) := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hMass := integrableOn_periodicTentWeight_div_cube
    ‖w‖ (norm_pos_iff.2 hw0)
  have hMajor := hMass.const_mul
    ((Real.cos (w.arg / 2))⁻¹ ^ 3)
  apply hMajor.mono'
  · exact (measurable_periodicTentWeight.complex_ofReal.mul
      ((measurable_const.add measurable_id.complex_ofReal).inv.pow_const 3)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_periodicTentWeight_mul_inv_cube_le
      w hw t (mem_Ioi.mp ht).le

private noncomputable def complexTentKernelDerivIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  (-3 : ℂ) * (periodicTentWeight t : ℂ) *
    (w + (t : ℂ))⁻¹ ^ 4

private lemma integrableOn_one_div_four_add_Ioi_zero
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => 1 / (r + t) ^ 4) (Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt
    (a := (-4 : ℝ)) (c := 0) (m := r) (by norm_num) (by simpa using hr)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  have hrt : 0 ≤ r + t := by linarith [mem_Ioi.mp ht]
  change (t + r) ^ (-4 : ℝ) = 1 / (r + t) ^ 4
  rw [add_comm t r, show (-4 : ℝ) = -(4 : ℝ) by norm_num,
    Real.rpow_neg hrt]
  simp [one_div]

private lemma re_ge_half_of_mem_ball
    (w0 w : ℂ) (_hw0 : 0 < w0.re)
    (hw : w ∈ Metric.ball w0 (w0.re / 2)) :
    w0.re / 2 < w.re := by
  have hNorm : ‖w - w0‖ < w0.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hReNorm : |w.re - w0.re| ≤ ‖w - w0‖ := by
    simpa using Complex.abs_re_le_norm (w - w0)
  have hLower := neg_abs_le (w.re - w0.re)
  linarith

private lemma norm_inv_four_add_real_le
    (w0 w : ℂ) (hw0 : 0 < w0.re)
    (hw : w ∈ Metric.ball w0 (w0.re / 2))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(w + (t : ℂ))⁻¹ ^ 4‖ ≤
      1 / (w0.re / 2 + t) ^ 4 := by
  have hwRe := re_ge_half_of_mem_ball w0 w hw0 hw
  have hRT : 0 < w0.re / 2 + t := by linarith
  have hDen : w0.re / 2 + t ≤ ‖w + (t : ℂ)‖ := by
    calc
      w0.re / 2 + t ≤ w.re + t := by linarith
      _ = (w + (t : ℂ)).re := by simp
      _ ≤ |(w + (t : ℂ)).re| := le_abs_self _
      _ ≤ ‖w + (t : ℂ)‖ := Complex.abs_re_le_norm _
  have hPow := pow_le_pow_left₀ (le_of_lt hRT) hDen 4
  have hInv := one_div_le_one_div_of_le (pow_pos hRT 4) hPow
  rw [norm_pow, norm_inv, inv_pow]
  simpa [one_div] using hInv

private lemma norm_complexTentKernelDerivIntegrand_le
    (w0 w : ℂ) (hw0 : 0 < w0.re)
    (hw : w ∈ Metric.ball w0 (w0.re / 2))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖complexTentKernelDerivIntegrand w t‖ ≤
      (3 / 4 : ℝ) * (1 / (w0.re / 2 + t) ^ 4) := by
  have hInv := norm_inv_four_add_real_le w0 w hw0 hw t ht
  have hwRe := re_ge_half_of_mem_ball w0 w hw0 hw
  have hDen : w0.re / 2 + t ≤ ‖w + (t : ℂ)‖ := by
    calc
      w0.re / 2 + t ≤ w.re + t := by linarith
      _ = (w + (t : ℂ)).re := by simp
      _ ≤ |(w + (t : ℂ)).re| := le_abs_self _
      _ ≤ ‖w + (t : ℂ)‖ := Complex.abs_re_le_norm _
  unfold complexTentKernelDerivIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (periodicTentWeight_nonneg t)]
  norm_num
  calc
    3 * periodicTentWeight t * (‖w + (t : ℂ)‖ ^ 4)⁻¹ ≤
        3 * (1 / 4 : ℝ) * ((w0.re / 2 + t) ^ 4)⁻¹ := by
      gcongr
      · exact periodicTentWeight_le_one_fourth t
    _ = (3 / 4 : ℝ) * ((w0.re / 2 + t) ^ 4)⁻¹ := by ring

private lemma hasDerivAt_complexTentKernel_integrand
    (w : ℂ) (t : ℝ) (hwt : w + (t : ℂ) ≠ 0) :
    HasDerivAt
      (fun z : ℂ => (periodicTentWeight t : ℂ) *
        (z + (t : ℂ))⁻¹ ^ 3)
      (complexTentKernelDerivIntegrand w t) w := by
  have hden : HasDerivAt (fun z : ℂ => z + (t : ℂ)) 1 w := by
    simpa only [id_eq] using (hasDerivAt_id w).add_const (t : ℂ)
  have hinv := hden.inv hwt
  have hpow := hinv.pow 3
  have hraw := hpow.const_mul (periodicTentWeight t : ℂ)
  apply hraw.congr_deriv
  unfold complexTentKernelDerivIntegrand
  simp only [Pi.inv_apply, Nat.cast_ofNat, Nat.reduceSub]
  field_simp [hwt]

private lemma hasDerivAt_complexTentKernel (w0 : ℂ) (hw0 : 0 < w0.re) :
    HasDerivAt complexTentKernel
      (∫ t : ℝ in Ioi 0, complexTentKernelDerivIntegrand w0 t) w0 := by
  let r : ℝ := w0.re / 2
  let s : Set ℂ := Metric.ball w0 r
  let F : ℂ → ℝ → ℂ := fun w t =>
    (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3
  let F' : ℂ → ℝ → ℂ := fun w t =>
    complexTentKernelDerivIntegrand w t
  let bound : ℝ → ℝ := fun t =>
    (3 / 4 : ℝ) * (1 / (r + t) ^ 4)
  have hr : 0 < r := by dsimp [r]; linarith
  have hParam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds w0 hr)
    (by
      exact Eventually.of_forall fun w =>
        (measurable_periodicTentWeight.complex_ofReal.mul
          ((measurable_const.add measurable_id.complex_ofReal).inv.pow_const 3)).aestronglyMeasurable)
    (by
      dsimp [F]
      exact integrableOn_complexTentKernel_integrand w0 hw0)
    (by
      dsimp [F', complexTentKernelDerivIntegrand]
      exact ((measurable_const.mul
        measurable_periodicTentWeight.complex_ofReal).mul
          ((measurable_const.add measurable_id.complex_ofReal).inv.pow_const 4)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro w hw
      dsimp [F', bound, r, s]
      exact norm_complexTentKernelDerivIntegrand_le
        w0 w hw0 hw t (mem_Ioi.mp ht).le)
    (by
      dsimp [bound]
      exact (integrableOn_one_div_four_add_Ioi_zero r hr).const_mul (3 / 4 : ℝ))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro w hw
      dsimp [F, F', s]
      apply hasDerivAt_complexTentKernel_integrand
      apply Complex.ne_zero_of_re_pos
      have hwRe := re_ge_half_of_mem_ball w0 w hw0 hw
      simp
      linarith [mem_Ioi.mp ht])
  convert hParam.2 using 1 <;> rfl

private lemma differentiableAt_complexTentKernel (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ complexTentKernel w :=
  (hasDerivAt_complexTentKernel w hw).differentiableAt

private lemma gamma_analyticAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hGammaOn : DifferentiableOn ℂ Complex.Gamma U := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro m hwm
    have hneg : w.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hwm
    change 0 < w.re at hw
    rw [hneg] at hw
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hw
  exact hGammaOn.analyticAt (hUOpen.mem_nhds hz)

private lemma digamma_analyticAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hGamma := gamma_analyticAt_of_re_pos z hz
  rw [Complex.digamma_def]
  simpa only [logDeriv] using
    hGamma.deriv.div hGamma (Complex.Gamma_ne_zero_of_re_pos hz)

private lemma digamma_asymptotic_model_differentiableAt
    (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun u : ℂ => Complex.log u - 1 / (2 * u)) w := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hLog : DifferentiableAt ℂ Complex.log w :=
    Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hDen : DifferentiableAt ℂ (fun u : ℂ => 2 * u) w := by
    fun_prop
  have hRecip : DifferentiableAt ℂ (fun u : ℂ => 1 / (2 * u)) w := by
    exact (differentiableAt_const (c := (1 : ℂ))).div hDen
      (mul_ne_zero (by norm_num) hw0)
  exact hLog.sub hRecip

private lemma digamma_remainder_differentiableOn_re_pos :
    DifferentiableOn ℂ
      (fun w : ℂ => Complex.digamma w -
        (Complex.log w - 1 / (2 * w)))
      {w : ℂ | 0 < w.re} := by
  intro w hw
  exact ((digamma_analyticAt_of_re_pos w hw).differentiableAt.sub
    (digamma_asymptotic_model_differentiableAt w hw)).differentiableWithinAt

private lemma neg_complexTentKernel_differentiableOn_re_pos :
    DifferentiableOn ℂ (fun w : ℂ => -complexTentKernel w)
      {w : ℂ | 0 < w.re} := by
  intro w hw
  exact (differentiableAt_complexTentKernel w hw).neg.differentiableWithinAt

private lemma rightHalfPlane_open :
    IsOpen {w : ℂ | 0 < w.re} :=
  Complex.continuous_re.isOpen_preimage _ isOpen_Ioi

private lemma rightHalfPlane_preconnected :
    IsPreconnected {w : ℂ | 0 < w.re} := by
  exact (convex_halfSpace_gt Complex.reCLM.isLinear (0 : ℝ)).isPreconnected

private lemma frequently_positive_real_eq_near_one :
    ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ),
      Complex.digamma z - (Complex.log z - 1 / (2 * z)) =
        -complexTentKernel z := by
  have hRealEventually : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), 0 < x :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left
  have hRealEqEventually : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ),
      Complex.digamma (x : ℂ) -
          (Complex.log (x : ℂ) - 1 / (2 * (x : ℂ))) =
        -complexTentKernel (x : ℂ) := by
    filter_upwards [hRealEventually] with x hx
    simpa only [complexTentKernel] using digamma_tent_representation_ofReal x hx
  have hReal : ∃ᶠ x : ℝ in 𝓝[≠] (1 : ℝ),
      Complex.digamma (x : ℂ) -
          (Complex.log (x : ℂ) - 1 / (2 * (x : ℂ))) =
        -complexTentKernel (x : ℂ) := hRealEqEventually.frequently
  rw [frequently_iff_seq_forall] at hReal ⊢
  obtain ⟨xs, hxs, hxEq⟩ := hReal
  refine ⟨fun n => (xs n : ℂ), ?_, fun n => hxEq n⟩
  rw [tendsto_nhdsWithin_iff] at hxs ⊢
  constructor
  · simpa using (tendsto_ofReal_iff.mpr hxs.1)
  · simpa using hxs.2

/-- Exact Euler--Maclaurin tent representation of the digamma remainder on
    the open right half-plane. -/
theorem digamma_eulerMaclaurin_tent_representation :
    ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Ioi 0,
          (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3) := by
  have hF : AnalyticOnNhd ℂ
      (fun w : ℂ => Complex.digamma w -
        (Complex.log w - 1 / (2 * w)))
      {w : ℂ | 0 < w.re} :=
    digamma_remainder_differentiableOn_re_pos.analyticOnNhd
      rightHalfPlane_open
  have hG : AnalyticOnNhd ℂ (fun w : ℂ => -complexTentKernel w)
      {w : ℂ | 0 < w.re} :=
    neg_complexTentKernel_differentiableOn_re_pos.analyticOnNhd
      rightHalfPlane_open
  have hEq := hF.eqOn_of_preconnected_of_frequently_eq hG
    rightHalfPlane_preconnected
    (z₀ := (1 : ℂ)) (by norm_num)
    frequently_positive_real_eq_near_one
  intro w hw
  simpa only [complexTentKernel] using hEq hw

/-- Once the exact Euler--Maclaurin representation is supplied, the scalar
mass theorem above closes the DLMF first-neglected-term estimate outright. -/
theorem first_neglected_term_of_eulerMaclaurin_tent_representation
    (hRepresentation : ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Ioi 0,
          (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3)) :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 :=
  first_neglected_term_of_eulerMaclaurin_tent hRepresentation
    periodicTentWeight_real_mass_bound

/-- The same one-premise route in the exact global quadratic form consumed
by C13 and V23. -/
theorem quadratic_remainder_bound_of_eulerMaclaurin_tent_representation
    (hRepresentation : ∀ w : ℂ, 0 < w.re →
      Complex.digamma w - (Complex.log w - 1 / (2 * w)) =
        -(∫ t : ℝ in Ioi 0,
          (periodicTentWeight t : ℂ) * (w + (t : ℂ))⁻¹ ^ 3)) :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2 :=
  quadratic_remainder_bound_of_eulerMaclaurin_tent hRepresentation
    periodicTentWeight_real_mass_bound

/-- The DLMF first-neglected-term bound, now with its exact integral
representation and scalar tent mass both discharged inside Lean. -/
theorem digamma_first_neglected_term_bound :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2 :=
  first_neglected_term_of_eulerMaclaurin_tent_representation
    digamma_eulerMaclaurin_tent_representation

/-- The premise-free global quadratic digamma remainder consumed by the
cutoff-13 and V23 Archimedean diagonal estimates. -/
theorem digamma_quadratic_remainder_bound :
    ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2 :=
  quadratic_remainder_bound_of_eulerMaclaurin_tent_representation
    digamma_eulerMaclaurin_tent_representation

end RiemannCvs.DigammaEulerMaclaurin
