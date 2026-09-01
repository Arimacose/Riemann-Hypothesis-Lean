import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import RiemannCvs.CombinedSymbolDyadicL2
import RiemannCvs.DigammaQuadraticRemainder

namespace RiemannCvs.C13ArchimedeanEndpoint

open Finset Filter
open RiemannCvs.CombinedSymbolDyadicL2

lemma log_thirteen_lt : Real.log 13 < (513 / 200 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (6 / 7 : ℝ)) (by norm_num) (by norm_num) 40
  norm_num at h
  linarith

lemma five_halves_lt_log_thirteen : (5 / 2 : ℝ) < Real.log 13 := by
  have h := Real.sum_range_le_log_div
    (x := (6 / 7 : ℝ)) (by norm_num) (by norm_num) 6
  norm_num at h
  linarith

lemma sqrt_thirteen_lower : (18 / 5 : ℝ) < Real.sqrt 13 := by
  have hs0 := Real.sqrt_nonneg (13 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  nlinarith

lemma sqrt_thirteen_upper : Real.sqrt 13 < (1803 / 500 : ℝ) := by
  have hs0 := Real.sqrt_nonneg (13 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  nlinarith

set_option maxHeartbeats 800000 in
lemma arctan_two_term_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hxnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hsum := (Real.hasSum_arctan hxnorm).tendsto_sum_nat
  have hsum' : Tendsto (fun n : ℕ => ∑ i ∈ range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
      atTop (nhds (Real.arctan x)) := by
    simpa [mul_div_assoc] using hsum
  have hanti : Antitone (fun n : ℕ =>
      x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
    have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
      simpa using mul_le_mul_of_nonneg_left hx2 (pow_nonneg hx0 (2 * n + 1))
    exact div_le_div₀ (by positivity) hpow (by positivity) (by norm_num)
  have h := hanti.alternating_series_le_tendsto hsum' 1
  norm_num [Finset.sum_range_succ] at h
  simpa [pow_three] using h

lemma two_arctan_inv_sqrt_thirteen_lower :
    (2701 / 5000 : ℝ) ≤ 2 * Real.arctan (Real.sqrt 13)⁻¹ := by
  let s : ℝ := Real.sqrt 13
  let t : ℝ := s⁻¹
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by norm_num)
  have hsUpper : s < (1803 / 500 : ℝ) := by
    simpa [s] using sqrt_thirteen_upper
  have htLower : (500 / 1803 : ℝ) < t := by
    dsimp [t]
    have h := one_div_lt_one_div_of_lt hs hsUpper
    norm_num at h
    simpa [one_div] using h
  have ht0 : 0 ≤ t := (inv_pos.2 hs).le
  have ht1 : t < 1 := by
    have hsOne : 1 < s := by
      have := sqrt_thirteen_lower
      dsimp [s]
      linarith
    exact inv_lt_one_of_one_lt₀ hsOne
  have hsSq : s ^ 2 = 13 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have htSq : t ^ 2 = (1 / 13 : ℝ) := by
    dsimp [t]
    field_simp [ne_of_gt hs]
    nlinarith
  have hPoly : t - t ^ 3 / 3 = (38 / 39 : ℝ) * t := by
    rw [show t ^ 3 = t ^ 2 * t by ring, htSq]
    ring
  have hSeries := arctan_two_term_lower ht0 ht1
  rw [hPoly] at hSeries
  dsimp [t, s] at hSeries ⊢
  nlinarith

lemma c13_log_ratio_lt_rational :
    6 * Real.log 13 / (7 + Real.sqrt 13) < (363 / 250 : ℝ) := by
  have hL := log_thirteen_lt
  have hs := sqrt_thirteen_lower
  have hden : 0 < 7 + Real.sqrt (13 : ℝ) := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

lemma log_three_sixty_three_div_two_fifty_lt :
    Real.log (363 / 250 : ℝ) < (373 / 1000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (113 / 613 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num at h
  linarith

lemma c13_log_ratio_lt :
    Real.log (6 * Real.log 13 / (7 + Real.sqrt 13)) <
      (373 / 1000 : ℝ) := by
  have hRatio := c13_log_ratio_lt_rational
  have hRatioPos : 0 < 6 * Real.log 13 / (7 + Real.sqrt 13) := by
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 13)]
  have hRatPos : 0 < (363 / 250 : ℝ) := by norm_num
  have hLog := Real.strictMonoOn_log hRatioPos hRatPos hRatio
  exact hLog.trans log_three_sixty_three_div_two_fifty_lt

theorem c13_archimedeanAsymptoticConstant_lower :
    (-949 / 1000 : ℝ) ≤ archimedeanDiagonalAsymptoticConstant 13 := by
  rw [c13_archimedeanDiagonalAsymptoticConstant_eq_reciprocal]
  have hAtan := two_arctan_inv_sqrt_thirteen_lower
  have hLog := c13_log_ratio_lt
  have hSqrt := sqrt_thirteen_upper
  nlinarith

lemma sqrt_two_upper : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma c13_height_960_lower :
    (1000 : ℝ) ≤ archimedeanAsymptoticHeight 13 960 := by
  unfold archimedeanAsymptoticHeight
  have hL0 : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hL0]
  have hPi := Real.pi_gt_d2
  have hL := log_thirteen_lt
  nlinarith

lemma c13_frequency_960_lower :
    (2000 : ℝ) ≤ archimedeanFrequency 13 960 := by
  rw [archimedeanFrequency_eq_two_mul_height]
  nlinarith [c13_height_960_lower]

lemma c13_geometricMass_le_one : archimedeanGeometricMass 13 ≤ 1 := by
  rw [c13_archimedeanGeometricMass_eq]
  nlinarith [sqrt_thirteen_upper]

lemma c13_geometricFirstMoment_le_one :
    archimedeanGeometricFirstMoment 13 ≤ 1 := by
  rw [c13_archimedeanGeometricFirstMoment_eq]
  nlinarith [sqrt_thirteen_upper]

theorem c13_archimedeanAsymptoticError_upper :
    archimedeanDiagonalAsymptoticError 13 960 ≤ (1 / 1000 : ℝ) := by
  let L : ℝ := Real.log 13
  let y : ℝ := archimedeanAsymptoticHeight 13 960
  let w : ℝ := archimedeanFrequency 13 960
  let A : ℝ := 1 / 8 + Real.sqrt 2 / 6
  let B : ℝ := archimedeanGeometricFirstMoment 13
  let M : ℝ := archimedeanGeometricMass 13
  have hL : (5 / 2 : ℝ) < L := by
    simpa [L] using five_halves_lt_log_thirteen
  have hL0 : 0 < L := by linarith
  have hy : (1000 : ℝ) ≤ y := by simpa [y] using c13_height_960_lower
  have hy0 : 0 < y := by linarith
  have hw : (2000 : ℝ) ≤ w := by simpa [w] using c13_frequency_960_lower
  have hw0 : 0 < w := by linarith
  have hySq : (1000 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
  have hwSq : (2000 : ℝ) ^ 2 ≤ w ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA : A ≤ (3 / 8 : ℝ) := by
    dsimp [A]
    nlinarith [sqrt_two_upper]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact archimedeanGeometricFirstMoment_nonneg 13 (by norm_num)
  have hB : B ≤ 1 := by simpa [B] using c13_geometricFirstMoment_le_one
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact archimedeanGeometricMass_nonneg 13 (by norm_num)
  have hM : M ≤ 1 := by simpa [M] using c13_geometricMass_le_one
  have hTermA : A / y ^ 2 ≤ (3 / 8 : ℝ) / (1000 : ℝ) ^ 2 := by
    calc
      A / y ^ 2 ≤ (3 / 8 : ℝ) / y ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hy0)).2 hA
      _ ≤ (3 / 8 : ℝ) / (1000 : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hySq
  have hInvY : 1 / y ≤ (1 / 1000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hy
  have hInvYSq : 1 / y ^ 2 ≤ (1 / (1000 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) hySq
  have hNumerator :
      1 / y + 1 / y ^ 2 ≤ (1 / 1000 : ℝ) + 1 / (1000 : ℝ) ^ 2 :=
    add_le_add hInvY hInvYSq
  have hDen : (5 : ℝ) ≤ 2 * L := by linarith
  have hTermTrigamma :
      (1 / y + 1 / y ^ 2) / (2 * L) ≤
        ((1 / 1000 : ℝ) + 1 / (1000 : ℝ) ^ 2) / 5 := by
    calc
      (1 / y + 1 / y ^ 2) / (2 * L) ≤
          ((1 / 1000 : ℝ) + 1 / (1000 : ℝ) ^ 2) / (2 * L) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 hNumerator
      _ ≤ ((1 / 1000 : ℝ) + 1 / (1000 : ℝ) ^ 2) / 5 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hDen
  have hTermB : 2 * B / w ^ 2 ≤ (2 : ℝ) / (2000 : ℝ) ^ 2 := by
    calc
      2 * B / w ^ 2 ≤ (2 : ℝ) / w ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hw0)).2 (by nlinarith)
      _ ≤ (2 : ℝ) / (2000 : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hwSq
  have hFactor0 : 0 ≤ 2 / L := by positivity
  have hFactor : 2 / L ≤ (4 / 5 : ℝ) := by
    rw [div_le_iff₀ hL0]
    nlinarith
  have hFactorMass : (2 / L) * M ≤ (4 / 5 : ℝ) := by
    calc
      (2 / L) * M ≤ (4 / 5 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hFactor hM0
      _ ≤ (4 / 5 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = 4 / 5 := by ring
  have hTermM : (2 / L) * M / w ^ 2 ≤
      (4 / 5 : ℝ) / (2000 : ℝ) ^ 2 := by
    calc
      (2 / L) * M / w ^ 2 ≤ (4 / 5 : ℝ) / w ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hw0)).2 hFactorMass
      _ ≤ (4 / 5 : ℝ) / (2000 : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hwSq
  unfold archimedeanDiagonalAsymptoticError
  dsimp only
  change A / y ^ 2 + (1 / y + 1 / y ^ 2) / (2 * L) +
      2 * B / w ^ 2 + (2 / L) * M / w ^ 2 ≤ (1 / 1000 : ℝ)
  nlinarith

/-- The cutoff-13, mode-960 endpoint is now a kernel-checked real inequality,
with no interval certificate left as a premise. -/
theorem c13_archimedeanEndpoint_bound :
    (-(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) := by
  nlinarith [c13_archimedeanAsymptoticConstant_lower,
    c13_archimedeanAsymptoticError_upper]

/-- The cutoff-13 diagonal route after closing the scalar endpoint.  Its sole
remaining analytic input is the global quadratic digamma remainder. -/
theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2) :
    Real.log x - 19 / 20 ≤
      -logarithmicArchimedeanDiagonal 13 x := by
  exact
    RiemannCvs.CombinedSymbolDyadicL2.c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound
      x hx hRemainder c13_archimedeanEndpoint_bound

/-- The same closed endpoint route with the right-half-plane sector factor
also discharged.  The premise is precisely the DLMF 5.11(ii)
first-neglected-term estimate before the elementary `sec³` bound. -/
theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_first_neglected_term
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hFirst : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        ((1 / 12 : ℝ) * (Real.cos (w.arg / 2))⁻¹ ^ 3) / ‖w‖ ^ 2) :
    Real.log x - 19 / 20 ≤
      -logarithmicArchimedeanDiagonal 13 x := by
  exact c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth
    x hx
      (RiemannCvs.DigammaQuadraticRemainder.quadratic_remainder_bound_of_first_neglected_term
        hFirst)

end RiemannCvs.C13ArchimedeanEndpoint
