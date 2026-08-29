import Mathlib

namespace RiemannCvs.BesselJ0Series

open Filter Real Set

/-!
# The real order-zero Bessel function from its everywhere-convergent series

This module defines the concrete function used by the Dunster source adapter:

`J₀(x) = ∑' n, (-1)^n (x² / 4)^n / (n!)²`.
-/

/-- The `n`th term in the real order-zero Bessel series. -/
noncomputable def besselJ0Term (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (x ^ 2 / 4) ^ n / (n.factorial : ℝ) ^ 2

/-- The concrete real order-zero Bessel function used in the PSWF source layer. -/
noncomputable def besselJ0 (x : ℝ) : ℝ :=
  ∑' n : ℕ, besselJ0Term n x

theorem summable_besselJ0Term (x : ℝ) :
    Summable (fun n : ℕ => besselJ0Term n x) := by
  refine (Real.summable_pow_div_factorial |x ^ 2 / 4|).of_norm_bounded ?_
  intro n
  have hBase : 0 ≤ |x ^ 2 / 4| := abs_nonneg _
  have hFactorial : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
  have hFactorialPos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  unfold besselJ0Term
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_pow, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / 4),
    Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n.factorial)]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hFactorialPos
  · nlinarith

theorem hasSum_besselJ0Term (x : ℝ) :
    HasSum (fun n : ℕ => besselJ0Term n x) (besselJ0 x) := by
  exact (summable_besselJ0Term x).hasSum

lemma norm_besselJ0Term_le_majorant
    (R x : ℝ) (n : ℕ)
    (hx : x ∈ Icc (-R) R) :
    ‖besselJ0Term n x‖ ≤ (R ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
  have hFactorial : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
  have hFactorialPos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hBaseNonneg : 0 ≤ x ^ 2 / 4 := by positivity
  have hMajorantBaseNonneg : 0 ≤ R ^ 2 / 4 := by positivity
  have hBaseLe : x ^ 2 / 4 ≤ R ^ 2 / 4 := by
    have hxSquare : x ^ 2 ≤ R ^ 2 := by nlinarith [hx.1, hx.2]
    linarith
  unfold besselJ0Term
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_pow, norm_pow, Real.norm_eq_abs, abs_of_nonneg hBaseNonneg,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n.factorial)]
  calc
    (x ^ 2 / 4) ^ n / (n.factorial : ℝ) ^ 2 ≤
        (x ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hFactorialPos
      · nlinarith
    _ ≤ (R ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
      gcongr

/-- Partial sums converge uniformly to `J₀` on every symmetric compact
interval. -/
theorem tendstoUniformlyOn_besselJ0_partialSums_Icc (R : ℝ) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ =>
        ∑ n ∈ Finset.range N, besselJ0Term n x)
      besselJ0 atTop (Icc (-R) R) := by
  unfold besselJ0
  exact tendstoUniformlyOn_tsum_nat
    (Real.summable_pow_div_factorial (R ^ 2 / 4))
    (fun n x hx => norm_besselJ0Term_le_majorant R x n hx)

/-- The uniform limit of the Bessel partial sums is continuous on every
symmetric compact interval. -/
theorem continuousOn_besselJ0_Icc
    (R : ℝ) :
    ContinuousOn besselJ0 (Icc (-R) R) := by
  unfold besselJ0
  apply continuousOn_tsum
  · intro n
    unfold besselJ0Term
    fun_prop
  · exact Real.summable_pow_div_factorial (R ^ 2 / 4)
  · intro n x hx
    exact norm_besselJ0Term_le_majorant R x n hx

/-- The concrete real order-zero Bessel series is continuous on `ℝ`. -/
theorem continuous_besselJ0 : Continuous besselJ0 := by
  rw [continuous_iff_continuousAt]
  intro x
  let R : ℝ := |x| + 1
  have hLeft : -R < x := by
    dsimp [R]
    linarith [neg_abs_le x]
  have hRight : x < R := by
    dsimp [R]
    linarith [le_abs_self x]
  exact (continuousOn_besselJ0_Icc R).continuousAt
    (Icc_mem_nhds hLeft hRight)

@[simp]
lemma besselJ0Term_zero (x : ℝ) : besselJ0Term 0 x = 1 := by
  simp [besselJ0Term]

@[simp]
lemma besselJ0Term_succ_at_zero (n : ℕ) : besselJ0Term (n + 1) 0 = 0 := by
  simp [besselJ0Term]

/-- The defining series has the standard normalization `J₀(0) = 1`. -/
@[simp]
theorem besselJ0_zero : besselJ0 0 = 1 := by
  unfold besselJ0
  rw [tsum_eq_single 0]
  · exact besselJ0Term_zero 0
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact besselJ0Term_succ_at_zero k

@[simp]
lemma besselJ0Term_neg (n : ℕ) (x : ℝ) :
    besselJ0Term n (-x) = besselJ0Term n x := by
  simp [besselJ0Term]

/-- The concrete order-zero Bessel function is even. -/
@[simp]
theorem besselJ0_neg (x : ℝ) : besselJ0 (-x) = besselJ0 x := by
  unfold besselJ0
  exact tsum_congr (fun n => besselJ0Term_neg n x)

theorem besselJ0_even : Function.Even besselJ0 := besselJ0_neg

@[simp]
lemma besselJ0Term_one (x : ℝ) :
    besselJ0Term 1 x = -(x ^ 2 / 4) := by
  simp [besselJ0Term]

@[simp]
lemma besselJ0Term_two (x : ℝ) :
    besselJ0Term 2 x = x ^ 4 / 64 := by
  norm_num [besselJ0Term]
  ring

/-- Successive series terms satisfy the order-zero Bessel coefficient
recurrence. -/
lemma besselJ0Term_succ (n : ℕ) (x : ℝ) :
    besselJ0Term (n + 1) x =
      (-(x ^ 2 / 4) / ((n : ℝ) + 1) ^ 2) * besselJ0Term n x := by
  unfold besselJ0Term
  rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
    show (n.factorial : ℝ) ≠ 0 by positivity]

end RiemannCvs.BesselJ0Series
