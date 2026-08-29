import RiemannCvs.BesselJ0Series

namespace RiemannCvs.BesselJ0DifferentialEquation

open Filter Real Set

/-!
# The differential equation of the concrete order-zero Bessel series

This module differentiates the repository series term by term and proves that
it satisfies the order-zero Bessel equation.  The result is the analytic bridge
needed before constructing the DLMF even and odd remainders.
-/

/-- Coefficient of `x^(2n)` in the concrete order-zero Bessel series. -/
noncomputable def powerCoefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / ((4 : ℝ) ^ n * (n.factorial : ℝ) ^ 2)

lemma besselJ0Term_eq_powerCoefficient_mul (n : ℕ) (x : ℝ) :
    BesselJ0Series.besselJ0Term n x =
      powerCoefficient n * x ^ (2 * n) := by
  unfold BesselJ0Series.besselJ0Term powerCoefficient
  rw [div_pow]
  rw [show (x ^ 2) ^ n = x ^ (2 * n) by rw [pow_mul]]
  ring

/-- The termwise first derivative of the concrete Bessel series. -/
noncomputable def derivTerm (n : ℕ) (x : ℝ) : ℝ :=
  powerCoefficient n * ((2 * n : ℕ) : ℝ) * x ^ (2 * n - 1)

/-- The termwise second derivative of the concrete Bessel series. -/
noncomputable def secondDerivTerm (n : ℕ) (x : ℝ) : ℝ :=
  powerCoefficient n * (((2 * n) * (2 * n - 1) : ℕ) : ℝ) *
    x ^ (2 * n - 2)

lemma hasDerivAt_besselJ0Term (n : ℕ) (x : ℝ) :
    HasDerivAt (BesselJ0Series.besselJ0Term n) (derivTerm n x) x := by
  change HasDerivAt (fun y => BesselJ0Series.besselJ0Term n y)
    (derivTerm n x) x
  simpa only [besselJ0Term_eq_powerCoefficient_mul, derivTerm, mul_assoc] using
    (hasDerivAt_pow (2 * n) x).const_mul (powerCoefficient n)

lemma hasDerivAt_derivTerm (n : ℕ) (x : ℝ) :
    HasDerivAt (derivTerm n) (secondDerivTerm n x) x := by
  change HasDerivAt (fun y => derivTerm n y) (secondDerivTerm n x) x
  have hsub : 2 * n - 1 - 1 = 2 * n - 2 := by omega
  have h := (hasDerivAt_pow (2 * n - 1) x).const_mul
    (powerCoefficient n * ((2 * n : ℕ) : ℝ))
  simpa only [derivTerm, secondDerivTerm, hsub, Nat.cast_mul, Nat.cast_ofNat,
    mul_assoc] using h

lemma powerCoefficient_succ (n : ℕ) :
    powerCoefficient (n + 1) =
      -(powerCoefficient n) / (4 * ((n : ℝ) + 1) ^ 2) := by
  unfold powerCoefficient
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [show (n.factorial : ℝ) ≠ 0 by positivity,
    show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

@[simp]
lemma derivTerm_zero (x : ℝ) : derivTerm 0 x = 0 := by
  simp [derivTerm]

@[simp]
lemma secondDerivTerm_zero (x : ℝ) : secondDerivTerm 0 x = 0 := by
  simp [secondDerivTerm]

lemma derivTerm_succ (n : ℕ) (x : ℝ) :
    derivTerm (n + 1) x =
      (-1 : ℝ) ^ (n + 1) * (x / 2) * (x ^ 2 / 4) ^ n /
        (((n : ℝ) + 1) * (n.factorial : ℝ) ^ 2) := by
  unfold derivTerm powerCoefficient
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hcoef : 2 * (n + 1) = 2 * n + 2 := by omega
  have hexp : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [hexp, hcoef, pow_succ, pow_succ, div_pow]
  rw [show (x ^ 2) ^ n = x ^ (2 * n) by rw [pow_mul]]
  push_cast
  field_simp [show (n.factorial : ℝ) ≠ 0 by positivity,
    show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

lemma secondDerivTerm_succ (n : ℕ) (x : ℝ) :
    secondDerivTerm (n + 1) x =
      (-1 : ℝ) ^ (n + 1) *
        (((2 : ℝ) * n + 1) / (2 * ((n : ℝ) + 1))) *
          ((x ^ 2 / 4) ^ n / (n.factorial : ℝ) ^ 2) := by
  unfold secondDerivTerm powerCoefficient
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hcoef : 2 * (n + 1) = 2 * n + 2 := by omega
  have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hexp : 2 * (n + 1) - 2 = 2 * n := by omega
  rw [hsub, hexp, hcoef, pow_succ, div_pow]
  rw [show (x ^ 2) ^ n = x ^ (2 * n) by rw [pow_mul]]
  push_cast
  field_simp [show (n.factorial : ℝ) ≠ 0 by positivity,
    show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- A compact-interval majorant for the first derivative terms. -/
noncomputable def derivMajorant (R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => R * (R ^ 2) ^ n / (n.factorial : ℝ)

/-- A compact-interval majorant for the second derivative terms. -/
noncomputable def secondDerivMajorant (R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (R ^ 2) ^ n / (n.factorial : ℝ)

lemma summable_derivMajorant (R : ℝ) : Summable (derivMajorant R) := by
  apply (summable_nat_add_iff 1).mp
  simpa [derivMajorant, mul_div_assoc] using
    (Real.summable_pow_div_factorial (R ^ 2)).mul_left R

lemma summable_secondDerivMajorant (R : ℝ) :
    Summable (secondDerivMajorant R) := by
  apply (summable_nat_add_iff 1).mp
  simpa [secondDerivMajorant] using
    Real.summable_pow_div_factorial (R ^ 2)

lemma norm_derivTerm_le_majorant
    (R : ℝ) (hR : 1 ≤ R) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (-R) R) :
    ‖derivTerm n x‖ ≤ derivMajorant R n := by
  cases n with
  | zero => simp [derivMajorant]
  | succ n =>
      rw [derivTerm_succ]
      have hRPos : 0 < R := by linarith
      have hxSq : x ^ 2 ≤ R ^ 2 := by nlinarith [hx.1, hx.2]
      have hBase : 0 ≤ x ^ 2 / 4 := by positivity
      have hBaseLe : x ^ 2 / 4 ≤ R ^ 2 := by linarith
      have hxAbs : |x| ≤ R := (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
      have hHalf : |x| / 2 ≤ R := by nlinarith [abs_nonneg x]
      have hFactorial : (1 : ℝ) ≤ (n.factorial : ℝ) := by
        exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
      have hFactorialNonneg : 0 ≤ (n.factorial : ℝ) := le_trans zero_le_one hFactorial
      have hDenom : (n.factorial : ℝ) ≤
          ((n : ℝ) + 1) * (n.factorial : ℝ) ^ 2 := by
        calc
          (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ 2 := by nlinarith
          _ ≤ ((n : ℝ) + 1) * (n.factorial : ℝ) ^ 2 := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (show (1 : ℝ) ≤ (n : ℝ) + 1 by
                exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
              (sq_nonneg (n.factorial : ℝ))
      simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, derivMajorant,
        abs_of_nonneg hBase,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
        abs_of_nonneg hFactorialNonneg]
      change |x| / 2 * (x ^ 2 / 4) ^ n /
          (((n : ℝ) + 1) * (n.factorial : ℝ) ^ 2) ≤
        R * (R ^ 2) ^ n / (n.factorial : ℝ)
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact hDenom

lemma norm_secondDerivTerm_le_majorant
    (R : ℝ) (hR : 1 ≤ R) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (-R) R) :
    ‖secondDerivTerm n x‖ ≤ secondDerivMajorant R n := by
  cases n with
  | zero => simp [secondDerivMajorant]
  | succ n =>
      rw [secondDerivTerm_succ]
      have hxSq : x ^ 2 ≤ R ^ 2 := by nlinarith [hx.1, hx.2]
      have hBase : 0 ≤ x ^ 2 / 4 := by positivity
      have hBaseLe : x ^ 2 / 4 ≤ R ^ 2 := by linarith
      have hRatioNonneg : 0 ≤
          ((2 : ℝ) * n + 1) / (2 * ((n : ℝ) + 1)) := by positivity
      have hRatioLe :
          ((2 : ℝ) * n + 1) / (2 * ((n : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
        linarith
      have hFactorial : (1 : ℝ) ≤ (n.factorial : ℝ) := by
        exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
      have hFactorialNonneg : 0 ≤ (n.factorial : ℝ) := le_trans zero_le_one hFactorial
      have hDenom : (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ 2 := by
        nlinarith
      simp only [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, abs_div, secondDerivMajorant,
        abs_of_nonneg hBase,
        abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * n + 1),
        abs_of_nonneg (by positivity : 0 ≤ 2 * ((n : ℝ) + 1)),
        abs_of_nonneg hFactorialNonneg]
      change (((2 : ℝ) * n + 1) / (2 * ((n : ℝ) + 1))) *
          ((x ^ 2 / 4) ^ n / (n.factorial : ℝ) ^ 2) ≤
        (R ^ 2) ^ n / (n.factorial : ℝ)
      calc
        _ ≤ 1 * ((R ^ 2) ^ n / (n.factorial : ℝ)) := by
          have hFrac :
              (x ^ 2 / 4) ^ n / (n.factorial : ℝ) ^ 2 ≤
                (R ^ 2) ^ n / (n.factorial : ℝ) := by
            apply div_le_div₀
            · positivity
            · gcongr
            · positivity
            · exact hDenom
          exact mul_le_mul hRatioLe hFrac (by positivity) zero_le_one
        _ = _ := one_mul _
lemma summable_derivTerm (x : ℝ) : Summable (fun n => derivTerm n x) := by
  let R : ℝ := |x| + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg x]
  have hx : x ∈ Ioo (-R) R := by
    constructor
    · dsimp [R]
      linarith [neg_abs_le x]
    · dsimp [R]
      linarith [le_abs_self x]
  exact (summable_derivMajorant R).of_norm_bounded
    (fun n => norm_derivTerm_le_majorant R hR n x hx)

lemma summable_secondDerivTerm (x : ℝ) :
    Summable (fun n => secondDerivTerm n x) := by
  let R : ℝ := |x| + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg x]
  have hx : x ∈ Ioo (-R) R := by
    constructor
    · dsimp [R]
      linarith [neg_abs_le x]
    · dsimp [R]
      linarith [le_abs_self x]
  exact (summable_secondDerivMajorant R).of_norm_bounded
    (fun n => norm_secondDerivTerm_le_majorant R hR n x hx)

/-- The globally convergent first-derivative series. -/
noncomputable def besselJ0Deriv (x : ℝ) : ℝ :=
  ∑' n : ℕ, derivTerm n x

/-- The globally convergent second-derivative series. -/
noncomputable def besselJ0SecondDeriv (x : ℝ) : ℝ :=
  ∑' n : ℕ, secondDerivTerm n x

/-- Termwise differentiation of the concrete Bessel series. -/
theorem hasDerivAt_besselJ0 (x : ℝ) :
    HasDerivAt BesselJ0Series.besselJ0 (besselJ0Deriv x) x := by
  let R : ℝ := |x| + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg x]
  have hx : x ∈ Ioo (-R) R := by
    constructor
    · dsimp [R]
      linarith [neg_abs_le x]
    · dsimp [R]
      linarith [le_abs_self x]
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_derivMajorant R) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_besselJ0Term n y)
    (fun n y hy => norm_derivTerm_le_majorant R hR n y hy)
    hx (BesselJ0Series.summable_besselJ0Term x) hx
  change HasDerivAt (fun z => (∑' n : ℕ, BesselJ0Series.besselJ0Term n z))
    (∑' n : ℕ, derivTerm n x) x
  exact h

/-- Termwise differentiation of the first-derivative series. -/
theorem hasDerivAt_besselJ0Deriv (x : ℝ) :
    HasDerivAt besselJ0Deriv (besselJ0SecondDeriv x) x := by
  let R : ℝ := |x| + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg x]
  have hx : x ∈ Ioo (-R) R := by
    constructor
    · dsimp [R]
      linarith [neg_abs_le x]
    · dsimp [R]
      linarith [le_abs_self x]
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_secondDerivMajorant R) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_derivTerm n y)
    (fun n y hy => norm_secondDerivTerm_le_majorant R hR n y hy)
    hx (summable_derivTerm x) hx
  change HasDerivAt (fun z => (∑' n : ℕ, derivTerm n z))
    (∑' n : ℕ, secondDerivTerm n x) x
  exact h

theorem differentiable_besselJ0 :
    Differentiable ℝ BesselJ0Series.besselJ0 :=
  fun x => (hasDerivAt_besselJ0 x).differentiableAt

theorem differentiable_besselJ0Deriv : Differentiable ℝ besselJ0Deriv :=
  fun x => (hasDerivAt_besselJ0Deriv x).differentiableAt

theorem deriv_besselJ0 (x : ℝ) :
    deriv BesselJ0Series.besselJ0 x = besselJ0Deriv x :=
  (hasDerivAt_besselJ0 x).deriv

theorem deriv_besselJ0Deriv (x : ℝ) :
    deriv besselJ0Deriv x = besselJ0SecondDeriv x :=
  (hasDerivAt_besselJ0Deriv x).deriv

/-- The derivative of the concrete series is itself globally differentiable. -/
theorem differentiable_deriv_besselJ0 :
    Differentiable ℝ (deriv BesselJ0Series.besselJ0) := by
  have hfun : deriv BesselJ0Series.besselJ0 = besselJ0Deriv := by
    funext x
    exact deriv_besselJ0 x
  rw [hfun]
  exact differentiable_besselJ0Deriv

/-- The iterated derivative is represented by the second-derivative series. -/
theorem deriv_deriv_besselJ0 (x : ℝ) :
    deriv (deriv BesselJ0Series.besselJ0) x = besselJ0SecondDeriv x := by
  have hfun : deriv BesselJ0Series.besselJ0 = besselJ0Deriv := by
    funext y
    exact deriv_besselJ0 y
  rw [hfun, deriv_besselJ0Deriv]

/-- Each adjacent pair of power-series coefficients satisfies the Bessel ODE
recurrence before summation. -/
lemma shifted_term_bessel_ode (n : ℕ) (x : ℝ) :
    x ^ 2 * secondDerivTerm (n + 1) x +
        x * derivTerm (n + 1) x +
        x ^ 2 * BesselJ0Series.besselJ0Term n x = 0 := by
  rw [besselJ0Term_eq_powerCoefficient_mul]
  unfold secondDerivTerm derivTerm
  rw [powerCoefficient_succ]
  have hSecondExponent : 2 * (n + 1) - 2 = 2 * n := by omega
  have hFirstExponent : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [hSecondExponent, hFirstExponent, pow_succ]
  push_cast
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  ring


lemma tsum_derivTerm_succ (x : ℝ) :
    (∑' n : ℕ, derivTerm (n + 1) x) = besselJ0Deriv x := by
  have h := (summable_derivTerm x).tsum_eq_zero_add
  rw [derivTerm_zero, zero_add] at h
  exact h.symm

lemma tsum_secondDerivTerm_succ (x : ℝ) :
    (∑' n : ℕ, secondDerivTerm (n + 1) x) = besselJ0SecondDeriv x := by
  have h := (summable_secondDerivTerm x).tsum_eq_zero_add
  rw [secondDerivTerm_zero, zero_add] at h
  exact h.symm

@[simp]
theorem besselJ0Deriv_zero : besselJ0Deriv 0 = 0 := by
  unfold besselJ0Deriv
  calc
    (∑' n : ℕ, derivTerm n 0) = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      cases n with
      | zero => simp
      | succ n => simp [derivTerm_succ]
    _ = 0 := tsum_zero

@[simp]
lemma secondDerivTerm_one_zero : secondDerivTerm 1 0 = -(1 / 2 : ℝ) := by
  norm_num [secondDerivTerm, powerCoefficient]

lemma secondDerivTerm_at_zero_of_ne_one (n : ℕ) (hn : n ≠ 1) :
    secondDerivTerm n 0 = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      by_cases hn0 : n = 0
      · subst n
        exact (hn rfl).elim
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        simp [secondDerivTerm_succ]

@[simp]
theorem besselJ0SecondDeriv_zero :
    besselJ0SecondDeriv 0 = -(1 / 2 : ℝ) := by
  unfold besselJ0SecondDeriv
  rw [tsum_eq_single 1]
  · exact secondDerivTerm_one_zero
  · intro n hn
    exact secondDerivTerm_at_zero_of_ne_one n hn

@[simp]
theorem deriv_besselJ0_zero : deriv BesselJ0Series.besselJ0 0 = 0 := by
  rw [deriv_besselJ0, besselJ0Deriv_zero]

@[simp]
theorem deriv_deriv_besselJ0_zero :
    deriv (deriv BesselJ0Series.besselJ0) 0 = -(1 / 2 : ℝ) := by
  rw [deriv_deriv_besselJ0, besselJ0SecondDeriv_zero]

lemma mul_besselJ0SecondDeriv_eq_tsum (x : ℝ) :
    x ^ 2 * besselJ0SecondDeriv x =
      ∑' n : ℕ, x ^ 2 * secondDerivTerm (n + 1) x := by
  rw [← tsum_secondDerivTerm_succ, ← tsum_mul_left]

lemma mul_besselJ0Deriv_eq_tsum (x : ℝ) :
    x * besselJ0Deriv x =
      ∑' n : ℕ, x * derivTerm (n + 1) x := by
  rw [← tsum_derivTerm_succ, ← tsum_mul_left]

lemma mul_besselJ0_eq_tsum (x : ℝ) :
    x ^ 2 * BesselJ0Series.besselJ0 x =
      ∑' n : ℕ, x ^ 2 * BesselJ0Series.besselJ0Term n x := by
  unfold BesselJ0Series.besselJ0
  rw [← tsum_mul_left]

lemma tsum_shifted_bessel_ode (x : ℝ) :
    (∑' n : ℕ,
      ((x ^ 2 * secondDerivTerm (n + 1) x +
        x * derivTerm (n + 1) x) +
        x ^ 2 * BesselJ0Series.besselJ0Term n x)) = 0 := by
  calc
    (∑' n : ℕ,
      ((x ^ 2 * secondDerivTerm (n + 1) x +
        x * derivTerm (n + 1) x) +
        x ^ 2 * BesselJ0Series.besselJ0Term n x)) =
        ∑' _n : ℕ, (0 : ℝ) := by
          apply tsum_congr
          intro n
          exact shifted_term_bessel_ode n x
    _ = 0 := tsum_zero

lemma summable_bessel_ode_second_term (x : ℝ) :
    Summable (fun n : ℕ => x ^ 2 * secondDerivTerm (n + 1) x) := by
  exact ((summable_nat_add_iff 1).mpr (summable_secondDerivTerm x)).mul_left
    (x ^ 2)

lemma summable_bessel_ode_first_term (x : ℝ) :
    Summable (fun n : ℕ => x * derivTerm (n + 1) x) := by
  exact ((summable_nat_add_iff 1).mpr (summable_derivTerm x)).mul_left x

lemma summable_bessel_ode_series_term (x : ℝ) :
    Summable (fun n : ℕ => x ^ 2 * BesselJ0Series.besselJ0Term n x) := by
  exact (BesselJ0Series.summable_besselJ0Term x).mul_left (x ^ 2)

lemma tsum_bessel_ode_first_two_terms (x : ℝ) :
    (∑' n : ℕ, x ^ 2 * secondDerivTerm (n + 1) x) +
        (∑' n : ℕ, x * derivTerm (n + 1) x) =
      ∑' n : ℕ,
        (x ^ 2 * secondDerivTerm (n + 1) x +
          x * derivTerm (n + 1) x) := by
  exact ((summable_bessel_ode_second_term x).tsum_add
    (summable_bessel_ode_first_term x)).symm

lemma tsum_bessel_ode_add_series_term (x : ℝ) :
    (∑' n : ℕ,
        (x ^ 2 * secondDerivTerm (n + 1) x +
          x * derivTerm (n + 1) x)) +
        (∑' n : ℕ, x ^ 2 * BesselJ0Series.besselJ0Term n x) =
      ∑' n : ℕ,
        ((x ^ 2 * secondDerivTerm (n + 1) x +
          x * derivTerm (n + 1) x) +
          x ^ 2 * BesselJ0Series.besselJ0Term n x) := by
  exact (((summable_bessel_ode_second_term x).add
      (summable_bessel_ode_first_term x)).tsum_add
    (summable_bessel_ode_series_term x)).symm

lemma tsum_bessel_ode_terms (x : ℝ) :
    (∑' n : ℕ, x ^ 2 * secondDerivTerm (n + 1) x) +
        (∑' n : ℕ, x * derivTerm (n + 1) x) +
        (∑' n : ℕ, x ^ 2 * BesselJ0Series.besselJ0Term n x) =
      ∑' n : ℕ,
        ((x ^ 2 * secondDerivTerm (n + 1) x +
          x * derivTerm (n + 1) x) +
          x ^ 2 * BesselJ0Series.besselJ0Term n x) := by
  rw [tsum_bessel_ode_first_two_terms, tsum_bessel_ode_add_series_term]

/-- The concrete repository series satisfies the order-zero Bessel equation
on the whole real axis.  The second derivative is represented by
`besselJ0SecondDeriv`, with both derivative identities proved above. -/
theorem besselJ0_differentialEquation (x : ℝ) :
    x ^ 2 * besselJ0SecondDeriv x +
        x * besselJ0Deriv x +
        x ^ 2 * BesselJ0Series.besselJ0 x = 0 := by
  calc
    x ^ 2 * besselJ0SecondDeriv x +
        x * besselJ0Deriv x +
        x ^ 2 * BesselJ0Series.besselJ0 x =
      (∑' n : ℕ, x ^ 2 * secondDerivTerm (n + 1) x) +
        (∑' n : ℕ, x * derivTerm (n + 1) x) +
        (∑' n : ℕ, x ^ 2 * BesselJ0Series.besselJ0Term n x) := by
          rw [mul_besselJ0SecondDeriv_eq_tsum,
            mul_besselJ0Deriv_eq_tsum, mul_besselJ0_eq_tsum]
    _ = ∑' n : ℕ,
        ((x ^ 2 * secondDerivTerm (n + 1) x +
          x * derivTerm (n + 1) x) +
          x ^ 2 * BesselJ0Series.besselJ0Term n x) := tsum_bessel_ode_terms x
    _ = 0 := tsum_shifted_bessel_ode x

/-- Derivative-form statement of the concrete Bessel equation. -/
theorem besselJ0_deriv_differentialEquation (x : ℝ) :
    x ^ 2 * deriv besselJ0Deriv x +
        x * deriv BesselJ0Series.besselJ0 x +
        x ^ 2 * BesselJ0Series.besselJ0 x = 0 := by
  rw [deriv_besselJ0Deriv, deriv_besselJ0]
  exact besselJ0_differentialEquation x

/-- Standard iterated-derivative form of the order-zero Bessel equation. -/
theorem besselJ0_second_order_differentialEquation (x : ℝ) :
    x ^ 2 * deriv (deriv BesselJ0Series.besselJ0) x +
        x * deriv BesselJ0Series.besselJ0 x +
        x ^ 2 * BesselJ0Series.besselJ0 x = 0 := by
  rw [deriv_deriv_besselJ0, deriv_besselJ0]
  exact besselJ0_differentialEquation x
end RiemannCvs.BesselJ0DifferentialEquation
