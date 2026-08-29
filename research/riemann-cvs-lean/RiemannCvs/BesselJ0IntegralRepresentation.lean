import RiemannCvs.BesselJ0DifferentialEquation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace RiemannCvs.BesselJ0IntegralRepresentation

open Filter Real Set Finset MeasureTheory
open scoped BigOperators Interval

/-!
# Integral representation of the concrete order-zero Bessel series

This module proves the Poisson--Schlafli real integral representation directly
from the repository power series.  It evaluates every even sine moment, uses
the real cosine power series with a summable `cosh |x|` majorant, commutes the
series with the interval integral, and identifies the resulting coefficients
with `BesselJ0Series.besselJ0Term`.

The proof avoids invoking ordinary ODE uniqueness at the regular singular point
`x = 0`.  The resulting oscillatory integral is the analytic starting point for
constructing the even and odd DLMF remainders.
-/

/-- The finite Wallis product in the even sine moment, in factorial form. -/
lemma wallisProduct_eq_factorialRatio (n : ℕ) :
    (∏ i ∈ range n, ((2 : ℝ) * i + 1) / (2 * i + 2)) =
      ((2 * n).factorial : ℝ) /
        ((4 : ℝ) ^ n * (n.factorial : ℝ) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prod_range_succ, ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
      ring

/-- Exact even sine moment used to identify the integrated cosine series. -/
lemma integral_sin_pow_even_factorial (n : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ (2 * n)) =
      Real.pi * ((2 * n).factorial : ℝ) /
        ((4 : ℝ) ^ n * (n.factorial : ℝ) ^ 2) := by
  rw [integral_sin_pow_even, wallisProduct_eq_factorialRatio]
  ring

/-- The `n`th cosine-series term for the oscillatory integral integrand. -/
noncomputable def cosineSeriesTerm (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (x * Real.sin t) ^ (2 * n) /
    ((2 * n).factorial : ℝ)

lemma continuous_cosineSeriesTerm (x : ℝ) (n : ℕ) :
    Continuous (cosineSeriesTerm x n) := by
  unfold cosineSeriesTerm
  fun_prop

lemma intervalIntegrable_cosineSeriesTerm (x : ℝ) (n : ℕ) :
    IntervalIntegrable (cosineSeriesTerm x n) volume 0 Real.pi :=
  (continuous_cosineSeriesTerm x n).intervalIntegrable 0 Real.pi

/-- The absolute value of each integrand term is bounded by the corresponding
even term of `cosh |x|`, independently of the integration variable. -/
lemma norm_cosineSeriesTerm_le (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖cosineSeriesTerm x n t‖ ≤
      |x| ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  unfold cosineSeriesTerm
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * n).factorial : ℝ))]
  gcongr
  exact mul_le_of_le_one_right (abs_nonneg x) (abs_sin_le_one t)

lemma continuous_besselJ0Integral_integrand (x : ℝ) :
    Continuous (fun t : ℝ => Real.cos (x * Real.sin t)) := by
  fun_prop

lemma intervalIntegrable_besselJ0Integral_integrand (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.cos (x * Real.sin t))
      volume 0 Real.pi :=
  (continuous_besselJ0Integral_integrand x).intervalIntegrable 0 Real.pi

/-- Dominated convergence exchanges the cosine power series with the interval
integral. -/
lemma hasSum_integral_cosineSeriesTerm (x : ℝ) :
    HasSum (fun n : ℕ =>
      ∫ t in (0 : ℝ)..Real.pi, cosineSeriesTerm x n t)
      (∫ t in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin t)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n : ℕ => fun _ : ℝ =>
      |x| ^ (2 * n) / ((2 * n).factorial : ℝ))
  · intro n
    exact (continuous_cosineSeriesTerm x n).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun t _ => norm_cosineSeriesTerm_le x n t
  · exact ae_of_all _ fun _ _ => (Real.hasSum_cosh |x|).summable
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ => by
      simpa [cosineSeriesTerm] using Real.hasSum_cos (x * Real.sin t)

/-- Integrating one cosine-series term produces `pi` times the corresponding
concrete repository `J0` term. -/
lemma integral_cosineSeriesTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi, cosineSeriesTerm x n t) =
      Real.pi * BesselJ0Series.besselJ0Term n x := by
  unfold cosineSeriesTerm
  simp_rw [mul_pow]
  have hfun :
      (fun t : ℝ => (-1 : ℝ) ^ n *
        (x ^ (2 * n) * Real.sin t ^ (2 * n)) /
          ((2 * n).factorial : ℝ)) =
        (fun t : ℝ =>
          ((-1 : ℝ) ^ n * x ^ (2 * n) /
            ((2 * n).factorial : ℝ)) * Real.sin t ^ (2 * n)) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_sin_pow_even_factorial]
  rw [BesselJ0DifferentialEquation.besselJ0Term_eq_powerCoefficient_mul]
  unfold BesselJ0DifferentialEquation.powerCoefficient
  field_simp [show ((2 * n).factorial : ℝ) ≠ 0 by positivity,
    show (n.factorial : ℝ) ≠ 0 by positivity]

/-- The unnormalized oscillatory integral equals `pi` times the concrete
repository `J0` series. -/
lemma integral_cos_eq_pi_mul_besselJ0 (x : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin t)) =
      Real.pi * BesselJ0Series.besselJ0 x := by
  have hIntegral :
      HasSum (fun n : ℕ => Real.pi * BesselJ0Series.besselJ0Term n x)
        (∫ t in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin t)) := by
    simpa only [integral_cosineSeriesTerm] using
      hasSum_integral_cosineSeriesTerm x
  have hSeries :
      HasSum (fun n : ℕ => Real.pi * BesselJ0Series.besselJ0Term n x)
        (Real.pi * BesselJ0Series.besselJ0 x) := by
    simpa only [BesselJ0Series.besselJ0] using
      (BesselJ0Series.summable_besselJ0Term x).hasSum.mul_left Real.pi
  exact hIntegral.unique hSeries

/-- The normalized Poisson--Schlafli integral candidate. -/
noncomputable def besselJ0Integral (x : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ t in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin t)

@[simp]
theorem besselJ0Integral_eq_besselJ0 (x : ℝ) :
    besselJ0Integral x = BesselJ0Series.besselJ0 x := by
  rw [besselJ0Integral, integral_cos_eq_pi_mul_besselJ0]
  field_simp [Real.pi_ne_zero]

/-- Poisson--Schlafli integral representation of the concrete repository
order-zero Bessel series, valid on the whole real axis. -/
theorem besselJ0_integral_representation (x : ℝ) :
    BesselJ0Series.besselJ0 x =
      Real.pi⁻¹ * ∫ t in (0 : ℝ)..Real.pi,
        Real.cos (x * Real.sin t) := by
  exact (besselJ0Integral_eq_besselJ0 x).symm

end RiemannCvs.BesselJ0IntegralRepresentation
