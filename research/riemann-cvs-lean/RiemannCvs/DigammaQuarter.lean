import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The digamma value at one quarter

Mathlib supplies `Complex.digamma_one_half`, while the cutoff-13
Archimedean endpoint also contains `Complex.digamma (1 / 4)`.  This file
derives the quarter value from Legendre duplication and Euler reflection.
The proof differentiates the two exact Gamma identities through
`logDeriv`; no numerical approximation is used.
-/

namespace RiemannCvs

open Complex
open scoped Real

private lemma logDeriv_gamma_add_const (b x : ℂ)
    (hG : DifferentiableAt ℂ Complex.Gamma (x + b)) :
    logDeriv (fun z : ℂ => Complex.Gamma (z + b)) x =
      Complex.digamma (x + b) := by
  change logDeriv (Complex.Gamma ∘ fun z : ℂ => z + b) x = _
  calc
    logDeriv (Complex.Gamma ∘ fun z : ℂ => z + b) x =
        logDeriv Complex.Gamma (x + b) * deriv (fun z : ℂ => z + b) x :=
      logDeriv_comp hG (by fun_prop)
    _ = Complex.digamma (x + b) := by
      simp [Complex.digamma_def]

private lemma logDeriv_gamma_const_mul (a x : ℂ)
    (hG : DifferentiableAt ℂ Complex.Gamma (a * x)) :
    logDeriv (fun z : ℂ => Complex.Gamma (a * z)) x =
      a * Complex.digamma (a * x) := by
  change logDeriv (Complex.Gamma ∘ fun z : ℂ => a * z) x = _
  calc
    logDeriv (Complex.Gamma ∘ fun z : ℂ => a * z) x =
        logDeriv Complex.Gamma (a * x) * deriv (fun z : ℂ => a * z) x :=
      logDeriv_comp hG (by fun_prop)
    _ = a * Complex.digamma (a * x) := by
      rw [deriv_const_mul_id]
      simp [Complex.digamma_def]
      ring

private lemma logDeriv_two_cpow_one_sub_two_mul (x : ℂ) :
    logDeriv (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) x =
      -2 * (Real.log 2 : ℂ) := by
  rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hpow : (2 : ℂ) ^ (1 - 2 * x) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (by norm_num))
  field_simp [hpow]
  rw [deriv_const_sub, deriv_const_mul_id]
  ring

private lemma logDeriv_gamma_one_sub (x : ℂ)
    (hG : DifferentiableAt ℂ Complex.Gamma (1 - x)) :
    logDeriv (fun z : ℂ => Complex.Gamma (1 - z)) x =
      -Complex.digamma (1 - x) := by
  change logDeriv (Complex.Gamma ∘ fun z : ℂ => 1 - z) x = _
  calc
    logDeriv (Complex.Gamma ∘ fun z : ℂ => 1 - z) x =
        logDeriv Complex.Gamma (1 - x) * deriv (fun z : ℂ => 1 - z) x :=
      logDeriv_comp hG (by fun_prop)
    _ = -Complex.digamma (1 - x) := by
      rw [deriv_const_sub_id]
      simp [Complex.digamma_def]

private lemma logDeriv_sin_const_mul (a x : ℂ) :
    logDeriv (fun z : ℂ => Complex.sin (a * z)) x =
      a * Complex.cot (a * x) := by
  change logDeriv (Complex.sin ∘ fun z : ℂ => a * z) x = _
  calc
    logDeriv (Complex.sin ∘ fun z : ℂ => a * z) x =
        logDeriv Complex.sin (a * x) * deriv (fun z : ℂ => a * z) x :=
      logDeriv_comp Complex.differentiableAt_sin (by fun_prop)
    _ = a * Complex.cot (a * x) := by
      rw [Complex.logDeriv_sin, deriv_const_mul_id]
      ring

/-- The exact quarter value
`ψ(1/4) = -γ - 3 log 2 - π/2`, derived from the Gamma duplication and
reflection formulas. -/
theorem digamma_one_fourth :
    Complex.digamma (1 / 4 : ℂ) =
      -(Real.eulerMascheroniConstant : ℂ) -
        3 * (Real.log 2 : ℂ) - (Real.pi : ℂ) / 2 := by
  have hG14 : DifferentiableAt ℂ Complex.Gamma (1 / 4 : ℂ) :=
    Complex.differentiableAt_Gamma _ (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hG34 : DifferentiableAt ℂ Complex.Gamma (3 / 4 : ℂ) :=
    Complex.differentiableAt_Gamma _ (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hG12 : DifferentiableAt ℂ Complex.Gamma (1 / 2 : ℂ) :=
    Complex.differentiableAt_Gamma _ (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hG14ne : Complex.Gamma (1 / 4 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hG34ne : Complex.Gamma (3 / 4 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hG12ne : Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero (by
      intro m h
      have hr := congrArg Complex.re h
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      norm_num at hr
      linarith)
  have hPowNe : (2 : ℂ) ^ (1 - 2 * (1 / 4 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (by norm_num))
  have hPowDiff : DifferentiableAt ℂ
      (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) (1 / 4 : ℂ) :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
  have hGShiftPoint : DifferentiableAt ℂ Complex.Gamma
      ((1 / 4 : ℂ) + 1 / 2) := by
    convert hG34 using 1
    all_goals norm_num
  have hGDoublePoint : DifferentiableAt ℂ Complex.Gamma
      (2 * (1 / 4 : ℂ)) := by
    convert hG12 using 1
    all_goals norm_num
  have hGShiftNe : Complex.Gamma ((1 / 4 : ℂ) + 1 / 2) ≠ 0 := by
    convert hG34ne using 1
    all_goals norm_num
  have hGShiftDiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z + 1 / 2)) (1 / 4 : ℂ) := by
    have hlin : DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) (1 / 4 : ℂ) := by
      fun_prop
    change DifferentiableAt ℂ
      (Complex.Gamma ∘ fun z : ℂ => z + 1 / 2) (1 / 4 : ℂ)
    exact DifferentiableAt.comp
      (f := fun z : ℂ => z + 1 / 2) (g := Complex.Gamma)
      (1 / 4 : ℂ) hGShiftPoint hlin
  have hGDoubleNe : Complex.Gamma (2 * (1 / 4 : ℂ)) ≠ 0 := by
    convert hG12ne using 1
    all_goals norm_num
  have hGDoubleDiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (2 * z)) (1 / 4 : ℂ) := by
    have hlin : DifferentiableAt ℂ (fun z : ℂ => 2 * z) (1 / 4 : ℂ) := by
      fun_prop
    change DifferentiableAt ℂ
      (Complex.Gamma ∘ fun z : ℂ => 2 * z) (1 / 4 : ℂ)
    exact DifferentiableAt.comp
      (f := fun z : ℂ => 2 * z) (g := Complex.Gamma)
      (1 / 4 : ℂ) hGDoublePoint hlin
  have hSqrtPiNe : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  have hDupFun :
      (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) =
        (fun z : ℂ => Complex.Gamma (2 * z) *
          (2 : ℂ) ^ (1 - 2 * z) * (Real.sqrt Real.pi : ℂ)) := by
    funext z
    exact Complex.Gamma_mul_Gamma_add_half z
  have hDup := congrArg
    (fun f : ℂ → ℂ => logDeriv f (1 / 4 : ℂ)) hDupFun
  rw [logDeriv_mul (f := fun z : ℂ => Complex.Gamma z)
      (g := fun z : ℂ => Complex.Gamma (z + 1 / 2))
      (1 / 4 : ℂ) hG14ne hGShiftNe hG14 hGShiftDiff] at hDup
  rw [logDeriv_mul_const
      (f := fun z : ℂ => Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z))
      (1 / 4 : ℂ) (Real.sqrt Real.pi : ℂ) hSqrtPiNe] at hDup
  rw [logDeriv_mul
      (f := fun z : ℂ => Complex.Gamma (2 * z))
      (g := fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z))
      (1 / 4 : ℂ) hGDoubleNe hPowNe hGDoubleDiff hPowDiff] at hDup
  have hShiftLog := logDeriv_gamma_add_const (1 / 2) (1 / 4) hGShiftPoint
  rw [hShiftLog] at hDup
  rw [logDeriv_gamma_const_mul 2 (1 / 4) hGDoublePoint,
      logDeriv_two_cpow_one_sub_two_mul (1 / 4)] at hDup
  have hIdLog : logDeriv (fun z : ℂ => Complex.Gamma z) (1 / 4 : ℂ) =
      Complex.digamma (1 / 4 : ℂ) := by rfl
  rw [hIdLog] at hDup
  norm_num at hDup
  rw [Complex.digamma_one_half] at hDup
  have hGOneSubPoint : DifferentiableAt ℂ Complex.Gamma
      (1 - (1 / 4 : ℂ)) := by
    convert hG34 using 1
    all_goals norm_num
  have hGOneSubNe : Complex.Gamma (1 - (1 / 4 : ℂ)) ≠ 0 := by
    convert hG34ne using 1
    all_goals norm_num
  have hGOneSubDiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 - z)) (1 / 4 : ℂ) := by
    have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 - z) (1 / 4 : ℂ) := by
      fun_prop
    change DifferentiableAt ℂ
      (Complex.Gamma ∘ fun z : ℂ => 1 - z) (1 / 4 : ℂ)
    exact DifferentiableAt.comp
      (f := fun z : ℂ => 1 - z) (g := Complex.Gamma)
      (1 / 4 : ℂ) hGOneSubPoint hlin
  have hArg : (Real.pi : ℂ) * (1 / 4 : ℂ) =
      ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hSin : Complex.sin ((Real.pi : ℂ) * (1 / 4 : ℂ)) ≠ 0 := by
    rw [hArg, ← Complex.ofReal_sin, Real.sin_pi_div_four]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) (by norm_num))
  have hSinDiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) (1 / 4 : ℂ) := by
    fun_prop
  have hPiNe : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hCot : Complex.cot ((Real.pi : ℂ) * (1 / 4 : ℂ)) = 1 := by
    rw [hArg, Complex.cot, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  have hRefFun :
      (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
        (fun z : ℂ => (Real.pi : ℂ) /
          Complex.sin ((Real.pi : ℂ) * z)) := by
    funext z
    exact Complex.Gamma_mul_Gamma_one_sub z
  have hRef := congrArg
    (fun f : ℂ → ℂ => logDeriv f (1 / 4 : ℂ)) hRefFun
  rw [logDeriv_mul
      (f := fun z : ℂ => Complex.Gamma z)
      (g := fun z : ℂ => Complex.Gamma (1 - z))
      (1 / 4 : ℂ) hG14ne hGOneSubNe hG14 hGOneSubDiff] at hRef
  rw [logDeriv_div
      (f := fun _z : ℂ => (Real.pi : ℂ))
      (g := fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      (1 / 4 : ℂ) hPiNe hSin (by fun_prop) hSinDiff] at hRef
  have hOneSubLog := logDeriv_gamma_one_sub (1 / 4) hGOneSubPoint
  rw [hOneSubLog, logDeriv_sin_const_mul (Real.pi : ℂ) (1 / 4)] at hRef
  rw [hIdLog, hCot] at hRef
  simp only [logDeriv_const, Pi.zero_apply, zero_sub, mul_one] at hRef
  norm_num at hRef
  have hLogTwo : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hLogTwo] at hDup
  ring_nf at hDup hRef ⊢
  linear_combination (1 / 2 : ℂ) * hDup + (1 / 2 : ℂ) * hRef

/-- Real-part form of `digamma_one_fourth`. -/
theorem digamma_one_fourth_re :
    (Complex.digamma (1 / 4 : ℂ)).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 - Real.pi / 2 := by
  rw [digamma_one_fourth]
  norm_num
  simpa using Complex.log_ofReal_re 2

end RiemannCvs
