import Mathlib

/-!
# Orthogonality of exact-parity prolate modes and their leakage tails

Distinct principal vectors of the time-frequency limiting problem are
orthogonal, their full Fourier transforms are orthogonal, and their retained
Fourier components are scalar multiples of the original principal vectors.
The exterior leakage tails are therefore orthogonal.  Exact Fourier
symmetrization preserves this diagonal structure.

This file records the Hilbert-space bookkeeping.  It does not construct the
principal vectors or prove the compressed Fourier eigenrelations.
-/

namespace RiemannCvs.SymmetrizedProlateOrthogonality

open scoped InnerProductSpace

variable {V : Type*}
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Orthogonality of total vectors and of all retained/cross terms implies
orthogonality of the two residual tails. -/
theorem residualsOrthogonal
    (f0 f1 p0 p1 t0 t1 : V)
    (hf0 : f0 = p0 + t0)
    (hf1 : f1 = p1 + t1)
    (hTotal : ⟪f0, f1⟫_ℝ = 0)
    (hPP : ⟪p0, p1⟫_ℝ = 0)
    (hPT : ⟪p0, t1⟫_ℝ = 0)
    (hTP : ⟪t0, p1⟫_ℝ = 0) :
    ⟪t0, t1⟫_ℝ = 0 := by
  rw [hf0, hf1, inner_add_left, inner_add_right, inner_add_right] at hTotal
  rw [hPP, hPT, hTP] at hTotal
  simpa using hTotal

/-- If the retained Fourier components are scalar multiples of orthogonal
principal vectors, all retained/exterior cross terms vanish. -/
theorem retained_tail_cross_zero
    (f0 f1 p0 p1 t0 t1 : V)
    (a0 a1 : ℝ)
    (hf0 : f0 = a0 • p0 + t0)
    (hf1 : f1 = a1 • p1 + t1)
    (hp0t1 : ⟪p0, f1⟫_ℝ = 0)
    (ht0p1 : ⟪f0, p1⟫_ℝ = 0)
    (hpp : ⟪p0, p1⟫_ℝ = 0) :
    ⟪p0, t1⟫_ℝ = 0 ∧ ⟪t0, p1⟫_ℝ = 0 := by
  constructor
  · rw [hf1, inner_add_right, real_inner_smul_right, hpp] at hp0t1
    simpa using hp0t1
  · rw [hf0, inner_add_left, real_inner_smul_left, hpp] at ht0p1
    simpa using ht0p1

/-- Orthogonality of distinct Fourier principal vectors passes to the exterior
leakage tails. -/
theorem prolateTailsOrthogonal
    (f0 f1 p0 p1 t0 t1 : V)
    (a0 a1 : ℝ)
    (hf0 : f0 = a0 • p0 + t0)
    (hf1 : f1 = a1 • p1 + t1)
    (hTotal : ⟪f0, f1⟫_ℝ = 0)
    (hPP : ⟪p0, p1⟫_ℝ = 0)
    (hp0f1 : ⟪p0, f1⟫_ℝ = 0)
    (hf0p1 : ⟪f0, p1⟫_ℝ = 0) :
    ⟪t0, t1⟫_ℝ = 0 := by
  obtain ⟨hPT, hTP⟩ := retained_tail_cross_zero
    f0 f1 p0 p1 t0 t1 a0 a1 hf0 hf1 hp0f1 hf0p1 hPP
  have hf0' : f0 = a0 • p0 + t0 := hf0
  have hf1' : f1 = a1 • p1 + t1 := hf1
  have hScaledPP : ⟪a0 • p0, a1 • p1⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hPP]
    ring
  have hScaledPT : ⟪a0 • p0, t1⟫_ℝ = 0 := by
    rw [real_inner_smul_left, hPT]
    ring
  have hScaledTP : ⟪t0, a1 • p1⟫_ℝ = 0 := by
    rw [real_inner_smul_right, hTP]
    ring
  exact residualsOrthogonal
    f0 f1 (a0 • p0) (a1 • p1) t0 t1
    hf0' hf1' hTotal hScaledPP hScaledPT hScaledTP

/-- Exact Fourier symmetrizations of two modes are orthogonal whenever the
principal vectors, their Fourier transforms, and the two mixed pairs are
orthogonal. -/
theorem symmetrizedModesOrthogonal
    (p0 p1 f0 f1 : V)
    (epsilon : ℝ)
    (hPP : ⟪p0, p1⟫_ℝ = 0)
    (hFF : ⟪f0, f1⟫_ℝ = 0)
    (hPF : ⟪p0, f1⟫_ℝ = 0)
    (hFP : ⟪f0, p1⟫_ℝ = 0) :
    ⟪p0 + epsilon • f0, p1 + epsilon • f1⟫_ℝ = 0 := by
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hPP, hFF, hPF, hFP]
  ring

/-- Pythagorean norm formula for a finite combination of three mutually
orthogonal leakage tails. -/
theorem threeTailCombinationNormSq
    (t0 t1 t2 : V)
    (a0 a1 a2 : ℝ)
    (h01 : ⟪t0, t1⟫_ℝ = 0)
    (h02 : ⟪t0, t2⟫_ℝ = 0)
    (h12 : ⟪t1, t2⟫_ℝ = 0) :
    ‖a0 • t0 + a1 • t1 + a2 • t2‖ ^ 2 =
      a0 ^ 2 * ‖t0‖ ^ 2 +
        a1 ^ 2 * ‖t1‖ ^ 2 +
        a2 ^ 2 * ‖t2‖ ^ 2 := by
  have h0_12 :
      ⟪a0 • t0, a1 • t1 + a2 • t2⟫_ℝ = 0 := by
    rw [inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, h01, h02]
    ring
  have h12Scaled : ⟪a1 • t1, a2 • t2⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, h12]
    ring
  rw [norm_add_sq_real, h0_12, add_zero,
    norm_add_sq_real, h12Scaled, add_zero,
    norm_smul, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs]
  rw [sq_abs a0, sq_abs a1, sq_abs a2]
  ring

end RiemannCvs.SymmetrizedProlateOrthogonality
