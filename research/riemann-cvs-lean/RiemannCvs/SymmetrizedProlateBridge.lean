import Mathlib

/-!
# Exact Fourier symmetrization of a time-limited prolate vector

A time-limited prolate eigenvector is only an approximate eigenvector of the
full Fourier transform.  There is, however, a simple exact construction:

`S_epsilon(p) = p + epsilon * Fourier(p)`,  with `epsilon^2 = 1`.

If the Fourier transform is an involution on the ambient real-even space, then
`S_epsilon(p)` has exact Fourier parity `epsilon`.  If `p` is retained by a
cutoff projection, the exterior part of `S_epsilon(p)` is exactly the Fourier
leakage of `p`; hence the optimal prolate defect scale is not lost by enforcing
exact parity.

This file formalizes only that algebra and norm bookkeeping.  It does not assert
that a zero-extended prolate function lies in the Schwartz/form domain required
by the Weil construction, nor does it identify a concrete boundary functional.
Those are separate analytic obligations.
-/

namespace RiemannCvs.SymmetrizedProlateBridge

section Algebra

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- Exact Fourier symmetrization in the sign `epsilon`. -/
def symmetrize (fourier : V →ₗ[ℝ] V) (epsilon : ℝ) (p : V) : V :=
  p + epsilon • fourier p

/-- If the Fourier map squares to the identity on `p` and `epsilon^2 = 1`, the
symmetrized vector has exact Fourier parity `epsilon`. -/
theorem symmetrize_fourier_eigenvector
    (fourier : V →ₗ[ℝ] V) (epsilon : ℝ) (p : V)
    (hFourierSq : fourier (fourier p) = p)
    (hSign : epsilon ^ 2 = 1) :
    fourier (symmetrize fourier epsilon p) =
      epsilon • symmetrize fourier epsilon p := by
  unfold symmetrize
  rw [map_add, map_smul, hFourierSq]
  rw [smul_add, smul_smul]
  have hCoeff : epsilon * epsilon = 1 := by
    simpa only [pow_two] using hSign
  rw [hCoeff, one_smul]
  module

/-- A linear boundary functional vanishes on the symmetrized vector exactly
when the corresponding source-side linear combination vanishes. -/
theorem boundary_zero_of_source_constraint
    (fourier : V →ₗ[ℝ] V)
    (ell : V →ₗ[ℝ] ℝ)
    (epsilon : ℝ) (p : V)
    (hBoundary : ell p + epsilon * ell (fourier p) = 0) :
    ell (symmetrize fourier epsilon p) = 0 := by
  unfold symmetrize
  rw [map_add, map_smul]
  simpa [smul_eq_mul] using hBoundary

/-- Exact Fourier parity turns one boundary zero into the transformed boundary
zero as well. -/
theorem transformed_boundary_zero
    (fourier : V →ₗ[ℝ] V)
    (ell : V →ₗ[ℝ] ℝ)
    (epsilon : ℝ) (p : V)
    (hEigen :
      fourier (symmetrize fourier epsilon p) =
        epsilon • symmetrize fourier epsilon p)
    (hBoundary : ell (symmetrize fourier epsilon p) = 0) :
    ell (fourier (symmetrize fourier epsilon p)) = 0 := by
  rw [hEigen, map_smul, hBoundary]
  simp

/-- If `p` has no exterior part, the exterior part of its exact Fourier
symmetrization is precisely the Fourier leakage. -/
theorem tail_symmetrize
    (fourier tail : V →ₗ[ℝ] V)
    (epsilon : ℝ) (p : V)
    (hTailP : tail p = 0) :
    tail (symmetrize fourier epsilon p) =
      epsilon • tail (fourier p) := by
  unfold symmetrize
  rw [map_add, map_smul, hTailP]
  simp

/-- If the retained Fourier transform of `p` is
`(epsilon * sigma) p`, then the retained part of the exact symmetrization is
`(1 + sigma) p`. -/
theorem retained_symmetrize_of_compressed_eigenvector
    (fourier retained : V →ₗ[ℝ] V)
    (epsilon sigma : ℝ) (p : V)
    (hRetainedP : retained p = p)
    (hCompressed :
      retained (fourier p) = (epsilon * sigma) • p)
    (hSign : epsilon ^ 2 = 1) :
    retained (symmetrize fourier epsilon p) =
      (1 + sigma) • p := by
  unfold symmetrize
  rw [map_add, map_smul, hRetainedP, hCompressed]
  rw [smul_smul]
  have hCoeff : epsilon * (epsilon * sigma) = sigma := by
    calc
      epsilon * (epsilon * sigma) = epsilon ^ 2 * sigma := by ring
      _ = sigma := by rw [hSign, one_mul]
  rw [hCoeff]
  module

end Algebra

section Norm

variable {V : Type*}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact parity symmetrization preserves the norm of the Fourier leakage when
`|epsilon| = 1`. -/
theorem norm_tail_symmetrize
    (fourier tail : V →ₗ[ℝ] V)
    (epsilon : ℝ) (p : V)
    (hTailP : tail p = 0)
    (hSignAbs : |epsilon| = 1) :
    ‖tail (symmetrize fourier epsilon p)‖ =
      ‖tail (fourier p)‖ := by
  rw [tail_symmetrize fourier tail epsilon p hTailP, norm_smul]
  simp [Real.norm_eq_abs, hSignAbs]

/-- Squared-norm version of `norm_tail_symmetrize`. -/
theorem normSq_tail_symmetrize
    (fourier tail : V →ₗ[ℝ] V)
    (epsilon : ℝ) (p : V)
    (hTailP : tail p = 0)
    (hSignAbs : |epsilon| = 1) :
    ‖tail (symmetrize fourier epsilon p)‖ ^ 2 =
      ‖tail (fourier p)‖ ^ 2 := by
  rw [norm_tail_symmetrize fourier tail epsilon p hTailP hSignAbs]

end Norm

section Hilbert

open scoped InnerProductSpace

variable {V : Type*}
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Exact total norm of a symmetrized unit vector.  The parameter `sigma` is
the signed Fourier overlap after removing the parity sign. -/
theorem normSq_symmetrize_unit
    (fourier : V →ₗ[ℝ] V)
    (epsilon sigma : ℝ) (p : V)
    (hP : ‖p‖ = 1)
    (hFourierP : ‖fourier p‖ = 1)
    (hOverlap : ⟪p, fourier p⟫_ℝ = epsilon * sigma)
    (hSign : epsilon ^ 2 = 1) :
    ‖symmetrize fourier epsilon p‖ ^ 2 = 2 + 2 * sigma := by
  have hnorm := norm_add_sq_real p (epsilon • fourier p)
  rw [hP, norm_smul, hFourierP, real_inner_smul_right,
    hOverlap] at hnorm
  simp only [one_pow, mul_one, Real.norm_eq_abs] at hnorm
  have hAbsSq : |epsilon| ^ 2 = 1 := by
    nlinarith [sq_abs epsilon]
  unfold symmetrize
  nlinarith

/-- If the unnormalized exterior defect is `1 - sigma^2`, normalization of the
exact symmetrization changes it to `(1 - sigma)/2`.  In particular, enforcing
exact Fourier parity preserves the fixed-index prolate exponential scale. -/
theorem normalized_tail_fraction
    (sigma : ℝ)
    (hSigma : -1 < sigma) :
    (1 - sigma ^ 2) / (2 + 2 * sigma) =
      (1 - sigma) / 2 := by
  have hden : 2 + 2 * sigma ≠ 0 := by
    nlinarith
  have hOnePlus : 1 + sigma ≠ 0 := by
    nlinarith
  rw [show 1 - sigma ^ 2 = (1 - sigma) * (1 + sigma) by ring]
  rw [show 2 + 2 * sigma = 2 * (1 + sigma) by ring]
  field_simp [hOnePlus]

end Hilbert

end RiemannCvs.SymmetrizedProlateBridge
