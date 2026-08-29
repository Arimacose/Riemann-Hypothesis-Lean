import Mathlib
import RiemannCvs.BoundaryRankOneGap

/-!
# V22 zero-mode correction

The cutoff-free archimedean closed form contains, for frequency `n = 0`, the
two positive geometric sums

`G₁(L) = sum exp (-(2k+1/2)L) / (2k+1/2)` and
`G₂(L) = sum exp (-(2k+1/2)L) / (2k+1/2)²`.

Writing `X₀` for the uncorrected trigamma term, their inclusion changes

`X_C(0)` to `X₀ - L G₁ - G₂`.

Because the archimedean diagonal contains `-(2/L) X_C(0)`, the corresponding
cutoff-free matrix entry is updated by

`T₀₀,new = T₀₀,old - (2 G₁ + 2 G₂/L)`.

This module proves the sign and rank-one consequences of that identity and
also records positivity of every finite partial sum.  Identifying the infinite
series with the concrete CvS integral and certifying its numerical value are
performed by the companion Arb/mpmath audit; they are not postulated here.
-/

namespace RiemannCvs.ZeroModeCorrection

noncomputable section

/-- The positive half-odd-integer exponent appearing in the geometric tail. -/
def halfOdd (k : ℕ) : ℝ := 2 * (k : ℝ) + 1 / 2

theorem halfOdd_pos (k : ℕ) : 0 < halfOdd k := by
  unfold halfOdd
  positivity

/-- The `k`th summand of `G₁(L)`. -/
def g1Term (L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(halfOdd k * L)) / halfOdd k

/-- The `k`th summand of `G₂(L)`. -/
def g2Term (L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(halfOdd k * L)) / (halfOdd k) ^ 2

theorem g1Term_pos (L : ℝ) (k : ℕ) : 0 < g1Term L k := by
  exact div_pos (Real.exp_pos _) (halfOdd_pos k)

theorem g2Term_pos (L : ℝ) (k : ℕ) : 0 < g2Term L k := by
  exact div_pos (Real.exp_pos _) (sq_pos_of_pos (halfOdd_pos k))

/-- A finite partial sum of the zero-frequency `G₁` correction. -/
def g1Partial (L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, g1Term L k

/-- A finite partial sum of the zero-frequency `G₂` correction. -/
def g2Partial (L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, g2Term L k

theorem g1Partial_nonneg (L : ℝ) (N : ℕ) : 0 ≤ g1Partial L N := by
  exact Finset.sum_nonneg fun k _ => (g1Term_pos L k).le

theorem g2Partial_nonneg (L : ℝ) (N : ℕ) : 0 ≤ g2Partial L N := by
  exact Finset.sum_nonneg fun k _ => (g2Term_pos L k).le

theorem g1Partial_pos (L : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < g1Partial L N := by
  exact Finset.sum_pos
    (fun k _ => g1Term_pos L k)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))

theorem g2Partial_pos (L : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < g2Partial L N := by
  exact Finset.sum_pos
    (fun k _ => g2Term_pos L k)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))

/-- The amount by which the corrected cutoff-free zero entry is lowered. -/
def zeroModeDelta (L G1 G2 : ℝ) : ℝ :=
  2 * G1 + 2 * G2 / L

theorem zeroModeDelta_pos
    (L G1 G2 : ℝ)
    (hL : 0 < L)
    (hG1 : 0 < G1)
    (hG2 : 0 ≤ G2) :
    0 < zeroModeDelta L G1 G2 := by
  have hquot : 0 ≤ 2 * G2 / L :=
    div_nonneg (mul_nonneg (by norm_num) hG2) hL.le
  unfold zeroModeDelta
  nlinarith

theorem zeroModeDelta_partial_pos
    (L : ℝ) {N : ℕ}
    (hL : 0 < L)
    (hN : 0 < N) :
    0 < zeroModeDelta L (g1Partial L N) (g2Partial L N) := by
  exact zeroModeDelta_pos L (g1Partial L N) (g2Partial L N)
    hL (g1Partial_pos L hN) (g2Partial_nonneg L N)

/-- Corrected zero-frequency `X_C` coefficient. -/
def correctedXC (base L G1 G2 : ℝ) : ℝ :=
  base - L * G1 - G2

theorem correctedXC_lt_base
    (base L G1 G2 : ℝ)
    (hL : 0 < L)
    (hG1 : 0 < G1)
    (hG2 : 0 ≤ G2) :
    correctedXC base L G1 G2 < base := by
  unfold correctedXC
  nlinarith [mul_pos hL hG1]

/-- The part of the archimedean diagonal in which `X_C` occurs. -/
def archDiagonal (background L XC : ℝ) : ℝ :=
  background - (2 / L) * XC

/-- The cutoff-free entry convention `T = W₀₂ - W_R - W_p`. -/
def cutoffFreeEntry (pole arch prime : ℝ) : ℝ :=
  pole - arch - prime

/-- Substituting the corrected `X_C(0)` raises `W_R(0,0)` by `zeroModeDelta`. -/
theorem archDiagonal_corrected
    (background base L G1 G2 : ℝ)
    (hL : L ≠ 0) :
    archDiagonal background L (correctedXC base L G1 G2) =
      archDiagonal background L base + zeroModeDelta L G1 G2 := by
  unfold archDiagonal correctedXC zeroModeDelta
  field_simp [hL]
  ring

/-- Consequently the cutoff-free zero entry is lowered by the same amount. -/
theorem cutoffFreeEntry_corrected
    (pole background prime base L G1 G2 : ℝ)
    (hL : L ≠ 0) :
    cutoffFreeEntry pole
        (archDiagonal background L (correctedXC base L G1 G2)) prime =
      cutoffFreeEntry pole (archDiagonal background L base) prime -
        zeroModeDelta L G1 G2 := by
  rw [archDiagonal_corrected background base L G1 G2 hL]
  unfold cutoffFreeEntry
  ring

/-- Abstract quadratic-form realization of the zero-mode rank-one update. -/
def correctedQuadratic
    (qOld zeroCoordinate : α → ℝ)
    (delta : ℝ) (x : α) : ℝ :=
  qOld x - delta * (zeroCoordinate x) ^ 2

/-- The correction is invisible on the zero-coordinate kernel. -/
theorem correctedQuadratic_eq_on_kernel
    (qOld zeroCoordinate : α → ℝ)
    (delta : ℝ) (x : α)
    (hZero : zeroCoordinate x = 0) :
    correctedQuadratic qOld zeroCoordinate delta x = qOld x := by
  exact RiemannCvs.BoundaryRankOneGap.updateVanishesOnBoundaryKernel
    qOld (correctedQuadratic qOld zeroCoordinate delta) zeroCoordinate
    delta x rfl hZero

/-- A positive zero-mode correction lowers every quadratic value. -/
theorem correctedQuadratic_le
    (qOld zeroCoordinate : α → ℝ)
    (delta : ℝ) (x : α)
    (hDelta : 0 ≤ delta) :
    correctedQuadratic qOld zeroCoordinate delta x ≤ qOld x := by
  exact RiemannCvs.BoundaryRankOneGap.negativeRankOneLowersValue
    qOld (correctedQuadratic qOld zeroCoordinate delta) zeroCoordinate
    delta x hDelta rfl

/-- A nonzero zero coordinate makes a positive correction strictly downward. -/
theorem correctedQuadratic_lt
    (qOld zeroCoordinate : α → ℝ)
    (delta : ℝ) (x : α)
    (hDelta : 0 < delta)
    (hZero : zeroCoordinate x ≠ 0) :
    correctedQuadratic qOld zeroCoordinate delta x < qOld x := by
  unfold correctedQuadratic
  have hsq : 0 < (zeroCoordinate x) ^ 2 := sq_pos_of_ne_zero hZero
  nlinarith

/-- In particular, any parity sector whose vectors have zero central Fourier
coordinate is unchanged by the V22 correction. -/
theorem zeroCoordinateSector_invisible
    (qOld zeroCoordinate : α → ℝ)
    (delta : ℝ)
    (hSector : ∀ x, zeroCoordinate x = 0) :
    ∀ x, correctedQuadratic qOld zeroCoordinate delta x = qOld x := by
  intro x
  exact correctedQuadratic_eq_on_kernel qOld zeroCoordinate delta x (hSector x)

end

end RiemannCvs.ZeroModeCorrection
