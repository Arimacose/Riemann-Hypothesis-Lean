import Mathlib

/-!
# Cumulative residues for a finite boundary-Weyl function

Let `lambda 0 < ... < lambda N` be the poles of a finite resolvent ratio and
let `r j` be its residues.  Before the first pole the weights

`a j = 1 / (lambda j - x)`

are positive and decreasing.  Abel summation rewrites

`sum_j r j * a j`

using the cumulative residues `R j = sum_{k <= j} r k`.  Thus nonnegative
proper prefix sums and a strictly positive final sum force the boundary-Weyl
function to be strictly positive before its first pole.  Individual residues
need not be positive.

This module proves the finite algebra and the resulting scalar no-zero
criterion.  It also records that the positive scalar denominator arising from
a negative rank-one update preserves that sign.  Identifying a concrete CvS
matrix ratio with this abstract Weyl sum, and obtaining bounds uniform in the
cutoff, remain separate analytic obligations.
-/

namespace RiemannCvs.BoundaryWeylCumulative

open scoped BigOperators

/-- Inclusive cumulative sum `r 0 + ... + r j`. -/
def prefixSum (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), r k

@[simp]
theorem prefixSum_zero (r : ℕ → ℝ) :
    prefixSum r 0 = r 0 := by
  simp [prefixSum]

@[simp]
theorem prefixSum_succ (r : ℕ → ℝ) (j : ℕ) :
    prefixSum r (j + 1) = prefixSum r j + r (j + 1) := by
  unfold prefixSum
  simpa [Nat.add_assoc] using
    (Finset.sum_range_succ (f := r) (j + 1))

/-- Finite Abel summation in the form adapted to cumulative residues. -/
theorem finiteAbelSummation
    (r weight : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), r j * weight j) =
      prefixSum r N * weight N +
        ∑ j ∈ Finset.range N,
          prefixSum r j * (weight j - weight (j + 1)) := by
  induction N with
  | zero =>
      simp [prefixSum]
  | succ N ih =>
      calc
        (∑ j ∈ Finset.range (N.succ + 1), r j * weight j) =
            (∑ j ∈ Finset.range (N + 1), r j * weight j) +
              r (N + 1) * weight (N + 1) := by
                simp only [Nat.succ_eq_add_one]
                rw [Finset.sum_range_succ]
        _ =
            (prefixSum r N * weight N +
                ∑ j ∈ Finset.range N,
                  prefixSum r j * (weight j - weight (j + 1))) +
              r (N + 1) * weight (N + 1) := by
                rw [ih]
        _ =
            prefixSum r N.succ * weight N.succ +
              ∑ j ∈ Finset.range N.succ,
                prefixSum r j * (weight j - weight (j + 1)) := by
                rw [Finset.sum_range_succ, prefixSum_succ]
                simp only [Nat.succ_eq_add_one]
                ring

/-- The Abel representation is nonnegative when all relevant cumulative sums
and weight drops are nonnegative. -/
theorem weightedSum_nonnegOfCumulative
    (r weight : ℕ → ℝ) (N : ℕ)
    (hPrefix : ∀ j, j ≤ N → 0 ≤ prefixSum r j)
    (hLastWeight : 0 ≤ weight N)
    (hWeightDecreasing : ∀ j, j < N → weight (j + 1) ≤ weight j) :
    0 ≤ ∑ j ∈ Finset.range (N + 1), r j * weight j := by
  rw [finiteAbelSummation]
  apply add_nonneg
  · exact mul_nonneg (hPrefix N le_rfl) hLastWeight
  · apply Finset.sum_nonneg
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact mul_nonneg
      (hPrefix j (Nat.le_of_lt hjN))
      (sub_nonneg.mpr (hWeightDecreasing j hjN))

/-- Proper cumulative sums may vanish, but a positive final cumulative sum and
a positive final weight make the whole weighted sum strictly positive. -/
theorem weightedSum_posOfCumulative
    (r weight : ℕ → ℝ) (N : ℕ)
    (hProperPrefix : ∀ j, j < N → 0 ≤ prefixSum r j)
    (hFinalPrefix : 0 < prefixSum r N)
    (hLastWeight : 0 < weight N)
    (hWeightDecreasing : ∀ j, j < N → weight (j + 1) ≤ weight j) :
    0 < ∑ j ∈ Finset.range (N + 1), r j * weight j := by
  rw [finiteAbelSummation]
  apply add_pos_of_pos_of_nonneg (mul_pos hFinalPrefix hLastWeight)
  apply Finset.sum_nonneg
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  exact mul_nonneg
    (hProperPrefix j hjN)
    (sub_nonneg.mpr (hWeightDecreasing j hjN))

/-- Finite boundary-Weyl sum with real poles and residues.  The sign convention
uses positive denominators to the left of the first pole. -/
noncomputable def finiteBoundaryWeyl
    (poles residues : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), residues j / (poles j - x)

/-- Cumulative residue criterion: the finite boundary-Weyl function is
strictly positive everywhere to the left of its first pole. -/
theorem finiteBoundaryWeyl_pos_beforeFirstPole
    (poles residues : ℕ → ℝ) (N : ℕ) (x : ℝ)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix : ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalPrefix : 0 < prefixSum residues N) :
    0 < finiteBoundaryWeyl poles residues N x := by
  have hLastWeight : 0 < 1 / (poles N - x) := by
    apply one_div_pos.mpr
    have hxN : x < poles N :=
      lt_of_lt_of_le hBefore (hPoles.monotone (Nat.zero_le N))
    exact sub_pos.mpr hxN
  have hWeightDecreasing :
      ∀ j, j < N →
        1 / (poles (j + 1) - x) ≤ 1 / (poles j - x) := by
    intro j _hjN
    have hxj : x < poles j :=
      lt_of_lt_of_le hBefore (hPoles.monotone (Nat.zero_le j))
    apply one_div_le_one_div_of_le (sub_pos.mpr hxj)
    have hj : poles j < poles (j + 1) := hPoles (Nat.lt_succ_self j)
    linarith
  simpa [finiteBoundaryWeyl, div_eq_mul_inv] using
    weightedSum_posOfCumulative residues
      (fun j => 1 / (poles j - x)) N
      hProperPrefix hFinalPrefix hLastWeight hWeightDecreasing

/-- In particular, the finite boundary-Weyl function has no zero before its
first pole. -/
theorem finiteBoundaryWeyl_ne_zero_beforeFirstPole
    (poles residues : ℕ → ℝ) (N : ℕ) (x : ℝ)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix : ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalPrefix : 0 < prefixSum residues N) :
    finiteBoundaryWeyl poles residues N x ≠ 0 :=
  ne_of_gt (finiteBoundaryWeyl_pos_beforeFirstPole
    poles residues N x hPoles hBefore hProperPrefix hFinalPrefix)

/-- Algebraic characteristic-factor consequence.  Once a concrete rectangular
displacement identity supplies

`oddCharacteristic = scale * finiteBoundaryWeyl * evenCharacteristic`,

the cumulative-residue criterion excludes an odd characteristic root below
the first even pole. -/
theorem factorizedNumerator_ne_zero_beforeFirstPole
    (poles residues : ℕ → ℝ) (N : ℕ) (x : ℝ)
    (scale evenCharacteristic oddCharacteristic : ℝ)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix : ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalPrefix : 0 < prefixSum residues N)
    (hScale : scale ≠ 0)
    (hEvenCharacteristic : evenCharacteristic ≠ 0)
    (hFactorization :
      oddCharacteristic =
        scale * finiteBoundaryWeyl poles residues N x *
          evenCharacteristic) :
    oddCharacteristic ≠ 0 := by
  rw [hFactorization]
  exact mul_ne_zero
    (mul_ne_zero hScale
      (ne_of_gt (finiteBoundaryWeyl_pos_beforeFirstPole
        poles residues N x hPoles hBefore
        hProperPrefix hFinalPrefix)))
    hEvenCharacteristic

/-- The scalar Sherman--Morrison denominator for a negative rank-one update is
positive when both the update size and the uncorrected Weyl value are
positive. -/
theorem rankOneDenominator_pos
    (delta weyl : ℝ)
    (hDelta : 0 < delta)
    (hWeyl : 0 < weyl) :
    0 < 1 + delta * weyl := by
  nlinarith [mul_pos hDelta hWeyl]

/-- The corresponding corrected scalar Weyl ratio remains positive. -/
theorem rankOneCorrectedWeyl_pos
    (delta weyl : ℝ)
    (hDelta : 0 < delta)
    (hWeyl : 0 < weyl) :
    0 < weyl / (1 + delta * weyl) := by
  exact div_pos hWeyl (rankOneDenominator_pos delta weyl hDelta hWeyl)

/-- Combined finite criterion for the rank-one corrected boundary-Weyl ratio.
This is the scalar sign conclusion used after a matrix-level
Sherman--Morrison identity has been established. -/
theorem rankOneCorrectedBoundaryWeyl_pos_beforeFirstPole
    (poles residues : ℕ → ℝ) (N : ℕ) (x delta : ℝ)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix : ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalPrefix : 0 < prefixSum residues N)
    (hDelta : 0 < delta) :
    0 < finiteBoundaryWeyl poles residues N x /
      (1 + delta * finiteBoundaryWeyl poles residues N x) := by
  apply rankOneCorrectedWeyl_pos delta
  · exact hDelta
  · exact finiteBoundaryWeyl_pos_beforeFirstPole
      poles residues N x hPoles hBefore hProperPrefix hFinalPrefix

end RiemannCvs.BoundaryWeylCumulative
