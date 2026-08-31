import Mathlib.Analysis.PSeries
import RiemannCvs.BoundaryWeylCumulative
import RiemannCvs.CvSParityDisplacement

/-!
# Combined-symbol dyadic L2 adapters

The V23 previous-core route keeps the Archimedean and prime pieces inside one
odd Loewner symbol.  This module supplies the kernel-checked algebra that turns
source estimates for that symbol into dyadic square-sum and rectangular-form
bounds.

There are four layers.

1. The exact parity formulas from `CvSParityDisplacement` give entry bounds
   for positive separated modes.
2. Finite Cauchy--Schwarz converts entry-square budgets into rectangular
   bilinear bounds.
3. The Mathlib reciprocal-square tail estimate gives the exact dyadic factor
   `1 / (2 * N)`.
4. Finite Abel summation turns an affine prefix bound into a weighted dyadic
   bound and exposes the strict endpoint expression consumed by the Arb
   certificate.

The source-specific identification of the concrete CvS symbol and its affine
prefix constants remains an explicit input.  No numerical certificate is
promoted to a Lean theorem here.
-/

namespace RiemannCvs.CombinedSymbolDyadicL2

open Finset
open scoped BigOperators

/-- The even-parity weighted numerator is controlled by pointwise symbol
amplitudes. -/
theorem evenWeightedNumerator_abs_le
    (symbol : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M) :
    |q * symbol q - p * symbol p| ≤ (p + q) * M := by
  calc
    |q * symbol q - p * symbol p| ≤
        |q * symbol q| + |p * symbol p| := abs_sub _ _
    _ = q * |symbol q| + p * |symbol p| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hp]
    _ ≤ q * M + p * M :=
      add_le_add
        (mul_le_mul_of_nonneg_left hqSymbol hq)
        (mul_le_mul_of_nonneg_left hpSymbol hp)
    _ = (p + q) * M := by ring

/-- The odd-parity weighted numerator obeys the same amplitude bound. -/
theorem oddWeightedNumerator_abs_le
    (symbol : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M) :
    |p * symbol q - q * symbol p| ≤ (p + q) * M := by
  calc
    |p * symbol q - q * symbol p| ≤
        |p * symbol q| + |q * symbol p| := abs_sub _ _
    _ = p * |symbol q| + q * |symbol p| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ p * M + q * M :=
      add_le_add
        (mul_le_mul_of_nonneg_left hqSymbol hp)
        (mul_le_mul_of_nonneg_left hpSymbol hq)
    _ = (p + q) * M := by ring

/-- Off the reflection diagonals, an even-parity Loewner entry is at most
`2*M/(q-p)` for positive ordered modes. -/
theorem oddDifferenceKernel_evenParity_abs_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hpq : p < q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      2 * M / (q - p) := by
  have hq : 0 ≤ q := le_trans hp (le_of_lt hpq)
  have hpNeQ : p ≠ q := ne_of_lt hpq
  have hpNeNegQ : p ≠ -q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hAdd : 0 < p + q := by linarith
  have hDen : 0 < (q - p) * (p + q) := mul_pos hSub hAdd
  have hDenAbs : |p ^ 2 - q ^ 2| = (q - p) * (p + q) := by
    rw [abs_of_neg]
    · ring
    · nlinarith
  rw [CvSParityDisplacement.oddDifferenceKernel_evenParity_offDiagonal
    symbol diagonal p q hpNeQ hpNeNegQ hOdd, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hDenAbs]
  have hNum := evenWeightedNumerator_abs_le symbol p q M hp hq
    hpSymbol hqSymbol
  calc
    2 * |q * symbol q - p * symbol p| / ((q - p) * (p + q)) ≤
        2 * ((p + q) * M) / ((q - p) * (p + q)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNum (by norm_num)) (le_of_lt hDen)
    _ = 2 * M / (q - p) := by
      field_simp [ne_of_gt hSub, ne_of_gt hAdd]

/-- Off the reflection diagonals, an odd-parity Loewner entry has the same
ordered-mode bound. -/
theorem oddDifferenceKernel_oddParity_abs_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hpq : p < q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      2 * M / (q - p) := by
  have hq : 0 ≤ q := le_trans hp (le_of_lt hpq)
  have hpNeQ : p ≠ q := ne_of_lt hpq
  have hpNeNegQ : p ≠ -q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hAdd : 0 < p + q := by linarith
  have hDen : 0 < (q - p) * (p + q) := mul_pos hSub hAdd
  have hDenAbs : |p ^ 2 - q ^ 2| = (q - p) * (p + q) := by
    rw [abs_of_neg]
    · ring
    · nlinarith
  rw [CvSParityDisplacement.oddDifferenceKernel_oddParity_offDiagonal
    symbol diagonal p q hpNeQ hpNeNegQ hOdd, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hDenAbs]
  have hNum := oddWeightedNumerator_abs_le symbol p q M hp hq
    hpSymbol hqSymbol
  calc
    2 * |p * symbol q - q * symbol p| / ((q - p) * (p + q)) ≤
        2 * ((p + q) * M) / ((q - p) * (p + q)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNum (by norm_num)) (le_of_lt hDen)
    _ = 2 * M / (q - p) := by
      field_simp [ne_of_gt hSub, ne_of_gt hAdd]

/-- A factor-two mode separation improves the even-parity entry to `4*M/q`. -/
theorem oddDifferenceKernel_evenParity_abs_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      4 * M / q := by
  have hpq : p < q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  calc
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
        2 * M / (q - p) :=
      oddDifferenceKernel_evenParity_abs_le symbol diagonal p q M hp hpq
        hpSymbol hqSymbol hOdd
    _ ≤ 4 * M / q := by
      rw [div_le_div_iff₀ hSub hq]
      have hProduct : 0 ≤ 2 * M * (q - 2 * p) := by positivity
      nlinarith

/-- A factor-two mode separation gives the same `4*M/q` odd-parity bound. -/
theorem oddDifferenceKernel_oddParity_abs_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      4 * M / q := by
  have hpq : p < q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  calc
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
        2 * M / (q - p) :=
      oddDifferenceKernel_oddParity_abs_le symbol diagonal p q M hp hpq
        hpSymbol hqSymbol hOdd
    _ ≤ 4 * M / q := by
      rw [div_le_div_iff₀ hSub hq]
      have hProduct : 0 ≤ 2 * M * (q - 2 * p) := by positivity
      nlinarith

/-- Squared even-parity entry budget on a factor-two separated block. -/
theorem oddDifferenceKernel_evenParity_sq_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (4 * M / q) ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  have hRight : 0 ≤ 4 * M / q := by positivity
  have hAbs := oddDifferenceKernel_evenParity_abs_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSq := (sq_le_sq₀
    (abs_nonneg
      (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)))
    hRight).2 hAbs
  simpa only [sq_abs] using hSq

/-- Squared odd-parity entry budget on a factor-two separated block. -/
theorem oddDifferenceKernel_oddParity_sq_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (4 * M / q) ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  have hRight : 0 ≤ 4 * M / q := by positivity
  have hAbs := oddDifferenceKernel_oddParity_abs_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSq := (sq_le_sq₀
    (abs_nonneg
      (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)))
    hRight).2 hAbs
  simpa only [sq_abs] using hSq

/-- Squaring the sum of two absolute values costs at most a factor two. -/
theorem abs_add_sq_le_two_mul_sum_sq (a b : ℝ) :
    (|a| + |b|) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (|a| - |b|)]

/-- A separated even-parity entry is controlled directly by the two symbol
squares carrying the dyadic reciprocal-square weight. -/
theorem oddDifferenceKernel_evenParity_sq_le_symbolSquares_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
  let M := |symbol p| + |symbol q|
  have hpSymbol : |symbol p| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol q)]
  have hqSymbol : |symbol q| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol p)]
  have hEntry := oddDifferenceKernel_evenParity_sq_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSumSq : M ^ 2 ≤ 2 * (symbol p ^ 2 + symbol q ^ 2) := by
    simpa only [M] using abs_add_sq_le_two_mul_sum_sq (symbol p) (symbol q)
  have hNumerator : 16 * M ^ 2 ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) := by
    nlinarith
  have hDen : 0 ≤ q ^ 2 := sq_nonneg q
  calc
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
        (4 * M / q) ^ 2 := hEntry
    _ = 16 * M ^ 2 / q ^ 2 := by ring
    _ ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) / q ^ 2 :=
      div_le_div_of_nonneg_right hNumerator hDen
    _ = 32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
      ring

/-- The same symbol-square dyadic weight controls a separated odd-parity
entry. -/
theorem oddDifferenceKernel_oddParity_sq_le_symbolSquares_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
  let M := |symbol p| + |symbol q|
  have hpSymbol : |symbol p| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol q)]
  have hqSymbol : |symbol q| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol p)]
  have hEntry := oddDifferenceKernel_oddParity_sq_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSumSq : M ^ 2 ≤ 2 * (symbol p ^ 2 + symbol q ^ 2) := by
    simpa only [M] using abs_add_sq_le_two_mul_sum_sq (symbol p) (symbol q)
  have hNumerator : 16 * M ^ 2 ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) := by
    nlinarith
  have hDen : 0 ≤ q ^ 2 := sq_nonneg q
  calc
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
        (4 * M / q) ^ 2 := hEntry
    _ = 16 * M ^ 2 / q ^ 2 := by ring
    _ ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) / q ^ 2 :=
      div_le_div_of_nonneg_right hNumerator hDen
    _ = 32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
      ring

/-- A column-wise entry-square budget sums with only the row cardinality. -/
theorem rectangular_sum_sq_le_card_mul_columnBudget
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (columnBudget : κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      (entry i j) ^ 2 ≤ columnBudget j) :
    (∑ i ∈ rows, ∑ j ∈ columns, (entry i j) ^ 2) ≤
      rows.card * ∑ j ∈ columns, columnBudget j := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, (entry i j) ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, columnBudget j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = rows.card * ∑ j ∈ columns, columnBudget j := by
      simp

/-- Finite Cauchy--Schwarz for a rectangular bilinear form. -/
theorem rectangular_bilinear_sq_le_entry_sq_mul_norms
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (∑ ij ∈ rows ×ˢ columns,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) *
        ((∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2) := by
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (rows ×ˢ columns)
    (fun ij => entry ij.1 ij.2)
    (fun ij => x ij.1 * y ij.2)
  have hFactor :
      (∑ ij ∈ rows ×ˢ columns, (x ij.1 * y ij.2) ^ 2) =
        (∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2 := by
    rw [Finset.sum_product]
    simpa only [mul_pow] using
      (Finset.sum_mul_sum rows columns
        (fun i => (x i) ^ 2) (fun j => (y j) ^ 2)).symm
  rw [hFactor] at hCauchy
  exact hCauchy

/-- Rectangular Cauchy--Schwarz after applying a column-wise square budget. -/
theorem rectangular_bilinear_sq_le_card_mul_columnBudget_mul_norms
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (columnBudget : κ → ℝ)
    (x : ι → ℝ) (y : κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      (entry i j) ^ 2 ≤ columnBudget j) :
    (∑ ij ∈ rows ×ˢ columns,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (rows.card * ∑ j ∈ columns, columnBudget j) *
        ((∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2) := by
  have hBilinear := rectangular_bilinear_sq_le_entry_sq_mul_norms
    rows columns entry x y
  have hEntries := rectangular_sum_sq_le_card_mul_columnBudget
    rows columns entry columnBudget hEntry
  have hEntriesProduct :
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) ≤
        rows.card * ∑ j ∈ columns, columnBudget j := by
    rw [Finset.sum_product]
    exact hEntries
  have hNorms :
      0 ≤ (∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2 := by
    positivity
  have hScale := mul_le_mul_of_nonneg_right hEntriesProduct hNorms
  exact hBilinear.trans hScale

/-- The reciprocal-square mass of one dyadic shell is at most `1/(2*N)`. -/
theorem dyadic_sum_inv_sq_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹)) ≤
      1 / (2 * (N : ℝ)) := by
  have hNle : N ≤ 2 * N := by omega
  have hBase := sum_Ioc_inv_sq_le_sub (α := ℝ) hN hNle
  calc
    (∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹)) ≤
        ((N : ℝ)⁻¹ - ((2 * N : ℕ) : ℝ)⁻¹) := hBase
    _ = 1 / (2 * (N : ℝ)) := by
      have hNReal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      push_cast
      field_simp [hNReal]
      ring

/-- Scaled reciprocal-square dyadic mass. -/
theorem dyadic_sum_scaled_inv_sq_le
    (N : ℕ) (hN : N ≠ 0) (C : ℝ) (hC : 0 ≤ C) :
    (∑ j ∈ Ioc N (2 * N), C * (((j : ℝ) ^ 2)⁻¹)) ≤
      C / (2 * (N : ℝ)) := by
  rw [← Finset.mul_sum]
  have hBase := dyadic_sum_inv_sq_le N hN
  have hScaled := mul_le_mul_of_nonneg_left hBase hC
  calc
    C * ∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹) ≤
        C * (1 / (2 * (N : ℝ))) := hScaled
    _ = C / (2 * (N : ℝ)) := by simp [div_eq_mul_inv]

/-- Abel upper bound supplied by an affine bound for every inclusive prefix. -/
theorem weightedSum_le_of_prefix_le_affine
    (r weight : ℕ → ℝ) (N : ℕ) (A B : ℝ)
    (hPrefix : ∀ j, j ≤ N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B)
    (hLastWeight : 0 ≤ weight N)
    (hWeightDecreasing : ∀ j, j < N → weight (j + 1) ≤ weight j) :
    (∑ j ∈ Finset.range (N + 1), r j * weight j) ≤
      A * (∑ j ∈ Finset.range (N + 1), weight j) + B * weight 0 := by
  let upper : ℕ → ℝ := fun j => A + if j = 0 then B else 0
  have hUpperPrefix : ∀ j,
      BoundaryWeylCumulative.prefixSum upper j = A * (j + 1) + B := by
    intro j
    induction j with
    | zero =>
        simp [BoundaryWeylCumulative.prefixSum, upper]
    | succ j ih =>
        rw [BoundaryWeylCumulative.prefixSum_succ, ih]
        simp [upper]
        ring
  have hFinal :
      BoundaryWeylCumulative.prefixSum r N * weight N ≤
        BoundaryWeylCumulative.prefixSum upper N * weight N := by
    apply mul_le_mul_of_nonneg_right _ hLastWeight
    rw [hUpperPrefix]
    exact hPrefix N le_rfl
  have hDrops :
      (∑ j ∈ Finset.range N,
          BoundaryWeylCumulative.prefixSum r j *
            (weight j - weight (j + 1))) ≤
        ∑ j ∈ Finset.range N,
          BoundaryWeylCumulative.prefixSum upper j *
            (weight j - weight (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    apply mul_le_mul_of_nonneg_right
    · rw [hUpperPrefix]
      exact hPrefix j (Nat.le_of_lt hjN)
    · exact sub_nonneg.mpr (hWeightDecreasing j hjN)
  calc
    (∑ j ∈ Finset.range (N + 1), r j * weight j) =
        BoundaryWeylCumulative.prefixSum r N * weight N +
          ∑ j ∈ Finset.range N,
            BoundaryWeylCumulative.prefixSum r j *
              (weight j - weight (j + 1)) :=
      BoundaryWeylCumulative.finiteAbelSummation r weight N
    _ ≤ BoundaryWeylCumulative.prefixSum upper N * weight N +
          ∑ j ∈ Finset.range N,
            BoundaryWeylCumulative.prefixSum upper j *
              (weight j - weight (j + 1)) :=
      add_le_add hFinal hDrops
    _ = ∑ j ∈ Finset.range (N + 1), upper j * weight j :=
      (BoundaryWeylCumulative.finiteAbelSummation upper weight N).symm
    _ = A * (∑ j ∈ Finset.range (N + 1), weight j) +
          B * weight 0 := by
      simp only [upper, add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp

/-- Reindex the positive dyadic shell as a zero-based range. -/
theorem dyadic_shifted_weight_sum_eq
    (N : ℕ) :
    (∑ k ∈ range N, ((((N + 1 + k : ℕ) : ℝ) ^ 2)⁻¹)) =
      ∑ j ∈ Ioc N (2 * N), ((((j : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hSets : Ioc N (2 * N) = Ico (N + 1) (2 * N + 1) := by
    ext j
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hSets, sum_Ico_eq_sum_range]
  have hLength : 2 * N + 1 - (N + 1) = N := by omega
  rw [hLength]

/-- Zero-based form of the dyadic reciprocal-square estimate. -/
theorem dyadic_shifted_weight_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ k ∈ range N, ((((N + 1 + k : ℕ) : ℝ) ^ 2)⁻¹)) ≤
      1 / (2 * (N : ℝ)) := by
  rw [dyadic_shifted_weight_sum_eq]
  exact dyadic_sum_inv_sq_le N hN

/-- Affine prefix control plus Abel summation gives an explicit weighted
dyadic estimate. -/
theorem dyadic_weighted_sum_le_of_prefix_le_affine
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0) (A B : ℝ) (hA : 0 ≤ A)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
      A / (2 * (N : ℝ)) +
        B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  let weight : ℕ → ℝ :=
    fun j => ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hLength : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  have hLastWeight : 0 ≤ weight (N - 1) := by
    positivity
  have hWeightDecreasing : ∀ j, j < N - 1 →
      weight (j + 1) ≤ weight j := by
    intro j _hj
    dsimp only [weight]
    have hBasePos : 0 < ((N + 1 + j : ℕ) : ℝ) := by positivity
    have hStep :
        ((N + 1 + j : ℕ) : ℝ) ≤
          ((N + 1 + (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ (N + 1 + j))
    have hSq :
        (((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
          (((N + 1 + (j + 1) : ℕ) : ℝ) ^ 2) := by
      nlinarith
    exact inv_anti₀ (sq_pos_of_pos hBasePos) hSq
  have hAbel := weightedSum_le_of_prefix_le_affine
    r weight (N - 1) A B
    (fun j hj => hPrefix j (by omega))
    hLastWeight hWeightDecreasing
  rw [hLength] at hAbel
  have hWeights :
      (∑ j ∈ range N, weight j) ≤ 1 / (2 * (N : ℝ)) := by
    simpa only [weight] using dyadic_shifted_weight_sum_le N hN
  have hScaled := mul_le_mul_of_nonneg_left hWeights hA
  calc
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        A * (∑ j ∈ range N, weight j) + B * weight 0 := by
      simpa only [weight] using hAbel
    _ ≤ A * (1 / (2 * (N : ℝ))) + B * weight 0 :=
      add_le_add hScaled le_rfl
    _ = A / (2 * (N : ℝ)) +
          B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      simp [weight, div_eq_mul_inv]

/-- A strict scaled endpoint check turns the Abel upper bound into the target
`sum < 1/N`. -/
theorem dyadic_weighted_sum_lt_one_div_of_prefix_le_affine
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0) (A B : ℝ) (hA : 0 ≤ A)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B)
    (hScaled :
      A / 2 + B * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  have hUpper := dyadic_weighted_sum_le_of_prefix_le_affine
    r N hN A B hA hPrefix
  have hNReal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        A / (2 * (N : ℝ)) +
          B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := hUpper
    _ = (1 / (N : ℝ)) *
          (A / 2 + B * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2)) := by
      field_simp [hNReal]
    _ < (1 / (N : ℝ)) * 1 :=
      mul_lt_mul_of_pos_left hScaled (by positivity)
    _ = 1 / (N : ℝ) := by ring

/-- Exact endpoint expression certified by the companion Arb script. -/
noncomputable def dyadicEndpointScaledUpper
    (main linear quadratic geometric : ℝ) (N : ℕ) : ℝ :=
  (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) / 2 +
    geometric * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2)

/-- The factor `N/(N+1)^2` decreases on positive natural modes. -/
theorem natCast_div_succ_sq_antitone
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (M : ℝ) / (((M + 1 : ℕ) : ℝ) ^ 2) ≤
      (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNMReal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hMReal : (1 : ℝ) ≤ M := hNReal.trans hNMReal
  have hNDen : 0 < (((N + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hMDen : 0 < (((M + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [div_le_div_iff₀ hMDen hNDen]
  push_cast
  have hFirst : 0 ≤ (M : ℝ) - N := sub_nonneg.mpr hNMReal
  have hSecond : 0 ≤ (N : ℝ) * M - 1 := by nlinarith
  have hProduct :
      0 ≤ ((M : ℝ) - N) * ((N : ℝ) * M - 1) :=
    mul_nonneg hFirst hSecond
  nlinarith

/-- The complete scaled endpoint is antitone once all decaying coefficients
are nonnegative. -/
theorem dyadicEndpointScaledUpper_antitone
    (main linear quadratic geometric : ℝ) (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M)
    (hLinear : 0 ≤ linear) (hQuadratic : 0 ≤ quadratic)
    (hGeometric : 0 ≤ geometric) :
    dyadicEndpointScaledUpper main linear quadratic geometric M ≤
      dyadicEndpointScaledUpper main linear quadratic geometric N := by
  have hNPos : 0 < (N : ℝ) := by positivity
  have hNMReal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hInv :
      1 / (M : ℝ) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNPos hNMReal
  have hInvSq :
      1 / (M : ℝ) ^ 2 ≤ 1 / (N : ℝ) ^ 2 := by
    have hNInv : 0 ≤ 1 / (N : ℝ) := by positivity
    have hMInv : 0 ≤ 1 / (M : ℝ) := by positivity
    have hSq := (sq_le_sq₀ hMInv hNInv).2 hInv
    simpa [one_div, inv_pow] using hSq
  have hLinearTerm :
      linear / (M : ℝ) ≤ linear / (N : ℝ) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInv hLinear
  have hQuadraticTerm :
      quadratic / (M : ℝ) ^ 2 ≤ quadratic / (N : ℝ) ^ 2 := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInvSq hQuadratic
  have hGeometricRatio := natCast_div_succ_sq_antitone N M hN hNM
  have hGeometricTerm :
      geometric * (M : ℝ) / (((M + 1 : ℕ) : ℝ) ^ 2) ≤
        geometric * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hGeometricRatio hGeometric
  unfold dyadicEndpointScaledUpper
  have hSlope :
      main + linear / (M : ℝ) + quadratic / (M : ℝ) ^ 2 ≤
        main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2 :=
    add_le_add (add_le_add le_rfl hLinearTerm) hQuadraticTerm
  exact add_le_add
    (div_le_div_of_nonneg_right hSlope (by norm_num))
    hGeometricTerm

/-- One strict endpoint certificate controls every later natural mode. -/
theorem dyadicEndpointScaledUpper_lt_one_of_start
    (main linear quadratic geometric : ℝ) (start N : ℕ)
    (hStart : 1 ≤ start) (hStartN : start ≤ N)
    (hLinear : 0 ≤ linear) (hQuadratic : 0 ≤ quadratic)
    (hGeometric : 0 ≤ geometric)
    (hEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric start < 1) :
    dyadicEndpointScaledUpper main linear quadratic geometric N < 1 :=
  (dyadicEndpointScaledUpper_antitone
    main linear quadratic geometric start N hStart hStartN
    hLinear hQuadratic hGeometric).trans_lt hEndpoint

/-- Direct interface from the Arb endpoint expression to one weighted shell. -/
theorem dyadic_weighted_sum_lt_one_div_of_endpoint
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0)
    (main linear quadratic geometric : ℝ)
    (hSlope :
      0 ≤ main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤
        (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) *
          (j + 1) + geometric)
    (hEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric N < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  apply dyadic_weighted_sum_lt_one_div_of_prefix_le_affine
    r N hN
    (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2)
    geometric hSlope hPrefix
  simpa only [dyadicEndpointScaledUpper] using hEndpoint

/-- A strict start-mode endpoint plus nonnegative coefficients controls every
later weighted shell once its source prefix bound has been identified. -/
theorem dyadic_weighted_sum_lt_one_div_of_start_endpoint
    (r : ℕ → ℝ) (start N : ℕ)
    (main linear quadratic geometric : ℝ)
    (hStart : 1 ≤ start) (hStartN : start ≤ N)
    (hMain : 0 ≤ main) (hLinear : 0 ≤ linear)
    (hQuadratic : 0 ≤ quadratic) (hGeometric : 0 ≤ geometric)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤
        (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) *
          (j + 1) + geometric)
    (hStartEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric start < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  have hN : N ≠ 0 := by omega
  have hSlope :
      0 ≤ main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2 := by
    positivity
  have hEndpoint := dyadicEndpointScaledUpper_lt_one_of_start
    main linear quadratic geometric start N hStart hStartN
    hLinear hQuadratic hGeometric hStartEndpoint
  exact dyadic_weighted_sum_lt_one_div_of_endpoint
    r N hN main linear quadratic geometric hSlope hPrefix hEndpoint

end RiemannCvs.CombinedSymbolDyadicL2
