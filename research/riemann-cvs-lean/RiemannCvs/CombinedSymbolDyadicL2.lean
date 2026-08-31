import Mathlib.Analysis.PSeries
import RiemannCvs.BoundaryWeylCumulative
import RiemannCvs.CvSParityDisplacement

/-!
# Combined-symbol dyadic L2 adapters

The V23 previous-core route keeps the Archimedean and prime pieces inside one
odd Loewner symbol.  This module supplies the kernel-checked algebra that turns
source estimates for that symbol into dyadic square-sum and rectangular-form
bounds.

There are seven layers.

1. A source-algebra layer builds the finite prime sine polynomial, proves its
   oddness, combines it with an odd Archimedean symbol, preserves the exact
   `1 / π` normalization through the Loewner kernel, and removes the endpoint
   phase `2 * π * n` on natural Fourier modes.
2. The exact parity formulas from `CvSParityDisplacement` give entry bounds
   for positive separated modes.
3. Finite Cauchy--Schwarz converts entry-square budgets into rectangular
   bilinear bounds.
4. The Mathlib reciprocal-square tail estimate gives the exact dyadic factor
   `1 / (2 * N)`.
5. Finite Abel summation turns an affine prefix bound into a weighted dyadic
   bound and exposes the strict endpoint expression consumed by the Arb
   certificate.
6. Rowwise square estimates and rectangular Cauchy--Schwarz send that scalar
   bound into a matrix Frobenius budget and then into coercive relative energy.
7. The newest-band specialization closes the constant `24*C`, while the exact
   doubled-shell identity supplies the one-half transport used by the recursive
   channel envelope.

The source-specific analytic identification of the concrete Archimedean and
prime matrix entries, and their affine prefix constants, remains an explicit
input.  No numerical certificate is promoted to a Lean theorem here.
-/

namespace RiemannCvs.CombinedSymbolDyadicL2

open Finset
open scoped BigOperators

/-!
## Combined-symbol source algebra

The prime-power contribution is a finite sine polynomial.  The following
definitions and identities close the purely algebraic part of combining it
with an odd Archimedean symbol and applying the concrete `1 / π` Fourier
normalization.  The remaining source task is to connect the analytic CvS
entries and their diagonal data to these functions.
-/

/-- A finite real sine polynomial, the exact shape of the prime-power part of
the combined CvS Loewner symbol. -/
noncomputable def finiteSineSymbol
    {ι : Type*} [Fintype ι]
    (weight phase : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, weight i * Real.sin (phase i * x)

/-- Every finite sine polynomial is odd. -/
theorem finiteSineSymbol_odd
    {ι : Type*} [Fintype ι]
    (weight phase : ι → ℝ) :
    Function.Odd (finiteSineSymbol weight phase) := by
  intro x
  simp [finiteSineSymbol]

/-- The source-level combined symbol keeps the Archimedean and prime pieces
inside one Loewner symbol. -/
noncomputable def combinedSineSymbol
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (weight phase : ι → ℝ) (x : ℝ) : ℝ :=
  arch x + finiteSineSymbol weight phase x

/-- An odd Archimedean symbol plus the prime sine polynomial is odd. -/
theorem combinedSineSymbol_odd
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (weight phase : ι → ℝ)
    (hArch : Function.Odd arch) :
    Function.Odd (combinedSineSymbol arch weight phase) := by
  intro x
  rw [combinedSineSymbol, combinedSineSymbol, hArch x,
    finiteSineSymbol_odd weight phase x]
  ring

/-- Fourier normalization used by the concrete CvS off-diagonal kernel. -/
noncomputable def fourierNormalizedSymbol
    (symbol : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.pi) * symbol x

/-- Fourier normalization preserves oddness. -/
theorem fourierNormalizedSymbol_odd
    (symbol : ℝ → ℝ) (hSymbol : Function.Odd symbol) :
    Function.Odd (fourierNormalizedSymbol symbol) := by
  intro x
  rw [fourierNormalizedSymbol, fourierNormalizedSymbol, hSymbol x]
  ring

/-- Adding source symbols and diagonal data adds their complete Loewner
kernels. -/
theorem oddDifferenceKernel_add
    (leftSymbol leftDiagonal rightSymbol rightDiagonal : ℝ → ℝ)
    (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fun x => leftSymbol x + rightSymbol x)
        (fun x => leftDiagonal x + rightDiagonal x) p q =
      CvSParityDisplacement.oddDifferenceKernel leftSymbol leftDiagonal p q +
        CvSParityDisplacement.oddDifferenceKernel rightSymbol rightDiagonal p q := by
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel]
  · simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    ring

/-- Scaling both the off-diagonal symbol and diagonal source data scales the
complete Loewner kernel exactly. -/
theorem oddDifferenceKernel_smul
    (symbol diagonal : ℝ → ℝ) (scale p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fun x => scale * symbol x)
        (fun x => scale * diagonal x) p q =
      scale * CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q := by
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel]
  · simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    ring

/-- The exact `1 / π` CvS normalization commutes with the complete Loewner
kernel when its diagonal data use the same normalization. -/
theorem oddDifferenceKernel_fourierNormalized
    (symbol diagonal : ℝ → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol symbol)
        (fourierNormalizedSymbol diagonal) p q =
      (1 / Real.pi) *
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q := by
  change CvSParityDisplacement.oddDifferenceKernel
      (fun x => (1 / Real.pi) * symbol x)
      (fun x => (1 / Real.pi) * diagonal x) p q = _
  exact oddDifferenceKernel_smul symbol diagonal (1 / Real.pi) p q

/-- End-to-end algebraic source identity: the normalized combined kernel is
the normalized sum of the Archimedean and prime sine Loewner kernels. -/
theorem oddDifferenceKernel_fourierNormalized_combined
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (weight phase : ι → ℝ)
    (primeDiagonal : ℝ → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol (combinedSineSymbol arch weight phase))
        (fourierNormalizedSymbol
          (fun x => archDiagonal x + primeDiagonal x)) p q =
      (1 / Real.pi) *
        (CvSParityDisplacement.oddDifferenceKernel arch archDiagonal p q +
          CvSParityDisplacement.oddDifferenceKernel
            (finiteSineSymbol weight phase) primeDiagonal p q) := by
  rw [oddDifferenceKernel_fourierNormalized]
  change (1 / Real.pi) *
      CvSParityDisplacement.oddDifferenceKernel
        (fun x => arch x + finiteSineSymbol weight phase x)
        (fun x => archDiagonal x + primeDiagonal x) p q = _
  exact congrArg (fun z => (1 / Real.pi) * z)
    (oddDifferenceKernel_add arch archDiagonal
      (finiteSineSymbol weight phase) primeDiagonal p q)

/-- The endpoint phase `2 * π * n` vanishes exactly on every natural Fourier
mode, justifying deletion of the `q = c` sine event from off-diagonal symbols. -/
theorem sin_two_pi_nat (n : ℕ) :
    Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
  rw [show 2 * Real.pi * (n : ℝ) = ((2 * n : ℕ) : ℝ) * Real.pi by
    push_cast
    ring]
  exact Real.sin_nat_mul_pi (2 * n)

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

/-!
## Rowwise matrix and relative-energy bridge

The following adapters turn the dyadic symbol-square estimate into finite
matrix, coercive-energy, newest-band, and exact half-transport budgets.
-/

/-- Scaling the concrete symbol scales its dyadic square budget by the exact
square of the normalization factor.  In the CvS source identification this
retains the Fourier normalization `1 / π` as `1 / π²`. -/
theorem scaled_shifted_symbolSquareBudget
    (symbol : ℝ → ℝ) (scale C : ℝ) (N : ℕ)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (scale * symbol ((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      (scale ^ 2 * C) / (N : ℝ) := by
  have hRewrite :
      (∑ j ∈ range N,
          (scale * symbol ((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) =
        scale ^ 2 *
          ∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hRewrite]
  calc
    scale ^ 2 *
        (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      scale ^ 2 * (C / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hSymbol (sq_nonneg scale)
    _ = (scale ^ 2 * C) / (N : ℝ) := by ring

/-- On a dyadic band `(N,2N]`, a weighted symbol-square budget controls the
ordinary square sum with the sharp elementary loss `(2N)²`. -/
theorem shifted_symbolSquare_sum_le_four_mul
    (symbol : ℝ → ℝ) (C : ℝ) (N : ℕ) (hN : N ≠ 0)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      4 * C * (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hBand : ∀ j ∈ range N,
      (((N + 1 + j : ℕ) : ℝ) ^ 2) ≤ (2 * (N : ℝ)) ^ 2 := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hNat : N + 1 + j ≤ 2 * N := by omega
    have hReal : ((N + 1 + j : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hNat
    exact sq_le_sq₀ (by positivity) (by positivity) |>.2 hReal
  have hTermwise :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        (2 * (N : ℝ)) ^ 2 *
          ∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    let mode : ℝ := ((N + 1 + j : ℕ) : ℝ)
    have hModePos : 0 < mode := by
      dsimp only [mode]
      positivity
    have hModeNe : mode ≠ 0 := ne_of_gt hModePos
    have hWeightNonnegative :
        0 ≤ symbol mode ^ 2 / mode ^ 2 := by positivity
    calc
      symbol mode ^ 2 = mode ^ 2 * (symbol mode ^ 2 / mode ^ 2) := by
        field_simp [hModeNe]
      _ ≤ (2 * (N : ℝ)) ^ 2 * (symbol mode ^ 2 / mode ^ 2) :=
        mul_le_mul_of_nonneg_right (hBand j hj) hWeightNonnegative
  calc
    (∑ j ∈ range N,
        symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      (2 * (N : ℝ)) ^ 2 *
        ∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2 := hTermwise
    _ ≤ (2 * (N : ℝ)) ^ 2 * (C / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hSymbol (sq_nonneg (2 * (N : ℝ)))
    _ = 4 * C * (N : ℝ) := by
      field_simp [hNR]
      ring

theorem shifted_entry_sum_sq_le_of_symbolSquareBudget
    (entry : ℕ → ℝ) (symbol : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hEntry : ∀ j ∈ range N,
      entry j ^ 2 ≤
        32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 +
            symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2))
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N, entry j ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  have hEntries :
      (∑ j ∈ range N, entry j ^ 2) ≤
        ∑ j ∈ range N,
          32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
                ((N + 1 + j : ℕ) : ℝ) ^ 2 +
              symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hEntry j hj
  have hReciprocal := dyadic_shifted_weight_sum_le N hN
  have hFixed :
      symbol p ^ 2 *
          (∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        symbol p ^ 2 * (1 / (2 * (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hReciprocal (sq_nonneg (symbol p))
  have hFixedRewrite :
      (∑ j ∈ range N,
          symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) =
        symbol p ^ 2 *
          ∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [div_eq_mul_inv]
  calc
    (∑ j ∈ range N, entry j ^ 2) ≤
        ∑ j ∈ range N,
          32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
                ((N + 1 + j : ℕ) : ℝ) ^ 2 +
              symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := hEntries
    _ = 32 *
          (∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2) +
        32 *
          (∑ j ∈ range N,
            symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 32 * (
          (∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2) +
          symbol p ^ 2 *
            ∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) := by
      rw [hFixedRewrite]
      ring
    _ ≤ 32 * (C / (N : ℝ) + symbol p ^ 2 * (1 / (2 * (N : ℝ)))) := by
      gcongr
    _ = 32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
      simp [div_eq_mul_inv]

theorem evenParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    (symbol diagonal : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hp : 0 ≤ p)
    (hsep : ∀ j, j < N → 2 * p ≤ ((N + 1 + j : ℕ) : ℝ))
    (hOdd : Function.Odd symbol)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            ((N + 1 + j : ℕ) : ℝ) +
          CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            (-((N + 1 + j : ℕ) : ℝ))) ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  apply shifted_entry_sum_sq_le_of_symbolSquareBudget
    (fun j =>
      CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          ((N + 1 + j : ℕ) : ℝ) +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          (-((N + 1 + j : ℕ) : ℝ)))
    symbol p N hN C
  · intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact oddDifferenceKernel_evenParity_sq_le_symbolSquares_of_two_mul_le
      symbol diagonal p ((N + 1 + j : ℕ) : ℝ) hp (by positivity)
      (hsep j hjN) hOdd
  · exact hSymbol

theorem oddParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    (symbol diagonal : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hp : 0 ≤ p)
    (hsep : ∀ j, j < N → 2 * p ≤ ((N + 1 + j : ℕ) : ℝ))
    (hOdd : Function.Odd symbol)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            ((N + 1 + j : ℕ) : ℝ) -
          CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            (-((N + 1 + j : ℕ) : ℝ))) ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  apply shifted_entry_sum_sq_le_of_symbolSquareBudget
    (fun j =>
      CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          ((N + 1 + j : ℕ) : ℝ) -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          (-((N + 1 + j : ℕ) : ℝ)))
    symbol p N hN C
  · intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact oddDifferenceKernel_oddParity_sq_le_symbolSquares_of_two_mul_le
      symbol diagonal p ((N + 1 + j : ℕ) : ℝ) hp (by positivity)
      (hsep j hjN) hOdd
  · exact hSymbol

theorem rectangular_sum_sq_le_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (N : ℕ) (C : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ)))) :
    (∑ i ∈ rows, ∑ j ∈ range N, entry i j ^ 2) ≤
      32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
  have hDivSum :
      (∑ i ∈ rows, oldSymbol i ^ 2 / (2 * (N : ℝ))) =
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  calc
    (∑ i ∈ rows, ∑ j ∈ range N, entry i j ^ 2) ≤
        ∑ i ∈ rows,
          32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hRow i hi
    _ = 32 * (rows.card * (C / (N : ℝ)) +
          (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hDivSum]
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem rectangular_bilinear_sq_le_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ)))) :
    (∑ ij ∈ rows ×ˢ range N,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))) *
      ((∑ i ∈ rows, x i ^ 2) * ∑ j ∈ range N, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    rows (range N) entry x y
  have hEntries := rectangular_sum_sq_le_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol N C hRow
  have hEntryProduct :
      (∑ ij ∈ rows ×ˢ range N, entry ij.1 ij.2 ^ 2) ≤
        32 * (rows.card * (C / (N : ℝ)) +
          (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
    rw [Finset.sum_product]
    exact hEntries
  have hNorms :
      0 ≤ (∑ i ∈ rows, x i ^ 2) * ∑ j ∈ range N, y j ^ 2 := by
    positivity
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntryProduct hNorms)

theorem relativeCoupling_of_squaredNormBudget
    (lowEnergy highEnergy cross lowGap highGap entrySqBudget q
      lowNormSq highNormSq : ℝ)
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hq : 0 ≤ q)
    (hLowNormSq : 0 ≤ lowNormSq) (hHighNormSq : 0 ≤ highNormSq)
    (hLowEnergy : lowGap * lowNormSq ≤ lowEnergy)
    (hHighEnergy : highGap * highNormSq ≤ highEnergy)
    (hCross : cross ^ 2 ≤ entrySqBudget * (lowNormSq * highNormSq))
    (hBudget : entrySqBudget ≤ q * lowGap * highGap) :
    cross ^ 2 ≤ q * lowEnergy * highEnergy := by
  have hLowReference : 0 ≤ lowGap * lowNormSq :=
    mul_nonneg hLowGap hLowNormSq
  have hHighReference : 0 ≤ highGap * highNormSq :=
    mul_nonneg hHighGap hHighNormSq
  have hLowEnergyNonnegative : 0 ≤ lowEnergy :=
    hLowReference.trans hLowEnergy
  have hReferenceProduct :
      (lowGap * lowNormSq) * (highGap * highNormSq) ≤
        lowEnergy * highEnergy := by
    calc
      (lowGap * lowNormSq) * (highGap * highNormSq) ≤
          lowEnergy * (highGap * highNormSq) :=
        mul_le_mul_of_nonneg_right hLowEnergy hHighReference
      _ ≤ lowEnergy * highEnergy :=
        mul_le_mul_of_nonneg_left hHighEnergy hLowEnergyNonnegative
  have hNormProduct : 0 ≤ lowNormSq * highNormSq :=
    mul_nonneg hLowNormSq hHighNormSq
  have hBudgetScaled := mul_le_mul_of_nonneg_right hBudget hNormProduct
  have hReferenceScaled := mul_le_mul_of_nonneg_left hReferenceProduct hq
  calc
    cross ^ 2 ≤ entrySqBudget * (lowNormSq * highNormSq) := hCross
    _ ≤ (q * lowGap * highGap) * (lowNormSq * highNormSq) := hBudgetScaled
    _ = q * ((lowGap * lowNormSq) * (highGap * highNormSq)) := by ring
    _ ≤ q * (lowEnergy * highEnergy) := hReferenceScaled
    _ = q * lowEnergy * highEnergy := by ring

theorem rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (lowEnergy highEnergy lowGap highGap q : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ))))
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap) (hq : 0 ≤ q)
    (hLowEnergy :
      lowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hHighEnergy :
      highGap * (∑ j ∈ range N, y j ^ 2) ≤ highEnergy)
    (hBudget :
      32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) ≤
          q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range N,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      q * lowEnergy * highEnergy := by
  let entrySqBudget :=
    32 * (rows.card * (C / (N : ℝ)) +
      (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))
  have hCross := rectangular_bilinear_sq_le_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y N C hRow
  exact relativeCoupling_of_squaredNormBudget
    lowEnergy highEnergy
    (∑ ij ∈ rows ×ˢ range N,
      entry ij.1 ij.2 * (x ij.1 * y ij.2))
    lowGap highGap entrySqBudget q
    (∑ i ∈ rows, x i ^ 2) (∑ j ∈ range N, y j ^ 2)
    hLowGap hHighGap hq (by positivity) (by positivity)
    hLowEnergy hHighEnergy (by simpa only [entrySqBudget] using hCross)
    (by simpa only [entrySqBudget] using hBudget)

/-- Frobenius-square budget produced by the separated-row symbol estimate. -/
noncomputable def rectangularSymbolSquareBudget
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ) : ℝ :=
  32 * (rows.card * (C / (N : ℝ)) +
    (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))

/-- Newest-band specialization of the matrix budget.  If the historical band
has at most `B` rows, its ordinary symbol-square sum is at most `4*C*B`, and
the target shell has length `4B`, then the complete Frobenius-square budget is
at most `24*C`. -/
theorem rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (B : ℕ) (C : ℝ)
    (hB : B ≠ 0) (hC : 0 ≤ C)
    (hCard : rows.card ≤ B)
    (hOldSymbol :
      (∑ i ∈ rows, oldSymbol i ^ 2) ≤ 4 * C * (B : ℝ)) :
    rectangularSymbolSquareBudget rows oldSymbol (4 * B) C ≤ 24 * C := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  have hCardReal : (rows.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hCard
  have hCardScaled : (rows.card : ℝ) * C ≤ (B : ℝ) * C :=
    mul_le_mul_of_nonneg_right hCardReal hC
  have hNumerator :
      8 * ((rows.card : ℝ) * C) +
          4 * (∑ i ∈ rows, oldSymbol i ^ 2) ≤
        24 * C * (B : ℝ) := by
    nlinarith
  have hIdentity :
      rectangularSymbolSquareBudget rows oldSymbol (4 * B) C =
        (8 * ((rows.card : ℝ) * C) +
          4 * (∑ i ∈ rows, oldSymbol i ^ 2)) / (B : ℝ) := by
    simp only [rectangularSymbolSquareBudget, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hBR]
    ring
  rw [hIdentity]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ))).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hNumerator)

/-- End-to-end newest-band adapter.  The dyadic symbol estimates reduce the
matrix side to `24*C`; one scalar comparison with the two coercive floors then
produces the relative-energy coefficient `q`. -/
theorem rectangular_relativeCoupling_newestBand_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (B : ℕ) (C : ℝ)
    (lowEnergy highEnergy lowGap highGap q : ℝ)
    (hB : B ≠ 0) (hC : 0 ≤ C) (hCard : rows.card ≤ B)
    (hOldSymbol :
      (∑ i ∈ rows, oldSymbol i ^ 2) ≤ 4 * C * (B : ℝ))
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range (4 * B), entry i j ^ 2) ≤
        32 * (C / ((4 * B : ℕ) : ℝ) +
          oldSymbol i ^ 2 / (2 * ((4 * B : ℕ) : ℝ))))
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap) (hq : 0 ≤ q)
    (hLowEnergy :
      lowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hHighEnergy :
      highGap * (∑ j ∈ range (4 * B), y j ^ 2) ≤ highEnergy)
    (hScalarBudget : 24 * C ≤ q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range (4 * B),
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      q * lowEnergy * highEnergy := by
  have hMatrixBudget :
      rectangularSymbolSquareBudget rows oldSymbol (4 * B) C ≤
        q * lowGap * highGap :=
    (rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul
      rows oldSymbol B C hB hC hCard hOldSymbol).trans hScalarBudget
  apply rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y (4 * B) C lowEnergy highEnergy
      lowGap highGap q hRow hLowGap hHighGap hq hLowEnergy hHighEnergy
  simpa only [rectangularSymbolSquareBudget] using hMatrixBudget

/-- With the historical rows fixed, doubling the target-shell length halves
the separated-symbol Frobenius-square budget exactly. -/
theorem rectangularSymbolSquareBudget_two_mul
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ)
    (hN : N ≠ 0) :
    rectangularSymbolSquareBudget rows oldSymbol (2 * N) C =
      rectangularSymbolSquareBudget rows oldSymbol N C / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [rectangularSymbolSquareBudget, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNR]

/-- A fixed-row separated-symbol budget transports with coefficient one half
when the target shell doubles and both coercive floors grow. -/
theorem rectangularSymbolSquareBudget_halfTransport
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ)
    (q lowGap highGap nextLowGap nextHighGap : ℝ)
    (hN : N ≠ 0) (hq : 0 ≤ q)
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (hBudget : rectangularSymbolSquareBudget rows oldSymbol N C ≤
      q * lowGap * highGap) :
    rectangularSymbolSquareBudget rows oldSymbol (2 * N) C ≤
      (q / 2) * nextLowGap * nextHighGap := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hGapProduct : lowGap * highGap ≤ nextLowGap * nextHighGap := by
    calc
      lowGap * highGap ≤ nextLowGap * highGap :=
        mul_le_mul_of_nonneg_right hLowGrowth hHighGap
      _ ≤ nextLowGap * nextHighGap :=
        mul_le_mul_of_nonneg_left hHighGrowth hNextLowGap
  rw [rectangularSymbolSquareBudget_two_mul rows oldSymbol N C hN]
  calc
    rectangularSymbolSquareBudget rows oldSymbol N C / 2 ≤
        (q * lowGap * highGap) / 2 := by gcongr
    _ = (q / 2) * (lowGap * highGap) := by ring
    _ ≤ (q / 2) * (nextLowGap * nextHighGap) :=
      mul_le_mul_of_nonneg_left hGapProduct (div_nonneg hq (by norm_num))
    _ = (q / 2) * nextLowGap * nextHighGap := by ring

/-- End-to-end half-transport adapter: the doubled-shell row estimates and the
previous scalar budget imply the next relative-energy coupling with coefficient
`q/2`. -/
theorem rectangular_relativeCoupling_halfTransport_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (lowEnergy nextHighEnergy lowGap highGap nextLowGap nextHighGap q : ℝ)
    (hN : N ≠ 0)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range (2 * N), entry i j ^ 2) ≤
        32 * (C / ((2 * N : ℕ) : ℝ) +
          oldSymbol i ^ 2 / (2 * ((2 * N : ℕ) : ℝ))))
    (hq : 0 ≤ q) (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (hLowEnergy :
      nextLowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hNextHighEnergy :
      nextHighGap * (∑ j ∈ range (2 * N), y j ^ 2) ≤ nextHighEnergy)
    (hPreviousBudget : rectangularSymbolSquareBudget rows oldSymbol N C ≤
      q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range (2 * N),
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (q / 2) * lowEnergy * nextHighEnergy := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hNextHighGap : 0 ≤ nextHighGap := hHighGap.trans hHighGrowth
  have hNextBudget :
      rectangularSymbolSquareBudget rows oldSymbol (2 * N) C ≤
        (q / 2) * nextLowGap * nextHighGap :=
    rectangularSymbolSquareBudget_halfTransport
      rows oldSymbol N C q lowGap highGap nextLowGap nextHighGap
      hN hq hLowGap hHighGap hLowGrowth hHighGrowth hPreviousBudget
  apply rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y (2 * N) C lowEnergy nextHighEnergy
      nextLowGap nextHighGap (q / 2) hRow hNextLowGap hNextHighGap
      (div_nonneg hq (by norm_num)) hLowEnergy hNextHighEnergy
  simpa only [rectangularSymbolSquareBudget] using hNextBudget

end RiemannCvs.CombinedSymbolDyadicL2
