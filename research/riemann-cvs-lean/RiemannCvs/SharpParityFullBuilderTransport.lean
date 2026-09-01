import RiemannCvs.FullBuilderSymbolDyadicL2
import RiemannCvs.AdjacentArchimedeanSharpGap

/-!
# Sharp parity transport for the complete cutoff-13 builder

This module replaces the provisional factor-32 rectangular estimate on the
regular historical-to-remote channel by the exact even/odd parity numerators.
For `p ≤ q/2` they retain the decisive `p/q` powers:

* even: `128/9 * (f(q)^2/q^2 + p^2*f(p)^2/q^4)`;
* odd:  `128/9 * (p^2*f(q)^2/q^4 + f(p)^2/q^2)`.

The raw cutoff-13 combined-symbol premises imply full-builder entry budgets
`499/1125` and `1037/2250` at `N=4B`.  Both fit below
`(1/30)*(428/125)*(207/50)`.  The retained `q⁻²` and `q⁻⁴` moments
propagate this directly to `N=4B*2^k` with coefficient
`(1/30)*2^(-k)`, eliminating the old `hPreviousBudget` premise for every
regular source shell.  The final finite-family theorems fit inside the
established `2/27` previous-core budget.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

lemma oddDifferenceKernel_evenParity_sq_le_sharpSeparated
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (128 / 9 : ℝ) *
        (symbol q ^ 2 / q ^ 2 + p ^ 2 * symbol p ^ 2 / q ^ 4) := by
  have hpq : p ≠ q := by nlinarith
  have hpNegQ : p ≠ -q := by nlinarith
  have hq0 : 0 ≤ q := hq.le
  have hpqSq : p ^ 2 ≤ q ^ 2 / 4 := by nlinarith [sq_nonneg (q - 2 * p)]
  have hDen : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hDenNe : p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  have hDenLower : (3 / 4 : ℝ) * q ^ 2 ≤ q ^ 2 - p ^ 2 := by
    nlinarith
  have hDenSqLower : (9 / 16 : ℝ) * q ^ 4 ≤ (q ^ 2 - p ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((q ^ 2 - p ^ 2) - (3 / 4 : ℝ) * q ^ 2)]
  have hInvDenSq :
      1 / (q ^ 2 - p ^ 2) ^ 2 ≤ 16 / (9 * q ^ 4) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q ^ 2 - p ^ 2) ^ 2)
      (by positivity : (0 : ℝ) < 9 * q ^ 4)]
    nlinarith
  have hNum :
      (q * symbol q - p * symbol p) ^ 2 ≤
        2 * (q ^ 2 * symbol q ^ 2 + p ^ 2 * symbol p ^ 2) := by
    nlinarith [sq_nonneg (q * symbol q + p * symbol p)]
  have hNum4 :
      4 * (q * symbol q - p * symbol p) ^ 2 ≤
        8 * (q ^ 2 * symbol q ^ 2 + p ^ 2 * symbol p ^ 2) := by
    nlinarith
  have hInv0 : 0 ≤ 1 / (q ^ 2 - p ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  rw [CvSParityDisplacement.oddDifferenceKernel_evenParity_offDiagonal
    symbol diagonal p q hpq hpNegQ hOdd]
  have hSum0 :
      0 ≤ q ^ 2 * symbol q ^ 2 + p ^ 2 * symbol p ^ 2 := by positivity
  calc
    (2 * (q * symbol q - p * symbol p) / (p ^ 2 - q ^ 2)) ^ 2 =
        4 * (q * symbol q - p * symbol p) ^ 2 /
          (p ^ 2 - q ^ 2) ^ 2 := by
      field_simp [hDenNe]
      ring
    _ = 4 * (q * symbol q - p * symbol p) ^ 2 *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      rw [show (p ^ 2 - q ^ 2) ^ 2 = (q ^ 2 - p ^ 2) ^ 2 by ring]
      ring
    _ ≤ 8 * (q ^ 2 * symbol q ^ 2 + p ^ 2 * symbol p ^ 2) *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hNum4 hInv0
    _ ≤ 8 * (q ^ 2 * symbol q ^ 2 + p ^ 2 * symbol p ^ 2) *
          (16 / (9 * q ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hInvDenSq (mul_nonneg (by norm_num) hSum0)
    _ = (128 / 9 : ℝ) *
        (symbol q ^ 2 / q ^ 2 + p ^ 2 * symbol p ^ 2 / q ^ 4) := by
      field_simp [ne_of_gt hq]
      ring

lemma oddDifferenceKernel_oddParity_sq_le_sharpSeparated
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (128 / 9 : ℝ) *
        (p ^ 2 * symbol q ^ 2 / q ^ 4 + symbol p ^ 2 / q ^ 2) := by
  have hpq : p ≠ q := by nlinarith
  have hpNegQ : p ≠ -q := by nlinarith
  have hpqSq : p ^ 2 ≤ q ^ 2 / 4 := by nlinarith [sq_nonneg (q - 2 * p)]
  have hDen : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hDenNe : p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  have hDenLower : (3 / 4 : ℝ) * q ^ 2 ≤ q ^ 2 - p ^ 2 := by
    nlinarith
  have hDenSqLower : (9 / 16 : ℝ) * q ^ 4 ≤ (q ^ 2 - p ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((q ^ 2 - p ^ 2) - (3 / 4 : ℝ) * q ^ 2)]
  have hInvDenSq :
      1 / (q ^ 2 - p ^ 2) ^ 2 ≤ 16 / (9 * q ^ 4) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q ^ 2 - p ^ 2) ^ 2)
      (by positivity : (0 : ℝ) < 9 * q ^ 4)]
    nlinarith
  have hNum :
      (p * symbol q - q * symbol p) ^ 2 ≤
        2 * (p ^ 2 * symbol q ^ 2 + q ^ 2 * symbol p ^ 2) := by
    nlinarith [sq_nonneg (p * symbol q + q * symbol p)]
  have hNum4 :
      4 * (p * symbol q - q * symbol p) ^ 2 ≤
        8 * (p ^ 2 * symbol q ^ 2 + q ^ 2 * symbol p ^ 2) := by
    nlinarith
  have hInv0 : 0 ≤ 1 / (q ^ 2 - p ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  rw [CvSParityDisplacement.oddDifferenceKernel_oddParity_offDiagonal
    symbol diagonal p q hpq hpNegQ hOdd]
  have hSum0 :
      0 ≤ p ^ 2 * symbol q ^ 2 + q ^ 2 * symbol p ^ 2 := by positivity
  calc
    (2 * (p * symbol q - q * symbol p) / (p ^ 2 - q ^ 2)) ^ 2 =
        4 * (p * symbol q - q * symbol p) ^ 2 /
          (p ^ 2 - q ^ 2) ^ 2 := by
      field_simp [hDenNe]
      ring
    _ = 4 * (p * symbol q - q * symbol p) ^ 2 *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      rw [show (p ^ 2 - q ^ 2) ^ 2 = (q ^ 2 - p ^ 2) ^ 2 by ring]
      ring
    _ ≤ 8 * (p ^ 2 * symbol q ^ 2 + q ^ 2 * symbol p ^ 2) *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hNum4 hInv0
    _ ≤ 8 * (p ^ 2 * symbol q ^ 2 + q ^ 2 * symbol p ^ 2) *
          (16 / (9 * q ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hInvDenSq (mul_nonneg (by norm_num) hSum0)
    _ = (128 / 9 : ℝ) *
        (p ^ 2 * symbol q ^ 2 / q ^ 4 + symbol p ^ 2 / q ^ 2) := by
      field_simp [ne_of_gt hq]
      ring

lemma fourierNormalizedSymbol_sq_le
    (symbol : ℝ → ℝ) (x : ℝ) :
    fourierNormalizedSymbol symbol x ^ 2 ≤
      (2500 / 24649 : ℝ) * symbol x ^ 2 := by
  unfold fourierNormalizedSymbol
  calc
    ((1 / Real.pi) * symbol x) ^ 2 =
        (1 / Real.pi : ℝ) ^ 2 * symbol x ^ 2 := by ring
    _ ≤ (2500 / 24649 : ℝ) * symbol x ^ 2 :=
      mul_le_mul_of_nonneg_right
        one_div_pi_sq_le_twoThousandFiveHundred_div_twentyFourThousandSixHundredFortyNine
        (sq_nonneg _)

theorem c13HistoricalCombinedLoewnerSymbol_dyadic_unweighted_sum_le
    (B : ℕ)
    (hRaw :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ)) :
    (∑ j ∈ Finset.range B,
        c13HistoricalCombinedLoewnerSymbol
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      (5000 / 24649 : ℝ) * (B : ℝ) := by
  have hTerm :
      (∑ j ∈ Finset.range B,
          c13HistoricalCombinedLoewnerSymbol
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range B,
          (2500 / 24649 : ℝ) *
            logarithmicCombinedSymbol
                (logarithmicArchimedeanSymbol 13) 13
                c13PrimePowerLocation c13PrimePowerBase
                (((B + 1 + j : ℕ) : ℝ)) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _hj
    exact fourierNormalizedSymbol_sq_le
      (logarithmicCombinedSymbol
        (logarithmicArchimedeanSymbol 13) 13
        c13PrimePowerLocation c13PrimePowerBase)
      (((B + 1 + j : ℕ) : ℝ))
  calc
    (∑ j ∈ Finset.range B,
        c13HistoricalCombinedLoewnerSymbol
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range B,
          (2500 / 24649 : ℝ) *
            logarithmicCombinedSymbol
                (logarithmicArchimedeanSymbol 13) 13
                c13PrimePowerLocation c13PrimePowerBase
                (((B + 1 + j : ℕ) : ℝ)) ^ 2 := by
      simpa only [c13HistoricalCombinedLoewnerSymbol] using hTerm
    _ = (2500 / 24649 : ℝ) *
        (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (2500 / 24649 : ℝ) * (2 * (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hRaw (by norm_num)
    _ = (5000 / 24649 : ℝ) * (B : ℝ) := by ring

lemma c13_logarithmicPoleLoewnerSymbol_sq_le_inv_sq
    (x : ℝ) (hx : 0 < x) :
    logarithmicPoleLoewnerSymbol 13 x ^ 2 ≤
      (1 / 16 : ℝ) * (x ^ 2)⁻¹ := by
  have hAbs :=
    c13_abs_logarithmicPoleLoewnerSymbol_le_one_div_four_mul_inv x hx
  have hRight0 : 0 ≤ 1 / (4 * x) := by positivity
  have hSq := (sq_le_sq₀
    (abs_nonneg (logarithmicPoleLoewnerSymbol 13 x)) hRight0).2 hAbs
  calc
    logarithmicPoleLoewnerSymbol 13 x ^ 2 =
        |logarithmicPoleLoewnerSymbol 13 x| ^ 2 := by rw [sq_abs]
    _ ≤ (1 / (4 * x)) ^ 2 := hSq
    _ = (1 / 16 : ℝ) * (x ^ 2)⁻¹ := by
      field_simp [ne_of_gt hx]
      norm_num

theorem c13_logarithmicPoleLoewnerSymbol_dyadic_unweighted_sum_le
    (B : ℕ) (hB : B ≠ 0) :
    (∑ j ∈ Finset.range B,
        logarithmicPoleLoewnerSymbol 13
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      1 / (32 * (B : ℝ)) := by
  have hTerm :
      (∑ j ∈ Finset.range B,
          logarithmicPoleLoewnerSymbol 13
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range B,
          (1 / 16 : ℝ) *
            ((((B + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact c13_logarithmicPoleLoewnerSymbol_sq_le_inv_sq
      (((B + 1 + j : ℕ) : ℝ)) (by positivity)
  calc
    (∑ j ∈ Finset.range B,
        logarithmicPoleLoewnerSymbol 13
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range B,
          (1 / 16 : ℝ) *
            ((((B + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := hTerm
    _ = (1 / 16 : ℝ) *
        ∑ j ∈ Finset.range B,
          ((((B + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / 16 : ℝ) * (1 / (2 * (B : ℝ))) :=
      mul_le_mul_of_nonneg_left (dyadic_shifted_weight_sum_le B hB)
        (by norm_num)
    _ = 1 / (32 * (B : ℝ)) := by ring

lemma sub_sq_le_oneHundredOne_split (a b : ℝ) :
    (a - b) ^ 2 ≤ (101 / 100 : ℝ) * a ^ 2 + 101 * b ^ 2 := by
  nlinarith [sq_nonneg (a + 100 * b)]

theorem c13HistoricalBuilderLoewnerSymbol_dyadic_unweighted_sum_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRaw :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ)) :
    (∑ j ∈ Finset.range B,
        c13HistoricalBuilderLoewnerSymbol
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      (21 / 100 : ℝ) * (B : ℝ) := by
  have hB0 : B ≠ 0 := by omega
  have hBR : (0 : ℝ) < B := by positivity
  have hCombined :=
    c13HistoricalCombinedLoewnerSymbol_dyadic_unweighted_sum_le B hRaw
  have hPole :=
    c13_logarithmicPoleLoewnerSymbol_dyadic_unweighted_sum_le B hB0
  have hTerm :
      (∑ j ∈ Finset.range B,
          c13HistoricalBuilderLoewnerSymbol
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (101 / 100 : ℝ) *
          (∑ j ∈ Finset.range B,
            c13HistoricalCombinedLoewnerSymbol
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) +
        101 *
          (∑ j ∈ Finset.range B,
            logarithmicPoleLoewnerSymbol 13
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) := by
    calc
      (∑ j ∈ Finset.range B,
          c13HistoricalBuilderLoewnerSymbol
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
          ∑ j ∈ Finset.range B,
            ((101 / 100 : ℝ) *
                c13HistoricalCombinedLoewnerSymbol
                    (((B + 1 + j : ℕ) : ℝ)) ^ 2 +
              101 * logarithmicPoleLoewnerSymbol 13
                    (((B + 1 + j : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro j _hj
        unfold c13HistoricalBuilderLoewnerSymbol
        nlinarith [sub_sq_le_oneHundredOne_split
          (c13HistoricalCombinedLoewnerSymbol (((B + 1 + j : ℕ) : ℝ)))
          (logarithmicPoleLoewnerSymbol 13 (((B + 1 + j : ℕ) : ℝ)))]
      _ = (101 / 100 : ℝ) *
          (∑ j ∈ Finset.range B,
            c13HistoricalCombinedLoewnerSymbol
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) +
        101 *
          (∑ j ∈ Finset.range B,
            logarithmicPoleLoewnerSymbol 13
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  calc
    (∑ j ∈ Finset.range B,
        c13HistoricalBuilderLoewnerSymbol
            (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (101 / 100 : ℝ) *
          (∑ j ∈ Finset.range B,
            c13HistoricalCombinedLoewnerSymbol
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) +
        101 *
          (∑ j ∈ Finset.range B,
            logarithmicPoleLoewnerSymbol 13
                (((B + 1 + j : ℕ) : ℝ)) ^ 2) := hTerm
    _ ≤ (101 / 100 : ℝ) * ((5000 / 24649 : ℝ) * (B : ℝ)) +
        101 * (1 / (32 * (B : ℝ))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hCombined (by norm_num))
        (mul_le_mul_of_nonneg_left hPole (by norm_num))
    _ ≤ (21 / 100 : ℝ) * (B : ℝ) := by
      have hBRLower : (3840 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      have hBSq : (3840 : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
      field_simp [ne_of_gt hBR]
      nlinarith

theorem rectangular_evenParity_sum_sq_le_sharpSeparated
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (symbol _diagonal : ℝ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (entry : ι → κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      entry i j ^ 2 ≤ (128 / 9 : ℝ) *
        (symbol (q j) ^ 2 / (q j) ^ 2 +
          (p i) ^ 2 * symbol (p i) ^ 2 / (q j) ^ 4)) :
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
      (128 / 9 : ℝ) *
        (rows.card *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 2) +
          (∑ i ∈ rows, (p i) ^ 2 * symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 4)) := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, (128 / 9 : ℝ) *
          (symbol (q j) ^ 2 / (q j) ^ 2 +
            (p i) ^ 2 * symbol (p i) ^ 2 / (q j) ^ 4) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = (128 / 9 : ℝ) *
        (rows.card *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 2) +
          (∑ i ∈ rows, (p i) ^ 2 * symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 4)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring_nf
      rw [Finset.sum_comm]

theorem rectangular_oddParity_sum_sq_le_sharpSeparated
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (symbol _diagonal : ℝ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (entry : ι → κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      entry i j ^ 2 ≤ (128 / 9 : ℝ) *
        ((p i) ^ 2 * symbol (q j) ^ 2 / (q j) ^ 4 +
          symbol (p i) ^ 2 / (q j) ^ 2)) :
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
      (128 / 9 : ℝ) *
        ((∑ i ∈ rows, (p i) ^ 2) *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 4) +
          (∑ i ∈ rows, symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 2)) := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, (128 / 9 : ℝ) *
          ((p i) ^ 2 * symbol (q j) ^ 2 / (q j) ^ 4 +
            symbol (p i) ^ 2 / (q j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = (128 / 9 : ℝ) *
        ((∑ i ∈ rows, (p i) ^ 2) *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 4) +
          (∑ i ∈ rows, symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      ring_nf
      congr 1 <;> rw [Finset.sum_comm]

theorem dyadic_shifted_fourth_weight_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j ∈ Finset.range N,
        ((((N + 1 + j : ℕ) : ℝ) ^ 4)⁻¹)) ≤
      1 / (2 * (N : ℝ) ^ 3) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hTerm :
      (∑ j ∈ Finset.range N,
          ((((N + 1 + j : ℕ) : ℝ) ^ 4)⁻¹)) ≤
        ∑ j ∈ Finset.range N,
          (1 / (N : ℝ) ^ 2) *
            ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Finset.sum_le_sum
    intro j _hj
    let q : ℝ := ((N + 1 + j : ℕ) : ℝ)
    have hq : (N : ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast (show N ≤ N + 1 + j by omega)
    have hq0 : 0 < q := hNR.trans_le hq
    have hSq : (N : ℝ) ^ 2 ≤ q ^ 2 := by nlinarith
    have hInv : 1 / q ^ 2 ≤ 1 / (N : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hNR) hSq
    have hInv' : (q ^ 2)⁻¹ ≤ 1 / (N : ℝ) ^ 2 := by
      simpa [one_div] using hInv
    change (q ^ 4)⁻¹ ≤ (1 / (N : ℝ) ^ 2) * (q ^ 2)⁻¹
    rw [show (q ^ 4)⁻¹ = (q ^ 2)⁻¹ * (q ^ 2)⁻¹ by
      field_simp [ne_of_gt hq0]]
    exact mul_le_mul_of_nonneg_right hInv' (by positivity)
  calc
    (∑ j ∈ Finset.range N,
        ((((N + 1 + j : ℕ) : ℝ) ^ 4)⁻¹)) ≤
        ∑ j ∈ Finset.range N,
          (1 / (N : ℝ) ^ 2) *
            ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := hTerm
    _ = (1 / (N : ℝ) ^ 2) *
        ∑ j ∈ Finset.range N,
          ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (N : ℝ) ^ 2) * (1 / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (dyadic_shifted_weight_sum_le N hN)
        (by positivity)
    _ = 1 / (2 * (N : ℝ) ^ 3) := by ring

/-!
### Exact moments for the historical-to-`4B` rectangle

The generic row estimate loses the decisive factor by treating the two
parity channels identically.  The next elementary lemmas retain the powers
of `p/q` in the exact even/odd formulas.
-/

lemma historicalBandMode_real_nonneg
    (B : ℕ) (i : Fin B) :
    0 ≤ (historicalBandMode B i : ℝ) := by
  positivity

lemma historicalBandMode_real_le_two_mul
    (B : ℕ) (i : Fin B) :
    (historicalBandMode B i : ℝ) ≤ 2 * (B : ℝ) := by
  unfold historicalBandMode
  exact_mod_cast (show B + 1 + (i : ℕ) ≤ 2 * B by omega)

lemma historicalBandMode_two_mul_le_fourRemote
    (B : ℕ) (i : Fin B) (j : Fin (4 * B)) :
    2 * (historicalBandMode B i : ℝ) ≤
      ((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) := by
  unfold historicalBandMode
  exact_mod_cast
    (show 2 * (B + 1 + (i : ℕ)) ≤ 4 * B + 1 + (j : ℕ) by omega)

lemma historicalBandMode_sq_sum_le_four_mul_cube
    (B : ℕ) :
    (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) ≤
      4 * (B : ℝ) ^ 3 := by
  calc
    (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) ≤
        ∑ _i : Fin B, (2 * (B : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (sq_le_sq₀ (historicalBandMode_real_nonneg B i)
        (by positivity)).2 (historicalBandMode_real_le_two_mul B i)
    _ = 4 * (B : ℝ) ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

lemma historicalBandMode_sq_symbol_sq_sum_le
    (B : ℕ) (symbol : ℝ → ℝ) (D : ℝ)
    (hSymbol :
      (∑ i : Fin B, symbol (historicalBandMode B i : ℝ) ^ 2) ≤
        D * (B : ℝ)) :
    (∑ i : Fin B,
        (historicalBandMode B i : ℝ) ^ 2 *
          symbol (historicalBandMode B i : ℝ) ^ 2) ≤
      4 * D * (B : ℝ) ^ 3 := by
  have hTerm :
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            symbol (historicalBandMode B i : ℝ) ^ 2) ≤
        ∑ i : Fin B,
          (2 * (B : ℝ)) ^ 2 *
            symbol (historicalBandMode B i : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _hi
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (historicalBandMode_real_nonneg B i)
        (by positivity)).2 (historicalBandMode_real_le_two_mul B i))
      (sq_nonneg _)
  calc
    (∑ i : Fin B,
        (historicalBandMode B i : ℝ) ^ 2 *
          symbol (historicalBandMode B i : ℝ) ^ 2) ≤
        ∑ i : Fin B,
          (2 * (B : ℝ)) ^ 2 *
            symbol (historicalBandMode B i : ℝ) ^ 2 := hTerm
    _ = (2 * (B : ℝ)) ^ 2 *
        (∑ i : Fin B,
          symbol (historicalBandMode B i : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (B : ℝ)) ^ 2 * (D * (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hSymbol (sq_nonneg _)
    _ = 4 * D * (B : ℝ) ^ 3 := by ring

lemma fourRemote_inv_sq_sum_le
    (B : ℕ) (hB : B ≠ 0) :
    (∑ j : Fin (4 * B),
        1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      1 / (8 * (B : ℝ)) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => 1 / (((4 * B + 1 + j : ℕ) : ℝ) ^ 2)) (4 * B)]
  have h := dyadic_shifted_weight_sum_le (4 * B) (by omega)
  calc
    (∑ j ∈ Finset.range (4 * B),
        1 / (((4 * B + 1 + j : ℕ) : ℝ) ^ 2)) ≤
        1 / (2 * ((4 * B : ℕ) : ℝ)) := by
      simpa [one_div] using h
    _ = 1 / (8 * (B : ℝ)) := by
      push_cast
      ring

lemma fourRemote_inv_fourth_sum_le
    (B : ℕ) (hB : B ≠ 0) :
    (∑ j : Fin (4 * B),
        1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      1 / (128 * (B : ℝ) ^ 3) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => 1 / (((4 * B + 1 + j : ℕ) : ℝ) ^ 4)) (4 * B)]
  have h := dyadic_shifted_fourth_weight_sum_le (4 * B) (by omega)
  calc
    (∑ j ∈ Finset.range (4 * B),
        1 / (((4 * B + 1 + j : ℕ) : ℝ) ^ 4)) ≤
        1 / (2 * ((4 * B : ℕ) : ℝ) ^ 3) := by
      simpa [one_div] using h
    _ = 1 / (128 * (B : ℝ) ^ 3) := by
      push_cast
      ring

lemma fourRemote_symbol_sq_div_fourth_sum_le
    (B : ℕ) (hB : B ≠ 0) (symbol : ℝ → ℝ) (C : ℝ)
    (hWeighted :
      (∑ j : Fin (4 * B),
          symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        C / ((4 * B : ℕ) : ℝ)) :
    (∑ j : Fin (4 * B),
        symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      C / (64 * (B : ℝ) ^ 3) := by
  have hBR : (0 : ℝ) < B := by positivity
  have hTerm :
      (∑ j : Fin (4 * B),
          symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        ∑ j : Fin (4 * B),
          (1 / (4 * (B : ℝ)) ^ 2) *
            (symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j _hj
    let q : ℝ := ((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)
    have hq : 4 * (B : ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast
        (show 4 * B ≤ 4 * B + 1 + (j : ℕ) by omega)
    have hq0 : 0 < q := (by positivity : (0 : ℝ) < 4 * B).trans_le hq
    have hSq : (4 * (B : ℝ)) ^ 2 ≤ q ^ 2 := by
      nlinarith
    have hInv : 1 / q ^ 2 ≤ 1 / (4 * (B : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hSq
    have hWeightedTerm : 0 ≤ symbol q ^ 2 / q ^ 2 := by positivity
    change symbol q ^ 2 / q ^ 4 ≤
      (1 / (4 * (B : ℝ)) ^ 2) * (symbol q ^ 2 / q ^ 2)
    calc
      symbol q ^ 2 / q ^ 4 = (1 / q ^ 2) * (symbol q ^ 2 / q ^ 2) := by
        field_simp [ne_of_gt hq0]
      _ ≤ (1 / (4 * (B : ℝ)) ^ 2) *
          (symbol q ^ 2 / q ^ 2) :=
        mul_le_mul_of_nonneg_right hInv hWeightedTerm
  calc
    (∑ j : Fin (4 * B),
        symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        ∑ j : Fin (4 * B),
          (1 / (4 * (B : ℝ)) ^ 2) *
            (symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := hTerm
    _ = (1 / (4 * (B : ℝ)) ^ 2) *
        (∑ j : Fin (4 * B),
          symbol (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (4 * (B : ℝ)) ^ 2) *
        (C / ((4 * B : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hWeighted (by positivity)
    _ = C / (64 * (B : ℝ) ^ 3) := by
      push_cast
      field_simp [ne_of_gt hBR]
      ring

theorem c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRaw :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ)) :
    (∑ i : Fin B,
        c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ) ^ 2) ≤
      (21 / 100 : ℝ) * (B : ℝ) := by
  simp only [historicalBandMode]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      c13HistoricalBuilderLoewnerSymbol (((B + 1 + i : ℕ) : ℝ)) ^ 2) B]
  simpa only [historicalBandMode] using
    c13HistoricalBuilderLoewnerSymbol_dyadic_unweighted_sum_le B hB hRaw

theorem c13HistoricalBuilderLoewnerSymbol_fourRemote_weighted_sum_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRaw :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ)) :
    (∑ j : Fin (4 * B),
        c13HistoricalBuilderLoewnerSymbol
            (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      (197 / 2000 : ℝ) / ((4 * B : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ =>
      c13HistoricalBuilderLoewnerSymbol
          (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
        (((4 * B + 1 + j : ℕ) : ℝ) ^ 2)) (4 * B)]
  exact c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
    (4 * B) (by omega) hRaw

theorem c13EvenHistoricalBuilderLoewnerRemote_four_mul_entry_sq_sum_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin (4 * B),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
      (499 / 1125 : ℝ) := by
  have hB0 : B ≠ 0 := by omega
  have hBR : (0 : ℝ) < B := by positivity
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le
      B hB hRawSource
  have hTarget :=
    c13HistoricalBuilderLoewnerSymbol_fourRemote_weighted_sum_le
      B hB hRawTarget
  have hSourceMoment :=
    historicalBandMode_sq_symbol_sq_sum_le B
      c13HistoricalBuilderLoewnerSymbol (21 / 100 : ℝ) hSource
  have hInvFour := fourRemote_inv_fourth_sum_le B hB0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin B)),
        ∀ j ∈ (Finset.univ : Finset (Fin (4 * B))),
          c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2 ≤
            (128 / 9 : ℝ) *
              (c13HistoricalBuilderLoewnerSymbol
                    (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2) +
                (historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (historicalBandMode B i : ℝ) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) := by
    intro i _hi j _hj
    unfold c13EvenHistoricalBuilderLoewnerRemoteEntry
      c13EvenHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_evenParity_sq_le_sharpSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (historicalBandMode_two_mul_le_fourRemote B i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_evenParity_sum_sq_le_sharpSeparated
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B)))
    c13HistoricalBuilderLoewnerSymbol
    c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin (4 * B) =>
      ((4 * B + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B)) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin (4 * B),
          c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((B : ℝ) *
              (∑ j : Fin (4 * B),
                c13HistoricalBuilderLoewnerSymbol
                    (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
            (∑ i : Fin B,
                (historicalBandMode B i : ℝ) ^ 2 *
                  c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hRect
  have hFirst :
      (B : ℝ) *
          (∑ j : Fin (4 * B),
            c13HistoricalBuilderLoewnerSymbol
                (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        (197 / 8000 : ℝ) := by
    calc
      (B : ℝ) *
          (∑ j : Fin (4 * B),
            c13HistoricalBuilderLoewnerSymbol
                (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
          (B : ℝ) *
            ((197 / 2000 : ℝ) / ((4 * B : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hTarget hBR.le
      _ = (197 / 8000 : ℝ) := by
        push_cast
        field_simp [ne_of_gt hBR]
        ring
  have hSecond :
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin (4 * B),
          1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      (21 / 3200 : ℝ) := by
    calc
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin (4 * B),
          1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
            (∑ j : Fin (4 * B),
              1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceMoment (by positivity)
      _ ≤ (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
          (1 / (128 * (B : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hInvFour (by positivity)
      _ = (21 / 3200 : ℝ) := by
        field_simp [ne_of_gt hBR]
        norm_num
  calc
    (∑ i : Fin B, ∑ j : Fin (4 * B),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((B : ℝ) *
              (∑ j : Fin (4 * B),
                c13HistoricalBuilderLoewnerSymbol
                    (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
            (∑ i : Fin B,
                (historicalBandMode B i : ℝ) ^ 2 *
                  c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := hRect'
    _ ≤ (128 / 9 : ℝ) * ((197 / 8000 : ℝ) + 21 / 3200) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by norm_num)
    _ = (499 / 1125 : ℝ) := by norm_num

theorem c13OddHistoricalBuilderLoewnerRemote_four_mul_entry_sq_sum_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin (4 * B),
        c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
      (1037 / 2250 : ℝ) := by
  have hB0 : B ≠ 0 := by omega
  have hBR : (0 : ℝ) < B := by positivity
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le
      B hB hRawSource
  have hTarget :=
    c13HistoricalBuilderLoewnerSymbol_fourRemote_weighted_sum_le
      B hB hRawTarget
  have hSourceModeSq := historicalBandMode_sq_sum_le_four_mul_cube B
  have hTargetFourth := fourRemote_symbol_sq_div_fourth_sum_le
    B hB0 c13HistoricalBuilderLoewnerSymbol (197 / 2000 : ℝ) hTarget
  have hInvSq := fourRemote_inv_sq_sum_le B hB0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin B)),
        ∀ j ∈ (Finset.univ : Finset (Fin (4 * B))),
          c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2 ≤
            (128 / 9 : ℝ) *
              ((historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4) +
                c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
    intro i _hi j _hj
    unfold c13OddHistoricalBuilderLoewnerRemoteEntry
      c13OddHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_oddParity_sq_le_sharpSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (historicalBandMode_two_mul_le_fourRemote B i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_oddParity_sum_sq_le_sharpSeparated
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B)))
    c13HistoricalBuilderLoewnerSymbol
    c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin (4 * B) =>
      ((4 * B + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B)) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin (4 * B),
          c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                c13HistoricalBuilderLoewnerSymbol
                    (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
            (∑ i : Fin B,
                c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := by
    simpa using hRect
  have hFirst :
      (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
          (∑ j : Fin (4 * B),
            c13HistoricalBuilderLoewnerSymbol
                (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        (197 / 32000 : ℝ) := by
    calc
      (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
          (∑ j : Fin (4 * B),
            c13HistoricalBuilderLoewnerSymbol
                (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          (4 * (B : ℝ) ^ 3) *
            (∑ j : Fin (4 * B),
              c13HistoricalBuilderLoewnerSymbol
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceModeSq (by positivity)
      _ ≤ (4 * (B : ℝ) ^ 3) *
          ((197 / 2000 : ℝ) / (64 * (B : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hTargetFourth (by positivity)
      _ = (197 / 32000 : ℝ) := by
        field_simp [ne_of_gt hBR]
        norm_num
  have hSecond :
      (∑ i : Fin B,
          c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin (4 * B),
          1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      (21 / 800 : ℝ) := by
    calc
      (∑ i : Fin B,
          c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin (4 * B),
          1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
          ((21 / 100 : ℝ) * (B : ℝ)) *
            (∑ j : Fin (4 * B),
              1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hSource (by positivity)
      _ ≤ ((21 / 100 : ℝ) * (B : ℝ)) *
          (1 / (8 * (B : ℝ))) :=
        mul_le_mul_of_nonneg_left hInvSq (by positivity)
      _ = (21 / 800 : ℝ) := by
        field_simp [ne_of_gt hBR]
        norm_num
  calc
    (∑ i : Fin B, ∑ j : Fin (4 * B),
        c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                c13HistoricalBuilderLoewnerSymbol
                    (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
            (∑ i : Fin B,
                c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin (4 * B),
                1 / (((4 * B + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := hRect'
    _ ≤ (128 / 9 : ℝ) * ((197 / 32000 : ℝ) + 21 / 800) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by norm_num)
    _ = (1037 / 2250 : ℝ) := by norm_num

theorem c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy_four_mul_sq_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B) x y ^ 2 ≤
      (499 / 1125 : ℝ) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B)))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B))),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B)
            ij.1 ij.2 ^ 2) ≤
      (499 / 1125 : ℝ) := by
    rw [Finset.sum_product]
    simpa using c13EvenHistoricalBuilderLoewnerRemote_four_mul_entry_sq_sum_le
      B hB hRawSource hRawTarget
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddHistoricalBuilderLoewnerRemoteCrossEnergy_four_mul_sq_le
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B) x y ^ 2 ≤
      (1037 / 2250 : ℝ) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B)))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B))),
        c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B)
            ij.1 ij.2 ^ 2) ≤
      (1037 / 2250 : ℝ) := by
    rw [Finset.sum_product]
    simpa using c13OddHistoricalBuilderLoewnerRemote_four_mul_entry_sq_sum_le
      B hB hRawSource hRawTarget
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

lemma c13_even_four_mul_entryBudget_le_oneThirtieth_gapProduct :
    (499 / 1125 : ℝ) ≤
      (1 / 30 : ℝ) * (428 / 125 : ℝ) * (207 / 50 : ℝ) := by
  norm_num

lemma c13_odd_four_mul_entryBudget_le_oneThirtieth_gapProduct :
    (1037 / 2250 : ℝ) ≤
      (1 / 30 : ℝ) * (428 / 125 : ℝ) * (207 / 50 : ℝ) := by
  norm_num

theorem c13HistoricalRemoteEvenBuilder_four_mul_relative_oneThirtieth
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteEvenBuilderMatrix B (4 * B)) x y) ^ 2 ≤
      (1 / 30 : ℝ) * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (4 * B) (4 * B) y := by
  have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB
  have hGapHigh : (207 / 50 : ℝ) ≤ c13ShellDynamicGap (4 * B) := by
    have h := c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840
      (2 * B) (by omega)
    have hEq : 2 * (2 * B) = 4 * B := by omega
    rw [hEq] at h
    exact h
  have hLowFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B (by omega) (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (4 * B) (4 * B) (by omega) (by omega) y
  have hLowEnergy :
      (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
        c13EvenBuilderShellEnergy B B x := by
    have hScaled :
        (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
          c13ShellDynamicGap B * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hGapLow (by positivity)
    have hFloor :
        c13ShellDynamicGap B * (∑ i, x i ^ 2) ≤
          c13EvenBuilderShellEnergy B B x := by
      simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowFloor
    exact hScaled.trans hFloor
  have hHighEnergy :
      (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
        c13EvenBuilderShellEnergy (4 * B) (4 * B) y := by
    have hScaled :
        (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
          c13ShellDynamicGap (4 * B) * (∑ j, y j ^ 2) :=
      mul_le_mul_of_nonneg_right hGapHigh (by positivity)
    have hFloor :
        c13ShellDynamicGap (4 * B) * (∑ j, y j ^ 2) ≤
          c13EvenBuilderShellEnergy (4 * B) (4 * B) y := by
      simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighFloor
    exact hScaled.trans hFloor
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderShellEnergy B B x)
    (c13EvenBuilderShellEnergy (4 * B) (4 * B) y)
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B) x y)
    (428 / 125) (207 / 50) (499 / 1125) (1 / 30)
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity)
    hLowEnergy hHighEnergy
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy_four_mul_sq_le
      B hB hRawSource hRawTarget x y)
    c13_even_four_mul_entryBudget_le_oneThirtieth_gapProduct

theorem c13HistoricalRemoteOddBuilder_four_mul_relative_oneThirtieth
    (B : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteOddBuilderMatrix B (4 * B)) x y) ^ 2 ≤
      (1 / 30 : ℝ) * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (4 * B) (4 * B) y := by
  have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB
  have hGapHigh : (207 / 50 : ℝ) ≤ c13ShellDynamicGap (4 * B) := by
    have h := c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840
      (2 * B) (by omega)
    have hEq : 2 * (2 * B) = 4 * B := by omega
    rw [hEq] at h
    exact h
  have hLowFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B (by omega) (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (4 * B) (4 * B) (by omega) (by omega) y
  have hLowEnergy :
      (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
        c13OddBuilderShellEnergy B B x := by
    have hScaled :
        (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
          c13ShellDynamicGap B * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hGapLow (by positivity)
    have hFloor :
        c13ShellDynamicGap B * (∑ i, x i ^ 2) ≤
          c13OddBuilderShellEnergy B B x := by
      simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowFloor
    exact hScaled.trans hFloor
  have hHighEnergy :
      (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
        c13OddBuilderShellEnergy (4 * B) (4 * B) y := by
    have hScaled :
        (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
          c13ShellDynamicGap (4 * B) * (∑ j, y j ^ 2) :=
      mul_le_mul_of_nonneg_right hGapHigh (by positivity)
    have hFloor :
        c13ShellDynamicGap (4 * B) * (∑ j, y j ^ 2) ≤
          c13OddBuilderShellEnergy (4 * B) (4 * B) y := by
      simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighFloor
    exact hScaled.trans hFloor
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13OddBuilderShellEnergy B B x)
    (c13OddBuilderShellEnergy (4 * B) (4 * B) y)
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B) x y)
    (428 / 125) (207 / 50) (1037 / 2250) (1 / 30)
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity)
    hLowEnergy hHighEnergy
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy_four_mul_sq_le
      B hB hRawSource hRawTarget x y)
    c13_odd_four_mul_entryBudget_le_oneThirtieth_gapProduct

/-!
### Dyadic continuation without the provisional rectangular budget

At a target `N = 4B * 2^k`, the terms carrying `q⁻⁴` improve by
`2^(-3k)` while the remaining terms improve by `2^(-k)`.  Thus the sharp
base estimate propagates directly at the matrix-entry level; no invocation of
the older factor-32 rectangular budget is needed.
-/

lemma remote_inv_sq_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j : Fin N,
        1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      1 / (2 * (N : ℝ)) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => 1 / (((N + 1 + j : ℕ) : ℝ) ^ 2)) N]
  simpa [one_div] using dyadic_shifted_weight_sum_le N hN

lemma remote_inv_fourth_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j : Fin N,
        1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      1 / (2 * (N : ℝ) ^ 3) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => 1 / (((N + 1 + j : ℕ) : ℝ) ^ 4)) N]
  simpa [one_div] using dyadic_shifted_fourth_weight_sum_le N hN

lemma remote_symbol_sq_div_fourth_sum_le
    (N : ℕ) (hN : N ≠ 0) (symbol : ℝ → ℝ) (C : ℝ)
    (hWeighted :
      (∑ j : Fin N,
          symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        C / (N : ℝ)) :
    (∑ j : Fin N,
        symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      C / (N : ℝ) ^ 3 := by
  have hNR : (0 : ℝ) < N := by positivity
  have hTerm :
      (∑ j : Fin N,
          symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        ∑ j : Fin N,
          (1 / (N : ℝ) ^ 2) *
            (symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j _hj
    let q : ℝ := ((N + 1 + (j : ℕ) : ℕ) : ℝ)
    have hq : (N : ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast (show N ≤ N + 1 + (j : ℕ) by omega)
    have hq0 : 0 < q := hNR.trans_le hq
    have hSq : (N : ℝ) ^ 2 ≤ q ^ 2 := by nlinarith
    have hInv : 1 / q ^ 2 ≤ 1 / (N : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hSq
    change symbol q ^ 2 / q ^ 4 ≤
      (1 / (N : ℝ) ^ 2) * (symbol q ^ 2 / q ^ 2)
    calc
      symbol q ^ 2 / q ^ 4 = (1 / q ^ 2) * (symbol q ^ 2 / q ^ 2) := by
        field_simp [ne_of_gt hq0]
      _ ≤ (1 / (N : ℝ) ^ 2) * (symbol q ^ 2 / q ^ 2) :=
        mul_le_mul_of_nonneg_right hInv (by positivity)
  calc
    (∑ j : Fin N,
        symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        ∑ j : Fin N,
          (1 / (N : ℝ) ^ 2) *
            (symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := hTerm
    _ = (1 / (N : ℝ) ^ 2) *
        (∑ j : Fin N,
          symbol (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (N : ℝ) ^ 2) * (C / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hWeighted (by positivity)
    _ = C / (N : ℝ) ^ 3 := by
      field_simp [ne_of_gt hNR]

theorem c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    (N : ℕ) (hN : 1920 ≤ N)
    (hRaw :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ j : Fin N,
        c13HistoricalBuilderLoewnerSymbol
            (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      (197 / 2000 : ℝ) / (N : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ =>
      c13HistoricalBuilderLoewnerSymbol (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
        (((N + 1 + j : ℕ) : ℝ) ^ 2)) N]
  exact c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
    N hN hRaw

theorem c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_sharpExpression
    (B N : ℕ) (hB : 3840 ≤ B) (hBN : 4 * B ≤ N)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin N,
        c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
      (128 / 9 : ℝ) *
        ((B : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ)) +
          (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
            (1 / (2 * (N : ℝ) ^ 3))) := by
  have hN0 : N ≠ 0 := by omega
  have hN1920 : 1920 ≤ N := by omega
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le
      B hB hRawSource
  have hSourceMoment := historicalBandMode_sq_symbol_sq_sum_le
    B c13HistoricalBuilderLoewnerSymbol (21 / 100 : ℝ) hSource
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN1920 hRawTarget
  have hInvFour := remote_inv_fourth_sum_le N hN0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin B)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)),
          c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2 ≤
            (128 / 9 : ℝ) *
              (c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2) +
                (historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (historicalBandMode B i : ℝ) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) := by
    intro i _hi j _hj
    unfold c13EvenHistoricalBuilderLoewnerRemoteEntry
      c13EvenHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_evenParity_sq_le_sharpSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_evenParity_sum_sq_le_sharpSeparated
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B N) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin N,
          c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((B : ℝ) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
            (∑ i : Fin B,
                (historicalBandMode B i : ℝ) ^ 2 *
                  c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin N,
                1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hRect
  have hFirst :
      (B : ℝ) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        (B : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hTarget (by positivity)
  have hSecond :
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
        (1 / (2 * (N : ℝ) ^ 3)) := by
    calc
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
            (∑ j : Fin N,
              1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceMoment (by positivity)
      _ ≤ (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
          (1 / (2 * (N : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hInvFour (by positivity)
  exact hRect'.trans
    (mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by norm_num))

theorem c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_sharpExpression
    (B N : ℕ) (hB : 3840 ≤ B) (hBN : 4 * B ≤ N)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin N,
        c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
      (128 / 9 : ℝ) *
        ((4 * (B : ℝ) ^ 3) *
            ((197 / 2000 : ℝ) / (N : ℝ) ^ 3) +
          ((21 / 100 : ℝ) * (B : ℝ)) *
            (1 / (2 * (N : ℝ)))) := by
  have hN0 : N ≠ 0 := by omega
  have hN1920 : 1920 ≤ N := by omega
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le
      B hB hRawSource
  have hSourceModeSq := historicalBandMode_sq_sum_le_four_mul_cube B
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN1920 hRawTarget
  have hTargetFourth := remote_symbol_sq_div_fourth_sum_le
    N hN0 c13HistoricalBuilderLoewnerSymbol (197 / 2000 : ℝ) hTarget
  have hInvSq := remote_inv_sq_sum_le N hN0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin B)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)),
          c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2 ≤
            (128 / 9 : ℝ) *
              ((historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4) +
                c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) := by
    intro i _hi j _hj
    unfold c13OddHistoricalBuilderLoewnerRemoteEntry
      c13OddHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_oddParity_sq_le_sharpSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_oddParity_sum_sq_le_sharpSeparated
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B N) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin N,
          c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
            (∑ i : Fin B,
                c13HistoricalBuilderLoewnerSymbol
                    (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin N,
                1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := by
    simpa using hRect
  have hFirst :
      (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        (4 * (B : ℝ) ^ 3) *
          ((197 / 2000 : ℝ) / (N : ℝ) ^ 3) := by
    calc
      (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          (4 * (B : ℝ) ^ 3) *
            (∑ j : Fin N,
              c13HistoricalBuilderLoewnerSymbol
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceModeSq (by positivity)
      _ ≤ (4 * (B : ℝ) ^ 3) *
          ((197 / 2000 : ℝ) / (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hTargetFourth (by positivity)
  have hSecond :
      (∑ i : Fin B,
          c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      ((21 / 100 : ℝ) * (B : ℝ)) *
        (1 / (2 * (N : ℝ))) := by
    calc
      (∑ i : Fin B,
          c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
          ((21 / 100 : ℝ) * (B : ℝ)) *
            (∑ j : Fin N,
              1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hSource (by positivity)
      _ ≤ ((21 / 100 : ℝ) * (B : ℝ)) *
          (1 / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hInvSq (by positivity)
  exact hRect'.trans
    (mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by norm_num))

lemma even_sharpExpression_dyadic_le
    (r : ℝ) (hr : 1 ≤ r) :
    (128 / 9 : ℝ) *
        ((197 / 8000 : ℝ) / r + (21 / 3200 : ℝ) / r ^ 3) ≤
      (499 / 1125 : ℝ) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrSq : 1 ≤ r ^ 2 := by nlinarith
  field_simp [ne_of_gt hr0]
  nlinarith

lemma odd_sharpExpression_dyadic_le
    (r : ℝ) (hr : 1 ≤ r) :
    (128 / 9 : ℝ) *
        ((197 / 32000 : ℝ) / r ^ 3 + (21 / 800 : ℝ) / r) ≤
      (1037 / 2250 : ℝ) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrSq : 1 ≤ r ^ 2 := by nlinarith
  field_simp [ne_of_gt hr0]
  nlinarith

theorem c13EvenHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin (4 * B * 2 ^ k),
        c13EvenHistoricalBuilderLoewnerRemoteEntry
            B (4 * B * 2 ^ k) i j ^ 2) ≤
      (499 / 1125 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
    simpa using Nat.mul_le_mul_left (4 * B) hPow
  have hGeneral :=
    c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_sharpExpression
      B (4 * B * 2 ^ k) hB hSeparated hRawSource hRawTarget
  let r : ℝ := (2 : ℝ) ^ k
  have hr : 1 ≤ r := by
    dsimp [r]
    exact one_le_pow₀ (by norm_num)
  have hBReal : (0 : ℝ) < B := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hCast : ((4 * B * 2 ^ k : ℕ) : ℝ) = 4 * (B : ℝ) * r := by
    dsimp [r]
    push_cast
    ring
  have hRewrite :
      (128 / 9 : ℝ) *
          ((B : ℝ) *
              ((197 / 2000 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ)) +
            (4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
              (1 / (2 * ((4 * B * 2 ^ k : ℕ) : ℝ) ^ 3))) =
        (128 / 9 : ℝ) *
          ((197 / 8000 : ℝ) / r + (21 / 3200 : ℝ) / r ^ 3) := by
    rw [hCast]
    field_simp [ne_of_gt hBReal, ne_of_gt hr0]
    ring
  rw [hRewrite] at hGeneral
  calc
    (∑ i : Fin B, ∑ j : Fin (4 * B * 2 ^ k),
        c13EvenHistoricalBuilderLoewnerRemoteEntry
            B (4 * B * 2 ^ k) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((197 / 8000 : ℝ) / r + (21 / 3200 : ℝ) / r ^ 3) := hGeneral
    _ ≤ (499 / 1125 : ℝ) / r := even_sharpExpression_dyadic_le r hr
    _ = (499 / 1125 : ℝ) * (1 / 2 : ℝ) ^ k := by
      dsimp [r]
      exact div_two_pow_eq_mul_half_pow (499 / 1125 : ℝ) k

theorem c13OddHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ)) :
    (∑ i : Fin B, ∑ j : Fin (4 * B * 2 ^ k),
        c13OddHistoricalBuilderLoewnerRemoteEntry
            B (4 * B * 2 ^ k) i j ^ 2) ≤
      (1037 / 2250 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
    simpa using Nat.mul_le_mul_left (4 * B) hPow
  have hGeneral :=
    c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_sharpExpression
      B (4 * B * 2 ^ k) hB hSeparated hRawSource hRawTarget
  let r : ℝ := (2 : ℝ) ^ k
  have hr : 1 ≤ r := by
    dsimp [r]
    exact one_le_pow₀ (by norm_num)
  have hBReal : (0 : ℝ) < B := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hCast : ((4 * B * 2 ^ k : ℕ) : ℝ) = 4 * (B : ℝ) * r := by
    dsimp [r]
    push_cast
    ring
  have hRewrite :
      (128 / 9 : ℝ) *
          ((4 * (B : ℝ) ^ 3) *
              ((197 / 2000 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ) ^ 3) +
            ((21 / 100 : ℝ) * (B : ℝ)) *
              (1 / (2 * ((4 * B * 2 ^ k : ℕ) : ℝ)))) =
        (128 / 9 : ℝ) *
          ((197 / 32000 : ℝ) / r ^ 3 + (21 / 800 : ℝ) / r) := by
    rw [hCast]
    field_simp [ne_of_gt hBReal, ne_of_gt hr0]
    ring
  rw [hRewrite] at hGeneral
  calc
    (∑ i : Fin B, ∑ j : Fin (4 * B * 2 ^ k),
        c13OddHistoricalBuilderLoewnerRemoteEntry
            B (4 * B * 2 ^ k) i j ^ 2) ≤
        (128 / 9 : ℝ) *
          ((197 / 32000 : ℝ) / r ^ 3 + (21 / 800 : ℝ) / r) := hGeneral
    _ ≤ (1037 / 2250 : ℝ) / r := odd_sharpExpression_dyadic_le r hr
    _ = (1037 / 2250 : ℝ) * (1 / 2 : ℝ) ^ k := by
      dsimp [r]
      exact div_two_pow_eq_mul_half_pow (1037 / 2250 : ℝ) k

theorem c13EvenHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B * 2 ^ k) → ℝ) :
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
        B (4 * B * 2 ^ k) x y ^ 2 ≤
      ((499 / 1125 : ℝ) * (1 / 2 : ℝ) ^ k) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B * 2 ^ k)))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B * 2 ^ k))),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)
            ij.1 ij.2 ^ 2) ≤
      (499 / 1125 : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [Finset.sum_product]
    simpa using c13EvenHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le
      B k hB hRawSource hRawTarget
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B * 2 ^ k) → ℝ) :
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
        B (4 * B * 2 ^ k) x y ^ 2 ≤
      ((1037 / 2250 : ℝ) * (1 / 2 : ℝ) ^ k) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B * 2 ^ k)))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B * 2 ^ k))),
        c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)
            ij.1 ij.2 ^ 2) ≤
      (1037 / 2250 : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [Finset.sum_product]
    simpa using c13OddHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le
      B k hB hRawSource hRawTarget
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

lemma c13_even_dyadic_entryBudget_le_gapProduct (k : ℕ) :
    (499 / 1125 : ℝ) * (1 / 2 : ℝ) ^ k ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (428 / 125 : ℝ) * (207 / 50 : ℝ) := by
  have h := mul_le_mul_of_nonneg_right
    c13_even_four_mul_entryBudget_le_oneThirtieth_gapProduct
    (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
  nlinarith

lemma c13_odd_dyadic_entryBudget_le_gapProduct (k : ℕ) :
    (1037 / 2250 : ℝ) * (1 / 2 : ℝ) ^ k ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (428 / 125 : ℝ) * (207 / 50 : ℝ) := by
  have h := mul_le_mul_of_nonneg_right
    c13_odd_four_mul_entryBudget_le_oneThirtieth_gapProduct
    (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
  nlinarith

lemma c13ShellDynamicGap_four_mul_two_pow_ge_207Over50
    (B k : ℕ) (hB : 3840 ≤ B) :
    (207 / 50 : ℝ) ≤ c13ShellDynamicGap (4 * B * 2 ^ k) := by
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
    simpa using Nat.mul_le_mul_left (4 * B) hPow
  have hBase : (207 / 50 : ℝ) ≤ c13ShellDynamicGap (4 * B) := by
    have h := c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840
      (2 * B) (by omega)
    have hEq : 2 * (2 * B) = 4 * B := by omega
    rw [hEq] at h
    exact h
  exact hBase.trans (c13ShellDynamicGap_mono (by omega) hSeparated)

theorem c13HistoricalRemoteEvenBuilder_dyadic_relative_oneThirtieth
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteEvenBuilderMatrix B (4 * B * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
  have hTarget : 960 ≤ 4 * B * 2 ^ k := by
    have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
      simpa using Nat.mul_le_mul_left (4 * B) hPow
    omega
  have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB
  have hGapHigh := c13ShellDynamicGap_four_mul_two_pow_ge_207Over50 B k hB
  have hLowFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B (by omega) (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (4 * B * 2 ^ k) (4 * B * 2 ^ k) hTarget (by omega) y
  have hLowEnergy :
      (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
        c13EvenBuilderShellEnergy B B x := by
    have hScaled :
        (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
          c13ShellDynamicGap B * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hGapLow (by positivity)
    have hFloor :
        c13ShellDynamicGap B * (∑ i, x i ^ 2) ≤
          c13EvenBuilderShellEnergy B B x := by
      simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowFloor
    exact hScaled.trans hFloor
  have hHighEnergy :
      (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
        c13EvenBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
    have hScaled :
        (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
          c13ShellDynamicGap (4 * B * 2 ^ k) * (∑ j, y j ^ 2) :=
      mul_le_mul_of_nonneg_right hGapHigh (by positivity)
    have hFloor :
        c13ShellDynamicGap (4 * B * 2 ^ k) * (∑ j, y j ^ 2) ≤
          c13EvenBuilderShellEnergy
            (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
      simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighFloor
    exact hScaled.trans hFloor
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderShellEnergy B B x)
    (c13EvenBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y)
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B * 2 ^ k) x y)
    (428 / 125) (207 / 50)
    ((499 / 1125) * (1 / 2 : ℝ) ^ k)
    ((1 / 30) * (1 / 2 : ℝ) ^ k)
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
    hLowEnergy hHighEnergy
    (c13EvenHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le
      B k hB hRawSource hRawTarget x y)
    (c13_even_dyadic_entryBudget_le_gapProduct k)

theorem c13HistoricalRemoteOddBuilder_dyadic_relative_oneThirtieth
    (B k : ℕ) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range (4 * B * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((4 * B * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((4 * B * 2 ^ k : ℕ) : ℝ))
    (x : Fin B → ℝ) (y : Fin (4 * B * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteOddBuilderMatrix B (4 * B * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
  have hTarget : 960 ≤ 4 * B * 2 ^ k := by
    have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
      simpa using Nat.mul_le_mul_left (4 * B) hPow
    omega
  have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB
  have hGapHigh := c13ShellDynamicGap_four_mul_two_pow_ge_207Over50 B k hB
  have hLowFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B (by omega) (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (4 * B * 2 ^ k) (4 * B * 2 ^ k) hTarget (by omega) y
  have hLowEnergy :
      (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
        c13OddBuilderShellEnergy B B x := by
    have hScaled :
        (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
          c13ShellDynamicGap B * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hGapLow (by positivity)
    have hFloor :
        c13ShellDynamicGap B * (∑ i, x i ^ 2) ≤
          c13OddBuilderShellEnergy B B x := by
      simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowFloor
    exact hScaled.trans hFloor
  have hHighEnergy :
      (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
        c13OddBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
    have hScaled :
        (207 / 50 : ℝ) * (∑ j, y j ^ 2) ≤
          c13ShellDynamicGap (4 * B * 2 ^ k) * (∑ j, y j ^ 2) :=
      mul_le_mul_of_nonneg_right hGapHigh (by positivity)
    have hFloor :
        c13ShellDynamicGap (4 * B * 2 ^ k) * (∑ j, y j ^ 2) ≤
          c13OddBuilderShellEnergy
            (4 * B * 2 ^ k) (4 * B * 2 ^ k) y := by
      simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighFloor
    exact hScaled.trans hFloor
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13OddBuilderShellEnergy B B x)
    (c13OddBuilderShellEnergy (4 * B * 2 ^ k) (4 * B * 2 ^ k) y)
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B * 2 ^ k) x y)
    (428 / 125) (207 / 50)
    ((1037 / 2250) * (1 / 2 : ℝ) ^ k)
    ((1 / 30) * (1 / 2 : ℝ) ^ k)
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
    hLowEnergy hHighEnergy
    (c13OddHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le
      B k hB hRawSource hRawTarget x y)
    (c13_odd_dyadic_entryBudget_le_gapProduct k)

theorem c13HistoricalRemoteEvenBuilder_dyadic_relative_toTarget_oneThirtieth
    (B k T : ℕ) (hTarget : T = 4 * B * 2 ^ k) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (x : Fin B → ℝ) (y : Fin T → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteEvenBuilderMatrix B T) x y) ^ 2 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        c13EvenBuilderShellEnergy B B x * c13EvenBuilderShellEnergy T T y := by
  subst T
  exact c13HistoricalRemoteEvenBuilder_dyadic_relative_oneThirtieth
    B k hB hRawSource hRawTarget x y

theorem c13HistoricalRemoteOddBuilder_dyadic_relative_toTarget_oneThirtieth
    (B k T : ℕ) (hTarget : T = 4 * B * 2 ^ k) (hB : 3840 ≤ B)
    (hRawSource :
      (∑ j ∈ Finset.range B,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (x : Fin B → ℝ) (y : Fin T → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteOddBuilderMatrix B T) x y) ^ 2 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) *
        c13OddBuilderShellEnergy B B x * c13OddBuilderShellEnergy T T y := by
  subst T
  exact c13HistoricalRemoteOddBuilder_dyadic_relative_oneThirtieth
    B k hB hRawSource hRawTarget x y

theorem c13HistoricalRemoteEvenBuilder_regularDyadicFamily_relative_twoOver27
    (B : ℕ → ℕ) (n T : ℕ) (hT : 960 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = 4 * B i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 3840 ≤ B i)
    (hRawSource : ∀ i ∈ Finset.range n,
      (∑ j ∈ Finset.range (B i),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B i + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B i : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteEvenBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      (2 / 27 : ℝ) *
        (∑ i ∈ Finset.range n,
          c13EvenBuilderShellEnergy (B i) (B i) (x i)) *
        c13EvenBuilderShellEnergy T T y := by
  let energy : ℕ → ℝ := fun i =>
    c13EvenBuilderShellEnergy (B i) (B i) (x i)
  let cross : ℕ → ℝ := fun i =>
    finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix (B i) T) (x i) y
  let budget : ℕ → ℝ := fun i =>
    (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ i
  have hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i := by
    intro i hi
    have hBi := hB i hi
    have hFloor :=
      c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
        (B i) (B i) (by omega) (by omega) (x i)
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (B i) (by omega))
      (finiteVectorEuclideanNormSq_nonneg (x i))).trans (by
        simpa [energy, c13EvenBuilderShellEnergy] using hFloor)
  have hTail : 0 ≤ c13EvenBuilderShellEnergy T T y := by
    have hFloor :=
      c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
        T T hT (by omega) y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg T hT)
      (finiteVectorEuclideanNormSq_nonneg y)).trans (by
        simpa [c13EvenBuilderShellEnergy] using hFloor)
  have hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i := by
    intro i _hi
    exact mul_nonneg (by norm_num) (by positivity)
  have hEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ i := by
    intro i _hi
    exact le_rfl
  have hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        c13EvenBuilderShellEnergy T T y := by
    intro i hi
    exact c13HistoricalRemoteEvenBuilder_dyadic_relative_toTarget_oneThirtieth
      (B i) i T (hTarget i hi) (hB i hi) (hRawSource i hi)
      hRawTarget (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13EvenBuilderShellEnergy T T y)
      (1 / 30 : ℝ) (2 / 27 : ℝ)
      hEnergy hBudget hTail (by norm_num) hEnvelope (by norm_num) hRelative

theorem c13HistoricalRemoteOddBuilder_regularDyadicFamily_relative_twoOver27
    (B : ℕ → ℕ) (n T : ℕ) (hT : 960 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = 4 * B i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 3840 ≤ B i)
    (hRawSource : ∀ i ∈ Finset.range n,
      (∑ j ∈ Finset.range (B i),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((B i + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        2 * (B i : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteOddBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      (2 / 27 : ℝ) *
        (∑ i ∈ Finset.range n,
          c13OddBuilderShellEnergy (B i) (B i) (x i)) *
        c13OddBuilderShellEnergy T T y := by
  let energy : ℕ → ℝ := fun i =>
    c13OddBuilderShellEnergy (B i) (B i) (x i)
  let cross : ℕ → ℝ := fun i =>
    finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix (B i) T) (x i) y
  let budget : ℕ → ℝ := fun i =>
    (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ i
  have hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i := by
    intro i hi
    have hBi := hB i hi
    have hFloor :=
      c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
        (B i) (B i) (by omega) (by omega) (x i)
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (B i) (by omega))
      (finiteVectorEuclideanNormSq_nonneg (x i))).trans (by
        simpa [energy, c13OddBuilderShellEnergy] using hFloor)
  have hTail : 0 ≤ c13OddBuilderShellEnergy T T y := by
    have hFloor :=
      c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
        T T hT (by omega) y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg T hT)
      (finiteVectorEuclideanNormSq_nonneg y)).trans (by
        simpa [c13OddBuilderShellEnergy] using hFloor)
  have hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i := by
    intro i _hi
    exact mul_nonneg (by norm_num) (by positivity)
  have hEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ i := by
    intro i _hi
    exact le_rfl
  have hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        c13OddBuilderShellEnergy T T y := by
    intro i hi
    exact c13HistoricalRemoteOddBuilder_dyadic_relative_toTarget_oneThirtieth
      (B i) i T (hTarget i hi) (hB i hi) (hRawSource i hi)
      hRawTarget (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13OddBuilderShellEnergy T T y)
      (1 / 30 : ℝ) (2 / 27 : ℝ)
      hEnergy hBudget hTail (by norm_num) hEnvelope (by norm_num) hRelative

end RiemannCvs.V23BoundaryWeylMainline
