import RiemannCvs.SharpParityFullBuilderTransport

/-!
# Weighted parity transport down to the `B = 960` analytic frontier

`SharpParityFullBuilderTransport` used the symmetric estimate
`(a-b)^2 <= 2a^2+2b^2`.  That is adequate from `B = 3840`, but it discards
which numerator term carries the target symbol and which carries the source
symbol.  Here the even and odd parity numerators are weighted in opposite
directions:

* even: `(a-b)^2 <= (3/2)a^2 + 3b^2`;
* odd:  `(a-b)^2 <= 3a^2 + (3/2)b^2`.

The resulting dyadic entry budgets preserve the exact `q^{-2}` and `q^{-4}`
moments and fit below `(1/30)2^{-k}` whenever the target shell begins at
`T >= 15360` and the historical source shell has `B >= 960`.  The proof also
reuses the already checked sharp pole-scale estimate to establish coercive
gaps `2` at `B >= 960` and `24/5` at `T >= 15360`.

Consequently the first analytic target has three fully analytic historical
channels, `B = 3840, 1920, 960`, consuming exactly `7/120`.  Only the fixed
shells below `960` remain finite exceptions, and their old certified budgets
fit in the exact residual `17/1080` with positive even and odd slack.  All
matrix statements below concern the literal cutoff-13 builder restrictions;
the only numerical inputs are the displayed raw combined-symbol inequalities.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

set_option maxHeartbeats 800000

lemma c13_logarithmicCvSPoleTail_le_one_div_two_mul
    (M : ℕ) (hM : M ≠ 0) :
    logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (M : ℝ)) ≤ 1 / (2 * (M : ℝ)) := by
  have hScale : logarithmicCvSPoleScale 13 ≤ 4 * Real.pi ^ 2 := by
    unfold logarithmicCvSPoleScale
    nlinarith [c13_poleLoewner_scale_le_four_pi_sq]
  have hDen : 0 < 8 * Real.pi ^ 2 * (M : ℝ) := by positivity
  rw [div_le_iff₀ hDen]
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  field_simp [ne_of_gt hMR]
  nlinarith

lemma c13_log_nat_ge_960_gt_17163Over2500
    (M : ℕ) (hM : 960 ≤ M) :
    (17163 / 2500 : ℝ) < Real.log (M : ℝ) := by
  have hMReal : (960 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLogMono : Real.log (960 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMReal
  have hLog3840 := c13_log_nat_ge_3840_gt_20633Over2500 3840 (by omega)
  change (20633 / 2500 : ℝ) < Real.log (3840 : ℝ) at hLog3840
  have hLogMul : Real.log (3840 : ℝ) =
      2 * Real.log 2 + Real.log 960 := by
    rw [show (3840 : ℝ) = 2 * 2 * 960 by norm_num]
    repeat' rw [Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLogMul] at hLog3840
  nlinarith [RiemannCvs.PrimeTranslationSupersolution.log_two_lt]

lemma c13_log_nat_ge_1920_gt_18888Over2500
    (M : ℕ) (hM : 1920 ≤ M) :
    (18888 / 2500 : ℝ) < Real.log (M : ℝ) := by
  have hMReal : (1920 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLogMono : Real.log (1920 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMReal
  have hLog960 := c13_log_nat_ge_960_gt_17163Over2500 960 (by omega)
  change (17163 / 2500 : ℝ) < Real.log (960 : ℝ) at hLog960
  have hLogMul : Real.log (1920 : ℝ) = Real.log 2 + Real.log 960 := by
    rw [show (1920 : ℝ) = 2 * 960 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hLogMul] at hLogMono
  nlinarith [log_two_gt_sixtyNineHundredths]

lemma c13_log_nat_ge_15360_gt_24083Over2500
    (M : ℕ) (hM : 15360 ≤ M) :
    (24083 / 2500 : ℝ) < Real.log (M : ℝ) := by
  have hMReal : (15360 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLogMono : Real.log (15360 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMReal
  have hLog3840 := c13_log_nat_ge_3840_gt_20633Over2500 3840 (by omega)
  change (20633 / 2500 : ℝ) < Real.log (3840 : ℝ) at hLog3840
  have hLogMul : Real.log (15360 : ℝ) =
      2 * Real.log 2 + Real.log 3840 := by
    rw [show (15360 : ℝ) = 2 * 2 * 3840 by norm_num]
    repeat' rw [Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLogMul] at hLogMono
  nlinarith [log_two_gt_sixtyNineHundredths]

lemma c13ShellDynamicGap_ge_two_of_ge_960
    (M : ℕ) (hM : 960 ≤ M) :
    (2 : ℝ) ≤ c13ShellDynamicGap M := by
  have hLog := c13_log_nat_ge_960_gt_17163Over2500 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_one_div_two_mul M (by omega)
  have hInv : 1 / (2 * (M : ℝ)) ≤ (1 / 1920 : ℝ) := by
    have hMR : (960 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  unfold c13ShellDynamicGap
  nlinarith

lemma c13ShellDynamicGap_ge_twentySevenTenths_of_ge_1920
    (M : ℕ) (hM : 1920 ≤ M) :
    (27 / 10 : ℝ) ≤ c13ShellDynamicGap M := by
  have hLog := c13_log_nat_ge_1920_gt_18888Over2500 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_one_div_two_mul M (by omega)
  have hInv : 1 / (2 * (M : ℝ)) ≤ (1 / 3840 : ℝ) := by
    have hMR : (1920 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  unfold c13ShellDynamicGap
  nlinarith

lemma c13ShellDynamicGap_ge_twentyFourFifths_of_ge_15360
    (M : ℕ) (hM : 15360 ≤ M) :
    (24 / 5 : ℝ) ≤ c13ShellDynamicGap M := by
  have hLog := c13_log_nat_ge_15360_gt_24083Over2500 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_one_div_two_mul M (by omega)
  have hInv : 1 / (2 * (M : ℝ)) ≤ (1 / 30720 : ℝ) := by
    have hMR : (15360 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  unfold c13ShellDynamicGap
  nlinarith

theorem c13HistoricalBuilderLoewnerSymbol_dyadic_unweighted_sum_le_of_ge960
    (B : ℕ) (hB : 960 ≤ B)
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
      have hBRLower : (960 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      have hBSq : (960 : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
      field_simp [ne_of_gt hBR]
      nlinarith

theorem c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le_of_ge960
    (B : ℕ) (hB : 960 ≤ B)
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
    c13HistoricalBuilderLoewnerSymbol_dyadic_unweighted_sum_le_of_ge960
      B hB hRaw

lemma sub_sq_le_threeHalves_three (a b : ℝ) :
    (a - b) ^ 2 ≤ (3 / 2 : ℝ) * a ^ 2 + 3 * b ^ 2 := by
  nlinarith [sq_nonneg (a + 2 * b)]

lemma sub_sq_le_three_threeHalves (a b : ℝ) :
    (a - b) ^ 2 ≤ 3 * a ^ 2 + (3 / 2 : ℝ) * b ^ 2 := by
  nlinarith [sq_nonneg (2 * a + b)]

lemma oddDifferenceKernel_evenParity_sq_le_weightedSeparated
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) * (symbol q ^ 2 / q ^ 2) +
          3 * (p ^ 2 * symbol p ^ 2 / q ^ 4)) := by
  have hpq : p ≠ q := by nlinarith
  have hpNegQ : p ≠ -q := by nlinarith
  have hpqSq : p ^ 2 ≤ q ^ 2 / 4 := by nlinarith [sq_nonneg (q - 2 * p)]
  have hDen : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hDenNe : p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  have hDenLower : (3 / 4 : ℝ) * q ^ 2 ≤ q ^ 2 - p ^ 2 := by nlinarith
  have hDenSqLower : (9 / 16 : ℝ) * q ^ 4 ≤ (q ^ 2 - p ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((q ^ 2 - p ^ 2) - (3 / 4 : ℝ) * q ^ 2)]
  have hInvDenSq :
      1 / (q ^ 2 - p ^ 2) ^ 2 ≤ 16 / (9 * q ^ 4) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q ^ 2 - p ^ 2) ^ 2)
      (by positivity : (0 : ℝ) < 9 * q ^ 4)]
    nlinarith
  have hNum := sub_sq_le_threeHalves_three
    (q * symbol q) (p * symbol p)
  have hNum4 :
      4 * (q * symbol q - p * symbol p) ^ 2 ≤
        4 * ((3 / 2 : ℝ) * (q ^ 2 * symbol q ^ 2) +
          3 * (p ^ 2 * symbol p ^ 2)) := by nlinarith
  have hInv0 : 0 ≤ 1 / (q ^ 2 - p ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  rw [CvSParityDisplacement.oddDifferenceKernel_evenParity_offDiagonal
    symbol diagonal p q hpq hpNegQ hOdd]
  have hSum0 :
      0 ≤ (3 / 2 : ℝ) * (q ^ 2 * symbol q ^ 2) +
        3 * (p ^ 2 * symbol p ^ 2) := by positivity
  calc
    (2 * (q * symbol q - p * symbol p) / (p ^ 2 - q ^ 2)) ^ 2 =
        4 * (q * symbol q - p * symbol p) ^ 2 *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      field_simp [hDenNe]
      ring
    _ ≤ 4 * ((3 / 2 : ℝ) * (q ^ 2 * symbol q ^ 2) +
          3 * (p ^ 2 * symbol p ^ 2)) *
          (1 / (q ^ 2 - p ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_right hNum4 hInv0
    _ ≤ 4 * ((3 / 2 : ℝ) * (q ^ 2 * symbol q ^ 2) +
          3 * (p ^ 2 * symbol p ^ 2)) * (16 / (9 * q ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hInvDenSq (mul_nonneg (by norm_num) hSum0)
    _ = (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) * (symbol q ^ 2 / q ^ 2) +
          3 * (p ^ 2 * symbol p ^ 2 / q ^ 4)) := by
      field_simp [ne_of_gt hq]
      ring

lemma oddDifferenceKernel_oddParity_sq_le_weightedSeparated
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (64 / 9 : ℝ) *
        (3 * (p ^ 2 * symbol q ^ 2 / q ^ 4) +
          (3 / 2 : ℝ) * (symbol p ^ 2 / q ^ 2)) := by
  have hpq : p ≠ q := by nlinarith
  have hpNegQ : p ≠ -q := by nlinarith
  have hpqSq : p ^ 2 ≤ q ^ 2 / 4 := by nlinarith [sq_nonneg (q - 2 * p)]
  have hDen : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hDenNe : p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  have hDenLower : (3 / 4 : ℝ) * q ^ 2 ≤ q ^ 2 - p ^ 2 := by nlinarith
  have hDenSqLower : (9 / 16 : ℝ) * q ^ 4 ≤ (q ^ 2 - p ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((q ^ 2 - p ^ 2) - (3 / 4 : ℝ) * q ^ 2)]
  have hInvDenSq :
      1 / (q ^ 2 - p ^ 2) ^ 2 ≤ 16 / (9 * q ^ 4) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q ^ 2 - p ^ 2) ^ 2)
      (by positivity : (0 : ℝ) < 9 * q ^ 4)]
    nlinarith
  have hNum := sub_sq_le_three_threeHalves
    (p * symbol q) (q * symbol p)
  have hNum4 :
      4 * (p * symbol q - q * symbol p) ^ 2 ≤
        4 * (3 * (p ^ 2 * symbol q ^ 2) +
          (3 / 2 : ℝ) * (q ^ 2 * symbol p ^ 2)) := by nlinarith
  have hInv0 : 0 ≤ 1 / (q ^ 2 - p ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  rw [CvSParityDisplacement.oddDifferenceKernel_oddParity_offDiagonal
    symbol diagonal p q hpq hpNegQ hOdd]
  have hSum0 :
      0 ≤ 3 * (p ^ 2 * symbol q ^ 2) +
        (3 / 2 : ℝ) * (q ^ 2 * symbol p ^ 2) := by positivity
  calc
    (2 * (p * symbol q - q * symbol p) / (p ^ 2 - q ^ 2)) ^ 2 =
        4 * (p * symbol q - q * symbol p) ^ 2 *
          (1 / (q ^ 2 - p ^ 2) ^ 2) := by
      field_simp [hDenNe]
      ring
    _ ≤ 4 * (3 * (p ^ 2 * symbol q ^ 2) +
          (3 / 2 : ℝ) * (q ^ 2 * symbol p ^ 2)) *
          (1 / (q ^ 2 - p ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_right hNum4 hInv0
    _ ≤ 4 * (3 * (p ^ 2 * symbol q ^ 2) +
          (3 / 2 : ℝ) * (q ^ 2 * symbol p ^ 2)) * (16 / (9 * q ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hInvDenSq (mul_nonneg (by norm_num) hSum0)
    _ = (64 / 9 : ℝ) *
        (3 * (p ^ 2 * symbol q ^ 2 / q ^ 4) +
          (3 / 2 : ℝ) * (symbol p ^ 2 / q ^ 2)) := by
      field_simp [ne_of_gt hq]
      ring

lemma rectangular_evenParity_sum_sq_le_weightedSeparated
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (symbol _diagonal : ℝ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (entry : ι → κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      entry i j ^ 2 ≤ (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) * (symbol (q j) ^ 2 / (q j) ^ 2) +
          3 * ((p i) ^ 2 * symbol (p i) ^ 2 / (q j) ^ 4))) :
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
      (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) * rows.card *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 2) +
          3 * (∑ i ∈ rows, (p i) ^ 2 * symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 4)) := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, (64 / 9 : ℝ) *
          ((3 / 2 : ℝ) * (symbol (q j) ^ 2 / (q j) ^ 2) +
            3 * ((p i) ^ 2 * symbol (p i) ^ 2 / (q j) ^ 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) * rows.card *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 2) +
          3 * (∑ i ∈ rows, (p i) ^ 2 * symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 4)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring_nf
      rw [Finset.sum_comm]

lemma rectangular_oddParity_sum_sq_le_weightedSeparated
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (symbol _diagonal : ℝ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (entry : ι → κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      entry i j ^ 2 ≤ (64 / 9 : ℝ) *
        (3 * ((p i) ^ 2 * symbol (q j) ^ 2 / (q j) ^ 4) +
          (3 / 2 : ℝ) * (symbol (p i) ^ 2 / (q j) ^ 2))) :
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
      (64 / 9 : ℝ) *
        (3 * (∑ i ∈ rows, (p i) ^ 2) *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 4) +
          (3 / 2 : ℝ) * (∑ i ∈ rows, symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 2)) := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, entry i j ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, (64 / 9 : ℝ) *
          (3 * ((p i) ^ 2 * symbol (q j) ^ 2 / (q j) ^ 4) +
            (3 / 2 : ℝ) * (symbol (p i) ^ 2 / (q j) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = (64 / 9 : ℝ) *
        (3 * (∑ i ∈ rows, (p i) ^ 2) *
            (∑ j ∈ columns, symbol (q j) ^ 2 / (q j) ^ 4) +
          (3 / 2 : ℝ) * (∑ i ∈ rows, symbol (p i) ^ 2) *
            (∑ j ∈ columns, 1 / (q j) ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      ring_nf
      congr 1 <;> rw [Finset.sum_comm]

theorem c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_weightedExpression
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N)
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
      (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) *
            ((B : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ))) +
          3 * ((4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
            (1 / (2 * (N : ℝ) ^ 3)))) := by
  have hN0 : N ≠ 0 := by omega
  have hN1920 : 1920 ≤ N := by omega
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le_of_ge960
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
            (64 / 9 : ℝ) *
              ((3 / 2 : ℝ) *
                  (c13HistoricalBuilderLoewnerSymbol
                      (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
                3 * ((historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (historicalBandMode B i : ℝ) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := by
    intro i _hi j _hj
    unfold c13EvenHistoricalBuilderLoewnerRemoteEntry
      c13EvenHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_evenParity_sq_le_weightedSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_evenParity_sum_sq_le_weightedSeparated
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B N) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin N,
          c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
        (64 / 9 : ℝ) *
          ((3 / 2 : ℝ) * (B : ℝ) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
            3 * (∑ i : Fin B,
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
  have hInside := add_le_add
    (mul_le_mul_of_nonneg_left hFirst (by norm_num : (0 : ℝ) ≤ 3 / 2))
    (mul_le_mul_of_nonneg_left hSecond (by norm_num : (0 : ℝ) ≤ 3))
  exact hRect'.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

theorem c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_weightedExpression
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N)
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
      (64 / 9 : ℝ) *
        (3 * ((4 * (B : ℝ) ^ 3) *
            ((197 / 2000 : ℝ) / (N : ℝ) ^ 3)) +
          (3 / 2 : ℝ) * (((21 / 100 : ℝ) * (B : ℝ)) *
            (1 / (2 * (N : ℝ))))) := by
  have hN0 : N ≠ 0 := by omega
  have hN1920 : 1920 ≤ N := by omega
  have hSource :=
    c13HistoricalBuilderLoewnerSymbol_historicalBand_sum_le_of_ge960
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
            (64 / 9 : ℝ) *
              (3 * ((historicalBandMode B i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
                (3 / 2 : ℝ) *
                  (c13HistoricalBuilderLoewnerSymbol
                      (historicalBandMode B i : ℝ) ^ 2 /
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := by
    intro i _hi j _hj
    unfold c13OddHistoricalBuilderLoewnerRemoteEntry
      c13OddHistoricalBuilderLoewnerRemoteNatEntry
    exact oddDifferenceKernel_oddParity_sq_le_weightedSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (historicalBandMode_real_nonneg B i) (by positivity)
      (c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_oddParity_sum_sq_le_weightedSeparated
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin B => (historicalBandMode B i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B N) hEntry
  have hRect' :
      (∑ i : Fin B, ∑ j : Fin N,
          c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
        (64 / 9 : ℝ) *
          (3 * (∑ i : Fin B, (historicalBandMode B i : ℝ) ^ 2) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
            (3 / 2 : ℝ) * (∑ i : Fin B,
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
  have hInside := add_le_add
    (mul_le_mul_of_nonneg_left hFirst (by norm_num : (0 : ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left hSecond (by norm_num : (0 : ℝ) ≤ 3 / 2))
  exact hRect'.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

noncomputable def c13EvenWeightedRemoteBudget (k : ℕ) : ℝ :=
  (64 / 9 : ℝ) *
    ((3 / 2 : ℝ) * ((197 / 8000 : ℝ) / (2 : ℝ) ^ k) +
      3 * ((21 / 3200 : ℝ) / ((2 : ℝ) ^ k) ^ 3))

noncomputable def c13OddWeightedRemoteBudget (k : ℕ) : ℝ :=
  (64 / 9 : ℝ) *
    (3 * ((197 / 32000 : ℝ) / ((2 : ℝ) ^ k) ^ 3) +
      (3 / 2 : ℝ) * ((21 / 800 : ℝ) / (2 : ℝ) ^ k))

lemma c13EvenWeightedRemoteBudget_le_eightTwentyFifths_half_pow
    (k : ℕ) (hk : 1 ≤ k) :
    c13EvenWeightedRemoteBudget k ≤
      (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k := by
  let r : ℝ := (2 : ℝ) ^ k
  have hr : 2 ≤ r := by
    cases k with
    | zero => omega
    | succ m =>
        dsimp [r]
        rw [pow_succ]
        have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        nlinarith
  have hr0 : 0 < r := by nlinarith
  have hrSq : 4 ≤ r ^ 2 := by nlinarith
  have hCore :
      (64 / 9 : ℝ) *
          ((3 / 2 : ℝ) * ((197 / 8000 : ℝ) / r) +
            3 * ((21 / 3200 : ℝ) / r ^ 3)) ≤
        (8 / 25 : ℝ) / r := by
    field_simp [ne_of_gt hr0]
    nlinarith
  calc
    c13EvenWeightedRemoteBudget k =
        (64 / 9 : ℝ) *
          ((3 / 2 : ℝ) * ((197 / 8000 : ℝ) / r) +
            3 * ((21 / 3200 : ℝ) / r ^ 3)) := by
      rfl
    _ ≤ (8 / 25 : ℝ) / r := hCore
    _ = (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k := by
      dsimp [r]
      exact div_two_pow_eq_mul_half_pow (8 / 25 : ℝ) k

lemma c13OddWeightedRemoteBudget_le_eightTwentyFifths_half_pow
    (k : ℕ) (hk : 1 ≤ k) :
    c13OddWeightedRemoteBudget k ≤
      (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k := by
  let r : ℝ := (2 : ℝ) ^ k
  have hr : 2 ≤ r := by
    cases k with
    | zero => omega
    | succ m =>
        dsimp [r]
        rw [pow_succ]
        have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        nlinarith
  have hr0 : 0 < r := by nlinarith
  have hrSq : 4 ≤ r ^ 2 := by nlinarith
  have hCore :
      (64 / 9 : ℝ) *
          (3 * ((197 / 32000 : ℝ) / r ^ 3) +
            (3 / 2 : ℝ) * ((21 / 800 : ℝ) / r)) ≤
        (8 / 25 : ℝ) / r := by
    field_simp [ne_of_gt hr0]
    nlinarith
  calc
    c13OddWeightedRemoteBudget k =
        (64 / 9 : ℝ) *
          (3 * ((197 / 32000 : ℝ) / r ^ 3) +
            (3 / 2 : ℝ) * ((21 / 800 : ℝ) / r)) := by
      rfl
    _ ≤ (8 / 25 : ℝ) / r := hCore
    _ = (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k := by
      dsimp [r]
      exact div_two_pow_eq_mul_half_pow (8 / 25 : ℝ) k

theorem c13EvenHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le_weighted
    (B k : ℕ) (hB : 960 ≤ B)
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
      c13EvenWeightedRemoteBudget k := by
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
    simpa using Nat.mul_le_mul_left (4 * B) hPow
  have hGeneral :=
    c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_weightedExpression
      B (4 * B * 2 ^ k) hB hSeparated hRawSource hRawTarget
  let r : ℝ := (2 : ℝ) ^ k
  have hBReal : (0 : ℝ) < B := by positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hCast : ((4 * B * 2 ^ k : ℕ) : ℝ) = 4 * (B : ℝ) * r := by
    dsimp [r]
    push_cast
    ring
  have hRewrite :
      (64 / 9 : ℝ) *
        ((3 / 2 : ℝ) *
            ((B : ℝ) * ((197 / 2000 : ℝ) /
              ((4 * B * 2 ^ k : ℕ) : ℝ))) +
          3 * ((4 * (21 / 100 : ℝ) * (B : ℝ) ^ 3) *
            (1 / (2 * ((4 * B * 2 ^ k : ℕ) : ℝ) ^ 3)))) =
        c13EvenWeightedRemoteBudget k := by
    rw [hCast]
    unfold c13EvenWeightedRemoteBudget
    dsimp [r]
    field_simp [ne_of_gt hBReal, ne_of_gt hr0]
    ring
  rw [hRewrite] at hGeneral
  exact hGeneral

theorem c13OddHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le_weighted
    (B k : ℕ) (hB : 960 ≤ B)
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
      c13OddWeightedRemoteBudget k := by
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSeparated : 4 * B ≤ 4 * B * 2 ^ k := by
    simpa using Nat.mul_le_mul_left (4 * B) hPow
  have hGeneral :=
    c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_weightedExpression
      B (4 * B * 2 ^ k) hB hSeparated hRawSource hRawTarget
  let r : ℝ := (2 : ℝ) ^ k
  have hBReal : (0 : ℝ) < B := by positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hCast : ((4 * B * 2 ^ k : ℕ) : ℝ) = 4 * (B : ℝ) * r := by
    dsimp [r]
    push_cast
    ring
  have hRewrite :
      (64 / 9 : ℝ) *
        (3 * ((4 * (B : ℝ) ^ 3) *
            ((197 / 2000 : ℝ) /
              ((4 * B * 2 ^ k : ℕ) : ℝ) ^ 3)) +
          (3 / 2 : ℝ) * (((21 / 100 : ℝ) * (B : ℝ)) *
            (1 / (2 * ((4 * B * 2 ^ k : ℕ) : ℝ))))) =
        c13OddWeightedRemoteBudget k := by
    rw [hCast]
    unfold c13OddWeightedRemoteBudget
    dsimp [r]
    field_simp [ne_of_gt hBReal, ne_of_gt hr0]
    ring
  rw [hRewrite] at hGeneral
  exact hGeneral

theorem c13EvenHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
    (B k : ℕ) (hB : 960 ≤ B)
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
      c13EvenWeightedRemoteBudget k *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B * 2 ^ k)))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B * 2 ^ k))),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)
            ij.1 ij.2 ^ 2) ≤ c13EvenWeightedRemoteBudget k := by
    rw [Finset.sum_product]
    simpa using
      c13EvenHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le_weighted
        B k hB hRawSource hRawTarget
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
    (B k : ℕ) (hB : 960 ≤ B)
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
      c13OddWeightedRemoteBudget k *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin (4 * B * 2 ^ k)))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin (4 * B * 2 ^ k))),
        c13OddHistoricalBuilderLoewnerRemoteEntry B (4 * B * 2 ^ k)
            ij.1 ij.2 ^ 2) ≤ c13OddWeightedRemoteBudget k := by
    rw [Finset.sum_product]
    simpa using
      c13OddHistoricalBuilderLoewnerRemote_dyadic_entry_sq_sum_le_weighted
        B k hB hRawSource hRawTarget
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hEntries (by positivity))

lemma c13EvenBuilderShellEnergy_ge_two_of_ge960
    (B : ℕ) (hB : 960 ≤ B) (x : Fin B → ℝ) :
    (2 : ℝ) * (∑ i, x i ^ 2) ≤ c13EvenBuilderShellEnergy B B x := by
  have hGap := c13ShellDynamicGap_ge_two_of_ge_960 B hB
  have hFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  exact (mul_le_mul_of_nonneg_right hGap (by positivity)).trans (by
    simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hFloor)

lemma c13OddBuilderShellEnergy_ge_two_of_ge960
    (B : ℕ) (hB : 960 ≤ B) (x : Fin B → ℝ) :
    (2 : ℝ) * (∑ i, x i ^ 2) ≤ c13OddBuilderShellEnergy B B x := by
  have hGap := c13ShellDynamicGap_ge_two_of_ge_960 B hB
  have hFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  exact (mul_le_mul_of_nonneg_right hGap (by positivity)).trans (by
    simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hFloor)

lemma c13EvenBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
    (N : ℕ) (hN : 15360 ≤ N) (y : Fin N → ℝ) :
    (24 / 5 : ℝ) * (∑ j, y j ^ 2) ≤ c13EvenBuilderShellEnergy N N y := by
  have hGap := c13ShellDynamicGap_ge_twentyFourFifths_of_ge_15360 N hN
  have hFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      N N (by omega) (by omega) y
  exact (mul_le_mul_of_nonneg_right hGap (by positivity)).trans (by
    simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hFloor)

lemma c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
    (N : ℕ) (hN : 15360 ≤ N) (y : Fin N → ℝ) :
    (24 / 5 : ℝ) * (∑ j, y j ^ 2) ≤ c13OddBuilderShellEnergy N N y := by
  have hGap := c13ShellDynamicGap_ge_twentyFourFifths_of_ge_15360 N hN
  have hFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      N N (by omega) (by omega) y
  exact (mul_le_mul_of_nonneg_right hGap (by positivity)).trans (by
    simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hFloor)

lemma c13EvenWeightedRemoteBudget_zero_le_gapProduct :
    c13EvenWeightedRemoteBudget 0 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ 0) *
        (428 / 125 : ℝ) * (24 / 5 : ℝ) := by
  norm_num [c13EvenWeightedRemoteBudget]

lemma c13OddWeightedRemoteBudget_zero_le_gapProduct :
    c13OddWeightedRemoteBudget 0 ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ 0) *
        (428 / 125 : ℝ) * (24 / 5 : ℝ) := by
  norm_num [c13OddWeightedRemoteBudget]

lemma c13EvenWeightedRemoteBudget_succ_le_gapProduct
    (k : ℕ) (hk : 1 ≤ k) :
    c13EvenWeightedRemoteBudget k ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) * 2 * (24 / 5 : ℝ) := by
  calc
    c13EvenWeightedRemoteBudget k ≤
        (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k :=
      c13EvenWeightedRemoteBudget_le_eightTwentyFifths_half_pow k hk
    _ = ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) * 2 * (24 / 5 : ℝ) := by ring

lemma c13OddWeightedRemoteBudget_succ_le_gapProduct
    (k : ℕ) (hk : 1 ≤ k) :
    c13OddWeightedRemoteBudget k ≤
      ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) * 2 * (24 / 5 : ℝ) := by
  calc
    c13OddWeightedRemoteBudget k ≤
        (8 / 25 : ℝ) * (1 / 2 : ℝ) ^ k :=
      c13OddWeightedRemoteBudget_le_eightTwentyFifths_half_pow k hk
    _ = ((1 / 30 : ℝ) * (1 / 2 : ℝ) ^ k) * 2 * (24 / 5 : ℝ) := by ring

theorem c13HistoricalRemoteEvenBuilder_dyadic_relative_oneThirtieth_of_ge960
    (B k : ℕ) (hB : 960 ≤ B) (hTarget : 15360 ≤ 4 * B * 2 ^ k)
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
  have hHigh :=
    c13EvenBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
      (4 * B * 2 ^ k) hTarget y
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  cases k with
  | zero =>
      have hTarget0 : 15360 ≤ 4 * B := by simpa using hTarget
      have hB3840 : 3840 ≤ B := by omega
      have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB3840
      have hLowFloor :=
        c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
          B B (by omega) (by omega) x
      have hLow :
          (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
            c13EvenBuilderShellEnergy B B x :=
        (mul_le_mul_of_nonneg_right hGapLow (by positivity)).trans (by
          simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq]
            using hLowFloor)
      apply relativeCoupling_of_squaredNormBudget
        (c13EvenBuilderShellEnergy B B x)
        (c13EvenBuilderShellEnergy (4 * B * 2 ^ 0) (4 * B * 2 ^ 0) y)
        (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B * 2 ^ 0) x y)
        (428 / 125) (24 / 5) (c13EvenWeightedRemoteBudget 0)
        ((1 / 30) * (1 / 2 : ℝ) ^ 0)
        (∑ i, x i ^ 2) (∑ j, y j ^ 2)
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
        hLow (by simpa using hHigh)
        (c13EvenHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
          B 0 hB hRawSource hRawTarget x y)
        c13EvenWeightedRemoteBudget_zero_le_gapProduct
  | succ k =>
      have hk : 1 ≤ Nat.succ k := by omega
      have hLow := c13EvenBuilderShellEnergy_ge_two_of_ge960 B hB x
      apply relativeCoupling_of_squaredNormBudget
        (c13EvenBuilderShellEnergy B B x)
        (c13EvenBuilderShellEnergy (4 * B * 2 ^ (Nat.succ k))
          (4 * B * 2 ^ (Nat.succ k)) y)
        (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
          B (4 * B * 2 ^ (Nat.succ k)) x y)
        2 (24 / 5) (c13EvenWeightedRemoteBudget (Nat.succ k))
        ((1 / 30) * (1 / 2 : ℝ) ^ (Nat.succ k))
        (∑ i, x i ^ 2) (∑ j, y j ^ 2)
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
        hLow (by simpa using hHigh)
        (c13EvenHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
          B (Nat.succ k) hB hRawSource hRawTarget x y)
        (c13EvenWeightedRemoteBudget_succ_le_gapProduct (Nat.succ k) hk)

theorem c13HistoricalRemoteOddBuilder_dyadic_relative_oneThirtieth_of_ge960
    (B k : ℕ) (hB : 960 ≤ B) (hTarget : 15360 ≤ 4 * B * 2 ^ k)
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
  have hHigh :=
    c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
      (4 * B * 2 ^ k) hTarget y
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  cases k with
  | zero =>
      have hTarget0 : 15360 ≤ 4 * B := by simpa using hTarget
      have hB3840 : 3840 ≤ B := by omega
      have hGapLow := c13ShellDynamicGap_ge_428Over125_of_ge_3840 B hB3840
      have hLowFloor :=
        c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
          B B (by omega) (by omega) x
      have hLow :
          (428 / 125 : ℝ) * (∑ i, x i ^ 2) ≤
            c13OddBuilderShellEnergy B B x :=
        (mul_le_mul_of_nonneg_right hGapLow (by positivity)).trans (by
          simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq]
            using hLowFloor)
      apply relativeCoupling_of_squaredNormBudget
        (c13OddBuilderShellEnergy B B x)
        (c13OddBuilderShellEnergy (4 * B * 2 ^ 0) (4 * B * 2 ^ 0) y)
        (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (4 * B * 2 ^ 0) x y)
        (428 / 125) (24 / 5) (c13OddWeightedRemoteBudget 0)
        ((1 / 30) * (1 / 2 : ℝ) ^ 0)
        (∑ i, x i ^ 2) (∑ j, y j ^ 2)
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
        hLow (by simpa using hHigh)
        (c13OddHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
          B 0 hB hRawSource hRawTarget x y)
        c13OddWeightedRemoteBudget_zero_le_gapProduct
  | succ k =>
      have hk : 1 ≤ Nat.succ k := by omega
      have hLow := c13OddBuilderShellEnergy_ge_two_of_ge960 B hB x
      apply relativeCoupling_of_squaredNormBudget
        (c13OddBuilderShellEnergy B B x)
        (c13OddBuilderShellEnergy (4 * B * 2 ^ (Nat.succ k))
          (4 * B * 2 ^ (Nat.succ k)) y)
        (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
          B (4 * B * 2 ^ (Nat.succ k)) x y)
        2 (24 / 5) (c13OddWeightedRemoteBudget (Nat.succ k))
        ((1 / 30) * (1 / 2 : ℝ) ^ (Nat.succ k))
        (∑ i, x i ^ 2) (∑ j, y j ^ 2)
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
        hLow (by simpa using hHigh)
        (c13OddHistoricalBuilderLoewnerRemote_dyadic_crossEnergy_sq_le_weighted
          B (Nat.succ k) hB hRawSource hRawTarget x y)
        (c13OddWeightedRemoteBudget_succ_le_gapProduct (Nat.succ k) hk)

theorem c13HistoricalRemoteEvenBuilder_dyadic_relative_toTarget_oneThirtieth_of_ge960
    (B k T : ℕ) (hTarget : T = 4 * B * 2 ^ k)
    (hT : 15360 ≤ T) (hB : 960 ≤ B)
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
  exact c13HistoricalRemoteEvenBuilder_dyadic_relative_oneThirtieth_of_ge960
    B k hB hT hRawSource hRawTarget x y

theorem c13HistoricalRemoteOddBuilder_dyadic_relative_toTarget_oneThirtieth_of_ge960
    (B k T : ℕ) (hTarget : T = 4 * B * 2 ^ k)
    (hT : 15360 ≤ T) (hB : 960 ≤ B)
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
  exact c13HistoricalRemoteOddBuilder_dyadic_relative_oneThirtieth_of_ge960
    B k hB hT hRawSource hRawTarget x y

theorem c13HistoricalRemoteEvenBuilder_lowFrontierDyadicFamily_relative_twoOver27
    (B : ℕ → ℕ) (n T : ℕ) (hT : 15360 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = 4 * B i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
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
    have hFloor := c13EvenBuilderShellEnergy_ge_two_of_ge960
      (B i) (hB i hi) (x i)
    change 0 ≤ c13EvenBuilderShellEnergy (B i) (B i) (x i)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 ≤ ∑ j, x i j ^ 2)).trans hFloor
  have hTail : 0 ≤ c13EvenBuilderShellEnergy T T y := by
    have hFloor := c13EvenBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
      T hT y
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 5)
      (by positivity : 0 ≤ ∑ j, y j ^ 2)).trans hFloor
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
    exact c13HistoricalRemoteEvenBuilder_dyadic_relative_toTarget_oneThirtieth_of_ge960
      (B i) i T (hTarget i hi) hT (hB i hi) (hRawSource i hi)
      hRawTarget (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13EvenBuilderShellEnergy T T y)
      (1 / 30 : ℝ) (2 / 27 : ℝ)
      hEnergy hBudget hTail (by norm_num) hEnvelope (by norm_num) hRelative

theorem c13HistoricalRemoteOddBuilder_lowFrontierDyadicFamily_relative_twoOver27
    (B : ℕ → ℕ) (n T : ℕ) (hT : 15360 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = 4 * B i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
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
    have hFloor := c13OddBuilderShellEnergy_ge_two_of_ge960
      (B i) (hB i hi) (x i)
    change 0 ≤ c13OddBuilderShellEnergy (B i) (B i) (x i)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 ≤ ∑ j, x i j ^ 2)).trans hFloor
  have hTail : 0 ≤ c13OddBuilderShellEnergy T T y := by
    have hFloor := c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
      T hT y
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 5)
      (by positivity : 0 ≤ ∑ j, y j ^ 2)).trans hFloor
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
    exact c13HistoricalRemoteOddBuilder_dyadic_relative_toTarget_oneThirtieth_of_ge960
      (B i) i T (hTarget i hi) hT (hB i hi) (hRawSource i hi)
      hRawTarget (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13OddBuilderShellEnergy T T y)
      (1 / 30 : ℝ) (2 / 27 : ℝ)
      hEnergy hBudget hTail (by norm_num) hEnvelope (by norm_num) hRelative

/-- The first analytic target `T = 15360` has exactly three historical source
shells at or above the new analytic frontier: `B = 3840, 1920, 960`.  Their
geometric budgets consume only `7/120`, not the full `2/27` allowance. -/
lemma v23_lowFrontier_firstThreeBudget :
    (∑ i ∈ Finset.range 3,
      (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ i) = 7 / 120 := by
  norm_num [Finset.sum_range_succ]

/-- Exact budget left for the fixed shells below `B = 960`. -/
lemma v23_lowFrontier_firstThreeResidual :
    (2 / 27 : ℝ) - 7 / 120 = 17 / 1080 := by
  norm_num

/-- The two remaining even regular finite bands cost `1/240 + 1/480`; the
resulting slack reproduces the independently certified finite allocation. -/
lemma v23_lowFrontier_evenFiniteResidual :
    (17 / 1080 : ℝ) - (1 / 240 + 1 / 480) = 41 / 4320 := by
  norm_num

/-- In the odd sector the remaining `1/240` regular band and the `1/384`
fixed-base exception leave the same positive slack as the finite certificate. -/
lemma v23_lowFrontier_oddFiniteResidual :
    (17 / 1080 : ℝ) - (1 / 240 + 1 / 384) = 31 / 3456 := by
  norm_num

end RiemannCvs.V23BoundaryWeylMainline
