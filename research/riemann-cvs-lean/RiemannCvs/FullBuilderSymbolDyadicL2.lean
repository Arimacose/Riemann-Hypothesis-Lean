import RiemannCvs.FullBuilderLoewnerTransport

/-!
# Sharp dyadic L2 budget for the complete cutoff-13 builder symbol

The complete cutoff-13 historical builder was identified in
`FullBuilderLoewnerTransport` as one odd Loewner symbol.  This module closes its
regular dyadic scalar budget without splitting the actual kernel into pole,
Archimedean, and prime matrix channels.

There are three quantitative ingredients.

1. The rational pole symbol satisfies `|P(x)| <= 1/(4*x)` for positive `x`,
   hence its weighted square sum on `(N,2N]` is at most `1/(32*N^3)`.
2. The actual historical combined symbol is Fourier-normalized by `1/pi`.
   Thus a raw combined-symbol certificate with constant `97/100` improves to
   `2425/24649` using the rigorous lower bound `pi > 3.14`.
3. The weighted Young inequality with parameter `1/3000` preserves the much
   larger combined-symbol contribution while absorbing the cubic pole tail.

For every `N >= 1920` the resulting full-builder constant is strictly below
`197/2000`.  The final even/odd corollaries feed this sharper scalar constant
directly into the exact `q*(1/2)^k` transport theorem.  The only remaining
input there is the tracked raw combined-symbol certificate and the source
rectangular budget; no midpoint diagnostic is promoted to a premise.
-/
noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.C13ArchimedeanEndpoint
open RiemannCvs.BoundaryWeylSchurTail

lemma c13_sinh_log_div_four_sq_eq :
    Real.sinh (Real.log 13 / 4) ^ 2 =
      (Real.sqrt 13 + (Real.sqrt 13)⁻¹ - 2) / 4 := by
  have hCosh := Real.cosh_two_mul (Real.log 13 / 4)
  rw [show 2 * (Real.log 13 / 4) = Real.log 13 / 2 by ring,
    Real.cosh_eq, exp_log_thirteen_div_two,
    show -(Real.log 13 / 2) = -Real.log 13 / 2 by ring,
    exp_neg_log_thirteen_div_two, Real.cosh_sq] at hCosh
  nlinarith

lemma c13_sinh_log_div_four_sq_le_twelveTwentyFifths :
    Real.sinh (Real.log 13 / 4) ^ 2 ≤ (12 / 25 : ℝ) := by
  have hsPos : 0 < Real.sqrt (13 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsLow : (18 / 5 : ℝ) < Real.sqrt 13 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsHigh : Real.sqrt 13 < (361 / 100 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hInv : (Real.sqrt 13)⁻¹ < (5 / 18 : ℝ) := by
    have hScaled := mul_lt_mul_of_pos_left hsLow (inv_pos.mpr hsPos)
    rw [inv_mul_cancel₀ (ne_of_gt hsPos)] at hScaled
    nlinarith
  rw [c13_sinh_log_div_four_sq_eq]
  nlinarith

lemma c13_poleLoewner_scale_le_four_pi_sq :
    4 * (32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2) ≤
      16 * Real.pi ^ 2 := by
  have hLog0 : 0 ≤ Real.log (13 : ℝ) := (Real.log_pos (by norm_num)).le
  have hSinh0 : 0 ≤ Real.sinh (Real.log 13 / 4) ^ 2 := sq_nonneg _
  have hScaleUpper :
      32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2 ≤
        32 * (513 / 200 : ℝ) * (12 / 25 : ℝ) := by
    calc
      32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2 ≤
          32 * (513 / 200 : ℝ) * Real.sinh (Real.log 13 / 4) ^ 2 := by
        gcongr
        exact le_of_lt log_thirteen_lt
      _ ≤ 32 * (513 / 200 : ℝ) * (12 / 25 : ℝ) := by
        gcongr
        exact c13_sinh_log_div_four_sq_le_twelveTwentyFifths
  have hPiSq : (314 / 100 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2]
  nlinarith

theorem c13_abs_logarithmicPoleLoewnerSymbol_le_one_div_four_mul_inv
    (x : ℝ) (hx : 0 < x) :
    |logarithmicPoleLoewnerSymbol 13 x| ≤ 1 / (4 * x) := by
  have hScale0 :
      0 ≤ 32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2 := by
    positivity
  have hDenPos :
      0 < Real.log 13 ^ 2 + 16 * Real.pi ^ 2 * x ^ 2 := by
    positivity
  unfold logarithmicPoleLoewnerSymbol rationalPoleLoewnerSymbol
  rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hScale0,
    abs_of_pos hx, abs_of_pos hDenPos]
  apply (div_le_iff₀ hDenPos).2
  have hScaleX :
      4 * (32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2) * x ^ 2 ≤
        16 * Real.pi ^ 2 * x ^ 2 :=
    mul_le_mul_of_nonneg_right c13_poleLoewner_scale_le_four_pi_sq
      (sq_nonneg x)
  field_simp [ne_of_gt hx]
  nlinarith [sq_nonneg (Real.log 13)]

lemma c13_logarithmicPoleLoewnerSymbol_shifted_weight_term_le
    (N j : ℕ) (hN : N ≠ 0) :
    logarithmicPoleLoewnerSymbol 13 (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
        (((N + 1 + j : ℕ) : ℝ)) ^ 2 ≤
      (1 / (16 * (N : ℝ) ^ 2)) *
        ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
  let t : ℝ := ((N + 1 + j : ℕ) : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hNt : (N : ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast (show N ≤ N + 1 + j by omega)
  have hAbs :=
    c13_abs_logarithmicPoleLoewnerSymbol_le_one_div_four_mul_inv t ht
  have hRight0 : 0 ≤ 1 / (4 * t) := by positivity
  have hSq :
      logarithmicPoleLoewnerSymbol 13 t ^ 2 ≤ (1 / (4 * t)) ^ 2 := by
    have h := (sq_le_sq₀
      (abs_nonneg (logarithmicPoleLoewnerSymbol 13 t)) hRight0).2 hAbs
    simpa only [sq_abs] using h
  have hDen : 16 * (N : ℝ) ^ 2 ≤ 16 * t ^ 2 := by
    nlinarith [sq_nonneg (t - (N : ℝ))]
  have hInv : 1 / (16 * t ^ 2) ≤ 1 / (16 * (N : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hDen
  change logarithmicPoleLoewnerSymbol 13 t ^ 2 / t ^ 2 ≤ _
  calc
    logarithmicPoleLoewnerSymbol 13 t ^ 2 / t ^ 2 =
        logarithmicPoleLoewnerSymbol 13 t ^ 2 * (t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (1 / (4 * t)) ^ 2 * (t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hSq (by positivity)
    _ = (1 / (16 * t ^ 2)) * (t ^ 2)⁻¹ := by ring
    _ ≤ (1 / (16 * (N : ℝ) ^ 2)) * (t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hInv (by positivity)

theorem c13_logarithmicPoleLoewnerSymbol_dyadic_weighted_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j ∈ Finset.range N,
        logarithmicPoleLoewnerSymbol 13 (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      1 / (32 * (N : ℝ) ^ 3) := by
  have hTerm :
      (∑ j ∈ Finset.range N,
          logarithmicPoleLoewnerSymbol 13 (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          (1 / (16 * (N : ℝ) ^ 2)) *
            ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact c13_logarithmicPoleLoewnerSymbol_shifted_weight_term_le N j hN
  calc
    (∑ j ∈ Finset.range N,
        logarithmicPoleLoewnerSymbol 13 (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          (1 / (16 * (N : ℝ) ^ 2)) *
            ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := hTerm
    _ = (1 / (16 * (N : ℝ) ^ 2)) *
        ∑ j ∈ Finset.range N,
          ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (16 * (N : ℝ) ^ 2)) * (1 / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (dyadic_shifted_weight_sum_le N hN)
        (by positivity)
    _ = 1 / (32 * (N : ℝ) ^ 3) := by ring

/-!
## Sharper Fourier-normalized route

The Arb certificate controls the unnormalized combined symbol by `97/100`.
The actual historical Loewner symbol carries a factor `1/pi`, so the square
budget improves by almost a factor ten before the pole is added.
-/

lemma one_div_pi_sq_le_twoThousandFiveHundred_div_twentyFourThousandSixHundredFortyNine :
    (1 / Real.pi : ℝ) ^ 2 ≤ 2500 / 24649 := by
  have hPiSq : (24649 / 2500 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2]
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 24649 / 2500)
    hPiSq
  calc
    (1 / Real.pi : ℝ) ^ 2 = 1 / Real.pi ^ 2 := by ring
    _ ≤ 1 / (24649 / 2500 : ℝ) := hInv
    _ = 2500 / 24649 := by norm_num

lemma fourierNormalizedSymbol_weighted_sq_le
    (symbol : ℝ → ℝ) (n : ℕ) :
    fourierNormalizedSymbol symbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      (2500 / 24649 : ℝ) *
        (symbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hTerm : 0 ≤ symbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by positivity
  unfold fourierNormalizedSymbol
  calc
    ((1 / Real.pi) * symbol (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 =
        (1 / Real.pi : ℝ) ^ 2 *
          (symbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
    _ ≤ (2500 / 24649 : ℝ) *
        (symbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        one_div_pi_sq_le_twoThousandFiveHundred_div_twentyFourThousandSixHundredFortyNine
        hTerm

theorem c13HistoricalCombinedLoewnerSymbol_dyadic_weighted_sum_le_normalized
    (N : ℕ)
    (hRaw :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ j ∈ Finset.range N,
        c13HistoricalCombinedLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      (2425 / 24649 : ℝ) / (N : ℝ) := by
  have hTerm :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          (2500 / 24649 : ℝ) *
            (logarithmicCombinedSymbol
                (logarithmicArchimedeanSymbol 13) 13
                c13PrimePowerLocation c13PrimePowerBase
                (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + j : ℕ) : ℝ)) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact fourierNormalizedSymbol_weighted_sq_le
      (logarithmicCombinedSymbol
        (logarithmicArchimedeanSymbol 13) 13
        c13PrimePowerLocation c13PrimePowerBase)
      (N + 1 + j)
  calc
    (∑ j ∈ Finset.range N,
        c13HistoricalCombinedLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          (2500 / 24649 : ℝ) *
            (logarithmicCombinedSymbol
                (logarithmicArchimedeanSymbol 13) 13
                c13PrimePowerLocation c13PrimePowerBase
                (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + j : ℕ) : ℝ)) ^ 2) := by
      simpa only [c13HistoricalCombinedLoewnerSymbol] using hTerm
    _ = (2500 / 24649 : ℝ) *
        (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (2500 / 24649 : ℝ) * ((97 / 100 : ℝ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hRaw (by norm_num)
    _ = (2425 / 24649 : ℝ) / (N : ℝ) := by ring

lemma sub_sq_le_threeThousandOne_split (a b : ℝ) :
    (a - b) ^ 2 ≤
      (3001 / 3000 : ℝ) * a ^ 2 + 3001 * b ^ 2 := by
  nlinarith [sq_nonneg (a + 3000 * b)]

lemma c13HistoricalBuilderLoewnerSymbol_weighted_term_le_sharp
    (n : ℕ) :
    c13HistoricalBuilderLoewnerSymbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      (3001 / 3000 : ℝ) *
          (c13HistoricalCombinedLoewnerSymbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2) +
        3001 *
          (logarithmicPoleLoewnerSymbol 13 (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hYoung := sub_sq_le_threeThousandOne_split
    (c13HistoricalCombinedLoewnerSymbol (n : ℝ))
    (logarithmicPoleLoewnerSymbol 13 (n : ℝ))
  unfold c13HistoricalBuilderLoewnerSymbol
  have hSq :
      (logarithmicPoleLoewnerSymbol 13 (n : ℝ) -
          c13HistoricalCombinedLoewnerSymbol (n : ℝ)) ^ 2 ≤
        (3001 / 3000 : ℝ) *
            c13HistoricalCombinedLoewnerSymbol (n : ℝ) ^ 2 +
          3001 * logarithmicPoleLoewnerSymbol 13 (n : ℝ) ^ 2 := by
    nlinarith
  calc
    (logarithmicPoleLoewnerSymbol 13 (n : ℝ) -
        c13HistoricalCombinedLoewnerSymbol (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 ≤
        ((3001 / 3000 : ℝ) *
            c13HistoricalCombinedLoewnerSymbol (n : ℝ) ^ 2 +
          3001 * logarithmicPoleLoewnerSymbol 13 (n : ℝ) ^ 2) /
            (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hSq (sq_nonneg (n : ℝ))
    _ = (3001 / 3000 : ℝ) *
          (c13HistoricalCombinedLoewnerSymbol (n : ℝ) ^ 2 / (n : ℝ) ^ 2) +
        3001 *
          (logarithmicPoleLoewnerSymbol 13 (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      ring

theorem c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharp
    (N : ℕ) (hN : N ≠ 0)
    (hCombined :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (2425 / 24649 : ℝ) / (N : ℝ)) :
    (∑ j ∈ Finset.range N,
        c13HistoricalBuilderLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      (3001 / 3000 : ℝ) * ((2425 / 24649 : ℝ) / (N : ℝ)) +
        3001 * (1 / (32 * (N : ℝ) ^ 3)) := by
  have hTerm :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          ((3001 / 3000 : ℝ) *
              (c13HistoricalCombinedLoewnerSymbol
                  (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + j : ℕ) : ℝ)) ^ 2) +
            3001 *
              (logarithmicPoleLoewnerSymbol 13
                  (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + j : ℕ) : ℝ)) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact c13HistoricalBuilderLoewnerSymbol_weighted_term_le_sharp
      (N + 1 + j)
  calc
    (∑ j ∈ Finset.range N,
        c13HistoricalBuilderLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N,
          ((3001 / 3000 : ℝ) *
              (c13HistoricalCombinedLoewnerSymbol
                  (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + j : ℕ) : ℝ)) ^ 2) +
            3001 *
              (logarithmicPoleLoewnerSymbol 13
                  (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + j : ℕ) : ℝ)) ^ 2)) := hTerm
    _ = (3001 / 3000 : ℝ) *
          (∑ j ∈ Finset.range N,
            c13HistoricalCombinedLoewnerSymbol
                (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + j : ℕ) : ℝ)) ^ 2) +
        3001 *
          (∑ j ∈ Finset.range N,
            logarithmicPoleLoewnerSymbol 13
                (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + j : ℕ) : ℝ)) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (3001 / 3000 : ℝ) * ((2425 / 24649 : ℝ) / (N : ℝ)) +
        3001 * (1 / (32 * (N : ℝ) ^ 3)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hCombined (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (c13_logarithmicPoleLoewnerSymbol_dyadic_weighted_sum_le N hN)
          (by norm_num)

lemma c13_fullBuilder_sharp_composed_constant_lt
    (N : ℕ) (hN : 1920 ≤ N) :
    (3001 / 3000 : ℝ) * ((2425 / 24649 : ℝ) / (N : ℝ)) +
        3001 * (1 / (32 * (N : ℝ) ^ 3)) <
      (197 / 2000 : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNLower : (1920 : ℝ) ≤ N := by exact_mod_cast hN
  apply (lt_div_iff₀ hNR).2
  field_simp [ne_of_gt hNR]
  nlinarith [sq_nonneg ((N : ℝ) - 1920)]

/-- The raw cutoff-13 combined-symbol certificate implies a full-builder
Loewner budget of `197/2000`.  This is the constant consumed by the exact
historical-shell transport and is more than ten times sharper than the
temporary unit budget. -/
theorem c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_lt_sharp
    (N : ℕ) (hN : 1920 ≤ N)
    (hRaw :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ j ∈ Finset.range N,
        c13HistoricalBuilderLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) <
      (197 / 2000 : ℝ) / (N : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have hCombined :=
    c13HistoricalCombinedLoewnerSymbol_dyadic_weighted_sum_le_normalized
      N hRaw
  exact (c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharp
    N hN0 hCombined).trans_lt
      (c13_fullBuilder_sharp_composed_constant_lt N hN)

theorem c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
    (N : ℕ) (hN : 1920 ≤ N)
    (hRaw :
      (∑ j ∈ Finset.range N,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ j ∈ Finset.range N,
        c13HistoricalBuilderLoewnerSymbol
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
      (197 / 2000 : ℝ) / (N : ℝ) :=
  (c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_lt_sharp
    N hN hRaw).le

theorem c13HistoricalRemoteEvenBuilder_dyadicTransport_of_rawCombined
    (B N k : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (q : ℝ)
    (hRawTarget :
      (∑ j ∈ Finset.range (N * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((N * 2 ^ k : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N (197 / 2000 : ℝ) ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (N * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B (N * 2 ^ k)) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y := by
  have hTarget : 1920 ≤ N * 2 ^ k := by
    have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hNTarget : N ≤ N * 2 ^ k := by
      simpa using Nat.mul_le_mul_left N hPow
    omega
  have hSymbolTarget :=
    c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
      (N * 2 ^ k) hTarget hRawTarget
  exact c13HistoricalRemoteEvenBuilder_dyadicTransport_fullLoewner
    B N k hB hBN (197 / 2000 : ℝ) q hSymbolTarget hq
    hPreviousBudget x y

theorem c13HistoricalRemoteOddBuilder_dyadicTransport_of_rawCombined
    (B N k : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (q : ℝ)
    (hRawTarget :
      (∑ j ∈ Finset.range (N * 2 ^ k),
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / ((N * 2 ^ k : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N (197 / 2000 : ℝ) ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (N * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B (N * 2 ^ k)) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y := by
  have hTarget : 1920 ≤ N * 2 ^ k := by
    have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hNTarget : N ≤ N * 2 ^ k := by
      simpa using Nat.mul_le_mul_left N hPow
    omega
  have hSymbolTarget :=
    c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
      (N * 2 ^ k) hTarget hRawTarget
  exact c13HistoricalRemoteOddBuilder_dyadicTransport_fullLoewner
    B N k hB hBN (197 / 2000 : ℝ) q hSymbolTarget hq
    hPreviousBudget x y

/-- A finite family of actual even historical builder blocks consumes the
sharp `197/2000` symbol budget as soon as the raw combined-symbol certificate
is available at the common target. -/
theorem c13HistoricalRemoteEvenBuilder_dyadicFamily_of_rawCombined
    (B baseTarget : ℕ → ℕ) (n T : ℕ)
    (q : ℕ → ℝ) (leading rho : ℝ)
    (hT : 1920 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = baseTarget i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
    (hSeparated : ∀ i ∈ Finset.range n, 4 * B i ≤ baseTarget i)
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (hq : ∀ i ∈ Finset.range n, 0 ≤ q i)
    (hqLeading : ∀ i ∈ Finset.range n, q i ≤ leading)
    (hPreviousBudget : ∀ i ∈ Finset.range n,
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin (B i)))
          (fun j => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode (B i) j : ℝ))
          (baseTarget i) (197 / 2000 : ℝ) ≤
        q i * c13ShellDynamicGap (B i) *
          c13ShellDynamicGap (baseTarget i))
    (hLeading : 0 ≤ leading) (hTotalBudget : 2 * leading ≤ rho)
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteEvenBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      rho *
        (∑ i ∈ Finset.range n,
          c13EvenBuilderShellEnergy (B i) (B i) (x i)) *
        c13EvenBuilderShellEnergy T T y := by
  have hSymbolTarget :=
    c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
      T hT hRawTarget
  exact c13HistoricalRemoteEvenBuilder_dyadicFamily_fullLoewner
    B baseTarget n T (197 / 2000 : ℝ) q leading rho
    (by omega) hTarget hB hSeparated hSymbolTarget hq hqLeading
    hPreviousBudget hLeading hTotalBudget x y

/-- Odd-parity finite-family companion of the sharp raw-symbol adapter. -/
theorem c13HistoricalRemoteOddBuilder_dyadicFamily_of_rawCombined
    (B baseTarget : ℕ → ℕ) (n T : ℕ)
    (q : ℕ → ℝ) (leading rho : ℝ)
    (hT : 1920 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = baseTarget i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
    (hSeparated : ∀ i ∈ Finset.range n, 4 * B i ≤ baseTarget i)
    (hRawTarget :
      (∑ j ∈ Finset.range T,
          logarithmicCombinedSymbol
              (logarithmicArchimedeanSymbol 13) 13
              c13PrimePowerLocation c13PrimePowerBase
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (T : ℝ))
    (hq : ∀ i ∈ Finset.range n, 0 ≤ q i)
    (hqLeading : ∀ i ∈ Finset.range n, q i ≤ leading)
    (hPreviousBudget : ∀ i ∈ Finset.range n,
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin (B i)))
          (fun j => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode (B i) j : ℝ))
          (baseTarget i) (197 / 2000 : ℝ) ≤
        q i * c13ShellDynamicGap (B i) *
          c13ShellDynamicGap (baseTarget i))
    (hLeading : 0 ≤ leading) (hTotalBudget : 2 * leading ≤ rho)
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteOddBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      rho *
        (∑ i ∈ Finset.range n,
          c13OddBuilderShellEnergy (B i) (B i) (x i)) *
        c13OddBuilderShellEnergy T T y := by
  have hSymbolTarget :=
    c13HistoricalBuilderLoewnerSymbol_dyadic_weighted_sum_le_sharpTarget
      T hT hRawTarget
  exact c13HistoricalRemoteOddBuilder_dyadicFamily_fullLoewner
    B baseTarget n T (197 / 2000 : ℝ) q leading rho
    (by omega) hTarget hB hSeparated hSymbolTarget hq hqLeading
    hPreviousBudget hLeading hTotalBudget x y

end RiemannCvs.V23BoundaryWeylMainline
