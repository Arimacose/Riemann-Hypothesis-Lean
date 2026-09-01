import RiemannCvs.PrimeTranslationFourierBridge
import RiemannCvs.PrimeTranslationSupersolution
import RiemannCvs.V23BoundaryWeylMainline

/-!
# Distance-sensitive prime-translation bounds

The global cutoff-13 translation estimate `10 / 3` is sharp enough for two
adjacent analytic bands, but it discards the Fourier separation between the
already certified finite prefix and a remote shell.  The exact off-diagonal
formula contains a Cauchy kernel `1 / (n-m)`.  This file keeps that decay.

The first layer is source-independent: one truncated translation coefficient
is at most `2 / (pi * |n-m|)`.  The second layer inserts the eight cutoff-13
von-Mangoldt weights and replaces their sum by the exact rational envelope
`2133 / 500`.  Later lemmas will aggregate the resulting entry bounds over the
fixed prefix `[1,3840]` and a remote positive-frequency shell.
-/

noncomputable section

open scoped BigOperators Real

namespace RiemannCvs.PrimeTranslationSeparatedBands

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.PrimeTranslationFourierBridge
open RiemannCvs.PrimeTranslationSupersolution
open RiemannCvs.V23BoundaryWeylMainline

/-- The exact Fourier coefficient of one truncated translation retains inverse
distance off the diagonal. -/
theorem abs_truncatedTranslationFourierEntry_le_two_div
    (L y : ℝ) (n m : ℤ) (hL : L ≠ 0) (hnm : n ≠ m) :
    |truncatedTranslationFourierEntry L y n m| ≤
      2 / (Real.pi * |(n : ℝ) - (m : ℝ)|) := by
  rw [truncatedTranslationFourierEntry_offDiagonal L y n m hL hnm,
    abs_div, abs_mul, abs_of_pos Real.pi_pos]
  have hnmR : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
  have hDiff : 0 < |(n : ℝ) - (m : ℝ)| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hnmR)
  have hDen : 0 < Real.pi * |(n : ℝ) - (m : ℝ)| :=
    mul_pos Real.pi_pos hDiff
  apply (div_le_div_iff_of_pos_right hDen).2
  calc
    |Real.sin (2 * Real.pi * (m : ℝ) * y / L) -
        Real.sin (2 * Real.pi * (n : ℝ) * y / L)| ≤
        |Real.sin (2 * Real.pi * (m : ℝ) * y / L)| +
          |Real.sin (2 * Real.pi * (n : ℝ) * y / L)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

/-- The eight true cutoff-13 von-Mangoldt weights have total mass strictly
below the sum of their certified rational envelopes. -/
theorem c13_logarithmicPrimeWeight_sum_lt_2133Over500 :
    (∑ i : Fin 8,
      logarithmicPrimeWeight (c13PrimePowerLocation i) (c13PrimePowerBase i)) <
        (2133 / 500 : ℝ) := by
  have hPoint : ∀ i : Fin 8,
      logarithmicPrimeWeight (c13PrimePowerLocation i) (c13PrimePowerBase i) <
        c13PrimeTranslationWeightUpper i := by
    intro i
    simpa [logarithmicPrimeWeight, c13PrimeTranslationWeight] using
      c13PrimeTranslationWeight_lt_upper i
  calc
    (∑ i : Fin 8,
        logarithmicPrimeWeight (c13PrimePowerLocation i) (c13PrimePowerBase i)) <
        ∑ i : Fin 8, c13PrimeTranslationWeightUpper i := by
          exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun i _hi => hPoint i)
    _ = (2133 / 500 : ℝ) := by
      norm_num [c13PrimeTranslationWeightUpper, Fin.sum_univ_succ]

/-- After summing all eight cutoff-13 events, every off-diagonal integer
Fourier entry is bounded by the simple rational Cauchy kernel `3/|n-m|`.
The constant `3` deliberately leaves a visible strict reserve over the exact
rational weight envelope. -/
theorem c13_finitePrimeTranslationFourierEntry_abs_le_three_div
    (n m : ℤ) (hnm : n ≠ m) :
    |finitePrimeTranslationFourierEntry
        13 c13PrimePowerLocation c13PrimePowerBase n m| ≤
      3 / |(n : ℝ) - (m : ℝ)| := by
  have hLog13 : Real.log (13 : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hnmR : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
  have hDist : 0 < |(n : ℝ) - (m : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr hnmR)
  have hWeightNonneg : ∀ i : Fin 8,
      0 ≤ logarithmicPrimeWeight
        (c13PrimePowerLocation i) (c13PrimePowerBase i) := by
    intro i
    fin_cases i <;>
      simp [logarithmicPrimeWeight, c13PrimePowerLocation,
        c13PrimePowerBase] <;> positivity
  unfold finitePrimeTranslationFourierEntry
  calc
    |∑ i : Fin 8,
        logarithmicPrimeWeight (c13PrimePowerLocation i) (c13PrimePowerBase i) *
          truncatedTranslationFourierEntry
            (Real.log 13) (Real.log (c13PrimePowerLocation i)) n m| ≤
        ∑ i : Fin 8,
          |logarithmicPrimeWeight
              (c13PrimePowerLocation i) (c13PrimePowerBase i) *
            truncatedTranslationFourierEntry
              (Real.log 13) (Real.log (c13PrimePowerLocation i)) n m| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 8,
          logarithmicPrimeWeight
              (c13PrimePowerLocation i) (c13PrimePowerBase i) *
            |truncatedTranslationFourierEntry
              (Real.log 13) (Real.log (c13PrimePowerLocation i)) n m| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul, abs_of_nonneg (hWeightNonneg i)]
    _ ≤ ∑ i : Fin 8,
          logarithmicPrimeWeight
              (c13PrimePowerLocation i) (c13PrimePowerBase i) *
            (2 / (Real.pi * |(n : ℝ) - (m : ℝ)|)) := by
          apply Finset.sum_le_sum
          intro i _hi
          exact mul_le_mul_of_nonneg_left
            (abs_truncatedTranslationFourierEntry_le_two_div
              (Real.log 13) (Real.log (c13PrimePowerLocation i))
              n m hLog13 hnm)
            (hWeightNonneg i)
    _ = (∑ i : Fin 8,
          logarithmicPrimeWeight
            (c13PrimePowerLocation i) (c13PrimePowerBase i)) *
          (2 / (Real.pi * |(n : ℝ) - (m : ℝ)|)) := by
          exact (Finset.sum_mul _ _ _).symm
    _ ≤ (2133 / 500 : ℝ) *
          (2 / (Real.pi * |(n : ℝ) - (m : ℝ)|)) := by
          exact mul_le_mul_of_nonneg_right
            (le_of_lt c13_logarithmicPrimeWeight_sum_lt_2133Over500)
            (by positivity)
    _ ≤ 3 / |(n : ℝ) - (m : ℝ)| := by
          have hPi : (3 : ℝ) < Real.pi := Real.pi_gt_three
          rw [show
            (2133 / 500 : ℝ) *
                (2 / (Real.pi * |(n : ℝ) - (m : ℝ)|)) =
              ((2133 / 500 : ℝ) * 2) /
                (Real.pi * |(n : ℝ) - (m : ℝ)|) by ring]
          rw [div_le_div_iff₀ (mul_pos Real.pi_pos hDist) hDist]
          nlinarith

/-- Entrywise even-parity consequence of the scalar Cauchy-kernel bound. -/
theorem c13_finitePrimeTranslationEvenModeMatrix_entry_abs_le
    {κ : Type*} [Fintype κ] (mode : κ → ℤ) (i j : κ)
    (hDiff : mode i ≠ mode j) (hSum : mode i ≠ -mode j) :
    |finitePrimeTranslationEvenModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode i j| ≤
      3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) + (mode j : ℝ)| := by
  rw [finitePrimeTranslationEvenModeMatrix]
  calc
    |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (mode j) +
        finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (-mode j)| ≤
        |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (mode j)| +
        |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (-mode j)| :=
      abs_add_le _ _
    _ ≤ 3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) - ((-mode j : ℤ) : ℝ)| :=
      add_le_add
        (c13_finitePrimeTranslationFourierEntry_abs_le_three_div
          (mode i) (mode j) hDiff)
        (c13_finitePrimeTranslationFourierEntry_abs_le_three_div
          (mode i) (-mode j) hSum)
    _ = 3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) + (mode j : ℝ)| := by
      rw [Int.cast_neg, sub_neg_eq_add]

/-- The odd compression has the identical separated-entry estimate. -/
theorem c13_finitePrimeTranslationOddModeMatrix_entry_abs_le
    {κ : Type*} [Fintype κ] (mode : κ → ℤ) (i j : κ)
    (hDiff : mode i ≠ mode j) (hSum : mode i ≠ -mode j) :
    |finitePrimeTranslationOddModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode i j| ≤
      3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) + (mode j : ℝ)| := by
  rw [finitePrimeTranslationOddModeMatrix]
  calc
    |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (mode j) -
        finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (-mode j)| ≤
        |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (mode j)| +
        |finitePrimeTranslationFourierEntry
          13 c13PrimePowerLocation c13PrimePowerBase (mode i) (-mode j)| :=
      abs_sub _ _
    _ ≤ 3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) - ((-mode j : ℤ) : ℝ)| :=
      add_le_add
        (c13_finitePrimeTranslationFourierEntry_abs_le_three_div
          (mode i) (mode j) hDiff)
        (c13_finitePrimeTranslationFourierEntry_abs_le_three_div
          (mode i) (-mode j) hSum)
    _ = 3 / |(mode i : ℝ) - (mode j : ℝ)| +
        3 / |(mode i : ℝ) + (mode j : ℝ)| := by
      rw [Int.cast_neg, sub_neg_eq_add]

/-- Positive-frequency map formed by a fixed prefix `[1,F]` followed by the
remote shell `(N,2N]`. -/
def fixedRemotePositiveMode (F N : ℕ) : Fin F ⊕ Fin N → ℤ :=
  Sum.elim
    (fun i => Int.ofNat ((i : ℕ) + 1))
    (fun j => Int.ofNat (N + (j : ℕ) + 1))

lemma fixedRemotePositiveMode_inl_pos
    (F N : ℕ) (i : Fin F) :
    0 < fixedRemotePositiveMode F N (Sum.inl i) := by
  change (0 : ℤ) < Int.ofNat ((i : ℕ) + 1)
  rw [Int.ofNat_eq_natCast, Int.natCast_pos]
  omega

lemma fixedRemotePositiveMode_inr_pos
    (F N : ℕ) (j : Fin N) :
    0 < fixedRemotePositiveMode F N (Sum.inr j) := by
  change (0 : ℤ) < Int.ofNat (N + (j : ℕ) + 1)
  rw [Int.ofNat_eq_natCast, Int.natCast_pos]
  omega

lemma fixedRemotePositiveMode_inl_lt_inr
    (F N : ℕ) (hFN : F ≤ N) (i : Fin F) (j : Fin N) :
    fixedRemotePositiveMode F N (Sum.inl i) <
      fixedRemotePositiveMode F N (Sum.inr j) := by
  change Int.ofNat ((i : ℕ) + 1) < Int.ofNat (N + (j : ℕ) + 1)
  have hi : (i : ℕ) < F := i.isLt
  have hNat : (i : ℕ) + 1 < N + (j : ℕ) + 1 := by omega
  simpa only [Int.ofNat_eq_natCast] using (Int.ofNat_lt.mpr hNat)

lemma fixedRemotePositiveMode_inl_ne_neg_inr
    (F N : ℕ) (i : Fin F) (j : Fin N) :
    fixedRemotePositiveMode F N (Sum.inl i) ≠
      -fixedRemotePositiveMode F N (Sum.inr j) := by
  have hLeft := fixedRemotePositiveMode_inl_pos F N i
  have hRight := fixedRemotePositiveMode_inr_pos F N j
  omega

/-- Every even-parity entry from `[1,F]` to `(N,2N]` is bounded by the
uniform separation kernel `6/(N+1-F)`. -/
theorem c13_fixedRemoteEvenPrimeEntry_abs_le_six_div_gap
    (F N : ℕ) (hFN : F ≤ N) (i : Fin F) (j : Fin N) :
    |finitePrimeTranslationEvenModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
      6 / ((N : ℝ) + 1 - (F : ℝ)) := by
  let a := fixedRemotePositiveMode F N (Sum.inl i)
  let b := fixedRemotePositiveMode F N (Sum.inr j)
  have habZ : a < b := fixedRemotePositiveMode_inl_lt_inr F N hFN i j
  have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast habZ
  have haZ : 0 < a := fixedRemotePositiveMode_inl_pos F N i
  have hbZ : 0 < b := fixedRemotePositiveMode_inr_pos F N j
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast haZ
  have hb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbZ
  have hDiff : a ≠ b := ne_of_lt habZ
  have hSum : a ≠ -b := fixedRemotePositiveMode_inl_ne_neg_inr F N i j
  have hiFNat : (i : ℕ) + 1 ≤ F := by omega
  have hiF : ((i : ℕ) : ℝ) + 1 ≤ (F : ℝ) := by exact_mod_cast hiFNat
  have hjNonneg : (0 : ℝ) ≤ (j : ℕ) := by positivity
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have haEq : (a : ℝ) = ((i : ℕ) : ℝ) + 1 := by
    simp [a, fixedRemotePositiveMode]
  have hbEq : (b : ℝ) = (N : ℝ) + (j : ℕ) + 1 := by
    simp [b, fixedRemotePositiveMode]
  have hGapPos : 0 < (N : ℝ) + 1 - (F : ℝ) := by linarith
  have hGapDiff :
      (N : ℝ) + 1 - (F : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    rw [haEq, hbEq]
    linarith
  have hGapSum :
      (N : ℝ) + 1 - (F : ℝ) ≤ (a : ℝ) + (b : ℝ) := by
    rw [haEq, hbEq]
    linarith
  have hEntry := c13_finitePrimeTranslationEvenModeMatrix_entry_abs_le
    (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j) hDiff hSum
  rw [show |(a : ℝ) - (b : ℝ)| = (b : ℝ) - (a : ℝ) by
      rw [abs_of_neg (sub_neg.mpr hab)]; ring,
    abs_of_pos (add_pos ha hb)] at hEntry
  calc
    |finitePrimeTranslationEvenModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
        3 / ((b : ℝ) - (a : ℝ)) + 3 / ((a : ℝ) + (b : ℝ)) := hEntry
    _ ≤ 3 / ((N : ℝ) + 1 - (F : ℝ)) +
          3 / ((N : ℝ) + 1 - (F : ℝ)) := by
      exact add_le_add
        (div_le_div_of_nonneg_left (by norm_num) hGapPos hGapDiff)
        (div_le_div_of_nonneg_left (by norm_num) hGapPos hGapSum)
    _ = 6 / ((N : ℝ) + 1 - (F : ℝ)) := by ring

/-- Odd-parity companion of the fixed-prefix/remote-shell entry bound. -/
theorem c13_fixedRemoteOddPrimeEntry_abs_le_six_div_gap
    (F N : ℕ) (hFN : F ≤ N) (i : Fin F) (j : Fin N) :
    |finitePrimeTranslationOddModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
      6 / ((N : ℝ) + 1 - (F : ℝ)) := by
  let a := fixedRemotePositiveMode F N (Sum.inl i)
  let b := fixedRemotePositiveMode F N (Sum.inr j)
  have habZ : a < b := fixedRemotePositiveMode_inl_lt_inr F N hFN i j
  have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast habZ
  have haZ : 0 < a := fixedRemotePositiveMode_inl_pos F N i
  have hbZ : 0 < b := fixedRemotePositiveMode_inr_pos F N j
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast haZ
  have hb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbZ
  have hDiff : a ≠ b := ne_of_lt habZ
  have hSum : a ≠ -b := fixedRemotePositiveMode_inl_ne_neg_inr F N i j
  have hiFNat : (i : ℕ) + 1 ≤ F := by omega
  have hiF : ((i : ℕ) : ℝ) + 1 ≤ (F : ℝ) := by exact_mod_cast hiFNat
  have hjNonneg : (0 : ℝ) ≤ (j : ℕ) := by positivity
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have haEq : (a : ℝ) = ((i : ℕ) : ℝ) + 1 := by
    simp [a, fixedRemotePositiveMode]
  have hbEq : (b : ℝ) = (N : ℝ) + (j : ℕ) + 1 := by
    simp [b, fixedRemotePositiveMode]
  have hGapPos : 0 < (N : ℝ) + 1 - (F : ℝ) := by linarith
  have hGapDiff :
      (N : ℝ) + 1 - (F : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    rw [haEq, hbEq]
    linarith
  have hGapSum :
      (N : ℝ) + 1 - (F : ℝ) ≤ (a : ℝ) + (b : ℝ) := by
    rw [haEq, hbEq]
    linarith
  have hEntry := c13_finitePrimeTranslationOddModeMatrix_entry_abs_le
    (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j) hDiff hSum
  rw [show |(a : ℝ) - (b : ℝ)| = (b : ℝ) - (a : ℝ) by
      rw [abs_of_neg (sub_neg.mpr hab)]; ring,
    abs_of_pos (add_pos ha hb)] at hEntry
  calc
    |finitePrimeTranslationOddModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
        3 / ((b : ℝ) - (a : ℝ)) + 3 / ((a : ℝ) + (b : ℝ)) := hEntry
    _ ≤ 3 / ((N : ℝ) + 1 - (F : ℝ)) +
          3 / ((N : ℝ) + 1 - (F : ℝ)) := by
      exact add_le_add
        (div_le_div_of_nonneg_left (by norm_num) hGapPos hGapDiff)
        (div_le_div_of_nonneg_left (by norm_num) hGapPos hGapSum)
    _ = 6 / ((N : ℝ) + 1 - (F : ℝ)) := by ring

/-- Rectangular Cauchy--Schwarz with a uniform entry bound, retaining both
cardinalities instead of replacing the rectangle by a square. -/
theorem rectangular_bilinear_sq_le_card_product_of_entry_abs_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (entry : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hEntry : ∀ i j, |entry i j| ≤ B) :
    (∑ ij ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset κ),
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * B ^ 2) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hEntrySq : ∀ i ∈ (Finset.univ : Finset ι),
      ∀ j ∈ (Finset.univ : Finset κ), (entry i j) ^ 2 ≤ B ^ 2 := by
    intro i _hi j _hj
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using hEntry i j
  have h := rectangular_bilinear_sq_le_card_mul_columnBudget_mul_norms
    (Finset.univ : Finset ι) (Finset.univ : Finset κ)
    entry (fun _ : κ => B ^ 2) x y hEntrySq
  simpa [mul_assoc] using h

/-- Even fixed-prefix/remote-shell bilinear form with an explicit coefficient
that decays like `F/N`. -/
theorem c13_fixedRemoteEvenPrimeBilinear_sq_le
    (F N : ℕ) (hFN : F ≤ N) (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin F)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        finitePrimeTranslationEvenModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (fixedRemotePositiveMode F N) (Sum.inl ij.1) (Sum.inr ij.2) *
          (x ij.1 * y ij.2)) ^ 2 ≤
      ((F : ℝ) * (N : ℝ) *
          (6 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have h := rectangular_bilinear_sq_le_card_product_of_entry_abs_le
    (fun i j => finitePrimeTranslationEvenModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j))
    x y (6 / ((N : ℝ) + 1 - (F : ℝ))) (by
      have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
      have hGap : 0 < (N : ℝ) + 1 - (F : ℝ) := by linarith
      exact div_nonneg (by norm_num) hGap.le) (fun i j =>
        c13_fixedRemoteEvenPrimeEntry_abs_le_six_div_gap F N hFN i j)
  simpa using h

/-- Odd fixed-prefix/remote-shell bilinear companion. -/
theorem c13_fixedRemoteOddPrimeBilinear_sq_le
    (F N : ℕ) (hFN : F ≤ N) (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin F)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        finitePrimeTranslationOddModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (fixedRemotePositiveMode F N) (Sum.inl ij.1) (Sum.inr ij.2) *
          (x ij.1 * y ij.2)) ^ 2 ≤
      ((F : ℝ) * (N : ℝ) *
          (6 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have h := rectangular_bilinear_sq_le_card_product_of_entry_abs_le
    (fun i j => finitePrimeTranslationOddModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j))
    x y (6 / ((N : ℝ) + 1 - (F : ℝ))) (by
      have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
      have hGap : 0 < (N : ℝ) + 1 - (F : ℝ) := by linarith
      exact div_nonneg (by norm_num) hGap.le) (fun i j =>
        c13_fixedRemoteOddPrimeEntry_abs_le_six_div_gap F N hFN i j)
  simpa using h

/-- Squared Euclidean coefficient produced by the fixed-prefix Frobenius
estimate. -/
noncomputable def c13FixedRemotePrimeCoefficient (F N : ℕ) : ℝ :=
  (F : ℝ) * (N : ℝ) *
    (6 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2

/-- Doubling the remote shell divides the fixed-prefix prime coefficient by at
least two.  This exact transport is the separated-band analogue of the dyadic
half-transport used by the analytic shell tower. -/
theorem c13FixedRemotePrimeCoefficient_two_mul_le_half
    (F N : ℕ) (hF : 1 ≤ F) (hFN : F ≤ N) :
    c13FixedRemotePrimeCoefficient F (2 * N) ≤
      (1 / 2 : ℝ) * c13FixedRemotePrimeCoefficient F N := by
  let f : ℝ := F
  let t : ℝ := N
  let d : ℝ := t + 1 - f
  let e : ℝ := 2 * t + 1 - f
  have hf : (1 : ℝ) ≤ f := by
    dsimp [f]
    exact_mod_cast hF
  have hft : f ≤ t := by
    dsimp [f, t]
    exact_mod_cast hFN
  have hfPos : 0 < f := by linarith
  have ht : 0 < t := hfPos.trans_le hft
  have hd : 0 < d := by dsimp [d]; linarith
  have he : 0 < e := by dsimp [e]; linarith
  have hTwoD : 2 * d ≤ e := by
    dsimp [d, e]
    linarith
  have hSq : (2 * d) ^ 2 ≤ e ^ 2 :=
    (sq_le_sq₀ (by positivity) he.le).2 hTwoD
  have hFrac : 4 / e ^ 2 ≤ 1 / d ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hd)]
    nlinarith
  have hScale : 0 ≤ 18 * f * t := by positivity
  unfold c13FixedRemotePrimeCoefficient
  push_cast
  change f * (2 * t) * (6 / e) ^ 2 ≤
    (1 / 2 : ℝ) * (f * t * (6 / d) ^ 2)
  calc
    f * (2 * t) * (6 / e) ^ 2 = (18 * f * t) * (4 / e ^ 2) := by
      field_simp [ne_of_gt he]
      all_goals ring
    _ ≤ (18 * f * t) * (1 / d ^ 2) :=
      mul_le_mul_of_nonneg_left hFrac hScale
    _ = (1 / 2 : ℝ) * (f * t * (6 / d) ^ 2) := by
      field_simp [ne_of_gt hd]
      all_goals ring

/-- Iterating the preceding transport yields a literal geometric envelope for
every fixed finite prefix. -/
theorem c13FixedRemotePrimeCoefficient_dyadic_le
    (F N k : ℕ) (hF : 1 ≤ F) (hFN : F ≤ N) :
    c13FixedRemotePrimeCoefficient F (N * 2 ^ k) ≤
      (1 / 2 : ℝ) ^ k * c13FixedRemotePrimeCoefficient F N := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hNle : N ≤ N * 2 ^ k :=
        Nat.le_mul_of_pos_right N (Nat.pow_pos (by omega))
      have hStep := c13FixedRemotePrimeCoefficient_two_mul_le_half
        F (N * 2 ^ k) hF (hFN.trans hNle)
      have hIndex : N * 2 ^ (k + 1) = 2 * (N * 2 ^ k) := by
        rw [pow_succ]
        ring
      calc
        c13FixedRemotePrimeCoefficient F (N * 2 ^ (k + 1)) =
            c13FixedRemotePrimeCoefficient F (2 * (N * 2 ^ k)) := by rw [hIndex]
        _ ≤ (1 / 2 : ℝ) *
              c13FixedRemotePrimeCoefficient F (N * 2 ^ k) := hStep
        _ ≤ (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ k * c13FixedRemotePrimeCoefficient F N) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) *
              c13FixedRemotePrimeCoefficient F N := by
              rw [pow_succ]
              ring

/-- At and beyond the first analytic scale `13^5 = 371293`, the squared
Euclidean operator coefficient of the prime channel from `[1,3840]` to
`(N,2N]` is already below `2/5`.  Unlike the global `10/3` estimate, this
coefficient tends to zero. -/
theorem c13_fixed3840_remote_primeCoefficient_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N) :
    (3840 : ℝ) * (N : ℝ) *
        (6 / ((N : ℝ) + 1 - (3840 : ℝ))) ^ 2 ≤
      (2 / 5 : ℝ) := by
  let t : ℝ := N
  have ht : (371293 : ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast hN
  have hd : 0 < t + 1 - 3840 := by linarith
  have hBase :
      (345600 : ℝ) * 371293 ≤ (371293 - 3839 : ℝ) ^ 2 := by
    norm_num
  have hFirst : 0 ≤ t - 371293 := by linarith
  have hSecond : 0 ≤ t + 371293 - 353278 := by linarith
  have hProduct := mul_nonneg hFirst hSecond
  have hPolynomial :
      (345600 : ℝ) * t ≤ (t - 3839) ^ 2 := by
    nlinarith
  change (3840 : ℝ) * t * (6 / (t + 1 - 3840)) ^ 2 ≤ (2 / 5 : ℝ)
  calc
    (3840 : ℝ) * t * (6 / (t + 1 - 3840)) ^ 2 =
        (138240 * t) / (t - 3839) ^ 2 := by
      field_simp [ne_of_gt (by linarith : 0 < t - 3839)]
      all_goals ring
    _ ≤ (2 / 5 : ℝ) := by
      rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < t - 3839))]
      nlinarith

/-- The first-scale rational bound and exact half-transport combine into a
summable geometric envelope along the analytic dyadic tower. -/
theorem c13_fixed3840_remote_primeCoefficient_dyadic_le
    (k : ℕ) :
    c13FixedRemotePrimeCoefficient 3840 (371293 * 2 ^ k) ≤
      (2 / 5 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hDyadic := c13FixedRemotePrimeCoefficient_dyadic_le
    3840 371293 k (by norm_num) (by norm_num)
  have hBase : c13FixedRemotePrimeCoefficient 3840 371293 ≤
      (2 / 5 : ℝ) := by
    simpa [c13FixedRemotePrimeCoefficient] using
      c13_fixed3840_remote_primeCoefficient_le_twoFifths 371293 (by norm_num)
  calc
    c13FixedRemotePrimeCoefficient 3840 (371293 * 2 ^ k) ≤
        (1 / 2 : ℝ) ^ k * c13FixedRemotePrimeCoefficient 3840 371293 := hDyadic
    _ ≤ (1 / 2 : ℝ) ^ k * (2 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hBase (by positivity)
    _ = (2 / 5 : ℝ) * (1 / 2 : ℝ) ^ k := by ring

theorem c13_fixed3840_remoteEvenPrimeBilinear_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin 3840)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        finitePrimeTranslationEvenModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (fixedRemotePositiveMode 3840 N) (Sum.inl ij.1) (Sum.inr ij.2) *
          (x ij.1 * y ij.2)) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hRaw := c13_fixedRemoteEvenPrimeBilinear_sq_le
    3840 N (by omega) x y
  have hCoeff := c13_fixed3840_remote_primeCoefficient_le_twoFifths N hN
  have hNorms : 0 ≤ (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoeff hNorms)

theorem c13_fixed3840_remoteOddPrimeBilinear_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin 3840)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        finitePrimeTranslationOddModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (fixedRemotePositiveMode 3840 N) (Sum.inl ij.1) (Sum.inr ij.2) *
          (x ij.1 * y ij.2)) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hRaw := c13_fixedRemoteOddPrimeBilinear_sq_le
    3840 N (by omega) x y
  have hCoeff := c13_fixed3840_remote_primeCoefficient_le_twoFifths N hN
  have hNorms : 0 ≤ (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoeff hNorms)

theorem c13_finitePrimeTranslationFourierEntry_symm (n m : ℤ) :
    finitePrimeTranslationFourierEntry
        13 c13PrimePowerLocation c13PrimePowerBase n m =
      finitePrimeTranslationFourierEntry
        13 c13PrimePowerLocation c13PrimePowerBase m n := by
  have hLog13 : Real.log (13 : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  unfold finitePrimeTranslationFourierEntry
  apply Finset.sum_congr rfl
  intro i _hi
  rw [truncatedTranslationFourierEntry_symm _ _ _ _ hLog13]

theorem c13_finitePrimeTranslationEvenModeMatrix_symm
    {κ : Type*} [Fintype κ] (mode : κ → ℤ) (i j : κ) :
    finitePrimeTranslationEvenModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode i j =
      finitePrimeTranslationEvenModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode j i := by
  unfold finitePrimeTranslationEvenModeMatrix
  rw [c13_finitePrimeTranslationFourierEntry_symm (mode i) (mode j),
    c13_finitePrimeTranslationFourierEntry_symm (mode i) (-mode j),
    finitePrimeTranslationFourierEntry_neg_left]

theorem c13_finitePrimeTranslationOddModeMatrix_symm
    {κ : Type*} [Fintype κ] (mode : κ → ℤ) (i j : κ) :
    finitePrimeTranslationOddModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode i j =
      finitePrimeTranslationOddModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase mode j i := by
  unfold finitePrimeTranslationOddModeMatrix
  rw [c13_finitePrimeTranslationFourierEntry_symm (mode i) (mode j),
    c13_finitePrimeTranslationFourierEntry_symm (mode i) (-mode j),
    finitePrimeTranslationFourierEntry_neg_left]

noncomputable def c13FixedRemoteEvenPrimeMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  finitePrimeTranslationEvenModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

noncomputable def c13FixedRemoteOddPrimeMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  finitePrimeTranslationOddModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

theorem c13_fixedRemoteEvenPrimeCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hFN : F ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPrimeMatrix F N) x y) ^ 2 ≤
      c13FixedRemotePrimeCoefficient F N *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteEvenPrimeMatrix F N) x y]
  · have h := c13_fixedRemoteEvenPrimeBilinear_sq_le F N hFN x y
    simpa only [c13FixedRemoteEvenPrimeMatrix, c13FixedRemotePrimeCoefficient,
      Finset.sum_product, Finset.sum_const_zero,
      mul_assoc, mul_left_comm, mul_comm] using h
  · intro i j
    exact c13_finitePrimeTranslationEvenModeMatrix_symm
      (fixedRemotePositiveMode F N) i j

theorem c13_fixedRemoteOddPrimeCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hFN : F ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPrimeMatrix F N) x y) ^ 2 ≤
      c13FixedRemotePrimeCoefficient F N *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteOddPrimeMatrix F N) x y]
  · have h := c13_fixedRemoteOddPrimeBilinear_sq_le F N hFN x y
    simpa only [c13FixedRemoteOddPrimeMatrix, c13FixedRemotePrimeCoefficient,
      Finset.sum_product, Finset.sum_const_zero,
      mul_assoc, mul_left_comm, mul_comm] using h
  · intro i j
    exact c13_finitePrimeTranslationOddModeMatrix_symm
      (fixedRemotePositiveMode F N) i j

/-- Actual averaged finite-matrix cross coordinate for the even prime channel.
The coefficient `2/5` is Euclidean and is not yet divided by the finite-prefix
and high-shell energy floors. -/
theorem c13_fixed3840_remoteEvenPrimeCrossEnergy_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPrimeMatrix 3840 N) x y) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteEvenPrimeMatrix 3840 N) x y]
  · have h := c13_fixed3840_remoteEvenPrimeBilinear_sq_le_twoFifths N hN x y
    simpa only [c13FixedRemoteEvenPrimeMatrix, Finset.sum_product,
      Finset.sum_const_zero, mul_assoc, mul_left_comm, mul_comm] using h
  · intro i j
    exact c13_finitePrimeTranslationEvenModeMatrix_symm
      (fixedRemotePositiveMode 3840 N) i j

/-- Odd-parity actual cross-coordinate companion. -/
theorem c13_fixed3840_remoteOddPrimeCrossEnergy_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPrimeMatrix 3840 N) x y) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteOddPrimeMatrix 3840 N) x y]
  · have h := c13_fixed3840_remoteOddPrimeBilinear_sq_le_twoFifths N hN x y
    simpa only [c13FixedRemoteOddPrimeMatrix, Finset.sum_product,
      Finset.sum_const_zero, mul_assoc, mul_left_comm, mul_comm] using h
  · intro i j
    exact c13_finitePrimeTranslationOddModeMatrix_symm
      (fixedRemotePositiveMode 3840 N) i j

lemma finiteMatrixBlockCrossEnergy_neg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy (-A) x y =
      -RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy A x y := by
  unfold RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
  change (1 / 2 : ℝ) *
      ((∑ i, ∑ j, x i * (-(A (Sum.inl i) (Sum.inr j))) * y j) +
       (∑ i, ∑ j, y i * (-(A (Sum.inr i) (Sum.inl j))) * x j)) =
    -((1 / 2 : ℝ) *
      ((∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j) +
       (∑ i, ∑ j, y i * A (Sum.inr i) (Sum.inl j) * x j)))
  have hLeft :
      (∑ i, ∑ j, x i * (-(A (Sum.inl i) (Sum.inr j))) * y j) =
        -(∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hRight :
      (∑ i, ∑ j, y i * (-(A (Sum.inr i) (Sum.inl j))) * x j) =
        -(∑ i, ∑ j, y i * A (Sum.inr i) (Sum.inl j) * x j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hLeft, hRight]
  ring

noncomputable def c13FixedRemoteEvenPrimeErrorMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  finiteLogarithmicPrimeEvenPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

noncomputable def c13FixedRemoteOddPrimeErrorMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  finiteLogarithmicPrimeOddPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

/-- The bound applies to the prime-error sign convention used by the literal
CvS builder, not merely to the auxiliary positive translation matrix. -/
theorem c13_fixed3840_remoteEvenPrimeErrorCrossEnergy_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPrimeErrorMatrix 3840 N) x y) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [c13FixedRemoteEvenPrimeErrorMatrix,
    finiteLogarithmicPrimeEvenPositiveModeErrorMatrix_eq_neg_translation
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode 3840 N) (by norm_num),
    finiteMatrixBlockCrossEnergy_neg, neg_sq]
  exact c13_fixed3840_remoteEvenPrimeCrossEnergy_sq_le_twoFifths N hN x y

theorem c13_fixed3840_remoteOddPrimeErrorCrossEnergy_sq_le_twoFifths
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPrimeErrorMatrix 3840 N) x y) ^ 2 ≤
      (2 / 5 : ℝ) * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [c13FixedRemoteOddPrimeErrorMatrix,
    finiteLogarithmicPrimeOddPositiveModeErrorMatrix_eq_neg_translation
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode 3840 N) (by norm_num),
    finiteMatrixBlockCrossEnergy_neg, neg_sq]
  exact c13_fixed3840_remoteOddPrimeCrossEnergy_sq_le_twoFifths N hN x y

/-- The actual even CvS prime-error channel is geometrically summable across
all remote dyadic shells based at `13^5`. -/
theorem c13_fixed3840_remoteEvenPrimeErrorCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPrimeErrorMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((2 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [c13FixedRemoteEvenPrimeErrorMatrix,
    finiteLogarithmicPrimeEvenPositiveModeErrorMatrix_eq_neg_translation
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode 3840 (371293 * 2 ^ k)) (by norm_num),
    finiteMatrixBlockCrossEnergy_neg, neg_sq]
  have hRaw := c13_fixedRemoteEvenPrimeCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) (by
      have hBase : 3840 ≤ 371293 := by norm_num
      exact hBase.trans
        (Nat.le_mul_of_pos_right 371293 (Nat.pow_pos (by omega)))) x y
  have hCoeff := c13_fixed3840_remote_primeCoefficient_dyadic_le k
  have hNorms : 0 ≤ (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoeff hNorms)

/-- Odd-parity geometrically summable prime-error channel. -/
theorem c13_fixed3840_remoteOddPrimeErrorCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (RiemannCvs.BoundaryWeylSchurTail.finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPrimeErrorMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((2 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  rw [c13FixedRemoteOddPrimeErrorMatrix,
    finiteLogarithmicPrimeOddPositiveModeErrorMatrix_eq_neg_translation
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode 3840 (371293 * 2 ^ k)) (by norm_num),
    finiteMatrixBlockCrossEnergy_neg, neg_sq]
  have hRaw := c13_fixedRemoteOddPrimeCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) (by
      have hBase : 3840 ≤ 371293 := by norm_num
      exact hBase.trans
        (Nat.le_mul_of_pos_right 371293 (Nat.pow_pos (by omega)))) x y
  have hCoeff := c13_fixed3840_remote_primeCoefficient_dyadic_le k
  have hNorms : 0 ≤ (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoeff hNorms)

end RiemannCvs.PrimeTranslationSeparatedBands
