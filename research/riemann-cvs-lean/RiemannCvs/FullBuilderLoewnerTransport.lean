import RiemannCvs.HistoricalCombinedLoewnerTransport

/-!
# Full-builder Loewner transport

The rational cutoff pole is not an essentially separate source channel.  For

`g(x) = -scale * x / (a + b*x^2)`,

its Loewner quotient `(g(q)-g(p))/(p-q)` is exactly

`scale * (a-b*p*q) / ((a+b*p^2)*(a+b*q^2))`,

the pole kernel used by the CvS builder.  Consequently the complete remote
builder block `pole - Archimedean/prime` is itself one odd-symbol Loewner
kernel.  This representation preserves all three-source cancellation, notably
the cancellation in the old odd `[1,20]` band that is lost by a componentwise
triangle estimate.

The module proves, using the literal cutoff-13 matrices:

* the rational pole/Loewner identity, including the diagonal;
* exact identification of both parity-compressed remote builder blocks with a
  single full symbol;
* row-square, rectangular cross-form, and actual shell-energy estimates;
* exact one-half transport when the target shell doubles;
* the closed `q * (1/2)^k` estimate at every dyadic distance;
* a finite-family theorem showing that all actual regular historical shells
  consume at most twice their leading full-symbol budget.

The remaining analytic input is deliberately explicit: a scalar square-sum
bound for the full symbol and one base rectangular budget for each newly
introduced historical shell.  No midpoint diagnostic is used as a theorem
premise.  This file does not assert the infinite boundary-Weyl limit or RH.
-/

noncomputable section
open scoped BigOperators Real

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def rationalPoleLoewnerSymbol
    (scale a b : ℝ) (x : ℝ) : ℝ :=
  -(scale * x / (a + b * x ^ 2))

noncomputable def rationalPoleLoewnerDiagonal
    (scale a b : ℝ) (x : ℝ) : ℝ :=
  CvSParityDisplacement.poleKernel scale a b x x

theorem poleKernel_eq_oddDifferenceKernel_rationalPoleLoewner
    (scale a b p q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    CvSParityDisplacement.poleKernel scale a b p q =
      CvSParityDisplacement.oddDifferenceKernel
        (rationalPoleLoewnerSymbol scale a b)
        (rationalPoleLoewnerDiagonal scale a b) p q := by
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel,
      rationalPoleLoewnerDiagonal]
  · have hpDen : a + b * p ^ 2 ≠ 0 := by
      have : 0 < a + b * p ^ 2 := by positivity
      exact ne_of_gt this
    have hqDen : a + b * q ^ 2 ≠ 0 := by
      have : 0 < a + b * q ^ 2 := by positivity
      exact ne_of_gt this
    simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    unfold rationalPoleLoewnerSymbol CvSParityDisplacement.poleKernel
    field_simp [hpDen, hqDen]
    ring

noncomputable def logarithmicPoleLoewnerSymbol (c : ℝ) : ℝ → ℝ :=
  rationalPoleLoewnerSymbol
    (32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2)
    ((Real.log c) ^ 2) (16 * Real.pi ^ 2)

noncomputable def logarithmicPoleLoewnerDiagonal (c : ℝ) : ℝ → ℝ :=
  rationalPoleLoewnerDiagonal
    (32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2)
    ((Real.log c) ^ 2) (16 * Real.pi ^ 2)

theorem logarithmicPoleKernel_eq_oddDifferenceKernel
    (c p q : ℝ) (hc : 1 < c) :
    logarithmicPoleKernel c p q =
      CvSParityDisplacement.oddDifferenceKernel
        (logarithmicPoleLoewnerSymbol c)
        (logarithmicPoleLoewnerDiagonal c) p q := by
  unfold logarithmicPoleKernel logarithmicPoleLoewnerSymbol
    logarithmicPoleLoewnerDiagonal
  exact poleKernel_eq_oddDifferenceKernel_rationalPoleLoewner
    _ _ _ p q (sq_pos_of_pos (Real.log_pos hc)) (by positivity)

theorem logarithmicPoleLoewnerSymbol_odd (c : ℝ) :
    Function.Odd (logarithmicPoleLoewnerSymbol c) := by
  intro x
  unfold logarithmicPoleLoewnerSymbol rationalPoleLoewnerSymbol
  simp only [neg_sq]
  ring

noncomputable def c13HistoricalBuilderLoewnerSymbol : ℝ → ℝ :=
  fun x => logarithmicPoleLoewnerSymbol 13 x -
    c13HistoricalCombinedLoewnerSymbol x

noncomputable def c13HistoricalBuilderLoewnerDiagonal : ℝ → ℝ :=
  fun x => logarithmicPoleLoewnerDiagonal 13 x -
    c13HistoricalCombinedLoewnerDiagonal x

theorem c13HistoricalBuilderLoewnerSymbol_odd :
    Function.Odd c13HistoricalBuilderLoewnerSymbol := by
  intro x
  rw [c13HistoricalBuilderLoewnerSymbol,
    c13HistoricalBuilderLoewnerSymbol,
    logarithmicPoleLoewnerSymbol_odd,
    c13HistoricalCombinedLoewnerSymbol_odd]
  ring

theorem c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel
    (p q : ℝ) :
    logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol 13)
        (logarithmicArchimedeanDiagonal 13) 13
        c13PrimePowerLocation c13PrimePowerBase p q =
      CvSParityDisplacement.oddDifferenceKernel
        c13HistoricalBuilderLoewnerSymbol
        c13HistoricalBuilderLoewnerDiagonal p q := by
  rw [logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicPoleKernel_eq_oddDifferenceKernel 13 p q (by norm_num)]
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel,
      c13HistoricalBuilderLoewnerDiagonal,
      c13HistoricalCombinedLoewnerDiagonal]
  · simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    unfold c13HistoricalBuilderLoewnerSymbol
      c13HistoricalCombinedLoewnerSymbol
    ring

noncomputable def c13EvenHistoricalBuilderLoewnerRemoteNatEntry
    (B N : ℕ) (i : Fin B) (j : ℕ) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ) ((N + 1 + j : ℕ) : ℝ) +
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ) (-((N + 1 + j : ℕ) : ℝ))

noncomputable def c13OddHistoricalBuilderLoewnerRemoteNatEntry
    (B N : ℕ) (i : Fin B) (j : ℕ) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ) ((N + 1 + j : ℕ) : ℝ) -
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (historicalBandMode B i : ℝ) (-((N + 1 + j : ℕ) : ℝ))

noncomputable def c13EvenHistoricalBuilderLoewnerRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  c13EvenHistoricalBuilderLoewnerRemoteNatEntry B N i j

noncomputable def c13OddHistoricalBuilderLoewnerRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  c13OddHistoricalBuilderLoewnerRemoteNatEntry B N i j

theorem c13HistoricalRemoteEvenBuilderMatrix_inl_inr_eq_fullLoewner
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13HistoricalRemoteEvenBuilderMatrix B N (Sum.inl i) (Sum.inr j) =
      c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j := by
  unfold c13HistoricalRemoteEvenBuilderMatrix
    logarithmicCvSBuilderEvenPositiveModeMatrix
    c13EvenHistoricalBuilderLoewnerRemoteEntry
    c13EvenHistoricalBuilderLoewnerRemoteNatEntry
  simp only [c13HistoricalRemotePositiveMode_inl,
    c13HistoricalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel]
  push_cast
  norm_num

theorem c13HistoricalRemoteOddBuilderMatrix_inl_inr_eq_fullLoewner
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13HistoricalRemoteOddBuilderMatrix B N (Sum.inl i) (Sum.inr j) =
      c13OddHistoricalBuilderLoewnerRemoteEntry B N i j := by
  unfold c13HistoricalRemoteOddBuilderMatrix
    logarithmicCvSBuilderOddPositiveModeMatrix
    c13OddHistoricalBuilderLoewnerRemoteEntry
    c13OddHistoricalBuilderLoewnerRemoteNatEntry
  simp only [c13HistoricalRemotePositiveMode_inl,
    c13HistoricalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel]
  push_cast
  norm_num

theorem c13EvenHistoricalBuilderLoewnerRemote_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j ∈ Finset.range N,
        c13EvenHistoricalBuilderLoewnerRemoteNatEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalBuilderLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  apply evenParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    c13HistoricalBuilderLoewnerSymbol
    c13HistoricalBuilderLoewnerDiagonal
    (historicalBandMode B i : ℝ) N hN C
  · positivity
  · exact fun j _hj => c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j
  · exact c13HistoricalBuilderLoewnerSymbol_odd
  · exact hSymbol

theorem c13OddHistoricalBuilderLoewnerRemote_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j ∈ Finset.range N,
        c13OddHistoricalBuilderLoewnerRemoteNatEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalBuilderLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  apply oddParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    c13HistoricalBuilderLoewnerSymbol
    c13HistoricalBuilderLoewnerDiagonal
    (historicalBandMode B i : ℝ) N hN C
  · positivity
  · exact fun j _hj => c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j
  · exact c13HistoricalBuilderLoewnerSymbol_odd
  · exact hSymbol

theorem c13EvenHistoricalBuilderLoewnerRemote_fin_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j : Fin N,
        c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalBuilderLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  change (∑ j : Fin N,
    c13EvenHistoricalBuilderLoewnerRemoteNatEntry B N i (j : ℕ) ^ 2) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => c13EvenHistoricalBuilderLoewnerRemoteNatEntry B N i j ^ 2) N]
  exact c13EvenHistoricalBuilderLoewnerRemote_row_sq_le
    B N hN hBN C hSymbol i

theorem c13OddHistoricalBuilderLoewnerRemote_fin_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j : Fin N,
        c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalBuilderLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  change (∑ j : Fin N,
    c13OddHistoricalBuilderLoewnerRemoteNatEntry B N i (j : ℕ) ^ 2) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => c13OddHistoricalBuilderLoewnerRemoteNatEntry B N i j ^ 2) N]
  exact c13OddHistoricalBuilderLoewnerRemote_row_sq_le
    B N hN hBN C hSymbol i

noncomputable def c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13EvenHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 *
      (x ij.1 * y ij.2)

noncomputable def c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13OddHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 *
      (x ij.1 * y ij.2)

theorem c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteEvenBuilderMatrix B N) x y =
      c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13HistoricalRemoteEvenBuilderMatrix B N) x y
    (c13HistoricalRemoteEvenBuilderMatrix_symm B N)]
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [c13HistoricalRemoteEvenBuilderMatrix_inl_inr_eq_fullLoewner]
  ring

theorem c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteOddBuilderMatrix B N) x y =
      c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13HistoricalRemoteOddBuilderMatrix B N) x y
    (c13HistoricalRemoteOddBuilderMatrix_symm B N)]
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [c13HistoricalRemoteOddBuilderMatrix_inl_inr_eq_fullLoewner]
  ring

theorem c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin N))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
        rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
    rw [Finset.sum_product]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin B)),
          ∑ j ∈ (Finset.univ : Finset (Fin N)),
            c13EvenHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin B)),
            32 * (C / (N : ℝ) +
              c13HistoricalBuilderLoewnerSymbol
                  (historicalBandMode B i : ℝ) ^ 2 /
                (2 * (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa using c13EvenHistoricalBuilderLoewnerRemote_fin_row_sq_le
          B N hN hBN C hSymbol i
      _ = rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
        unfold rectangularSymbolSquareBudget
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        rw [← Finset.mul_sum, Finset.sum_div]
        ring
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalBuilderLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin N))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13OddHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
        rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
    rw [Finset.sum_product]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin B)),
          ∑ j ∈ (Finset.univ : Finset (Fin N)),
            c13OddHistoricalBuilderLoewnerRemoteEntry B N i j ^ 2) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin B)),
            32 * (C / (N : ℝ) +
              c13HistoricalBuilderLoewnerSymbol
                  (historicalBandMode B i : ℝ) ^ 2 /
                (2 * (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa using c13OddHistoricalBuilderLoewnerRemote_fin_row_sq_le
          B N hN hBN C hSymbol i
      _ = rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
        unfold rectangularSymbolSquareBudget
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        rw [← Finset.mul_sum, Finset.sum_div]
        ring
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

/-- The complete cutoff-13 builder, including its rational pole, is transported
with one exact factor `1/2` because it is a single odd-symbol Loewner kernel. -/
theorem c13HistoricalRemoteEvenBuilder_halfTransport_fullLoewner
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalBuilderLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B (2 * N)) x y) ^ 2 ≤
      (q / 2) * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (2 * N) (2 * N) y := by
  have hN0 : N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapN := c13ShellDynamicGap_nonneg N hN960
  have hGap2N := c13ShellDynamicGap_nonneg (2 * N) h2N960
  have hGapGrowth := c13ShellDynamicGap_mono
    (M := N) (N := 2 * N) (by omega) (by omega)
  have hBudget := rectangularSymbolSquareBudget_halfTransport
    (Finset.univ : Finset (Fin B))
    (fun i => c13HistoricalBuilderLoewnerSymbol
      (historicalBandMode B i : ℝ))
    N C q
    (c13ShellDynamicGap B) (c13ShellDynamicGap N)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    hN0 hq hGapB hGapN le_rfl hGapGrowth hPreviousBudget
  have hCross :=
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
      B (2 * N) (by omega) (by omega) C hSymbolNext x y
  have hLowEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderShellEnergy B B x)
    (c13EvenBuilderShellEnergy (2 * N) (2 * N) y)
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (2 * N) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalBuilderLoewnerSymbol
        (historicalBandMode B i : ℝ)) (2 * N) C)
    (q / 2) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hGapB hGap2N (div_nonneg hq (by norm_num))
    (by positivity) (by positivity)
  · simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowEnergy
  · simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighEnergy
  · exact hCross
  · exact hBudget

theorem c13HistoricalRemoteOddBuilder_halfTransport_fullLoewner
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalBuilderLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B (2 * N)) x y) ^ 2 ≤
      (q / 2) * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (2 * N) (2 * N) y := by
  have hN0 : N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapN := c13ShellDynamicGap_nonneg N hN960
  have hGap2N := c13ShellDynamicGap_nonneg (2 * N) h2N960
  have hGapGrowth := c13ShellDynamicGap_mono
    (M := N) (N := 2 * N) (by omega) (by omega)
  have hBudget := rectangularSymbolSquareBudget_halfTransport
    (Finset.univ : Finset (Fin B))
    (fun i => c13HistoricalBuilderLoewnerSymbol
      (historicalBandMode B i : ℝ))
    N C q
    (c13ShellDynamicGap B) (c13ShellDynamicGap N)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    hN0 hq hGapB hGapN le_rfl hGapGrowth hPreviousBudget
  have hCross :=
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
      B (2 * N) (by omega) (by omega) C hSymbolNext x y
  have hLowEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13OddBuilderShellEnergy B B x)
    (c13OddBuilderShellEnergy (2 * N) (2 * N) y)
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (2 * N) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalBuilderLoewnerSymbol
        (historicalBandMode B i : ℝ)) (2 * N) C)
    (q / 2) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hGapB hGap2N (div_nonneg hq (by norm_num))
    (by positivity) (by positivity)
  · simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowEnergy
  · simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighEnergy
  · exact hCross
  · exact hBudget

theorem rectangularSymbolSquareBudget_mul_two_pow
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ)
    (hN : N ≠ 0) : ∀ k : ℕ,
    rectangularSymbolSquareBudget rows oldSymbol (N * 2 ^ k) C =
      rectangularSymbolSquareBudget rows oldSymbol N C / (2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hNk : N * 2 ^ k ≠ 0 := mul_ne_zero hN (pow_ne_zero _ (by norm_num))
      rw [pow_succ]
      rw [show N * (2 ^ k * 2) = 2 * (N * 2 ^ k) by ring]
      rw [rectangularSymbolSquareBudget_two_mul
        rows oldSymbol (N * 2 ^ k) C hNk, ih]
      rw [pow_succ]
      ring

lemma div_two_pow_eq_mul_half_pow (q : ℝ) (k : ℕ) :
    q / (2 : ℝ) ^ k = q * (1 / 2 : ℝ) ^ k := by
  rw [div_pow]
  simp [div_eq_mul_inv]

theorem c13HistoricalBuilderLoewnerBudget_dyadicTransport
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N)
    (C q : ℝ) (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N) :
    ∀ k : ℕ,
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) (N * 2 ^ k) C ≤
        (q * (1 / 2 : ℝ) ^ k) * c13ShellDynamicGap B *
          c13ShellDynamicGap (N * 2 ^ k) := by
  intro k
  have hN0 : N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hNTarget : N ≤ N * 2 ^ k := by
    simpa using Nat.mul_le_mul_left N hPow
  have hTarget960 : 960 ≤ N * 2 ^ k := hN960.trans hNTarget
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapN := c13ShellDynamicGap_nonneg N hN960
  have hGapGrowth := c13ShellDynamicGap_mono
    (M := N) (N := N * 2 ^ k) (by omega) hNTarget
  have hGapProduct :
      c13ShellDynamicGap B * c13ShellDynamicGap N ≤
        c13ShellDynamicGap B * c13ShellDynamicGap (N * 2 ^ k) :=
    mul_le_mul_of_nonneg_left hGapGrowth hGapB
  rw [rectangularSymbolSquareBudget_mul_two_pow
    (Finset.univ : Finset (Fin B))
    (fun i => c13HistoricalBuilderLoewnerSymbol
      (historicalBandMode B i : ℝ)) N C hN0 k]
  calc
    rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C / (2 : ℝ) ^ k ≤
        (q * c13ShellDynamicGap B * c13ShellDynamicGap N) /
          (2 : ℝ) ^ k := by
      exact div_le_div_of_nonneg_right hPreviousBudget (by positivity)
    _ = (q * (1 / 2 : ℝ) ^ k) *
        (c13ShellDynamicGap B * c13ShellDynamicGap N) := by
      rw [← div_two_pow_eq_mul_half_pow q k]
      ring
    _ ≤ (q * (1 / 2 : ℝ) ^ k) *
        (c13ShellDynamicGap B * c13ShellDynamicGap (N * 2 ^ k)) :=
      mul_le_mul_of_nonneg_left hGapProduct
        (mul_nonneg hq (by positivity))
    _ = (q * (1 / 2 : ℝ) ^ k) * c13ShellDynamicGap B *
        c13ShellDynamicGap (N * 2 ^ k) := by ring

theorem c13HistoricalRemoteEvenBuilder_dyadicTransport_fullLoewner
    (B N k : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolTarget :
      (∑ j ∈ Finset.range (N * 2 ^ k),
          c13HistoricalBuilderLoewnerSymbol
              (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((N * 2 ^ k : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (N * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B (N * 2 ^ k)) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y := by
  have hN0 : N ≠ 0 := by omega
  have hTarget0 : N * 2 ^ k ≠ 0 :=
    mul_ne_zero hN0 (pow_ne_zero _ (by norm_num))
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hNTarget : N ≤ N * 2 ^ k := by
    simpa using Nat.mul_le_mul_left N hPow
  have hSeparation : 4 * B ≤ N * 2 ^ k := hBN.trans hNTarget
  have hTarget960 : 960 ≤ N * 2 ^ k := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapTarget := c13ShellDynamicGap_nonneg (N * 2 ^ k) hTarget960
  have hBudget := c13HistoricalBuilderLoewnerBudget_dyadicTransport
    B N hB hBN C q hq hPreviousBudget k
  have hCross :=
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
      B (N * 2 ^ k) hTarget0 hSeparation C hSymbolTarget x y
  have hLowEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (N * 2 ^ k) (N * 2 ^ k) hTarget960 (by omega) y
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderShellEnergy B B x)
    (c13EvenBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y)
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B (N * 2 ^ k) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (N * 2 ^ k))
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalBuilderLoewnerSymbol
        (historicalBandMode B i : ℝ)) (N * 2 ^ k) C)
    (q * (1 / 2 : ℝ) ^ k) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hGapB hGapTarget (mul_nonneg hq (by positivity))
    (by positivity) (by positivity)
  · simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowEnergy
  · simpa [c13EvenBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighEnergy
  · exact hCross
  · exact hBudget

theorem c13HistoricalRemoteOddBuilder_dyadicTransport_fullLoewner
    (B N k : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolTarget :
      (∑ j ∈ Finset.range (N * 2 ^ k),
          c13HistoricalBuilderLoewnerSymbol
              (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N * 2 ^ k + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((N * 2 ^ k : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (N * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B (N * 2 ^ k)) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y := by
  have hN0 : N ≠ 0 := by omega
  have hTarget0 : N * 2 ^ k ≠ 0 :=
    mul_ne_zero hN0 (pow_ne_zero _ (by norm_num))
  have hPow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hNTarget : N ≤ N * 2 ^ k := by
    simpa using Nat.mul_le_mul_left N hPow
  have hSeparation : 4 * B ≤ N * 2 ^ k := hBN.trans hNTarget
  have hTarget960 : 960 ≤ N * 2 ^ k := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapTarget := c13ShellDynamicGap_nonneg (N * 2 ^ k) hTarget960
  have hBudget := c13HistoricalBuilderLoewnerBudget_dyadicTransport
    B N hB hBN C q hq hPreviousBudget k
  have hCross :=
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy_sq_le_symbolBudget
      B (N * 2 ^ k) hTarget0 hSeparation C hSymbolTarget x y
  have hLowEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (N * 2 ^ k) (N * 2 ^ k) hTarget960 (by omega) y
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  apply relativeCoupling_of_squaredNormBudget
    (c13OddBuilderShellEnergy B B x)
    (c13OddBuilderShellEnergy (N * 2 ^ k) (N * 2 ^ k) y)
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B (N * 2 ^ k) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (N * 2 ^ k))
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalBuilderLoewnerSymbol
        (historicalBandMode B i : ℝ)) (N * 2 ^ k) C)
    (q * (1 / 2 : ℝ) ^ k) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hGapB hGapTarget (mul_nonneg hq (by positivity))
    (by positivity) (by positivity)
  · simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hLowEnergy
  · simpa [c13OddBuilderShellEnergy, finiteVectorEuclideanNormSq] using hHighEnergy
  · exact hCross
  · exact hBudget

theorem c13HistoricalRemoteEvenBuilder_dyadicTransport_toTarget_fullLoewner
    (B N k T : ℕ) (hTarget : T = N * 2 ^ k)
    (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolTarget :
      (∑ j ∈ Finset.range T,
          c13HistoricalBuilderLoewnerSymbol
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤ C / (T : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin T → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B T) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy T T y := by
  subst T
  exact c13HistoricalRemoteEvenBuilder_dyadicTransport_fullLoewner
    B N k hB hBN C q hSymbolTarget hq hPreviousBudget x y

theorem c13HistoricalRemoteOddBuilder_dyadicTransport_toTarget_fullLoewner
    (B N k T : ℕ) (hTarget : T = N * 2 ^ k)
    (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolTarget :
      (∑ j ∈ Finset.range T,
          c13HistoricalBuilderLoewnerSymbol
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤ C / (T : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin T → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B T) x y) ^ 2 ≤
      (q * (1 / 2 : ℝ) ^ k) * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy T T y := by
  subst T
  exact c13HistoricalRemoteOddBuilder_dyadicTransport_fullLoewner
    B N k hB hBN C q hSymbolTarget hq hPreviousBudget x y

/-- A finite family of actual even historical source shells at dyadic distances
from one common target consumes at most twice its leading full-symbol budget. -/
theorem c13HistoricalRemoteEvenBuilder_dyadicFamily_fullLoewner
    (B baseTarget : ℕ → ℕ) (n T : ℕ) (C : ℝ)
    (q : ℕ → ℝ) (leading rho : ℝ)
    (hT : 960 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = baseTarget i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
    (hSeparated : ∀ i ∈ Finset.range n, 4 * B i ≤ baseTarget i)
    (hSymbolTarget :
      (∑ j ∈ Finset.range T,
          c13HistoricalBuilderLoewnerSymbol
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤ C / (T : ℝ))
    (hq : ∀ i ∈ Finset.range n, 0 ≤ q i)
    (hqLeading : ∀ i ∈ Finset.range n, q i ≤ leading)
    (hPreviousBudget : ∀ i ∈ Finset.range n,
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin (B i)))
          (fun j => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode (B i) j : ℝ)) (baseTarget i) C ≤
        q i * c13ShellDynamicGap (B i) *
          c13ShellDynamicGap (baseTarget i))
    (hLeading : 0 ≤ leading) (hTotalBudget : 2 * leading ≤ rho)
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteEvenBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      rho *
        (∑ i ∈ Finset.range n, c13EvenBuilderShellEnergy (B i) (B i) (x i)) *
        c13EvenBuilderShellEnergy T T y := by
  let energy : ℕ → ℝ := fun i =>
    c13EvenBuilderShellEnergy (B i) (B i) (x i)
  let cross : ℕ → ℝ := fun i =>
    finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix (B i) T) (x i) y
  let budget : ℕ → ℝ := fun i => q i * (1 / 2 : ℝ) ^ i
  have hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i := by
    intro i hi
    have hFloor :=
      c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
        (B i) (B i) (hB i hi) (by omega) (x i)
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (B i) (hB i hi))
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
    intro i hi
    exact mul_nonneg (hq i hi) (by positivity)
  have hEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ leading * (1 / (2 : ℝ)) ^ i := by
    intro i hi
    exact mul_le_mul_of_nonneg_right (hqLeading i hi) (by positivity)
  have hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        c13EvenBuilderShellEnergy T T y := by
    intro i hi
    exact c13HistoricalRemoteEvenBuilder_dyadicTransport_toTarget_fullLoewner
      (B i) (baseTarget i) i T (hTarget i hi)
      (hB i hi) (hSeparated i hi) C (q i) hSymbolTarget
      (hq i hi) (hPreviousBudget i hi) (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13EvenBuilderShellEnergy T T y)
      leading rho hEnergy hBudget hTail hLeading hEnvelope hTotalBudget hRelative

/-- Odd-parity companion of the actual full-symbol dyadic family theorem. -/
theorem c13HistoricalRemoteOddBuilder_dyadicFamily_fullLoewner
    (B baseTarget : ℕ → ℕ) (n T : ℕ) (C : ℝ)
    (q : ℕ → ℝ) (leading rho : ℝ)
    (hT : 960 ≤ T)
    (hTarget : ∀ i ∈ Finset.range n, T = baseTarget i * 2 ^ i)
    (hB : ∀ i ∈ Finset.range n, 960 ≤ B i)
    (hSeparated : ∀ i ∈ Finset.range n, 4 * B i ≤ baseTarget i)
    (hSymbolTarget :
      (∑ j ∈ Finset.range T,
          c13HistoricalBuilderLoewnerSymbol
              (((T + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((T + 1 + j : ℕ) : ℝ)) ^ 2) ≤ C / (T : ℝ))
    (hq : ∀ i ∈ Finset.range n, 0 ≤ q i)
    (hqLeading : ∀ i ∈ Finset.range n, q i ≤ leading)
    (hPreviousBudget : ∀ i ∈ Finset.range n,
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin (B i)))
          (fun j => c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode (B i) j : ℝ)) (baseTarget i) C ≤
        q i * c13ShellDynamicGap (B i) *
          c13ShellDynamicGap (baseTarget i))
    (hLeading : 0 ≤ leading) (hTotalBudget : 2 * leading ≤ rho)
    (x : ∀ i, Fin (B i) → ℝ) (y : Fin T → ℝ) :
    (∑ i ∈ Finset.range n,
        finiteMatrixBlockCrossEnergy
          (c13HistoricalRemoteOddBuilderMatrix (B i) T) (x i) y) ^ 2 ≤
      rho *
        (∑ i ∈ Finset.range n, c13OddBuilderShellEnergy (B i) (B i) (x i)) *
        c13OddBuilderShellEnergy T T y := by
  let energy : ℕ → ℝ := fun i =>
    c13OddBuilderShellEnergy (B i) (B i) (x i)
  let cross : ℕ → ℝ := fun i =>
    finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix (B i) T) (x i) y
  let budget : ℕ → ℝ := fun i => q i * (1 / 2 : ℝ) ^ i
  have hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i := by
    intro i hi
    have hFloor :=
      c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
        (B i) (B i) (hB i hi) (by omega) (x i)
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (B i) (hB i hi))
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
    intro i hi
    exact mul_nonneg (hq i hi) (by positivity)
  have hEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ leading * (1 / (2 : ℝ)) ^ i := by
    intro i hi
    exact mul_le_mul_of_nonneg_right (hqLeading i hi) (by positivity)
  have hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        c13OddBuilderShellEnergy T T y := by
    intro i hi
    exact c13HistoricalRemoteOddBuilder_dyadicTransport_toTarget_fullLoewner
      (B i) (baseTarget i) i T (hTarget i hi)
      (hB i hi) (hSeparated i hi) C (q i) hSymbolTarget
      (hq i hi) (hPreviousBudget i hi) (x i) y
  simpa only [energy, cross, budget] using
    relativeCoupling_of_dyadicChannelBudgets
      energy cross budget n (c13OddBuilderShellEnergy T T y)
      leading rho hEnergy hBudget hTail hLeading hEnvelope hTotalBudget hRelative

end RiemannCvs.V23BoundaryWeylMainline
