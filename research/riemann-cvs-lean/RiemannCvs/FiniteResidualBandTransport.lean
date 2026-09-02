import RiemannCvs.FiniteMomentLowModeTransport

/-!
# Coercivity-adapted finite residual bands

The single interval `(20,120]` has a weak odd minimum eigenvalue.  Splitting it
at the two natural doubling coordinates `30` and `60` restores strong source
coercivity while keeping every target estimate analytic.  This module develops
the arbitrary finite-interval bridge needed for those three literal bands.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def finiteIntervalMode
    (A M : ℕ) (i : Fin M) : ℕ := A + 1 + (i : ℕ)

lemma finiteIntervalMode_nonneg (A M : ℕ) (i : Fin M) :
    0 ≤ (finiteIntervalMode A M i : ℝ) := by positivity

lemma finiteIntervalMode_le (A M : ℕ) (i : Fin M) :
    finiteIntervalMode A M i ≤ A + M := by
  unfold finiteIntervalMode
  omega

lemma finiteIntervalMode_two_mul_le_remoteMode
    (A M N : ℕ) (hAMN : 2 * (A + M) ≤ N)
    (i : Fin M) (j : Fin N) :
    2 * (finiteIntervalMode A M i : ℝ) ≤
      ((N + 1 + (j : ℕ) : ℕ) : ℝ) := by
  exact_mod_cast (show 2 * finiteIntervalMode A M i ≤ N + 1 + (j : ℕ) by
    have hMode := finiteIntervalMode_le A M i
    omega)

noncomputable def c13FiniteIntervalPositiveMode
    (A M : ℕ) : Fin M → ℤ :=
  fun i => (finiteIntervalMode A M i : ℤ)

noncomputable def c13FiniteIntervalRemotePositiveMode
    (A M N : ℕ) : Fin M ⊕ Fin N → ℤ :=
  Sum.elim
    (fun i => (finiteIntervalMode A M i : ℤ))
    (fun j => ((N + 1 + (j : ℕ) : ℕ) : ℤ))

@[simp] lemma c13FiniteIntervalRemotePositiveMode_inl
    (A M N : ℕ) (i : Fin M) :
    c13FiniteIntervalRemotePositiveMode A M N (Sum.inl i) =
      (finiteIntervalMode A M i : ℤ) := by rfl

@[simp] lemma c13FiniteIntervalRemotePositiveMode_inr
    (A M N : ℕ) (j : Fin N) :
    c13FiniteIntervalRemotePositiveMode A M N (Sum.inr j) =
      ((N + 1 + (j : ℕ) : ℕ) : ℤ) := by rfl

noncomputable def c13FiniteIntervalRemoteEvenBuilderMatrix
    (A M N : ℕ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13FiniteIntervalRemotePositiveMode A M N)

noncomputable def c13FiniteIntervalRemoteOddBuilderMatrix
    (A M N : ℕ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderOddPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13FiniteIntervalRemotePositiveMode A M N)

noncomputable def c13EvenBuilderFiniteIntervalEnergy
    (A M : ℕ) (x : Fin M → ℝ) : ℝ :=
  finiteMatrixQuadraticEnergy
    (logarithmicCvSBuilderEvenPositiveModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13FiniteIntervalPositiveMode A M)) x

noncomputable def c13OddBuilderFiniteIntervalEnergy
    (A M : ℕ) (x : Fin M → ℝ) : ℝ :=
  finiteMatrixQuadraticEnergy
    (logarithmicCvSBuilderOddPositiveModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13FiniteIntervalPositiveMode A M)) x

theorem c13FiniteIntervalRemoteEvenBuilderMatrix_symm
    (A M N : ℕ) (a b : Fin M ⊕ Fin N) :
    c13FiniteIntervalRemoteEvenBuilderMatrix A M N a b =
      c13FiniteIntervalRemoteEvenBuilderMatrix A M N b a := by
  exact logarithmicCvSBuilderEvenPositiveModeMatrix_symm
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13FiniteIntervalRemotePositiveMode A M N) a b

theorem c13FiniteIntervalRemoteOddBuilderMatrix_symm
    (A M N : ℕ) (a b : Fin M ⊕ Fin N) :
    c13FiniteIntervalRemoteOddBuilderMatrix A M N a b =
      c13FiniteIntervalRemoteOddBuilderMatrix A M N b a := by
  exact logarithmicCvSBuilderOddPositiveModeMatrix_symm
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13FiniteIntervalRemotePositiveMode A M N) a b

noncomputable def c13EvenFiniteIntervalBuilderLoewnerRemoteEntry
    (A M N : ℕ) (i : Fin M) (j : Fin N) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      ((N + 1 + (j : ℕ) : ℕ) : ℝ) +
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      (-((N + 1 + (j : ℕ) : ℕ) : ℝ))

noncomputable def c13OddFiniteIntervalBuilderLoewnerRemoteEntry
    (A M N : ℕ) (i : Fin M) (j : Fin N) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      ((N + 1 + (j : ℕ) : ℕ) : ℝ) -
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      (-((N + 1 + (j : ℕ) : ℕ) : ℝ))

theorem c13FiniteIntervalRemoteEvenBuilderMatrix_inl_inr_eq_fullLoewner
    (A M N : ℕ) (i : Fin M) (j : Fin N) :
    c13FiniteIntervalRemoteEvenBuilderMatrix A M N (Sum.inl i) (Sum.inr j) =
      c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N i j := by
  unfold c13FiniteIntervalRemoteEvenBuilderMatrix
    logarithmicCvSBuilderEvenPositiveModeMatrix
    c13EvenFiniteIntervalBuilderLoewnerRemoteEntry
  simp only [c13FiniteIntervalRemotePositiveMode_inl,
    c13FiniteIntervalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel]
  push_cast
  norm_num

theorem c13FiniteIntervalRemoteOddBuilderMatrix_inl_inr_eq_fullLoewner
    (A M N : ℕ) (i : Fin M) (j : Fin N) :
    c13FiniteIntervalRemoteOddBuilderMatrix A M N (Sum.inl i) (Sum.inr j) =
      c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N i j := by
  unfold c13FiniteIntervalRemoteOddBuilderMatrix
    logarithmicCvSBuilderOddPositiveModeMatrix
    c13OddFiniteIntervalBuilderLoewnerRemoteEntry
  simp only [c13FiniteIntervalRemotePositiveMode_inl,
    c13FiniteIntervalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel,
    c13_logarithmicCutoffFreeKernel_eq_builderOddDifferenceKernel]
  push_cast
  norm_num

noncomputable def c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy
    (A M N : ℕ) (x : Fin M → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin M)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N ij.1 ij.2 *
      (x ij.1 * y ij.2)

noncomputable def c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy
    (A M N : ℕ) (x : Fin M → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin M)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N ij.1 ij.2 *
      (x ij.1 * y ij.2)

theorem c13FiniteIntervalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner
    (A M N : ℕ) (x : Fin M → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteEvenBuilderMatrix A M N) x y =
      c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FiniteIntervalRemoteEvenBuilderMatrix A M N) x y
    (c13FiniteIntervalRemoteEvenBuilderMatrix_symm A M N)]
  unfold c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [c13FiniteIntervalRemoteEvenBuilderMatrix_inl_inr_eq_fullLoewner]
  ring

theorem c13FiniteIntervalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner
    (A M N : ℕ) (x : Fin M → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteOddBuilderMatrix A M N) x y =
      c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FiniteIntervalRemoteOddBuilderMatrix A M N) x y
    (c13FiniteIntervalRemoteOddBuilderMatrix_symm A M N)]
  unfold c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [c13FiniteIntervalRemoteOddBuilderMatrix_inl_inr_eq_fullLoewner]
  ring

noncomputable def c13EvenFiniteIntervalRemoteBudget
    (M N : ℕ) (sourceSecond : ℝ) : ℝ :=
  (64 / 9 : ℝ) *
    ((3 / 2 : ℝ) * ((M : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ))) +
      3 * (sourceSecond * (1 / (2 * (N : ℝ) ^ 3))))

noncomputable def c13OddFiniteIntervalRemoteBudget
    (N : ℕ) (sourceModeSecond sourceZero : ℝ) : ℝ :=
  (64 / 9 : ℝ) *
    (3 * (sourceModeSecond * ((197 / 2000 : ℝ) / (N : ℝ) ^ 3)) +
      (3 / 2 : ℝ) * (sourceZero * (1 / (2 * (N : ℝ)))))

theorem c13EvenFiniteIntervalBuilderLoewnerRemote_entry_sq_sum_le
    (A M N : ℕ) (hN : 1920 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceSecond : ℝ) (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceSecond :
      (∑ i : Fin M,
        (finiteIntervalMode A M i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceSecond)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ i : Fin M, ∑ j : Fin N,
      c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2) ≤
      c13EvenFiniteIntervalRemoteBudget M N sourceSecond := by
  have hN0 : N ≠ 0 := by omega
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN hRawTarget
  have hInvFour := remote_inv_fourth_sum_le N hN0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin M)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)),
          c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2 ≤
            (64 / 9 : ℝ) *
              ((3 / 2 : ℝ) *
                  (c13HistoricalBuilderLoewnerSymbol
                      (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
                3 * ((finiteIntervalMode A M i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (finiteIntervalMode A M i : ℝ) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := by
    intro i _hi j _hj
    unfold c13EvenFiniteIntervalBuilderLoewnerRemoteEntry
    exact oddDifferenceKernel_evenParity_sq_le_weightedSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (finiteIntervalMode_nonneg A M i) (by positivity)
      (finiteIntervalMode_two_mul_le_remoteMode A M N hSep i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_evenParity_sum_sq_le_weightedSeparated
    (Finset.univ : Finset (Fin M)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin M => (finiteIntervalMode A M i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N) hEntry
  have hRect' :
      (∑ i : Fin M, ∑ j : Fin N,
          c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2) ≤
        (64 / 9 : ℝ) *
          ((3 / 2 : ℝ) * (M : ℝ) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) +
            3 * (∑ i : Fin M,
                (finiteIntervalMode A M i : ℝ) ^ 2 *
                  c13HistoricalBuilderLoewnerSymbol
                    (finiteIntervalMode A M i : ℝ) ^ 2) *
              (∑ j : Fin N,
                1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4))) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hRect
  have hFirst :
      (M : ℝ) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        (M : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hTarget (by positivity)
  have hSecond :
      (∑ i : Fin M,
          (finiteIntervalMode A M i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (finiteIntervalMode A M i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
      sourceSecond * (1 / (2 * (N : ℝ) ^ 3)) := by
    calc
      (∑ i : Fin M,
          (finiteIntervalMode A M i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (finiteIntervalMode A M i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          sourceSecond *
            (∑ j : Fin N,
              1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceSecond (by positivity)
      _ ≤ sourceSecond * (1 / (2 * (N : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hInvFour hSourceSecondNonneg
  have hInside := add_le_add
    (mul_le_mul_of_nonneg_left hFirst (by norm_num : (0 : ℝ) ≤ 3 / 2))
    (mul_le_mul_of_nonneg_left hSecond (by norm_num : (0 : ℝ) ≤ 3))
  exact hRect'.trans (by
    unfold c13EvenFiniteIntervalRemoteBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

theorem c13OddFiniteIntervalBuilderLoewnerRemote_entry_sq_sum_le
    (A M N : ℕ) (hN : 1920 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceModeSecond sourceZero : ℝ)
    (hSourceModeSecondNonneg : 0 ≤ sourceModeSecond)
    (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceModeSecond :
      (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) ≤
        sourceModeSecond)
    (hSourceZero :
      (∑ i : Fin M,
        c13HistoricalBuilderLoewnerSymbol
          (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceZero)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ)) :
    (∑ i : Fin M, ∑ j : Fin N,
      c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2) ≤
      c13OddFiniteIntervalRemoteBudget N sourceModeSecond sourceZero := by
  have hN0 : N ≠ 0 := by omega
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN hRawTarget
  have hTargetFourth := remote_symbol_sq_div_fourth_sum_le
    N hN0 c13HistoricalBuilderLoewnerSymbol (197 / 2000 : ℝ) hTarget
  have hInvSq := remote_inv_sq_sum_le N hN0
  have hEntry :
      ∀ i ∈ (Finset.univ : Finset (Fin M)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)),
          c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2 ≤
            (64 / 9 : ℝ) *
              (3 * ((finiteIntervalMode A M i : ℝ) ^ 2 *
                    c13HistoricalBuilderLoewnerSymbol
                      (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
                (3 / 2 : ℝ) *
                  (c13HistoricalBuilderLoewnerSymbol
                      (finiteIntervalMode A M i : ℝ) ^ 2 /
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := by
    intro i _hi j _hj
    unfold c13OddFiniteIntervalBuilderLoewnerRemoteEntry
    exact oddDifferenceKernel_oddParity_sq_le_weightedSeparated
      c13HistoricalBuilderLoewnerSymbol
      c13HistoricalBuilderLoewnerDiagonal
      (finiteIntervalMode A M i : ℝ)
      (((N + 1 + (j : ℕ) : ℕ) : ℝ))
      (finiteIntervalMode_nonneg A M i) (by positivity)
      (finiteIntervalMode_two_mul_le_remoteMode A M N hSep i j)
      c13HistoricalBuilderLoewnerSymbol_odd
  have hRect := rectangular_oddParity_sum_sq_le_weightedSeparated
    (Finset.univ : Finset (Fin M)) (Finset.univ : Finset (Fin N))
    c13HistoricalBuilderLoewnerSymbol c13HistoricalBuilderLoewnerDiagonal
    (fun i : Fin M => (finiteIntervalMode A M i : ℝ))
    (fun j : Fin N => ((N + 1 + (j : ℕ) : ℕ) : ℝ))
    (c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N) hEntry
  have hRect' :
      (∑ i : Fin M, ∑ j : Fin N,
          c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N i j ^ 2) ≤
        (64 / 9 : ℝ) *
          (3 * (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) *
              (∑ j : Fin N,
                c13HistoricalBuilderLoewnerSymbol
                    (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) +
            (3 / 2 : ℝ) * (∑ i : Fin M,
                c13HistoricalBuilderLoewnerSymbol
                    (finiteIntervalMode A M i : ℝ) ^ 2) *
              (∑ j : Fin N,
                1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2))) := by
    simpa using hRect
  have hFirst :
      (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
        sourceModeSecond * ((197 / 2000 : ℝ) / (N : ℝ) ^ 3) := by
    calc
      (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) *
          (∑ j : Fin N,
            c13HistoricalBuilderLoewnerSymbol
                (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
              (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) ≤
          sourceModeSecond *
            (∑ j : Fin N,
              c13HistoricalBuilderLoewnerSymbol
                  (((N + 1 + (j : ℕ) : ℕ) : ℝ)) ^ 2 /
                (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hSourceModeSecond (by positivity)
      _ ≤ sourceModeSecond * ((197 / 2000 : ℝ) / (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hTargetFourth hSourceModeSecondNonneg
  have hSecond :
      (∑ i : Fin M,
          c13HistoricalBuilderLoewnerSymbol
              (finiteIntervalMode A M i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
      sourceZero * (1 / (2 * (N : ℝ))) := by
    calc
      (∑ i : Fin M,
          c13HistoricalBuilderLoewnerSymbol
              (finiteIntervalMode A M i : ℝ) ^ 2) *
        (∑ j : Fin N,
          1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) ≤
          sourceZero *
            (∑ j : Fin N,
              1 / (((N + 1 + (j : ℕ) : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hSourceZero (by positivity)
      _ ≤ sourceZero * (1 / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hInvSq hSourceZeroNonneg
  have hInside := add_le_add
    (mul_le_mul_of_nonneg_left hFirst (by norm_num : (0 : ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left hSecond (by norm_num : (0 : ℝ) ≤ 3 / 2))
  exact hRect'.trans (by
    unfold c13OddFiniteIntervalRemoteBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

theorem c13EvenFiniteIntervalBuilderLoewnerRemote_crossEnergy_sq_le
    (A M N : ℕ) (hN : 1920 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceSecond : ℝ) (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceSecond :
      (∑ i : Fin M,
        (finiteIntervalMode A M i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceSecond)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (x : Fin M → ℝ) (y : Fin N → ℝ) :
    c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y ^ 2 ≤
      c13EvenFiniteIntervalRemoteBudget M N sourceSecond *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin M)) (Finset.univ : Finset (Fin N))
    (c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin M)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13EvenFiniteIntervalBuilderLoewnerRemoteEntry A M N ij.1 ij.2 ^ 2) ≤
          c13EvenFiniteIntervalRemoteBudget M N sourceSecond := by
    rw [Finset.sum_product]
    exact c13EvenFiniteIntervalBuilderLoewnerRemote_entry_sq_sum_le
      A M N hN hSep sourceSecond hSourceSecondNonneg hSourceSecond hRawTarget
  unfold c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddFiniteIntervalBuilderLoewnerRemote_crossEnergy_sq_le
    (A M N : ℕ) (hN : 1920 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceModeSecond sourceZero : ℝ)
    (hSourceModeSecondNonneg : 0 ≤ sourceModeSecond)
    (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceModeSecond :
      (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) ≤
        sourceModeSecond)
    (hSourceZero :
      (∑ i : Fin M,
        c13HistoricalBuilderLoewnerSymbol
          (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceZero)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (x : Fin M → ℝ) (y : Fin N → ℝ) :
    c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y ^ 2 ≤
      c13OddFiniteIntervalRemoteBudget N sourceModeSecond sourceZero *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin M)) (Finset.univ : Finset (Fin N))
    (c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin M)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13OddFiniteIntervalBuilderLoewnerRemoteEntry A M N ij.1 ij.2 ^ 2) ≤
          c13OddFiniteIntervalRemoteBudget N sourceModeSecond sourceZero := by
    rw [Finset.sum_product]
    exact c13OddFiniteIntervalBuilderLoewnerRemote_entry_sq_sum_le
      A M N hN hSep sourceModeSecond sourceZero
      hSourceModeSecondNonneg hSourceZeroNonneg
      hSourceModeSecond hSourceZero hRawTarget
  unfold c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13FiniteIntervalRemoteEvenBuilder_relative_of_sourceCertificate
    (A M N : ℕ) (hN : 15360 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceSecond sourceGap q : ℝ)
    (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceGap : 0 ≤ sourceGap) (hq : 0 ≤ q)
    (hSourceSecond :
      (∑ i : Fin M,
        (finiteIntervalMode A M i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceSecond)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (hBudget : c13EvenFiniteIntervalRemoteBudget M N sourceSecond ≤
      q * sourceGap * (24 / 5 : ℝ))
    (x : Fin M → ℝ) (y : Fin N → ℝ)
    (hSourceEnergy : sourceGap * (∑ i, x i ^ 2) ≤
      c13EvenBuilderFiniteIntervalEnergy A M x) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteEvenBuilderMatrix A M N) x y) ^ 2 ≤
      q * c13EvenBuilderFiniteIntervalEnergy A M x *
        c13EvenBuilderShellEnergy N N y := by
  have hTargetEnergy :=
    c13EvenBuilderShellEnergy_ge_twentyFourFifths_of_ge15360 N hN y
  have hCross :=
    c13EvenFiniteIntervalBuilderLoewnerRemote_crossEnergy_sq_le
      A M N (by omega) hSep sourceSecond hSourceSecondNonneg
      hSourceSecond hRawTarget x y
  rw [c13FiniteIntervalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  exact relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderFiniteIntervalEnergy A M x)
    (c13EvenBuilderShellEnergy N N y)
    (c13EvenFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y)
    sourceGap (24 / 5) (c13EvenFiniteIntervalRemoteBudget M N sourceSecond) q
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hSourceGap (by norm_num) hq (by positivity) (by positivity)
    hSourceEnergy (by simpa using hTargetEnergy) hCross hBudget

theorem c13FiniteIntervalRemoteOddBuilder_relative_of_sourceCertificate
    (A M N : ℕ) (hN : 15360 ≤ N) (hSep : 2 * (A + M) ≤ N)
    (sourceModeSecond sourceZero sourceGap q : ℝ)
    (hSourceModeSecondNonneg : 0 ≤ sourceModeSecond)
    (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceGap : 0 ≤ sourceGap) (hq : 0 ≤ q)
    (hSourceModeSecond :
      (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) ≤
        sourceModeSecond)
    (hSourceZero :
      (∑ i : Fin M,
        c13HistoricalBuilderLoewnerSymbol
          (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceZero)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (hBudget : c13OddFiniteIntervalRemoteBudget N
        sourceModeSecond sourceZero ≤ q * sourceGap * (24 / 5 : ℝ))
    (x : Fin M → ℝ) (y : Fin N → ℝ)
    (hSourceEnergy : sourceGap * (∑ i, x i ^ 2) ≤
      c13OddBuilderFiniteIntervalEnergy A M x) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteOddBuilderMatrix A M N) x y) ^ 2 ≤
      q * c13OddBuilderFiniteIntervalEnergy A M x *
        c13OddBuilderShellEnergy N N y := by
  have hTargetEnergy :=
    c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360 N hN y
  have hCross :=
    c13OddFiniteIntervalBuilderLoewnerRemote_crossEnergy_sq_le
      A M N (by omega) hSep sourceModeSecond sourceZero
      hSourceModeSecondNonneg hSourceZeroNonneg
      hSourceModeSecond hSourceZero hRawTarget x y
  rw [c13FiniteIntervalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  exact relativeCoupling_of_squaredNormBudget
    (c13OddBuilderFiniteIntervalEnergy A M x)
    (c13OddBuilderShellEnergy N N y)
    (c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy A M N x y)
    sourceGap (24 / 5)
    (c13OddFiniteIntervalRemoteBudget N sourceModeSecond sourceZero) q
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hSourceGap (by norm_num) hq (by positivity) (by positivity)
    hSourceEnergy (by simpa using hTargetEnergy) hCross hBudget

structure C13EvenFiniteIntervalSourceCertificate
    (A M : ℕ) (sourceSecond sourceGap : ℝ) : Prop where
  sourceSecondMoment :
    (∑ i : Fin M,
      (finiteIntervalMode A M i : ℝ) ^ 2 *
        c13HistoricalBuilderLoewnerSymbol
          (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceSecond
  sourceEnergyFloor : ∀ x : Fin M → ℝ,
    sourceGap * (∑ i, x i ^ 2) ≤
      c13EvenBuilderFiniteIntervalEnergy A M x

structure C13OddFiniteIntervalSourceCertificate
    (A M : ℕ) (sourceModeSecond sourceZero sourceGap : ℝ) : Prop where
  sourceModeSecondMoment :
    (∑ i : Fin M, (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceModeSecond
  sourceZeroMoment :
    (∑ i : Fin M,
      c13HistoricalBuilderLoewnerSymbol
        (finiteIntervalMode A M i : ℝ) ^ 2) ≤ sourceZero
  sourceEnergyFloor : ∀ x : Fin M → ℝ,
    sourceGap * (∑ i, x i ^ 2) ≤
      c13OddBuilderFiniteIntervalEnergy A M x

lemma c13EvenFiniteIntervalRemoteBudget_60_60_15360_le :
    c13EvenFiniteIntervalRemoteBudget 60 15360 107500 ≤
      (1 / 900 : ℝ) * (22 / 25) * (24 / 5) := by
  norm_num [c13EvenFiniteIntervalRemoteBudget]

lemma c13OddFiniteIntervalRemoteBudget_60_60_15360_le :
    c13OddFiniteIntervalRemoteBudget 15360 509410 (49 / 4) ≤
      (1 / 900 : ℝ) * (22 / 25) * (24 / 5) := by
  norm_num [c13OddFiniteIntervalRemoteBudget]

lemma c13EvenFiniteIntervalRemoteBudget_30_30_15360_le :
    c13EvenFiniteIntervalRemoteBudget 30 15360 12110 ≤
      (1 / 900 : ℝ) * (49 / 100) * (24 / 5) := by
  norm_num [c13EvenFiniteIntervalRemoteBudget]

lemma c13OddFiniteIntervalRemoteBudget_30_30_15360_le :
    c13OddFiniteIntervalRemoteBudget 15360 64355 (27 / 5) ≤
      (1 / 900 : ℝ) * (49 / 100) * (24 / 5) := by
  norm_num [c13OddFiniteIntervalRemoteBudget]

lemma c13EvenFiniteIntervalRemoteBudget_20_10_15360_le :
    c13EvenFiniteIntervalRemoteBudget 10 15360 1530 ≤
      (1 / 900 : ℝ) * (19 / 100) * (24 / 5) := by
  norm_num [c13EvenFiniteIntervalRemoteBudget]

lemma c13OddFiniteIntervalRemoteBudget_20_10_15360_le :
    c13OddFiniteIntervalRemoteBudget 15360 6585 (47 / 20) ≤
      (1 / 900 : ℝ) * (19 / 100) * (24 / 5) := by
  norm_num [c13OddFiniteIntervalRemoteBudget]

lemma v23_lowFrontier_afterResidualIntervalChannels :
    (2 / 27 : ℝ) - 7 / 120 - 1 / 350 - 1 / 500 - 1 / 795 -
        3 * (1 / 900) = 63031 / 10017000 := by
  norm_num

lemma v23_lowFrontier_afterResidualIntervals_and_oddFixed :
    (2 / 27 : ℝ) - 7 / 120 - 1 / 350 - 1 / 500 - 1 / 795 -
        3 * (1 / 900) - 1 / 3072 = 7650593 / 1282176000 := by
  norm_num

theorem c13FiniteIntervalRemoteEvenBuilder_60_60_15360_relative_oneOver900
    (hSource : C13EvenFiniteIntervalSourceCertificate
      60 60 107500 (22 / 25 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 60 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteEvenBuilderMatrix 60 60 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13EvenBuilderFiniteIntervalEnergy 60 60 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteEvenBuilder_relative_of_sourceCertificate
    60 60 15360 (by norm_num) (by norm_num)
    107500 (22 / 25) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteIntervalRemoteBudget_60_60_15360_le x y
    (hSource.sourceEnergyFloor x)

theorem c13FiniteIntervalRemoteOddBuilder_60_60_15360_relative_oneOver900
    (hSource : C13OddFiniteIntervalSourceCertificate
      60 60 509410 (49 / 4 : ℝ) (22 / 25 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 60 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteOddBuilderMatrix 60 60 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13OddBuilderFiniteIntervalEnergy 60 60 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteOddBuilder_relative_of_sourceCertificate
    60 60 15360 (by norm_num) (by norm_num)
    509410 (49 / 4) (22 / 25) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceModeSecondMoment hSource.sourceZeroMoment hRawTarget
    c13OddFiniteIntervalRemoteBudget_60_60_15360_le x y
    (hSource.sourceEnergyFloor x)

theorem c13FiniteIntervalRemoteEvenBuilder_30_30_15360_relative_oneOver900
    (hSource : C13EvenFiniteIntervalSourceCertificate
      30 30 12110 (49 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 30 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteEvenBuilderMatrix 30 30 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13EvenBuilderFiniteIntervalEnergy 30 30 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteEvenBuilder_relative_of_sourceCertificate
    30 30 15360 (by norm_num) (by norm_num)
    12110 (49 / 100) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteIntervalRemoteBudget_30_30_15360_le x y
    (hSource.sourceEnergyFloor x)

theorem c13FiniteIntervalRemoteOddBuilder_30_30_15360_relative_oneOver900
    (hSource : C13OddFiniteIntervalSourceCertificate
      30 30 64355 (27 / 5 : ℝ) (49 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 30 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteOddBuilderMatrix 30 30 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13OddBuilderFiniteIntervalEnergy 30 30 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteOddBuilder_relative_of_sourceCertificate
    30 30 15360 (by norm_num) (by norm_num)
    64355 (27 / 5) (49 / 100) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceModeSecondMoment hSource.sourceZeroMoment hRawTarget
    c13OddFiniteIntervalRemoteBudget_30_30_15360_le x y
    (hSource.sourceEnergyFloor x)

theorem c13FiniteIntervalRemoteEvenBuilder_20_10_15360_relative_oneOver900
    (hSource : C13EvenFiniteIntervalSourceCertificate
      20 10 1530 (19 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 10 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteEvenBuilderMatrix 20 10 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13EvenBuilderFiniteIntervalEnergy 20 10 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteEvenBuilder_relative_of_sourceCertificate
    20 10 15360 (by norm_num) (by norm_num)
    1530 (19 / 100) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteIntervalRemoteBudget_20_10_15360_le x y
    (hSource.sourceEnergyFloor x)

theorem c13FiniteIntervalRemoteOddBuilder_20_10_15360_relative_oneOver900
    (hSource : C13OddFiniteIntervalSourceCertificate
      20 10 6585 (47 / 20 : ℝ) (19 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 10 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13FiniteIntervalRemoteOddBuilderMatrix 20 10 15360) x y) ^ 2 ≤
      (1 / 900 : ℝ) * c13OddBuilderFiniteIntervalEnergy 20 10 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13FiniteIntervalRemoteOddBuilder_relative_of_sourceCertificate
    20 10 15360 (by norm_num) (by norm_num)
    6585 (47 / 20) (19 / 100) (1 / 900)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceModeSecondMoment hSource.sourceZeroMoment hRawTarget
    c13OddFiniteIntervalRemoteBudget_20_10_15360_le x y
    (hSource.sourceEnergyFloor x)

end RiemannCvs.V23BoundaryWeylMainline
