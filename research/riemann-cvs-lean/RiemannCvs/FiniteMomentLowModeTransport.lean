import RiemannCvs.SharpParityLowFrontierTransport

/-!
# Finite source moments into the analytic remote shell

The uniform low-frontier theorem starts at source base `B = 960`.  For the
three standard positive source shells immediately below it, carrying the full
finite Schur certificate through three growing target matrices is unnecessary.
The cross kernel only needs a finite source symbol moment and a finite source
energy floor; all target moments and the target energy floor are already
analytic at `T = 15360`.

This file isolates that alternative bridge.  No finite moment or eigenvalue is
asserted without a premise.  The final specializations show exactly which
small, fixed certificates are sufficient for `B = 480, 240, 120`.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def c13EvenFiniteMomentRemoteBudget
    (B N : ℕ) (sourceSecond : ℝ) : ℝ :=
  (64 / 9 : ℝ) *
    ((3 / 2 : ℝ) * ((B : ℝ) * ((197 / 2000 : ℝ) / (N : ℝ))) +
      3 * (sourceSecond * (1 / (2 * (N : ℝ) ^ 3))))

noncomputable def c13OddFiniteMomentRemoteBudget
    (B N : ℕ) (sourceZero : ℝ) : ℝ :=
  (64 / 9 : ℝ) *
    (3 * ((4 * (B : ℝ) ^ 3) *
      ((197 / 2000 : ℝ) / (N : ℝ) ^ 3)) +
      (3 / 2 : ℝ) * (sourceZero * (1 / (2 * (N : ℝ)))))

/-- The even remote Frobenius budget with the finite source second moment left
as an explicit premise.  This removes every lower bound on `B`. -/
theorem c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_of_sourceSecondMoment
    (B N : ℕ) (hN : 1920 ≤ N) (hBN : 4 * B ≤ N)
    (sourceSecond : ℝ) (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceSecond :
      (∑ i : Fin B,
        (historicalBandMode B i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ) ^ 2) ≤ sourceSecond)
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
      c13EvenFiniteMomentRemoteBudget B N sourceSecond := by
  have hN0 : N ≠ 0 := by omega
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN hRawTarget
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
      sourceSecond * (1 / (2 * (N : ℝ) ^ 3)) := by
    calc
      (∑ i : Fin B,
          (historicalBandMode B i : ℝ) ^ 2 *
            c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
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
    unfold c13EvenFiniteMomentRemoteBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

/-- Odd companion: the only finite symbol input is the unweighted source
square sum; the elementary source-mode second moment remains analytic. -/
theorem c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_of_sourceZeroMoment
    (B N : ℕ) (hN : 1920 ≤ N) (hBN : 4 * B ≤ N)
    (sourceZero : ℝ) (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceZero :
      (∑ i : Fin B,
        c13HistoricalBuilderLoewnerSymbol
          (historicalBandMode B i : ℝ) ^ 2) ≤ sourceZero)
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
      c13OddFiniteMomentRemoteBudget B N sourceZero := by
  have hN0 : N ≠ 0 := by omega
  have hSourceModeSq := historicalBandMode_sq_sum_le_four_mul_cube B
  have hTarget := c13HistoricalBuilderLoewnerSymbol_remote_weighted_sum_le
    N hN hRawTarget
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
      sourceZero * (1 / (2 * (N : ℝ))) := by
    calc
      (∑ i : Fin B,
          c13HistoricalBuilderLoewnerSymbol
              (historicalBandMode B i : ℝ) ^ 2) *
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
    unfold c13OddFiniteMomentRemoteBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64 / 9)
    simpa [mul_assoc] using hInside)

/-- Cauchy converts the even finite-moment Frobenius estimate into a bilinear
cross-energy estimate. -/
theorem c13EvenHistoricalBuilderLoewnerRemote_crossEnergy_sq_le_of_sourceSecondMoment
    (B N : ℕ) (hN : 1920 ≤ N) (hBN : 4 * B ≤ N)
    (sourceSecond : ℝ) (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceSecond :
      (∑ i : Fin B,
        (historicalBandMode B i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ) ^ 2) ≤ sourceSecond)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      c13EvenFiniteMomentRemoteBudget B N sourceSecond *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    (c13EvenHistoricalBuilderLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13EvenHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
          c13EvenFiniteMomentRemoteBudget B N sourceSecond := by
    rw [Finset.sum_product]
    exact c13EvenHistoricalBuilderLoewnerRemote_entry_sq_sum_le_of_sourceSecondMoment
      B N hN hBN sourceSecond hSourceSecondNonneg hSourceSecond hRawTarget
  unfold c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

/-- Odd bilinear companion. -/
theorem c13OddHistoricalBuilderLoewnerRemote_crossEnergy_sq_le_of_sourceZeroMoment
    (B N : ℕ) (hN : 1920 ≤ N) (hBN : 4 * B ≤ N)
    (sourceZero : ℝ) (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceZero :
      (∑ i : Fin B,
        c13HistoricalBuilderLoewnerSymbol
          (historicalBandMode B i : ℝ) ^ 2) ≤ sourceZero)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      c13OddFiniteMomentRemoteBudget B N sourceZero *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B)) (Finset.univ : Finset (Fin N))
    (c13OddHistoricalBuilderLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13OddHistoricalBuilderLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
          c13OddFiniteMomentRemoteBudget B N sourceZero := by
    rw [Finset.sum_product]
    exact c13OddHistoricalBuilderLoewnerRemote_entry_sq_sum_le_of_sourceZeroMoment
      B N hN hBN sourceZero hSourceZeroNonneg hSourceZero hRawTarget
  unfold c13OddHistoricalBuilderLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

/-- Full even builder relative bound from one finite source moment, one finite
source energy floor, and the already analytic target certificate. -/
theorem c13HistoricalRemoteEvenBuilder_relative_of_finiteSourceMoment
    (B N : ℕ) (hN : 15360 ≤ N) (hBN : 4 * B ≤ N)
    (sourceSecond sourceGap q : ℝ)
    (hSourceSecondNonneg : 0 ≤ sourceSecond)
    (hSourceGap : 0 ≤ sourceGap) (hq : 0 ≤ q)
    (hSourceSecond :
      (∑ i : Fin B,
        (historicalBandMode B i : ℝ) ^ 2 *
          c13HistoricalBuilderLoewnerSymbol
            (historicalBandMode B i : ℝ) ^ 2) ≤ sourceSecond)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (hBudget : c13EvenFiniteMomentRemoteBudget B N sourceSecond ≤
      q * sourceGap * (24 / 5 : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ)
    (hSourceEnergy : sourceGap * (∑ i, x i ^ 2) ≤
      c13EvenBuilderShellEnergy B B x) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B N) x y) ^ 2 ≤
      q * c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy N N y := by
  have hTargetEnergy :=
    c13EvenBuilderShellEnergy_ge_twentyFourFifths_of_ge15360 N hN y
  have hCross :=
    c13EvenHistoricalBuilderLoewnerRemote_crossEnergy_sq_le_of_sourceSecondMoment
      B N (by omega) hBN sourceSecond hSourceSecondNonneg hSourceSecond
      hRawTarget x y
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq_fullLoewner]
  exact relativeCoupling_of_squaredNormBudget
    (c13EvenBuilderShellEnergy B B x) (c13EvenBuilderShellEnergy N N y)
    (c13EvenHistoricalBuilderLoewnerRemoteCrossEnergy B N x y)
    sourceGap (24 / 5) (c13EvenFiniteMomentRemoteBudget B N sourceSecond) q
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hSourceGap (by norm_num) hq (by positivity) (by positivity)
    hSourceEnergy (by simpa using hTargetEnergy) hCross hBudget

/-- Odd full-builder companion. -/
theorem c13HistoricalRemoteOddBuilder_relative_of_finiteSourceMoment
    (B N : ℕ) (hN : 15360 ≤ N) (hBN : 4 * B ≤ N)
    (sourceZero sourceGap q : ℝ)
    (hSourceZeroNonneg : 0 ≤ sourceZero)
    (hSourceGap : 0 ≤ sourceGap) (hq : 0 ≤ q)
    (hSourceZero :
      (∑ i : Fin B,
        c13HistoricalBuilderLoewnerSymbol
          (historicalBandMode B i : ℝ) ^ 2) ≤ sourceZero)
    (hRawTarget :
      (∑ j ∈ Finset.range N,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (N : ℝ))
    (hBudget : c13OddFiniteMomentRemoteBudget B N sourceZero ≤
      q * sourceGap * (24 / 5 : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ)
    (hSourceEnergy : sourceGap * (∑ i, x i ^ 2) ≤
      c13OddBuilderShellEnergy B B x) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B N) x y) ^ 2 ≤
      q * c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy N N y := by
  have hTargetEnergy :=
    c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360 N hN y
  have hCross :=
    c13OddHistoricalBuilderLoewnerRemote_crossEnergy_sq_le_of_sourceZeroMoment
      B N (by omega) hBN sourceZero hSourceZeroNonneg hSourceZero
      hRawTarget x y
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  exact relativeCoupling_of_squaredNormBudget
    (c13OddBuilderShellEnergy B B x) (c13OddBuilderShellEnergy N N y)
    (c13OddHistoricalBuilderLoewnerRemoteCrossEnergy B N x y)
    sourceGap (24 / 5) (c13OddFiniteMomentRemoteBudget B N sourceZero) q
    (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hSourceGap (by norm_num) hq (by positivity) (by positivity)
    hSourceEnergy (by simpa using hTargetEnergy) hCross hBudget

/-! Exact rational endpoints selected by the finite-moment route diagnostic.
These lemmas contain no numerical premise; they verify that the proposed small
source certificates fit the desired relative budgets. -/

lemma c13EvenFiniteMomentRemoteBudget_480_15360_le :
    c13EvenFiniteMomentRemoteBudget 480 15360 49740000 ≤
      (1 / 350 : ℝ) * (129 / 50) * (24 / 5) := by
  norm_num [c13EvenFiniteMomentRemoteBudget]

lemma c13OddFiniteMomentRemoteBudget_480_15360_le :
    c13OddFiniteMomentRemoteBudget 480 15360 92 ≤
      (1 / 350 : ℝ) * (129 / 50) * (24 / 5) := by
  norm_num [c13OddFiniteMomentRemoteBudget]

lemma c13EvenFiniteMomentRemoteBudget_240_15360_le :
    c13EvenFiniteMomentRemoteBudget 240 15360 6274000 ≤
      (1 / 500 : ℝ) * (177 / 100) * (24 / 5) := by
  norm_num [c13EvenFiniteMomentRemoteBudget]

lemma c13OddFiniteMomentRemoteBudget_240_15360_le :
    c13OddFiniteMomentRemoteBudget 240 15360 47 ≤
      (1 / 500 : ℝ) * (177 / 100) * (24 / 5) := by
  norm_num [c13OddFiniteMomentRemoteBudget]

lemma c13EvenFiniteMomentRemoteBudget_120_15360_le :
    c13EvenFiniteMomentRemoteBudget 120 15360 735000 ≤
      (1 / 795 : ℝ) * (137 / 100) * (24 / 5) := by
  norm_num [c13EvenFiniteMomentRemoteBudget]

lemma c13OddFiniteMomentRemoteBudget_120_15360_le :
    c13OddFiniteMomentRemoteBudget 120 15360 (219 / 10) ≤
      (1 / 795 : ℝ) * (137 / 100) * (24 / 5) := by
  norm_num [c13OddFiniteMomentRemoteBudget]

/-- After the three finite-moment channels are charged, more than `0.0096`
remains for `[21,120]` and the fixed base. -/
lemma v23_lowFrontier_afterThreeFiniteMomentChannels :
    (2 / 27 : ℝ) - 7 / 120 - 1 / 350 - 1 / 500 - 1 / 795 =
      96421 / 10017000 := by
  norm_num


/-- A compact finite certificate for an even standard source shell.  Its matrix
has dimension only `B`; no remote target matrix is part of the certificate. -/
structure C13EvenFiniteSourceMomentCertificate
    (B : ℕ) (sourceSecond sourceGap : ℝ) : Prop where
  sourceSecondMoment :
    (∑ i : Fin B,
      (historicalBandMode B i : ℝ) ^ 2 *
        c13HistoricalBuilderLoewnerSymbol
          (historicalBandMode B i : ℝ) ^ 2) ≤ sourceSecond
  sourceEnergyFloor : ∀ x : Fin B → ℝ,
    sourceGap * (∑ i, x i ^ 2) ≤ c13EvenBuilderShellEnergy B B x

/-- Odd finite source certificate. -/
structure C13OddFiniteSourceMomentCertificate
    (B : ℕ) (sourceZero sourceGap : ℝ) : Prop where
  sourceZeroMoment :
    (∑ i : Fin B,
      c13HistoricalBuilderLoewnerSymbol
        (historicalBandMode B i : ℝ) ^ 2) ≤ sourceZero
  sourceEnergyFloor : ∀ x : Fin B → ℝ,
    sourceGap * (∑ i, x i ^ 2) ≤ c13OddBuilderShellEnergy B B x

/-- The literal `B=480` even source shell reaches target base `15360` with a
`1/350` relative coefficient from a 480-dimensional source certificate. -/
theorem c13HistoricalRemoteEvenBuilder_480_15360_relative_oneOver350
    (hSource : C13EvenFiniteSourceMomentCertificate
      480 49740000 (129 / 50 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 480 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix 480 15360) x y) ^ 2 ≤
      (1 / 350 : ℝ) * c13EvenBuilderShellEnergy 480 480 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteEvenBuilder_relative_of_finiteSourceMoment
    480 15360 (by norm_num) (by norm_num)
    49740000 (129 / 50) (1 / 350)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteMomentRemoteBudget_480_15360_le x y
    (hSource.sourceEnergyFloor x)

/-- Odd `B=480` companion. -/
theorem c13HistoricalRemoteOddBuilder_480_15360_relative_oneOver350
    (hSource : C13OddFiniteSourceMomentCertificate 480 92 (129 / 50 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 480 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix 480 15360) x y) ^ 2 ≤
      (1 / 350 : ℝ) * c13OddBuilderShellEnergy 480 480 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteOddBuilder_relative_of_finiteSourceMoment
    480 15360 (by norm_num) (by norm_num)
    92 (129 / 50) (1 / 350)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceZeroMoment hRawTarget
    c13OddFiniteMomentRemoteBudget_480_15360_le x y
    (hSource.sourceEnergyFloor x)

/-- The `B=240` even source shell needs only a 240-dimensional source
certificate and spends `1/500`. -/
theorem c13HistoricalRemoteEvenBuilder_240_15360_relative_oneOver500
    (hSource : C13EvenFiniteSourceMomentCertificate
      240 6274000 (177 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 240 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix 240 15360) x y) ^ 2 ≤
      (1 / 500 : ℝ) * c13EvenBuilderShellEnergy 240 240 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteEvenBuilder_relative_of_finiteSourceMoment
    240 15360 (by norm_num) (by norm_num)
    6274000 (177 / 100) (1 / 500)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteMomentRemoteBudget_240_15360_le x y
    (hSource.sourceEnergyFloor x)

/-- Odd `B=240` companion. -/
theorem c13HistoricalRemoteOddBuilder_240_15360_relative_oneOver500
    (hSource : C13OddFiniteSourceMomentCertificate 240 47 (177 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 240 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix 240 15360) x y) ^ 2 ≤
      (1 / 500 : ℝ) * c13OddBuilderShellEnergy 240 240 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteOddBuilder_relative_of_finiteSourceMoment
    240 15360 (by norm_num) (by norm_num)
    47 (177 / 100) (1 / 500)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceZeroMoment hRawTarget
    c13OddFiniteMomentRemoteBudget_240_15360_le x y
    (hSource.sourceEnergyFloor x)

/-- The `B=120` even source shell spends `1/795`. -/
theorem c13HistoricalRemoteEvenBuilder_120_15360_relative_oneOver795
    (hSource : C13EvenFiniteSourceMomentCertificate
      120 735000 (137 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 120 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix 120 15360) x y) ^ 2 ≤
      (1 / 795 : ℝ) * c13EvenBuilderShellEnergy 120 120 x *
        c13EvenBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteEvenBuilder_relative_of_finiteSourceMoment
    120 15360 (by norm_num) (by norm_num)
    735000 (137 / 100) (1 / 795)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceSecondMoment hRawTarget
    c13EvenFiniteMomentRemoteBudget_120_15360_le x y
    (hSource.sourceEnergyFloor x)

/-- Odd `B=120` companion. -/
theorem c13HistoricalRemoteOddBuilder_120_15360_relative_oneOver795
    (hSource : C13OddFiniteSourceMomentCertificate
      120 (219 / 10 : ℝ) (137 / 100 : ℝ))
    (hRawTarget :
      (∑ j ∈ Finset.range 15360,
        logarithmicCombinedSymbol
            (logarithmicArchimedeanSymbol 13) 13
            c13PrimePowerLocation c13PrimePowerBase
            (((15360 + 1 + j : ℕ) : ℝ)) ^ 2 /
          (((15360 + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        (97 / 100 : ℝ) / (15360 : ℝ))
    (x : Fin 120 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix 120 15360) x y) ^ 2 ≤
      (1 / 795 : ℝ) * c13OddBuilderShellEnergy 120 120 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13HistoricalRemoteOddBuilder_relative_of_finiteSourceMoment
    120 15360 (by norm_num) (by norm_num)
    (219 / 10) (137 / 100) (1 / 795)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceZeroMoment hRawTarget
    c13OddFiniteMomentRemoteBudget_120_15360_le x y
    (hSource.sourceEnergyFloor x)

end RiemannCvs.V23BoundaryWeylMainline
