import RiemannCvs.FirstAnalyticMultiblockBudget

/-!
# Concrete historical combined-Loewner half transport

This module implements the source grouping selected by the cutoff-13
`N = 15360` diagnostic, but every theorem below is symbolic and checked by the
Lean kernel.  For a historical source shell `(B,2B]` and a remote target shell
`(N,2N]`, it keeps the Archimedean and finite-prime difference quotients inside
one Fourier-normalized odd Loewner symbol and separates only the rational pole.

The main chain is:

1. identify the literal cutoff-13 combined symbol and diagonal;
2. prove even/odd row-square and rectangular cross-form estimates for every
   separated pair `(B,2B]` to `(N,2N]` with `4B <= N`;
3. prove that doubling only the target shell halves the fixed-source Loewner
   matrix budget exactly, then normalize by the already closed dynamic shell
   coercivity floors;
4. identify the actual positive-mode builder cross entry and cross energy as
   `pole - combinedLoewner`;
5. exploit the stronger shell-to-shell pole masses `O(1/B)` and `O(1/N)`, rather
   than the older fixed-prefix bound, and prove exact pole half transport;
6. reassemble the complete actual builder at the amplitude level, retaining
   the prime/Archimedean cancellation and avoiding the coarse factor-two
   triangle estimate.

The combined-Loewner conclusions still expose two honest scalar inputs:

* a weighted combined-symbol square estimate on the next target shell;
* the preceding rectangular symbol budget relative to the two coercive gaps.

Those inputs are exactly where the tracked Arb source certificate and the
finite bridge data must eventually be internalized or consumed.  The pole
factorization, dynamic-gap monotonicity, real matrix identities, half-transport
algebra, and actual shell-energy normalization in this file have no numerical
oracle premise.  This module does not assert the infinite boundary--Weyl limit
or the Riemann hypothesis.
-/
noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def c13HistoricalCombinedLoewnerSymbol : ℝ → ℝ :=
  fourierNormalizedSymbol
    (logarithmicCombinedSymbol
      (logarithmicArchimedeanSymbol 13) 13
      c13PrimePowerLocation c13PrimePowerBase)

noncomputable def c13HistoricalCombinedLoewnerDiagonal : ℝ → ℝ :=
  fun x => logarithmicArchimedeanDiagonal 13 x +
    finiteLogarithmicPrimeDiagonal 13
      c13PrimePowerLocation c13PrimePowerBase x

theorem c13HistoricalCombinedLoewnerSymbol_odd :
    Function.Odd c13HistoricalCombinedLoewnerSymbol := by
  exact fourierNormalizedSymbol_odd _
    (logarithmicCombinedSymbol_odd
      (logarithmicArchimedeanSymbol 13) 13
      c13PrimePowerLocation c13PrimePowerBase
      (logarithmicArchimedeanSymbol_odd 13))

/-! The same source band may be transported to any later dyadic shell.
The parameter `N` is both the left cutoff and the number of target modes in
`(N,2N]`; the first post-frontier historical channel has `N = 4B`. -/

noncomputable def c13EvenHistoricalLoewnerRemoteNatEntry
    (B N : ℕ) (i : Fin B) (j : ℕ) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalCombinedLoewnerSymbol
      c13HistoricalCombinedLoewnerDiagonal
      (historicalBandMode B i : ℝ) ((N + 1 + j : ℕ) : ℝ) +
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalCombinedLoewnerSymbol
      c13HistoricalCombinedLoewnerDiagonal
      (historicalBandMode B i : ℝ) (-((N + 1 + j : ℕ) : ℝ))

noncomputable def c13OddHistoricalLoewnerRemoteNatEntry
    (B N : ℕ) (i : Fin B) (j : ℕ) : ℝ :=
  CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalCombinedLoewnerSymbol
      c13HistoricalCombinedLoewnerDiagonal
      (historicalBandMode B i : ℝ) ((N + 1 + j : ℕ) : ℝ) -
    CvSParityDisplacement.oddDifferenceKernel
      c13HistoricalCombinedLoewnerSymbol
      c13HistoricalCombinedLoewnerDiagonal
      (historicalBandMode B i : ℝ) (-((N + 1 + j : ℕ) : ℝ))

noncomputable def c13EvenHistoricalLoewnerRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  c13EvenHistoricalLoewnerRemoteNatEntry B N i j

noncomputable def c13OddHistoricalLoewnerRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  c13OddHistoricalLoewnerRemoteNatEntry B N i j

lemma c13_historicalBandMode_two_mul_le_remoteMode
    (B N : ℕ) (hBN : 4 * B ≤ N) (i : Fin B) (j : ℕ) :
    2 * (historicalBandMode B i : ℝ) ≤ ((N + 1 + j : ℕ) : ℝ) := by
  exact_mod_cast (show 2 * historicalBandMode B i ≤ N + 1 + j by
    unfold historicalBandMode
    have hi : (i : ℕ) < B := i.isLt
    omega)

theorem c13EvenHistoricalLoewnerRemote_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j ∈ Finset.range N,
        c13EvenHistoricalLoewnerRemoteNatEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalCombinedLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  apply evenParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    c13HistoricalCombinedLoewnerSymbol
    c13HistoricalCombinedLoewnerDiagonal
    (historicalBandMode B i : ℝ) N hN C
  · positivity
  · exact fun j _hj => c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j
  · exact c13HistoricalCombinedLoewnerSymbol_odd
  · exact hSymbol

theorem c13OddHistoricalLoewnerRemote_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j ∈ Finset.range N,
        c13OddHistoricalLoewnerRemoteNatEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalCombinedLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  apply oddParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    c13HistoricalCombinedLoewnerSymbol
    c13HistoricalCombinedLoewnerDiagonal
    (historicalBandMode B i : ℝ) N hN C
  · positivity
  · exact fun j _hj => c13_historicalBandMode_two_mul_le_remoteMode B N hBN i j
  · exact c13HistoricalCombinedLoewnerSymbol_odd
  · exact hSymbol

theorem c13EvenHistoricalLoewnerRemote_fin_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j : Fin N, c13EvenHistoricalLoewnerRemoteEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalCombinedLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  change (∑ j : Fin N,
    c13EvenHistoricalLoewnerRemoteNatEntry B N i (j : ℕ) ^ 2) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => c13EvenHistoricalLoewnerRemoteNatEntry B N i j ^ 2) N]
  exact c13EvenHistoricalLoewnerRemote_row_sq_le B N hN hBN C hSymbol i

theorem c13OddHistoricalLoewnerRemote_fin_row_sq_le
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (i : Fin B) :
    (∑ j : Fin N, c13OddHistoricalLoewnerRemoteEntry B N i j ^ 2) ≤
      32 * (C / (N : ℝ) +
        c13HistoricalCombinedLoewnerSymbol (historicalBandMode B i : ℝ) ^ 2 /
          (2 * (N : ℝ))) := by
  change (∑ j : Fin N,
    c13OddHistoricalLoewnerRemoteNatEntry B N i (j : ℕ) ^ 2) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => c13OddHistoricalLoewnerRemoteNatEntry B N i j ^ 2) N]
  exact c13OddHistoricalLoewnerRemote_row_sq_le B N hN hBN C hSymbol i

noncomputable def c13EvenHistoricalLoewnerRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13EvenHistoricalLoewnerRemoteEntry B N ij.1 ij.2 * (x ij.1 * y ij.2)

noncomputable def c13OddHistoricalLoewnerRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13OddHistoricalLoewnerRemoteEntry B N ij.1 ij.2 * (x ij.1 * y ij.2)

theorem c13EvenHistoricalLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13EvenHistoricalLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin N))
    (c13EvenHistoricalLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13EvenHistoricalLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
        rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
    rw [Finset.sum_product]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin B)),
          ∑ j ∈ (Finset.univ : Finset (Fin N)),
            c13EvenHistoricalLoewnerRemoteEntry B N i j ^ 2) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin B)),
            32 * (C / (N : ℝ) +
              c13HistoricalCombinedLoewnerSymbol
                  (historicalBandMode B i : ℝ) ^ 2 /
                (2 * (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa using c13EvenHistoricalLoewnerRemote_fin_row_sq_le
          B N hN hBN C hSymbol i
      _ = rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
        unfold rectangularSymbolSquareBudget
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        rw [← Finset.mul_sum, Finset.sum_div]
        ring
  unfold c13EvenHistoricalLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

theorem c13OddHistoricalLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C : ℝ)
    (hSymbol :
      (∑ j ∈ Finset.range N,
          c13HistoricalCombinedLoewnerSymbol
              (((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / (N : ℝ))
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13OddHistoricalLoewnerRemoteCrossEnergy B N x y ^ 2 ≤
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin B))
    (Finset.univ : Finset (Fin N))
    (c13OddHistoricalLoewnerRemoteEntry B N) x y
  have hEntries :
      (∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13OddHistoricalLoewnerRemoteEntry B N ij.1 ij.2 ^ 2) ≤
        rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
    rw [Finset.sum_product]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin B)),
          ∑ j ∈ (Finset.univ : Finset (Fin N)),
            c13OddHistoricalLoewnerRemoteEntry B N i j ^ 2) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin B)),
            32 * (C / (N : ℝ) +
              c13HistoricalCombinedLoewnerSymbol
                  (historicalBandMode B i : ℝ) ^ 2 /
                (2 * (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa using c13OddHistoricalLoewnerRemote_fin_row_sq_le
          B N hN hBN C hSymbol i
      _ = rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C := by
        unfold rectangularSymbolSquareBudget
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        rw [← Finset.mul_sum, Finset.sum_div]
        ring
  unfold c13OddHistoricalLoewnerRemoteCrossEnergy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

/-- Once one historical Loewner channel fits a relative coefficient `q`,
doubling only its target shell transports the concrete even cross form with
coefficient `q/2`.  The Archimedean and prime pieces remain inside the same
combined symbol throughout. -/
theorem c13EvenHistoricalCombinedLoewner_halfTransport
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C q : ℝ)
    (lowGap highGap nextLowGap nextHighGap : ℝ)
    (lowEnergy nextHighEnergy : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q) (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ)
    (hLowEnergy : nextLowGap * (∑ i, x i ^ 2) ≤ lowEnergy)
    (hNextHighEnergy : nextHighGap * (∑ j, y j ^ 2) ≤ nextHighEnergy)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * lowGap * highGap) :
    c13EvenHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) * lowEnergy * nextHighEnergy := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hNextHighGap : 0 ≤ nextHighGap := hHighGap.trans hHighGrowth
  have hCross := c13EvenHistoricalLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    B (2 * N) (by omega) (by omega) C hSymbolNext x y
  have hBudget := rectangularSymbolSquareBudget_halfTransport
    (Finset.univ : Finset (Fin B))
    (fun i => c13HistoricalCombinedLoewnerSymbol
      (historicalBandMode B i : ℝ))
    N C q lowGap highGap nextLowGap nextHighGap
    hN hq hLowGap hHighGap hLowGrowth hHighGrowth hPreviousBudget
  exact relativeCoupling_of_squaredNormBudget
    lowEnergy nextHighEnergy
    (c13EvenHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y)
    nextLowGap nextHighGap
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalCombinedLoewnerSymbol
        (historicalBandMode B i : ℝ)) (2 * N) C)
    (q / 2) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hNextLowGap hNextHighGap (div_nonneg hq (by norm_num))
    (by positivity) (by positivity) hLowEnergy hNextHighEnergy hCross hBudget

/-- Odd-parity companion of the concrete combined-Loewner half transport. -/
theorem c13OddHistoricalCombinedLoewner_halfTransport
    (B N : ℕ) (hN : N ≠ 0) (hBN : 4 * B ≤ N) (C q : ℝ)
    (lowGap highGap nextLowGap nextHighGap : ℝ)
    (lowEnergy nextHighEnergy : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q) (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ)
    (hLowEnergy : nextLowGap * (∑ i, x i ^ 2) ≤ lowEnergy)
    (hNextHighEnergy : nextHighGap * (∑ j, y j ^ 2) ≤ nextHighEnergy)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * lowGap * highGap) :
    c13OddHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) * lowEnergy * nextHighEnergy := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hNextHighGap : 0 ≤ nextHighGap := hHighGap.trans hHighGrowth
  have hCross := c13OddHistoricalLoewnerRemoteCrossEnergy_sq_le_symbolBudget
    B (2 * N) (by omega) (by omega) C hSymbolNext x y
  have hBudget := rectangularSymbolSquareBudget_halfTransport
    (Finset.univ : Finset (Fin B))
    (fun i => c13HistoricalCombinedLoewnerSymbol
      (historicalBandMode B i : ℝ))
    N C q lowGap highGap nextLowGap nextHighGap
    hN hq hLowGap hHighGap hLowGrowth hHighGrowth hPreviousBudget
  exact relativeCoupling_of_squaredNormBudget
    lowEnergy nextHighEnergy
    (c13OddHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y)
    nextLowGap nextHighGap
    (rectangularSymbolSquareBudget
      (Finset.univ : Finset (Fin B))
      (fun i => c13HistoricalCombinedLoewnerSymbol
        (historicalBandMode B i : ℝ)) (2 * N) C)
    (q / 2) (∑ i, x i ^ 2) (∑ j, y j ^ 2)
    hNextLowGap hNextHighGap (div_nonneg hq (by norm_num))
    (by positivity) (by positivity) hLowEnergy hNextHighEnergy hCross hBudget

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

/-- The premise-free cutoff-13 shell gap grows with the left endpoint. -/
theorem c13ShellDynamicGap_mono
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    c13ShellDynamicGap M ≤ c13ShellDynamicGap N := by
  have hMR : (0 : ℝ) < M := by positivity
  have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hNR : (0 : ℝ) < N := hMR.trans_le hMNR
  have hLog : Real.log (M : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hMR hMNR
  have hInv : 1 / (N : ℝ) ≤ 1 / (M : ℝ) :=
    one_div_le_one_div_of_le hMR hMNR
  have hScale : 0 ≤ logarithmicCvSPoleScale 13 :=
    logarithmicCvSPoleScale_nonneg 13 (by norm_num)
  have hDen : 0 < 8 * Real.pi ^ 2 := by positivity
  have hPole :
      logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (N : ℝ)) ≤
        logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) := by
    rw [show logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (N : ℝ)) =
        (logarithmicCvSPoleScale 13 / (8 * Real.pi ^ 2)) *
          (1 / (N : ℝ)) by ring,
      show logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) =
        (logarithmicCvSPoleScale 13 / (8 * Real.pi ^ 2)) *
          (1 / (M : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hInv (div_nonneg hScale hDen.le)
  unfold c13ShellDynamicGap
  linarith

/-- Concrete even combined-Loewner half transport between actual cutoff-13
shell energies.  The source is `(B,2B]`; the target advances from `(N,2N]` to
`(2N,4N]`. -/
theorem c13EvenHistoricalCombinedLoewner_halfTransport_shellEnergy
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    c13EvenHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode B B)) x *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * N) (2 * N))) y := by
  have hN : N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hLowEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  apply c13EvenHistoricalCombinedLoewner_halfTransport
    B N hN hBN C q
    (c13ShellDynamicGap B) (c13ShellDynamicGap N)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode B B)) x)
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode (2 * N) (2 * N))) y)
    hSymbolNext hq
  · exact c13ShellDynamicGap_nonneg B hB
  · exact c13ShellDynamicGap_nonneg N hN960
  · exact le_rfl
  · exact c13ShellDynamicGap_mono (by omega) (by omega)
  · exact hLowEnergy
  · exact hHighEnergy
  · exact hPreviousBudget

/-- Odd-parity actual-shell companion of the concrete half transport. -/
theorem c13OddHistoricalCombinedLoewner_halfTransport_shellEnergy
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (C q : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hq : 0 ≤ q)
    (hPreviousBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    c13OddHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode B B)) x *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * N) (2 * N))) y := by
  have hN : N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hLowEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  apply c13OddHistoricalCombinedLoewner_halfTransport
    B N hN hBN C q
    (c13ShellDynamicGap B) (c13ShellDynamicGap N)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode B B)) x)
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode (2 * N) (2 * N))) y)
    hSymbolNext hq
  · exact c13ShellDynamicGap_nonneg B hB
  · exact c13ShellDynamicGap_nonneg N hN960
  · exact le_rfl
  · exact c13ShellDynamicGap_mono (by omega) (by omega)
  · exact hLowEnergy
  · exact hHighEnergy
  · exact hPreviousBudget

/-!
## Literal remote builder identification

The following mode map represents the actual positive frequencies in the
source band `(B,2B]` and a remote target shell `(N,2N]`.  It is deliberately
defined on a sum type so that the standard finite block-energy coordinates
apply without a reindexing hypothesis.
-/

noncomputable def c13HistoricalRemotePositiveMode
    (B N : ℕ) : Fin B ⊕ Fin N → ℤ :=
  Sum.elim
    (fun i => (historicalBandMode B i : ℤ))
    (fun j => ((N + 1 + (j : ℕ) : ℕ) : ℤ))

@[simp] lemma c13HistoricalRemotePositiveMode_inl
    (B N : ℕ) (i : Fin B) :
    c13HistoricalRemotePositiveMode B N (Sum.inl i) =
      (historicalBandMode B i : ℤ) := by
  rfl

@[simp] lemma c13HistoricalRemotePositiveMode_inr
    (B N : ℕ) (j : Fin N) :
    c13HistoricalRemotePositiveMode B N (Sum.inr j) =
      ((N + 1 + (j : ℕ) : ℕ) : ℤ) := by
  rfl

/-- Literal even cutoff-13 builder on a historical source band and a remote
target shell. -/
noncomputable def c13HistoricalRemoteEvenBuilderMatrix (B N : ℕ) :
    Matrix (Fin B ⊕ Fin N) (Fin B ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N)

/-- Odd-parity companion of the literal remote builder. -/
noncomputable def c13HistoricalRemoteOddBuilderMatrix (B N : ℕ) :
    Matrix (Fin B ⊕ Fin N) (Fin B ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderOddPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N)

noncomputable def c13EvenHistoricalPoleRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  logarithmicPoleKernel 13
      (historicalBandMode B i : ℝ) ((N + 1 + (j : ℕ) : ℕ) : ℝ) +
    logarithmicPoleKernel 13
      (historicalBandMode B i : ℝ) (-((N + 1 + (j : ℕ) : ℕ) : ℝ))

noncomputable def c13OddHistoricalPoleRemoteEntry
    (B N : ℕ) (i : Fin B) (j : Fin N) : ℝ :=
  logarithmicPoleKernel 13
      (historicalBandMode B i : ℝ) ((N + 1 + (j : ℕ) : ℕ) : ℝ) -
    logarithmicPoleKernel 13
      (historicalBandMode B i : ℝ) (-((N + 1 + (j : ℕ) : ℕ) : ℝ))

/-- The actual even builder cross entry is the rank-two pole entry minus the
single combined Archimedean/prime Loewner entry. -/
theorem c13HistoricalRemoteEvenBuilderMatrix_inl_inr
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13HistoricalRemoteEvenBuilderMatrix B N (Sum.inl i) (Sum.inr j) =
      c13EvenHistoricalPoleRemoteEntry B N i j -
        c13EvenHistoricalLoewnerRemoteEntry B N i j := by
  unfold c13HistoricalRemoteEvenBuilderMatrix
    logarithmicCvSBuilderEvenPositiveModeMatrix
  simp only [c13HistoricalRemotePositiveMode_inl,
    c13HistoricalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]
  rw [logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel]
  unfold c13EvenHistoricalPoleRemoteEntry
    c13EvenHistoricalLoewnerRemoteEntry
    c13EvenHistoricalLoewnerRemoteNatEntry
    c13HistoricalCombinedLoewnerSymbol
    c13HistoricalCombinedLoewnerDiagonal
  push_cast
  ring

/-- Odd-parity actual builder cross-entry identity. -/
theorem c13HistoricalRemoteOddBuilderMatrix_inl_inr
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13HistoricalRemoteOddBuilderMatrix B N (Sum.inl i) (Sum.inr j) =
      c13OddHistoricalPoleRemoteEntry B N i j -
        c13OddHistoricalLoewnerRemoteEntry B N i j := by
  unfold c13HistoricalRemoteOddBuilderMatrix
    logarithmicCvSBuilderOddPositiveModeMatrix
  simp only [c13HistoricalRemotePositiveMode_inl,
    c13HistoricalRemotePositiveMode_inr]
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]
  rw [logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel]
  unfold c13OddHistoricalPoleRemoteEntry
    c13OddHistoricalLoewnerRemoteEntry
    c13OddHistoricalLoewnerRemoteNatEntry
    c13HistoricalCombinedLoewnerSymbol
    c13HistoricalCombinedLoewnerDiagonal
  push_cast
  ring

theorem c13HistoricalRemoteEvenBuilderMatrix_symm
    (B N : ℕ) (a b : Fin B ⊕ Fin N) :
    c13HistoricalRemoteEvenBuilderMatrix B N a b =
      c13HistoricalRemoteEvenBuilderMatrix B N b a := by
  unfold c13HistoricalRemoteEvenBuilderMatrix
    logarithmicCvSBuilderEvenPositiveModeMatrix
  rw [logarithmicCvSBuilderEntry_symm]
  rw [logarithmicCvSBuilderEntry_symm
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N a)
    (-(c13HistoricalRemotePositiveMode B N b))]
  rw [← logarithmicCvSBuilderEntry_neg_right_eq_neg_left
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N b)
    (c13HistoricalRemotePositiveMode B N a)]

theorem c13HistoricalRemoteOddBuilderMatrix_symm
    (B N : ℕ) (a b : Fin B ⊕ Fin N) :
    c13HistoricalRemoteOddBuilderMatrix B N a b =
      c13HistoricalRemoteOddBuilderMatrix B N b a := by
  unfold c13HistoricalRemoteOddBuilderMatrix
    logarithmicCvSBuilderOddPositiveModeMatrix
  rw [logarithmicCvSBuilderEntry_symm]
  rw [logarithmicCvSBuilderEntry_symm
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N a)
    (-(c13HistoricalRemotePositiveMode B N b))]
  rw [← logarithmicCvSBuilderEntry_neg_right_eq_neg_left
    13 c13PrimePowerLocation c13PrimePowerBase
    (c13HistoricalRemotePositiveMode B N b)
    (c13HistoricalRemotePositiveMode B N a)]

noncomputable def c13EvenHistoricalPoleRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13EvenHistoricalPoleRemoteEntry B N ij.1 ij.2 * (x ij.1 * y ij.2)

noncomputable def c13OddHistoricalPoleRemoteCrossEnergy
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin B)) ×ˢ
      (Finset.univ : Finset (Fin N)),
    c13OddHistoricalPoleRemoteEntry B N ij.1 ij.2 * (x ij.1 * y ij.2)

/-- At the bilinear-form level the actual even builder retains exactly the
same pole-minus-combined-Loewner grouping as each entry. -/
theorem c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteEvenBuilderMatrix B N) x y =
      c13EvenHistoricalPoleRemoteCrossEnergy B N x y -
        c13EvenHistoricalLoewnerRemoteCrossEnergy B N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13HistoricalRemoteEvenBuilderMatrix B N) x y
    (c13HistoricalRemoteEvenBuilderMatrix_symm B N)]
  unfold c13EvenHistoricalPoleRemoteCrossEnergy
    c13EvenHistoricalLoewnerRemoteCrossEnergy
  rw [Finset.sum_product, Finset.sum_product]
  calc
    (∑ i, ∑ j,
        x i * c13HistoricalRemoteEvenBuilderMatrix B N
          (Sum.inl i) (Sum.inr j) * y j) =
        ∑ i, ∑ j,
          (c13EvenHistoricalPoleRemoteEntry B N i j * (x i * y j) -
            c13EvenHistoricalLoewnerRemoteEntry B N i j * (x i * y j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [c13HistoricalRemoteEvenBuilderMatrix_inl_inr]
      ring
    _ = (∑ i, ∑ j,
          c13EvenHistoricalPoleRemoteEntry B N i j * (x i * y j)) -
        ∑ i, ∑ j,
          c13EvenHistoricalLoewnerRemoteEntry B N i j * (x i * y j) := by
      simp_rw [Finset.sum_sub_distrib]

/-- Odd-parity bilinear builder identity. -/
theorem c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq
    (B N : ℕ) (x : Fin B → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13HistoricalRemoteOddBuilderMatrix B N) x y =
      c13OddHistoricalPoleRemoteCrossEnergy B N x y -
        c13OddHistoricalLoewnerRemoteCrossEnergy B N x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13HistoricalRemoteOddBuilderMatrix B N) x y
    (c13HistoricalRemoteOddBuilderMatrix_symm B N)]
  unfold c13OddHistoricalPoleRemoteCrossEnergy
    c13OddHistoricalLoewnerRemoteCrossEnergy
  rw [Finset.sum_product, Finset.sum_product]
  calc
    (∑ i, ∑ j,
        x i * c13HistoricalRemoteOddBuilderMatrix B N
          (Sum.inl i) (Sum.inr j) * y j) =
        ∑ i, ∑ j,
          (c13OddHistoricalPoleRemoteEntry B N i j * (x i * y j) -
            c13OddHistoricalLoewnerRemoteEntry B N i j * (x i * y j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [c13HistoricalRemoteOddBuilderMatrix_inl_inr]
      ring
    _ = (∑ i, ∑ j,
          c13OddHistoricalPoleRemoteEntry B N i j * (x i * y j)) -
        ∑ i, ∑ j,
          c13OddHistoricalLoewnerRemoteEntry B N i j * (x i * y j) := by
      simp_rw [Finset.sum_sub_distrib]

/-!
## Sharper shell-to-shell pole transport

Unlike a fixed prefix, the historical source band `(B,2B]` has reciprocal
square mass `O(1/B)`.  The rank-one pole factorization therefore supplies a
coefficient `O(1/(B*N))` for a remote target `(N,2N]`.
-/

theorem c13EvenHistoricalPoleRemoteEntry_factorization
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13EvenHistoricalPoleRemoteEntry B N i j =
      (2 * logarithmicCvSPoleScale 13) *
        logarithmicCvSPoleEvenWeight 13
          (finGlobalShellPositiveMode B B i) *
        logarithmicCvSPoleEvenWeight 13
          (finGlobalShellPositiveMode N N j) := by
  simpa [c13EvenHistoricalPoleRemoteEntry, historicalBandMode,
    finGlobalShellPositiveMode, logarithmicCvSPoleEntry_eq_kernel,
    add_assoc, add_comm, add_left_comm] using
    logarithmicCvSPoleEntry_even_factorization 13
      (finGlobalShellPositiveMode B B i)
      (finGlobalShellPositiveMode N N j)

theorem c13OddHistoricalPoleRemoteEntry_factorization
    (B N : ℕ) (i : Fin B) (j : Fin N) :
    c13OddHistoricalPoleRemoteEntry B N i j =
      (-(2 * logarithmicCvSPoleScale 13)) *
        logarithmicCvSPoleOddWeight 13
          (finGlobalShellPositiveMode B B i) *
        logarithmicCvSPoleOddWeight 13
          (finGlobalShellPositiveMode N N j) := by
  simpa [c13OddHistoricalPoleRemoteEntry, historicalBandMode,
    finGlobalShellPositiveMode, logarithmicCvSPoleEntry_eq_kernel,
    add_assoc, add_comm, add_left_comm] using
    logarithmicCvSPoleEntry_odd_factorization 13
      (finGlobalShellPositiveMode B B i)
      (finGlobalShellPositiveMode N N j)

noncomputable def c13HistoricalEvenPoleShellCoefficient (B N : ℕ) : ℝ :=
  (2 * logarithmicCvSPoleScale 13) ^ 2 *
    (1 / (64 * Real.pi ^ 2 * (B : ℝ))) *
    (1 / (64 * Real.pi ^ 2 * (N : ℝ)))

noncomputable def c13HistoricalOddPoleShellCoefficient (B N : ℕ) : ℝ :=
  (2 * logarithmicCvSPoleScale 13) ^ 2 *
    (1 / (16 * Real.pi ^ 2 * (B : ℝ))) *
    (1 / (16 * Real.pi ^ 2 * (N : ℝ)))

theorem c13EvenHistoricalPoleRemoteCrossEnergy_sq_le_coefficient
    (B N : ℕ) (hB : B ≠ 0) (hN : N ≠ 0)
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13EvenHistoricalPoleRemoteCrossEnergy B N x y ^ 2 ≤
      c13HistoricalEvenPoleShellCoefficient B N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let u : Fin B ⊕ Fin N → ℝ := Sum.elim
    (fun i => logarithmicCvSPoleEvenWeight 13
      (finGlobalShellPositiveMode B B i))
    (fun j => logarithmicCvSPoleEvenWeight 13
      (finGlobalShellPositiveMode N N j))
  let A : Matrix (Fin B ⊕ Fin N) (Fin B ⊕ Fin N) ℝ :=
    fun a b => (2 * logarithmicCvSPoleScale 13) * u a * u b
  have hRank :
      finiteMatrixBlockCrossEnergy A x y ^ 2 ≤
        (2 * logarithmicCvSPoleScale 13) ^ 2 *
          (∑ i, u (Sum.inl i) ^ 2) *
          (∑ j, u (Sum.inr j) ^ 2) *
          (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
    simpa only [A, mul_assoc] using
      RiemannCvs.PoleSeparatedBands.finiteMatrixBlockCrossEnergy_rankOne_sq_le
        (2 * logarithmicCvSPoleScale 13) u x y
  have hCross :
      c13EvenHistoricalPoleRemoteCrossEnergy B N x y =
        finiteMatrixBlockCrossEnergy A x y := by
    have hLeft := finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm A x y (by
      intro a b
      dsimp only [A]
      ring)
    calc
      c13EvenHistoricalPoleRemoteCrossEnergy B N x y =
          ∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j := by
        unfold c13EvenHistoricalPoleRemoteCrossEnergy
        rw [Finset.sum_product]
        simp_rw [c13EvenHistoricalPoleRemoteEntry_factorization]
        dsimp only [A, u, Sum.elim_inl, Sum.elim_inr]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = finiteMatrixBlockCrossEnergy A x y := hLeft.symm
  rw [hCross]
  dsimp only [u, Sum.elim_inl, Sum.elim_inr] at hRank
  refine hRank.trans ?_
  unfold c13HistoricalEvenPoleShellCoefficient
  have hLow := logarithmicCvSPoleEvenWeight_shell_sum_le_strong
    13 B B hB
  have hHigh := logarithmicCvSPoleEvenWeight_shell_sum_le_strong
    13 N N hN
  gcongr
  exact mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)

theorem c13OddHistoricalPoleRemoteCrossEnergy_sq_le_coefficient
    (B N : ℕ) (hB : B ≠ 0) (hN : N ≠ 0)
    (x : Fin B → ℝ) (y : Fin N → ℝ) :
    c13OddHistoricalPoleRemoteCrossEnergy B N x y ^ 2 ≤
      c13HistoricalOddPoleShellCoefficient B N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let u : Fin B ⊕ Fin N → ℝ := Sum.elim
    (fun i => logarithmicCvSPoleOddWeight 13
      (finGlobalShellPositiveMode B B i))
    (fun j => logarithmicCvSPoleOddWeight 13
      (finGlobalShellPositiveMode N N j))
  let A : Matrix (Fin B ⊕ Fin N) (Fin B ⊕ Fin N) ℝ :=
    fun a b => (-(2 * logarithmicCvSPoleScale 13)) * u a * u b
  have hRank :
      finiteMatrixBlockCrossEnergy A x y ^ 2 ≤
        (-(2 * logarithmicCvSPoleScale 13)) ^ 2 *
          (∑ i, u (Sum.inl i) ^ 2) *
          (∑ j, u (Sum.inr j) ^ 2) *
          (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
    simpa only [A, mul_assoc] using
      RiemannCvs.PoleSeparatedBands.finiteMatrixBlockCrossEnergy_rankOne_sq_le
        (-(2 * logarithmicCvSPoleScale 13)) u x y
  have hCross :
      c13OddHistoricalPoleRemoteCrossEnergy B N x y =
        finiteMatrixBlockCrossEnergy A x y := by
    have hLeft := finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm A x y (by
      intro a b
      dsimp only [A]
      ring)
    calc
      c13OddHistoricalPoleRemoteCrossEnergy B N x y =
          ∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j := by
        unfold c13OddHistoricalPoleRemoteCrossEnergy
        rw [Finset.sum_product]
        simp_rw [c13OddHistoricalPoleRemoteEntry_factorization]
        dsimp only [A, u, Sum.elim_inl, Sum.elim_inr]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = finiteMatrixBlockCrossEnergy A x y := hLeft.symm
  rw [hCross]
  dsimp only [u, Sum.elim_inl, Sum.elim_inr] at hRank
  refine hRank.trans ?_
  unfold c13HistoricalOddPoleShellCoefficient
  have hLow := logarithmicCvSPoleOddWeight_shell_sum_le 13 B B hB
  have hHigh := logarithmicCvSPoleOddWeight_shell_sum_le 13 N N hN
  rw [neg_sq]
  gcongr
  exact mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)

lemma c13HistoricalEvenPoleShellCoefficient_two_mul
    (B N : ℕ) (hN : N ≠ 0) :
    c13HistoricalEvenPoleShellCoefficient B (2 * N) =
      c13HistoricalEvenPoleShellCoefficient B N / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold c13HistoricalEvenPoleShellCoefficient
  push_cast
  field_simp [hNR, Real.pi_ne_zero]

lemma c13HistoricalOddPoleShellCoefficient_two_mul
    (B N : ℕ) (hN : N ≠ 0) :
    c13HistoricalOddPoleShellCoefficient B (2 * N) =
      c13HistoricalOddPoleShellCoefficient B N / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold c13HistoricalOddPoleShellCoefficient
  push_cast
  field_simp [hNR, Real.pi_ne_zero]

/-- Exact half transport of the even source-shell pole channel, normalized by
the actual cutoff-13 shell energies. -/
theorem c13EvenHistoricalPole_halfTransport_shellEnergy
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (q : ℝ)
    (hq : 0 ≤ q)
    (hPreviousBudget :
      c13HistoricalEvenPoleShellCoefficient B N ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    c13EvenHistoricalPoleRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode B B)) x *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * N) (2 * N))) y := by
  have hB0 : B ≠ 0 := by omega
  have hN0 : N ≠ 0 := by omega
  have h2N0 : 2 * N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapN := c13ShellDynamicGap_nonneg N hN960
  have hGap2N := c13ShellDynamicGap_nonneg (2 * N) h2N960
  have hGapGrowth := c13ShellDynamicGap_mono (M := N) (N := 2 * N)
    (by omega) (by omega)
  have hGapProduct :
      c13ShellDynamicGap B * c13ShellDynamicGap N ≤
        c13ShellDynamicGap B * c13ShellDynamicGap (2 * N) :=
    mul_le_mul_of_nonneg_left hGapGrowth hGapB
  have hCoefficient :
      c13HistoricalEvenPoleShellCoefficient B (2 * N) ≤
        (q / 2) * c13ShellDynamicGap B * c13ShellDynamicGap (2 * N) := by
    rw [c13HistoricalEvenPoleShellCoefficient_two_mul B N hN0]
    calc
      c13HistoricalEvenPoleShellCoefficient B N / 2 ≤
          (q * c13ShellDynamicGap B * c13ShellDynamicGap N) / 2 := by
        gcongr
      _ = (q / 2) *
          (c13ShellDynamicGap B * c13ShellDynamicGap N) := by ring
      _ ≤ (q / 2) *
          (c13ShellDynamicGap B * c13ShellDynamicGap (2 * N)) :=
        mul_le_mul_of_nonneg_left hGapProduct (div_nonneg hq (by norm_num))
      _ = (q / 2) * c13ShellDynamicGap B *
          c13ShellDynamicGap (2 * N) := by ring
  have hLowEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  have hCross := c13EvenHistoricalPoleRemoteCrossEnergy_sq_le_coefficient
    B (2 * N) hB0 h2N0 x y
  exact relativeCoupling_of_squaredNormBudget
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode B B)) x)
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode (2 * N) (2 * N))) y)
    (c13EvenHistoricalPoleRemoteCrossEnergy B (2 * N) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (c13HistoricalEvenPoleShellCoefficient B (2 * N)) (q / 2)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    hGapB hGap2N (div_nonneg hq (by norm_num))
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
    hLowEnergy hHighEnergy hCross hCoefficient

/-- Odd-parity shell-to-shell pole half transport. -/
theorem c13OddHistoricalPole_halfTransport_shellEnergy
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N) (q : ℝ)
    (hq : 0 ≤ q)
    (hPreviousBudget :
      c13HistoricalOddPoleShellCoefficient B N ≤
        q * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    c13OddHistoricalPoleRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
      (q / 2) *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode B B)) x *
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * N) (2 * N))) y := by
  have hB0 : B ≠ 0 := by omega
  have hN0 : N ≠ 0 := by omega
  have h2N0 : 2 * N ≠ 0 := by omega
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hGapB := c13ShellDynamicGap_nonneg B hB
  have hGapN := c13ShellDynamicGap_nonneg N hN960
  have hGap2N := c13ShellDynamicGap_nonneg (2 * N) h2N960
  have hGapGrowth := c13ShellDynamicGap_mono (M := N) (N := 2 * N)
    (by omega) (by omega)
  have hGapProduct :
      c13ShellDynamicGap B * c13ShellDynamicGap N ≤
        c13ShellDynamicGap B * c13ShellDynamicGap (2 * N) :=
    mul_le_mul_of_nonneg_left hGapGrowth hGapB
  have hCoefficient :
      c13HistoricalOddPoleShellCoefficient B (2 * N) ≤
        (q / 2) * c13ShellDynamicGap B * c13ShellDynamicGap (2 * N) := by
    rw [c13HistoricalOddPoleShellCoefficient_two_mul B N hN0]
    calc
      c13HistoricalOddPoleShellCoefficient B N / 2 ≤
          (q * c13ShellDynamicGap B * c13ShellDynamicGap N) / 2 := by
        gcongr
      _ = (q / 2) *
          (c13ShellDynamicGap B * c13ShellDynamicGap N) := by ring
      _ ≤ (q / 2) *
          (c13ShellDynamicGap B * c13ShellDynamicGap (2 * N)) :=
        mul_le_mul_of_nonneg_left hGapProduct (div_nonneg hq (by norm_num))
      _ = (q / 2) * c13ShellDynamicGap B *
          c13ShellDynamicGap (2 * N) := by ring
  have hLowEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighEnergy :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  have hCross := c13OddHistoricalPoleRemoteCrossEnergy_sq_le_coefficient
    B (2 * N) hB0 h2N0 x y
  exact relativeCoupling_of_squaredNormBudget
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode B B)) x)
    (finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode (2 * N) (2 * N))) y)
    (c13OddHistoricalPoleRemoteCrossEnergy B (2 * N) x y)
    (c13ShellDynamicGap B) (c13ShellDynamicGap (2 * N))
    (c13HistoricalOddPoleShellCoefficient B (2 * N)) (q / 2)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    hGapB hGap2N (div_nonneg hq (by norm_num))
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
    hLowEnergy hHighEnergy hCross hCoefficient

noncomputable def c13EvenBuilderShellEnergy
    (old shell : ℕ) (x : Fin shell → ℝ) : ℝ :=
  finiteMatrixQuadraticEnergy
    (logarithmicCvSBuilderEvenPositiveModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old shell)) x

noncomputable def c13OddBuilderShellEnergy
    (old shell : ℕ) (x : Fin shell → ℝ) : ℝ :=
  finiteMatrixQuadraticEnergy
    (logarithmicCvSBuilderOddPositiveModeMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old shell)) x

/-- Complete even historical builder half transport with the
Archimedean/prime Loewner block kept intact and the rank-two pole kept as the
second amplitude channel. -/
theorem c13HistoricalRemoteEvenBuilder_halfTransport_amplitude
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N)
    (C qLoewner qPole ampLoewner ampPole : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hqLoewner : 0 ≤ qLoewner) (hqPole : 0 ≤ qPole)
    (hampLoewner : 0 ≤ ampLoewner) (hampPole : 0 ≤ ampPole)
    (hAmpLoewner : qLoewner / 2 ≤ ampLoewner ^ 2)
    (hAmpPole : qPole / 2 ≤ ampPole ^ 2)
    (hPreviousLoewnerBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        qLoewner * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (hPreviousPoleBudget :
      c13HistoricalEvenPoleShellCoefficient B N ≤
        qPole * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteEvenBuilderMatrix B (2 * N)) x y) ^ 2 ≤
      (ampPole + ampLoewner) ^ 2 *
        c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (2 * N) (2 * N) y := by
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hLowFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  have hLowEnergy : 0 ≤ c13EvenBuilderShellEnergy B B x := by
    unfold c13EvenBuilderShellEnergy
    exact (mul_nonneg (c13ShellDynamicGap_nonneg B hB)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hLowFloor
  have hHighEnergy : 0 ≤ c13EvenBuilderShellEnergy (2 * N) (2 * N) y := by
    unfold c13EvenBuilderShellEnergy
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (2 * N) h2N960)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hHighFloor
  have hEnergyProduct :
      0 ≤ c13EvenBuilderShellEnergy B B x *
        c13EvenBuilderShellEnergy (2 * N) (2 * N) y :=
    mul_nonneg hLowEnergy hHighEnergy
  have hLoewner :=
    c13EvenHistoricalCombinedLoewner_halfTransport_shellEnergy
      B N hB hBN C qLoewner hSymbolNext hqLoewner
      hPreviousLoewnerBudget x y
  have hPole := c13EvenHistoricalPole_halfTransport_shellEnergy
    B N hB hBN qPole hqPole hPreviousPoleBudget x y
  have hLoewnerAmp :
      (-c13EvenHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y) ^ 2 ≤
        ampLoewner ^ 2 * c13EvenBuilderShellEnergy B B x *
          c13EvenBuilderShellEnergy (2 * N) (2 * N) y := by
    rw [neg_sq]
    refine hLoewner.trans ?_
    have hScaled := mul_le_mul_of_nonneg_right hAmpLoewner hEnergyProduct
    simpa [c13EvenBuilderShellEnergy, mul_assoc] using hScaled
  have hPoleAmp :
      c13EvenHistoricalPoleRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
        ampPole ^ 2 * c13EvenBuilderShellEnergy B B x *
          c13EvenBuilderShellEnergy (2 * N) (2 * N) y := by
    refine hPole.trans ?_
    have hScaled := mul_le_mul_of_nonneg_right hAmpPole hEnergyProduct
    simpa [c13EvenBuilderShellEnergy, mul_assoc] using hScaled
  have hCombined := relativeCoupling_of_twoSourceAmplitudeBounds
    (c13EvenBuilderShellEnergy B B x)
    (c13EvenBuilderShellEnergy (2 * N) (2 * N) y)
    (c13EvenHistoricalPoleRemoteCrossEnergy B (2 * N) x y)
    (-c13EvenHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y)
    ampPole ampLoewner hLowEnergy hHighEnergy hampPole hampLoewner
    hPoleAmp hLoewnerAmp
  rw [c13HistoricalRemoteEvenBuilderMatrix_crossEnergy_eq]
  simpa [sub_eq_add_neg] using hCombined

/-- Odd-parity complete historical builder half transport at amplitude level. -/
theorem c13HistoricalRemoteOddBuilder_halfTransport_amplitude
    (B N : ℕ) (hB : 960 ≤ B) (hBN : 4 * B ≤ N)
    (C qLoewner qPole ampLoewner ampPole : ℝ)
    (hSymbolNext :
      (∑ j ∈ Finset.range (2 * N),
          c13HistoricalCombinedLoewnerSymbol
              (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2 /
            (((2 * N + 1 + j : ℕ) : ℝ)) ^ 2) ≤
        C / ((2 * N : ℕ) : ℝ))
    (hqLoewner : 0 ≤ qLoewner) (hqPole : 0 ≤ qPole)
    (hampLoewner : 0 ≤ ampLoewner) (hampPole : 0 ≤ ampPole)
    (hAmpLoewner : qLoewner / 2 ≤ ampLoewner ^ 2)
    (hAmpPole : qPole / 2 ≤ ampPole ^ 2)
    (hPreviousLoewnerBudget :
      rectangularSymbolSquareBudget
          (Finset.univ : Finset (Fin B))
          (fun i => c13HistoricalCombinedLoewnerSymbol
            (historicalBandMode B i : ℝ)) N C ≤
        qLoewner * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (hPreviousPoleBudget :
      c13HistoricalOddPoleShellCoefficient B N ≤
        qPole * c13ShellDynamicGap B * c13ShellDynamicGap N)
    (x : Fin B → ℝ) (y : Fin (2 * N) → ℝ) :
    (finiteMatrixBlockCrossEnergy
      (c13HistoricalRemoteOddBuilderMatrix B (2 * N)) x y) ^ 2 ≤
      (ampPole + ampLoewner) ^ 2 *
        c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (2 * N) (2 * N) y := by
  have hN960 : 960 ≤ N := by omega
  have h2N960 : 960 ≤ 2 * N := by omega
  have hLowFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      B B hB (by omega) x
  have hHighFloor :=
    c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (2 * N) (2 * N) h2N960 (by omega) y
  have hLowEnergy : 0 ≤ c13OddBuilderShellEnergy B B x := by
    unfold c13OddBuilderShellEnergy
    exact (mul_nonneg (c13ShellDynamicGap_nonneg B hB)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hLowFloor
  have hHighEnergy : 0 ≤ c13OddBuilderShellEnergy (2 * N) (2 * N) y := by
    unfold c13OddBuilderShellEnergy
    exact (mul_nonneg (c13ShellDynamicGap_nonneg (2 * N) h2N960)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hHighFloor
  have hEnergyProduct :
      0 ≤ c13OddBuilderShellEnergy B B x *
        c13OddBuilderShellEnergy (2 * N) (2 * N) y :=
    mul_nonneg hLowEnergy hHighEnergy
  have hLoewner :=
    c13OddHistoricalCombinedLoewner_halfTransport_shellEnergy
      B N hB hBN C qLoewner hSymbolNext hqLoewner
      hPreviousLoewnerBudget x y
  have hPole := c13OddHistoricalPole_halfTransport_shellEnergy
    B N hB hBN qPole hqPole hPreviousPoleBudget x y
  have hLoewnerAmp :
      (-c13OddHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y) ^ 2 ≤
        ampLoewner ^ 2 * c13OddBuilderShellEnergy B B x *
          c13OddBuilderShellEnergy (2 * N) (2 * N) y := by
    rw [neg_sq]
    refine hLoewner.trans ?_
    have hScaled := mul_le_mul_of_nonneg_right hAmpLoewner hEnergyProduct
    simpa [c13OddBuilderShellEnergy, mul_assoc] using hScaled
  have hPoleAmp :
      c13OddHistoricalPoleRemoteCrossEnergy B (2 * N) x y ^ 2 ≤
        ampPole ^ 2 * c13OddBuilderShellEnergy B B x *
          c13OddBuilderShellEnergy (2 * N) (2 * N) y := by
    refine hPole.trans ?_
    have hScaled := mul_le_mul_of_nonneg_right hAmpPole hEnergyProduct
    simpa [c13OddBuilderShellEnergy, mul_assoc] using hScaled
  have hCombined := relativeCoupling_of_twoSourceAmplitudeBounds
    (c13OddBuilderShellEnergy B B x)
    (c13OddBuilderShellEnergy (2 * N) (2 * N) y)
    (c13OddHistoricalPoleRemoteCrossEnergy B (2 * N) x y)
    (-c13OddHistoricalLoewnerRemoteCrossEnergy B (2 * N) x y)
    ampPole ampLoewner hLowEnergy hHighEnergy hampPole hampLoewner
    hPoleAmp hLoewnerAmp
  rw [c13HistoricalRemoteOddBuilderMatrix_crossEnergy_eq]
  simpa [sub_eq_add_neg] using hCombined

end RiemannCvs.V23BoundaryWeylMainline
