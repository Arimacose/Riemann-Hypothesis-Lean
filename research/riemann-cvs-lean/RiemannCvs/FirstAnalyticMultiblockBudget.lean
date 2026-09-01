import RiemannCvs.AdjacentArchimedeanSharpGap

/-!
# First analytic multiblock budget after the finite frontier

The rigorous finite certificate reaches `N = 7680`.  The next analytic step
adds the shell `(7680,15360]`, which sees two qualitatively different source
groups:

* the adjacent source `(3840,7680]`, controlled by the premise-free builder
  estimate with relative coefficient `37/40`;
* all older source blocks, controlled by the historical dyadic budget `2/27`.

The exact arithmetic is the decisive point:

```text
37/40 + 2/27 = 1079/1080 < 1,
1 - 1079/1080 = 1/1080.
```

The combination below uses a weighted two-channel Cauchy inequality rather
than the coarse estimate `(a+b)^2 <= 2*a^2+2*b^2`, so no factor two destroys
the reserve.  The even endpoint consumes the existing `1/30` geometrically
transported dyadic envelope.  The odd endpoint additionally consumes the
separately budgeted `[1,20]` channel with coefficient `1/384` through the
existing odd historical adapter.

This module closes the multiblock *budget algebra* and connects it to the
literal even and odd adjacent builder blocks.  The hypotheses named
`hRelative` and `hBudgetEnvelope` still represent the source-specific
historical transport estimates.  Establishing those estimates for the
concrete infinite dyadic tower, and then taking the boundary--Weyl limit, are
separate obligations; no numerical diagnostic is imported into these proofs.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

/-- The exact cost of the adjacent and historical source groups. -/
lemma v23_firstAnalyticMultiblockBudget :
    (37 / 40 : ℝ) + 2 / 27 = 1079 / 1080 := by
  norm_num

/-- The strict relative-energy reserve left after the first multiblock step. -/
lemma v23_firstAnalyticMultiblockSlack :
    (1 : ℝ) - ((37 / 40 : ℝ) + 2 / 27) = 1 / 1080 := by
  norm_num

/-- Weighted two-channel Cauchy with the exact V23 coefficients.

No sign assumptions on the abstract energies are needed: the two supplied
relative inequalities and the square
`((37/40) * historicalCross - (2/27) * adjacentCross)^2` contain all of the
algebraic information required for the conclusion. -/
theorem relativeCoupling_of_v23AdjacentAndHistoricalBudgets
    (historicalEnergy adjacentEnergy tail historicalCross adjacentCross : ℝ)
    (hHistorical : historicalCross ^ 2 ≤
      (2 / 27 : ℝ) * historicalEnergy * tail)
    (hAdjacent : adjacentCross ^ 2 ≤
      (37 / 40 : ℝ) * adjacentEnergy * tail) :
    (historicalCross + adjacentCross) ^ 2 ≤
      (1079 / 1080 : ℝ) * (historicalEnergy + adjacentEnergy) * tail := by
  have hHistoricalScaled := mul_le_mul_of_nonneg_left hHistorical
    (show (0 : ℝ) ≤ 37 / 40 by norm_num)
  have hAdjacentScaled := mul_le_mul_of_nonneg_left hAdjacent
    (show (0 : ℝ) ≤ 2 / 27 by norm_num)
  have hWeighted := sq_nonneg
    ((37 / 40 : ℝ) * historicalCross - (2 / 27 : ℝ) * adjacentCross)
  nlinarith

/-- Combine an abstract even historical channel with the actual adjacent
cutoff-13 builder block. -/
theorem c13EvenBuilderAdjacentWithHistorical_relative_1079Over1080
    (M : ℕ) (hM : 3840 ≤ M)
    (historicalEnergy historicalCross : ℝ)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ)
    (hHistorical : historicalCross ^ 2 ≤
      (2 / 27 : ℝ) * historicalEnergy *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y) :
    (historicalCross + finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (1079 / 1080 : ℝ) *
        (historicalEnergy + finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) x) *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  exact relativeCoupling_of_v23AdjacentAndHistoricalBudgets
    historicalEnergy
    (finiteMatrixBlockBaseEnergy
      (c13EvenBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy
      (c13EvenBuilderCoreNewestBlock M (2 * M)) y)
    historicalCross
    (finiteMatrixBlockCrossEnergy
      (c13EvenBuilderCoreNewestBlock M (2 * M)) x y)
    hHistorical
    (c13EvenBuilderAdjacent_relative_37Over40 M hM x y)

/-- Combine an abstract odd historical channel with the actual adjacent
cutoff-13 builder block. -/
theorem c13OddBuilderAdjacentWithHistorical_relative_1079Over1080
    (M : ℕ) (hM : 3840 ≤ M)
    (historicalEnergy historicalCross : ℝ)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ)
    (hHistorical : historicalCross ^ 2 ≤
      (2 / 27 : ℝ) * historicalEnergy *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y) :
    (historicalCross + finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (1079 / 1080 : ℝ) *
        (historicalEnergy + finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) x) *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  exact relativeCoupling_of_v23AdjacentAndHistoricalBudgets
    historicalEnergy
    (finiteMatrixBlockBaseEnergy
      (c13OddBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy
      (c13OddBuilderCoreNewestBlock M (2 * M)) y)
    historicalCross
    (finiteMatrixBlockCrossEnergy
      (c13OddBuilderCoreNewestBlock M (2 * M)) x y)
    hHistorical
    (c13OddBuilderAdjacent_relative_37Over40 M hM x y)

/-- If the historical even channels obey the existing `1/30` newest-envelope
and exact half transport, then they spend at most `2/27`; the sharpened
adjacent channel closes the complete two-level block with coefficient
`1079/1080`. -/
theorem c13EvenBuilderAdjacentWithDyadicHistorical_relative_1079Over1080
    (M : ℕ) (hM : 3840 ≤ M)
    (energy cross budget : ℕ → ℝ) (n : ℕ)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ)
    (hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i)
    (hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i)
    (hBudgetEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ (1 / 30 : ℝ) * (1 / (2 : ℝ)) ^ i)
    (hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y) :
    ((∑ i ∈ Finset.range n, cross i) + finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (1079 / 1080 : ℝ) *
        ((∑ i ∈ Finset.range n, energy i) + finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) x) *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  let tail := finiteMatrixBlockTailEnergy
    (c13EvenBuilderCoreNewestBlock M (2 * M)) y
  have hTailLower := c13EvenBuilderAdjacentTailEnergy_ge_207Over50 M hM y
  have hTail : 0 ≤ tail := by
    have hFloor : 0 ≤ (207 / 50 : ℝ) * finiteVectorEuclideanNormSq y :=
      mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg y)
    exact hFloor.trans (by simpa [tail] using hTailLower)
  have hHistorical := relativeCoupling_of_dyadicChannelBudgets
    energy cross budget n tail (1 / 30 : ℝ) (2 / 27 : ℝ)
    hEnergy hBudget hTail (by norm_num) hBudgetEnvelope (by norm_num)
    (by simpa [tail] using hRelative)
  apply c13EvenBuilderAdjacentWithHistorical_relative_1079Over1080
    M hM (∑ i ∈ Finset.range n, energy i)
      (∑ i ∈ Finset.range n, cross i) x y
  simpa [tail] using hHistorical

/-- Odd companion: the fixed `[1,20]` channel keeps its independent `1/384`
budget, while the remaining dyadic family has leading coefficient `1/30`.
Together they fit inside `2/27`, and the adjacent `37/40` channel leaves the
strict global slack `1/1080`. -/
theorem c13OddBuilderAdjacentWithFixedAndDyadicHistorical_relative_1079Over1080
    (M : ℕ) (hM : 3840 ≤ M)
    (exceptionEnergy exceptionCross : ℝ)
    (energy cross budget : ℕ → ℝ) (n : ℕ)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ)
    (hExceptionEnergy : 0 ≤ exceptionEnergy)
    (hExceptionRelative : exceptionCross ^ 2 ≤
      (1 / 384 : ℝ) * exceptionEnergy *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y)
    (hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i)
    (hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i)
    (hBudgetEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ (1 / 30 : ℝ) * (1 / (2 : ℝ)) ^ i)
    (hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y) :
    (exceptionCross + (∑ i ∈ Finset.range n, cross i) +
        finiteMatrixBlockCrossEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (1079 / 1080 : ℝ) *
        (exceptionEnergy + (∑ i ∈ Finset.range n, energy i) +
          finiteMatrixBlockBaseEnergy
            (c13OddBuilderCoreNewestBlock M (2 * M)) x) *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  let tail := finiteMatrixBlockTailEnergy
    (c13OddBuilderCoreNewestBlock M (2 * M)) y
  have hTailLower := c13OddBuilderAdjacentTailEnergy_ge_207Over50 M hM y
  have hTail : 0 ≤ tail := by
    have hFloor : 0 ≤ (207 / 50 : ℝ) * finiteVectorEuclideanNormSq y :=
      mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg y)
    exact hFloor.trans (by simpa [tail] using hTailLower)
  have hHistorical := relativeCoupling_of_v23OddFixedBaseAndDyadicBudgets
    exceptionEnergy exceptionCross energy cross budget n tail
    hExceptionEnergy (by simpa [tail] using hExceptionRelative)
    hEnergy hBudget hTail hBudgetEnvelope (by simpa [tail] using hRelative)
  apply c13OddBuilderAdjacentWithHistorical_relative_1079Over1080
    M hM (exceptionEnergy + ∑ i ∈ Finset.range n, energy i)
      (exceptionCross + ∑ i ∈ Finset.range n, cross i) x y
  simpa [tail] using hHistorical

end RiemannCvs.V23BoundaryWeylMainline
