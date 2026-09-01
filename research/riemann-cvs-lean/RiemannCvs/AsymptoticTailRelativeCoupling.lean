import RiemannCvs.ArchimedeanRemainderSchur

noncomputable section
open scoped BigOperators

/-!
# Asymptotic tail relative-coupling bridge

The cutoff-13 shell theorem supplies an actual high-block Euclidean gap of
`9/5`.  This module inserts that closed gap into the squared-norm relative
coupling adapter.  For the balanced recursive coefficient `4/9`, the remaining
scalar cross-block condition simplifies exactly to

`entrySqBudget ≤ (4/5) * lowGap`.

The final two theorems apply this reduction directly to the concrete even and
odd CvS matrix towers, including their literal core, cross, and tail energies.
No high-block coercivity premise remains in those consumers.
-/

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

/-- A `9/5` high gap converts the balanced `4/9` determinant condition into
the single cross-budget threshold `(4/5) * lowGap`. -/
theorem relativeCoupling_fourNinth_of_nineFifthsHighGap
    (lowEnergy highEnergy cross lowGap entrySqBudget
      lowNormSq highNormSq : ℝ)
    (hLowGap : 0 ≤ lowGap)
    (hLowNormSq : 0 ≤ lowNormSq) (hHighNormSq : 0 ≤ highNormSq)
    (hLowEnergy : lowGap * lowNormSq ≤ lowEnergy)
    (hHighEnergy : (9 / 5 : ℝ) * highNormSq ≤ highEnergy)
    (hCross : cross ^ 2 ≤ entrySqBudget * (lowNormSq * highNormSq))
    (hBudget : entrySqBudget ≤ (4 / 5 : ℝ) * lowGap) :
    cross ^ 2 ≤ (4 / 9 : ℝ) * lowEnergy * highEnergy := by
  apply relativeCoupling_of_squaredNormBudget
    lowEnergy highEnergy cross lowGap (9 / 5) entrySqBudget (4 / 9)
      lowNormSq highNormSq hLowGap (by norm_num) (by norm_num)
      hLowNormSq hHighNormSq hLowEnergy hHighEnergy hCross
  calc
    entrySqBudget ≤ (4 / 5 : ℝ) * lowGap := hBudget
    _ = (4 / 9 : ℝ) * lowGap * (9 / 5) := by ring

/-- Concrete odd-tower relative coupling with its high-energy premise closed. -/
theorem c13_logarithmicCvSBuilderOddTowerCross_relative_fourNinth_of_squaredNormBudget
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n)
    (lowGap entrySqBudget : ℝ)
    (hLowGap : 0 ≤ lowGap)
    (hLowEnergy :
      lowGap * finiteVectorEuclideanNormSq
          (logarithmicCvSBuilderOddTowerVector z size n) ≤
        finiteMatrixTowerEnergy
          (logarithmicCvSBuilderOddTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderOddTowerVector z size) n)
    (hCross :
      (finiteMatrixTowerCrossEnergy
          (logarithmicCvSBuilderOddTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderOddTowerVector z size)
          (logarithmicCvSBuilderOddTowerShellVector z size shell)
          (logarithmicCvSBuilderOddTowerSplit size shell hSize) n) ^ 2 ≤
        entrySqBudget *
          (finiteVectorEuclideanNormSq
              (logarithmicCvSBuilderOddTowerVector z size n) *
            finiteVectorEuclideanNormSq
              (finGlobalShellVector z (size n) (shell n))))
    (hBudget : entrySqBudget ≤ (4 / 5 : ℝ) * lowGap) :
    (finiteMatrixTowerCrossEnergy
        (logarithmicCvSBuilderOddTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderOddTowerVector z size)
        (logarithmicCvSBuilderOddTowerShellVector z size shell)
        (logarithmicCvSBuilderOddTowerSplit size shell hSize) n) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixTowerEnergy
          (logarithmicCvSBuilderOddTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderOddTowerVector z size) n *
        finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderOddTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderOddTowerShellVector z size shell)
          (logarithmicCvSBuilderOddTowerSplit size shell hSize) n := by
  apply relativeCoupling_fourNinth_of_nineFifthsHighGap
    (finiteMatrixTowerEnergy
      (logarithmicCvSBuilderOddTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderOddTowerVector z size) n)
    (finiteMatrixTowerTailEnergy
      (logarithmicCvSBuilderOddTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderOddTowerShellVector z size shell)
      (logarithmicCvSBuilderOddTowerSplit size shell hSize) n)
    (finiteMatrixTowerCrossEnergy
      (logarithmicCvSBuilderOddTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderOddTowerVector z size)
      (logarithmicCvSBuilderOddTowerShellVector z size shell)
      (logarithmicCvSBuilderOddTowerSplit size shell hSize) n)
    lowGap entrySqBudget
    (finiteVectorEuclideanNormSq
      (logarithmicCvSBuilderOddTowerVector z size n))
    (finiteVectorEuclideanNormSq
      (finGlobalShellVector z (size n) (shell n)))
    hLowGap (finiteVectorEuclideanNormSq_nonneg _)
    (finiteVectorEuclideanNormSq_nonneg _) hLowEnergy
    (c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_nineFifths_normSq
      z size shell hSize n hOld hShell)
    hCross hBudget

/-- Concrete even-tower relative coupling with its high-energy premise closed. -/
theorem c13_logarithmicCvSBuilderEvenTowerCross_relative_fourNinth_of_squaredNormBudget
    (z0 : ℝ) (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n)
    (lowGap entrySqBudget : ℝ)
    (hLowGap : 0 ≤ lowGap)
    (hLowEnergy :
      lowGap * finiteVectorEuclideanNormSq
          (logarithmicCvSBuilderEvenTowerVector z0 z size n) ≤
        finiteMatrixTowerEnergy
          (logarithmicCvSBuilderEvenTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderEvenTowerVector z0 z size) n)
    (hCross :
      (finiteMatrixTowerCrossEnergy
          (logarithmicCvSBuilderEvenTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderEvenTowerVector z0 z size)
          (logarithmicCvSBuilderEvenTowerShellVector z size shell)
          (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n) ^ 2 ≤
        entrySqBudget *
          (finiteVectorEuclideanNormSq
              (logarithmicCvSBuilderEvenTowerVector z0 z size n) *
            finiteVectorEuclideanNormSq
              (finGlobalShellVector z (size n) (shell n))))
    (hBudget : entrySqBudget ≤ (4 / 5 : ℝ) * lowGap) :
    (finiteMatrixTowerCrossEnergy
        (logarithmicCvSBuilderEvenTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderEvenTowerVector z0 z size)
        (logarithmicCvSBuilderEvenTowerShellVector z size shell)
        (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixTowerEnergy
          (logarithmicCvSBuilderEvenTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderEvenTowerVector z0 z size) n *
        finiteMatrixTowerTailEnergy
          (logarithmicCvSBuilderEvenTowerMatrix
            13 c13PrimePowerLocation c13PrimePowerBase size)
          (logarithmicCvSBuilderEvenTowerShellVector z size shell)
          (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n := by
  apply relativeCoupling_fourNinth_of_nineFifthsHighGap
    (finiteMatrixTowerEnergy
      (logarithmicCvSBuilderEvenTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderEvenTowerVector z0 z size) n)
    (finiteMatrixTowerTailEnergy
      (logarithmicCvSBuilderEvenTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderEvenTowerShellVector z size shell)
      (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n)
    (finiteMatrixTowerCrossEnergy
      (logarithmicCvSBuilderEvenTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderEvenTowerVector z0 z size)
      (logarithmicCvSBuilderEvenTowerShellVector z size shell)
      (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n)
    lowGap entrySqBudget
    (finiteVectorEuclideanNormSq
      (logarithmicCvSBuilderEvenTowerVector z0 z size n))
    (finiteVectorEuclideanNormSq
      (finGlobalShellVector z (size n) (shell n)))
    hLowGap (finiteVectorEuclideanNormSq_nonneg _)
    (finiteVectorEuclideanNormSq_nonneg _) hLowEnergy
    (c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_nineFifths_normSq
      z size shell hSize n hOld hShell)
    hCross hBudget

end RiemannCvs.V23BoundaryWeylMainline
