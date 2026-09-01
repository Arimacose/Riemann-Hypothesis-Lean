import RiemannCvs.AsymptoticTailRelativeCoupling

noncomputable section
open scoped BigOperators

/-!
# Asymptotic tail operator compression

This module replaces entrywise cross-block estimates by a quadratic-form
compression argument.  On the union `[N+1,4N]`, the pole, Archimedean
remainder, and prime translation pieces have the uniform total form bound
`481/100`; the diagonal main term has no off-diagonal block.  Polarization
therefore controls the literal adjacent-shell cross energy without Frobenius or
absolute-entry Schur losses.

The exact logarithmic shell gaps then give a premise-free `4/9` relative bound
from `N = 13^5` onward.  On the dyadic schedule `13^5 * 2^n`, the module keeps
the sharper coefficient and proves its summability.
-/

namespace RiemannCvs.V23BoundaryWeylMainline

open Finset
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

theorem finiteVectorEuclideanNormSq_blockVector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) :
    finiteVectorEuclideanNormSq (finiteMatrixBlockVector x y) =
      finiteVectorEuclideanNormSq x + finiteVectorEuclideanNormSq y := by
  simp [finiteVectorEuclideanNormSq, finiteMatrixBlockVector]

theorem finiteMatrixBlockCrossEnergy_smul_left
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (r : ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    finiteMatrixBlockCrossEnergy A (fun i => r * x i) y =
      r * finiteMatrixBlockCrossEnergy A x y := by
  have hLeft :
      (∑ i, ∑ j, (r * x i) * A (Sum.inl i) (Sum.inr j) * y j) =
        r * ∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hRight :
      (∑ i, ∑ j, y i * A (Sum.inr i) (Sum.inl j) * (r * x j)) =
        r * ∑ i, ∑ j, y i * A (Sum.inr i) (Sum.inl j) * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold finiteMatrixBlockCrossEnergy
  rw [hLeft, hRight]
  ring

theorem finiteMatrixBlockCrossEnergy_neg_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    finiteMatrixBlockCrossEnergy A x (fun j => -y j) =
      -finiteMatrixBlockCrossEnergy A x y := by
  have hLeft :
      (∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * (-y j)) =
        -(∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inr j) * y j) := by
    simp_rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hRight :
      (∑ i, ∑ j, (-y i) * A (Sum.inr i) (Sum.inl j) * x j) =
        -(∑ i, ∑ j, y i * A (Sum.inr i) (Sum.inl j) * x j) := by
    simp_rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold finiteMatrixBlockCrossEnergy
  rw [hLeft, hRight]
  ring

theorem finiteMatrixBlockTailEnergy_neg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (y : κ → ℝ) :
    finiteMatrixBlockTailEnergy A (fun j => -y j) =
      finiteMatrixBlockTailEnergy A y := by
  unfold finiteMatrixBlockTailEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteVectorEuclideanNormSq_smul
    {ι : Type*} [Fintype ι]
    (r : ℝ) (x : ι → ℝ) :
    finiteVectorEuclideanNormSq (fun i => r * x i) =
      r ^ 2 * finiteVectorEuclideanNormSq x := by
  unfold finiteVectorEuclideanNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A uniform absolute quadratic-form bound on a full block matrix controls
its off-diagonal compression with the same operator coefficient.  The proof
uses polarization at every scalar rescaling and the discriminant adapter, so
it avoids both a Frobenius loss and entrywise absolute-value cancellation. -/
theorem finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : ι → ℝ) (y : κ → ℝ) (B : ℝ)
    (hB : 0 < B)
    (hBound : ∀ z : ι ⊕ κ → ℝ,
      |finiteMatrixQuadraticEnergy A z| ≤
        B * finiteVectorEuclideanNormSq z) :
    (finiteMatrixBlockCrossEnergy A x y) ^ 2 ≤
      B ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let lowNormSq := finiteVectorEuclideanNormSq x
  let highNormSq := finiteVectorEuclideanNormSq y
  let cross := finiteMatrixBlockCrossEnergy A x y
  have hLowNormSq : 0 ≤ lowNormSq := finiteVectorEuclideanNormSq_nonneg _
  have hHighNormSq : 0 ≤ highNormSq := finiteVectorEuclideanNormSq_nonneg _
  rcases hLowNormSq.eq_or_lt with hLowZero | hLowPos
  · have hx : ∀ i, x i = 0 := by
      intro i
      have hLowZero' : (∑ i, x i ^ 2) = 0 := by
        simpa only [lowNormSq, finiteVectorEuclideanNormSq] using hLowZero.symm
      have hxiSq : x i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i hi => sq_nonneg (x i))).mp hLowZero' i (Finset.mem_univ i)
      exact (sq_eq_zero_iff).mp hxiSq
    have hCrossZero : cross = 0 := by
      dsimp only [cross]
      unfold finiteMatrixBlockCrossEnergy
      simp [hx]
    change cross ^ 2 ≤ B ^ 2 * (lowNormSq * highNormSq)
    rw [hCrossZero, hLowZero.symm]
    norm_num
  · have hScaledLow : 0 < B * lowNormSq := mul_pos hB hLowPos
    have hDet : cross ^ 2 ≤
        (B * lowNormSq) * (B * highNormSq) := by
      apply relativeCoupling_of_scaledFormNonnegative
        (B * lowNormSq) cross (B * highNormSq) hScaledLow
      intro r
      let xr : ι → ℝ := fun i => r * x i
      let yn : κ → ℝ := fun j => -y j
      let plus := finiteMatrixBlockVector xr y
      let minus := finiteMatrixBlockVector xr yn
      have hPlus := hBound plus
      have hMinus := hBound minus
      have hPlusEnergy :
          finiteMatrixQuadraticEnergy A plus =
            finiteMatrixBlockBaseEnergy A xr +
              2 * finiteMatrixBlockCrossEnergy A xr y +
                finiteMatrixBlockTailEnergy A y := by
        simpa only [plus] using finiteMatrixQuadraticEnergy_blockVector A xr y
      have hMinusEnergy :
          finiteMatrixQuadraticEnergy A minus =
            finiteMatrixBlockBaseEnergy A xr -
              2 * finiteMatrixBlockCrossEnergy A xr y +
                finiteMatrixBlockTailEnergy A y := by
        rw [show minus = finiteMatrixBlockVector xr yn by rfl,
          finiteMatrixQuadraticEnergy_blockVector A xr yn,
          finiteMatrixBlockCrossEnergy_neg_right A xr y,
          finiteMatrixBlockTailEnergy_neg A y]
        ring
      have hPlusNorm :
          finiteVectorEuclideanNormSq plus = r ^ 2 * lowNormSq + highNormSq := by
        rw [show plus = finiteMatrixBlockVector xr y by rfl,
          finiteVectorEuclideanNormSq_blockVector,
          show finiteVectorEuclideanNormSq xr = r ^ 2 * lowNormSq by
            simpa only [xr, lowNormSq] using
              finiteVectorEuclideanNormSq_smul r x]
      have hMinusNorm :
          finiteVectorEuclideanNormSq minus = r ^ 2 * lowNormSq + highNormSq := by
        rw [show minus = finiteMatrixBlockVector xr yn by rfl,
          finiteVectorEuclideanNormSq_blockVector,
          show finiteVectorEuclideanNormSq xr = r ^ 2 * lowNormSq by
            simpa only [xr, lowNormSq] using
              finiteVectorEuclideanNormSq_smul r x]
        have hyn : finiteVectorEuclideanNormSq yn = highNormSq := by
          dsimp only [yn, highNormSq, finiteVectorEuclideanNormSq]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hyn]
      have hDifference :
          finiteMatrixQuadraticEnergy A plus -
              finiteMatrixQuadraticEnergy A minus =
            4 * r * cross := by
        rw [hPlusEnergy, hMinusEnergy,
          finiteMatrixBlockCrossEnergy_smul_left A r x y]
        dsimp only [cross]
        ring
      have hPolarization :
          2 * |r * cross| ≤ B * (r ^ 2 * lowNormSq + highNormSq) := by
        have hTriangle :
            |finiteMatrixQuadraticEnergy A plus -
                finiteMatrixQuadraticEnergy A minus| ≤
              |finiteMatrixQuadraticEnergy A plus| +
                |finiteMatrixQuadraticEnergy A minus| := abs_sub _ _
        rw [hDifference] at hTriangle
        rw [hPlusNorm] at hPlus
        rw [hMinusNorm] at hMinus
        have hNonnegative : 0 ≤ B * (r ^ 2 * lowNormSq + highNormSq) := by
          positivity
        have hBoth :
            |finiteMatrixQuadraticEnergy A plus| +
                |finiteMatrixQuadraticEnergy A minus| ≤
              2 * (B * (r ^ 2 * lowNormSq + highNormSq)) := by
          linarith
        have hFour : |4 * r * cross| ≤
            2 * (B * (r ^ 2 * lowNormSq + highNormSq)) :=
          hTriangle.trans hBoth
        rw [show |4 * r * cross| = 4 * |r * cross| by
          norm_num [abs_mul]
          ring] at hFour
        linarith
      have hLower : -2 * |r * cross| ≤ 2 * r * cross := by
        have h := neg_abs_le (r * cross)
        nlinarith
      nlinarith
    dsimp only [cross, lowNormSq, highNormSq] at hDet ⊢
    nlinarith

/-- The same entry envelope used for one dyadic shell remains uniformly
bounded on the three-shell union `[old+1,4*old]`. -/
lemma triadic_archCoefficient_le_sixtyThreeFiftieth
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old) :
    (shell : ℝ) *
        (1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
          2 * (1 / 4 : ℝ) / (3 * (old : ℝ))) ≤
      (63 / 50 : ℝ) := by
  have hOldPos : (0 : ℝ) < old := by positivity
  have hShellReal : (shell : ℝ) ≤ 3 * (old : ℝ) := by exact_mod_cast hShell
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hScale : (shell : ℝ) * E ≤ (3 * (old : ℝ)) * E :=
    mul_le_mul_of_nonneg_right hShellReal hE
  have hOldReal : (960 : ℝ) ≤ (old : ℝ) := by exact_mod_cast hOld
  have hInv : 1 / (4 * (old : ℝ)) ≤ (1 / 3840 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (old : ℝ))
      (by norm_num : (0 : ℝ) < 3840)]
    nlinarith
  calc
    (shell : ℝ) *
        (1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
          2 * (1 / 4 : ℝ) / (3 * (old : ℝ))) = (shell : ℝ) * E := rfl
    _ ≤ (3 * (old : ℝ)) * E := hScale
    _ = 5 / 4 + 1 / (4 * (old : ℝ)) := by
      dsimp only [E]
      field_simp [ne_of_gt hOldPos]
      ring
    _ ≤ 5 / 4 + 1 / 3840 := by linarith
    _ ≤ 63 / 50 := by norm_num

theorem evenRemainder_energy_abs_le_sixtyThreeFiftieth_of_centered
    (c : ℝ) (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤
          (1 / 4 : ℝ) / (old : ℝ)) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
          (finGlobalShellPositiveMode old shell)) x| ≤
      (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hEntry : ∀ i j : Fin shell,
      |logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤ E := by
    intro i j
    exact evenRemainder_entry_abs_le c (1 / 4) old shell (by omega)
      (by norm_num) hCentered i j
  have hEnergy := energy_abs_le_card_mul_of_entry_abs_le
    (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
      (finGlobalShellPositiveMode old shell)) x E hE hEntry
  have hCoeff : (Fintype.card (Fin shell) : ℝ) * E ≤ 63 / 50 := by
    simpa only [Fintype.card_fin, Nat.cast_id, E] using
      triadic_archCoefficient_le_sixtyThreeFiftieth old shell hOld hShell
  exact hEnergy.trans (mul_le_mul_of_nonneg_right hCoeff
    (finiteVectorEuclideanNormSq_nonneg x))

theorem oddRemainder_energy_abs_le_sixtyThreeFiftieth_of_centered
    (c : ℝ) (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤
          (1 / 4 : ℝ) / (old : ℝ)) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
          (finGlobalShellPositiveMode old shell)) x| ≤
      (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hEntry : ∀ i j : Fin shell,
      |logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤ E := by
    intro i j
    exact oddRemainder_entry_abs_le c (1 / 4) old shell (by omega)
      (by norm_num) hCentered i j
  have hEnergy := energy_abs_le_card_mul_of_entry_abs_le
    (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
      (finGlobalShellPositiveMode old shell)) x E hE hEntry
  have hCoeff : (Fintype.card (Fin shell) : ℝ) * E ≤ 63 / 50 := by
    simpa only [Fintype.card_fin, Nat.cast_id, E] using
      triadic_archCoefficient_le_sixtyThreeFiftieth old shell hOld hShell
  exact hEnergy.trans (mul_le_mul_of_nonneg_right hCoeff
    (finiteVectorEuclideanNormSq_nonneg x))

theorem c13_evenRemainder_energy_abs_le_sixtyThreeFiftieth
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix 13
          (finGlobalShellPositiveMode old shell)) x| ≤
      (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact evenRemainder_energy_abs_le_sixtyThreeFiftieth_of_centered
    13 old shell hOld hShell x
      (c13_centeredArchimedeanSymbol_shell_abs_le old shell hOld)

theorem c13_oddRemainder_energy_abs_le_sixtyThreeFiftieth
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix 13
          (finGlobalShellPositiveMode old shell)) x| ≤
      (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact oddRemainder_energy_abs_le_sixtyThreeFiftieth_of_centered
    13 old shell hOld hShell x
      (c13_centeredArchimedeanSymbol_shell_abs_le old shell hOld)

noncomputable def c13EvenShellTotalErrorMatrix
    (old shell : ℕ) : Matrix (Fin shell) (Fin shell) ℝ :=
  ∑ k, logarithmicCvSBuilderEvenPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old shell) k

noncomputable def c13OddShellTotalErrorMatrix
    (old shell : ℕ) : Matrix (Fin shell) (Fin shell) ℝ :=
  ∑ k, logarithmicCvSBuilderOddPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old shell) k

/-- On the three-shell union, pole, Archimedean remainder, and prime
translation errors have the uniform operator-form budget
`13/60 + 63/50 + 10/3 = 481/100`. -/
theorem c13EvenShellTotalError_energy_abs_le_fourHundredEightyOneHundredths
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13EvenShellTotalErrorMatrix old shell) x| ≤
      (481 / 100 : ℝ) * finiteVectorEuclideanNormSq x := by
  have hNorm : 0 ≤ finiteVectorEuclideanNormSq x :=
    finiteVectorEuclideanNormSq_nonneg x
  have hPoleRaw := c13_logarithmicCvSBuilderEvenShellPoleError_le_poleTail
    c13PrimePowerLocation c13PrimePowerBase old shell (by omega) x
  have hPole :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x| ≤
        (13 / 60 : ℝ) * finiteVectorEuclideanNormSq x :=
    hPoleRaw.trans (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld) hNorm)
  have hArch :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x| ≤
        (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
    simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using
      c13_evenRemainder_energy_abs_le_sixtyThreeFiftieth
        old shell hOld hShell x
  have hPrime :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| ≤
        (10 / 3 : ℝ) * finiteVectorEuclideanNormSq x := by
    simpa [logarithmicCvSBuilderEvenPositiveModeErrorMatrix] using
      c13_finiteLogarithmicPrimeEvenShellErrorEnergy_abs_le_tenThird
        old shell x
  rw [c13EvenShellTotalErrorMatrix, finiteMatrixQuadraticEnergy_sum,
    Fin.sum_univ_three]
  calc
    |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x +
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x +
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| ≤
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x| +
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x| +
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderEvenPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (13 / 60 : ℝ) * finiteVectorEuclideanNormSq x +
        (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x +
        (10 / 3 : ℝ) * finiteVectorEuclideanNormSq x := by
      exact add_le_add (add_le_add hPole hArch) hPrime
    _ = (481 / 100 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13OddShellTotalError_energy_abs_le_fourHundredEightyOneHundredths
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ 3 * old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddShellTotalErrorMatrix old shell) x| ≤
      (481 / 100 : ℝ) * finiteVectorEuclideanNormSq x := by
  have hNorm : 0 ≤ finiteVectorEuclideanNormSq x :=
    finiteVectorEuclideanNormSq_nonneg x
  have hPoleRaw := c13_logarithmicCvSBuilderOddShellPoleError_le_poleTail
    c13PrimePowerLocation c13PrimePowerBase old shell (by omega) x
  have hPole :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x| ≤
        (13 / 60 : ℝ) * finiteVectorEuclideanNormSq x :=
    hPoleRaw.trans (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld) hNorm)
  have hArch :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x| ≤
        (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x := by
    simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using
      c13_oddRemainder_energy_abs_le_sixtyThreeFiftieth
        old shell hOld hShell x
  have hPrime :
      |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| ≤
        (10 / 3 : ℝ) * finiteVectorEuclideanNormSq x := by
    simpa [logarithmicCvSBuilderOddPositiveModeErrorMatrix] using
      c13_finiteLogarithmicPrimeOddShellErrorEnergy_abs_le_tenThird
        old shell x
  rw [c13OddShellTotalErrorMatrix, finiteMatrixQuadraticEnergy_sum,
    Fin.sum_univ_three]
  calc
    |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x +
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x +
        finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| ≤
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 0) x| +
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 1) x| +
        |finiteMatrixQuadraticEnergy
          (logarithmicCvSBuilderOddPositiveModeErrorMatrix
            13 c13PrimePowerLocation c13PrimePowerBase
              (finGlobalShellPositiveMode old shell) 2) x| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (13 / 60 : ℝ) * finiteVectorEuclideanNormSq x +
        (63 / 50 : ℝ) * finiteVectorEuclideanNormSq x +
        (10 / 3 : ℝ) * finiteVectorEuclideanNormSq x := by
      exact add_le_add (add_le_add hPole hArch) hPrime
    _ = (481 / 100 : ℝ) * finiteVectorEuclideanNormSq x := by ring

/-- Retain the full logarithmically growing diagonal reserve instead of
flattening it to the uniform cutoff value `9/5`. -/
noncomputable def c13ShellDynamicGap (old : ℕ) : ℝ :=
  Real.log (old : ℝ) - 19 / 20 -
    (logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (old : ℝ)) +
      1 / 2 + 10 / 3)

theorem c13ShellDynamicGap_nonneg
    (old : ℕ) (hOld : 960 ≤ old) :
    0 ≤ c13ShellDynamicGap old := by
  simpa only [c13ShellDynamicGap] using
    c13_shell_complete_scalar_reserve_nonneg old hOld

theorem c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    c13ShellDynamicGap old * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (c13ShellDynamicGap old) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_evenRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simp [c13ShellDynamicGap])
  simpa using h

theorem c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    c13ShellDynamicGap old * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (c13ShellDynamicGap old) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_oddRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simp [c13ShellDynamicGap])
  simpa using h

/-- Euclidean coordinate norm is invariant under a finite equivalence. -/
theorem finiteVectorEuclideanNormSq_pullback
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (x : α → ℝ) :
    finiteVectorEuclideanNormSq (finiteVectorPullback e x) =
      finiteVectorEuclideanNormSq x := by
  unfold finiteVectorEuclideanNormSq
  symm
  apply Fintype.sum_equiv e
  intro i
  simp [finiteVectorPullback]

/-- A full quadratic-form bound is unchanged by exact reindexing. -/
theorem finiteMatrixQuadraticEnergy_pullback_abs_le
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix α α ℝ) (B : ℝ)
    (hBound : ∀ x : α → ℝ,
      |finiteMatrixQuadraticEnergy A x| ≤
        B * finiteVectorEuclideanNormSq x)
    (z : β → ℝ) :
    |finiteMatrixQuadraticEnergy (finiteMatrixPullback e A) z| ≤
      B * finiteVectorEuclideanNormSq z := by
  let x : α → ℝ := fun i => z (e i)
  have hPull : finiteVectorPullback e x = z := by
    funext j
    simp [finiteVectorPullback, x]
  have h := hBound x
  rw [finiteMatrixQuadraticEnergy_pullback e A x, hPull] at h
  have hNorm := finiteVectorEuclideanNormSq_pullback e x
  rw [hPull] at hNorm
  rw [hNorm]
  exact h

/-- Split `[old+1,4*old]` into the adjacent dyadic shells
`[old+1,2*old]` and `[2*old+1,4*old]`. -/
noncomputable def c13AdjacentDyadicShellSplitEquiv (old : ℕ) :
    Fin (3 * old) ≃ Fin old ⊕ Fin (2 * old) :=
  finBlockSplitEquiv (by omega)

noncomputable def c13EvenTriadicShellBuilderMatrix (old : ℕ) :
    Matrix (Fin (3 * old)) (Fin (3 * old)) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old (3 * old))

noncomputable def c13OddTriadicShellBuilderMatrix (old : ℕ) :
    Matrix (Fin (3 * old)) (Fin (3 * old)) ℝ :=
  logarithmicCvSBuilderOddPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (finGlobalShellPositiveMode old (3 * old))

noncomputable def c13EvenAdjacentDyadicShellBuilderMatrix (old : ℕ) :
    Matrix (Fin old ⊕ Fin (2 * old)) (Fin old ⊕ Fin (2 * old)) ℝ :=
  finiteMatrixPullback (c13AdjacentDyadicShellSplitEquiv old)
    (c13EvenTriadicShellBuilderMatrix old)

noncomputable def c13OddAdjacentDyadicShellBuilderMatrix (old : ℕ) :
    Matrix (Fin old ⊕ Fin (2 * old)) (Fin old ⊕ Fin (2 * old)) ℝ :=
  finiteMatrixPullback (c13AdjacentDyadicShellSplitEquiv old)
    (c13OddTriadicShellBuilderMatrix old)

noncomputable def c13EvenAdjacentDyadicShellErrorMatrix (old : ℕ) :
    Matrix (Fin old ⊕ Fin (2 * old)) (Fin old ⊕ Fin (2 * old)) ℝ :=
  finiteMatrixPullback (c13AdjacentDyadicShellSplitEquiv old)
    (c13EvenShellTotalErrorMatrix old (3 * old))

noncomputable def c13OddAdjacentDyadicShellErrorMatrix (old : ℕ) :
    Matrix (Fin old ⊕ Fin (2 * old)) (Fin old ⊕ Fin (2 * old)) ℝ :=
  finiteMatrixPullback (c13AdjacentDyadicShellSplitEquiv old)
    (c13OddShellTotalErrorMatrix old (3 * old))

theorem c13EvenAdjacentDyadicShellBuilderMatrix_inl_inl
    (old : ℕ) (i j : Fin old) :
    c13EvenAdjacentDyadicShellBuilderMatrix old (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old old) i j := by
  simp [c13EvenAdjacentDyadicShellBuilderMatrix,
    c13EvenTriadicShellBuilderMatrix, finiteMatrixPullback,
    c13AdjacentDyadicShellSplitEquiv, finBlockSplitEquiv,
    logarithmicCvSBuilderEvenPositiveModeMatrix,
    finGlobalShellPositiveMode]

theorem c13EvenAdjacentDyadicShellBuilderMatrix_inr_inr
    (old : ℕ) (i j : Fin (2 * old)) :
    c13EvenAdjacentDyadicShellBuilderMatrix old (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode (2 * old) (2 * old)) i j := by
  simp [c13EvenAdjacentDyadicShellBuilderMatrix,
    c13EvenTriadicShellBuilderMatrix, finiteMatrixPullback,
    c13AdjacentDyadicShellSplitEquiv, finBlockSplitEquiv,
    logarithmicCvSBuilderEvenPositiveModeMatrix,
    finGlobalShellPositiveMode]
  congr 2 <;> omega

theorem c13OddAdjacentDyadicShellBuilderMatrix_inl_inl
    (old : ℕ) (i j : Fin old) :
    c13OddAdjacentDyadicShellBuilderMatrix old (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old old) i j := by
  simp [c13OddAdjacentDyadicShellBuilderMatrix,
    c13OddTriadicShellBuilderMatrix, finiteMatrixPullback,
    c13AdjacentDyadicShellSplitEquiv, finBlockSplitEquiv,
    logarithmicCvSBuilderOddPositiveModeMatrix,
    finGlobalShellPositiveMode]

theorem c13OddAdjacentDyadicShellBuilderMatrix_inr_inr
    (old : ℕ) (i j : Fin (2 * old)) :
    c13OddAdjacentDyadicShellBuilderMatrix old (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode (2 * old) (2 * old)) i j := by
  simp [c13OddAdjacentDyadicShellBuilderMatrix,
    c13OddTriadicShellBuilderMatrix, finiteMatrixPullback,
    c13AdjacentDyadicShellSplitEquiv, finBlockSplitEquiv,
    logarithmicCvSBuilderOddPositiveModeMatrix,
    finGlobalShellPositiveMode]
  congr 2 <;> omega

theorem c13EvenAdjacentDyadicShellBaseEnergy_eq
    (old : ℕ) (x : Fin old → ℝ) :
    finiteMatrixBlockBaseEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) x =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode old old)) x := by
  unfold finiteMatrixBlockBaseEnergy finiteMatrixQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [c13EvenAdjacentDyadicShellBuilderMatrix_inl_inl]

theorem c13EvenAdjacentDyadicShellTailEnergy_eq
    (old : ℕ) (y : Fin (2 * old) → ℝ) :
    finiteMatrixBlockTailEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) y =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * old) (2 * old))) y := by
  unfold finiteMatrixBlockTailEnergy finiteMatrixQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [c13EvenAdjacentDyadicShellBuilderMatrix_inr_inr]

theorem c13OddAdjacentDyadicShellBaseEnergy_eq
    (old : ℕ) (x : Fin old → ℝ) :
    finiteMatrixBlockBaseEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) x =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode old old)) x := by
  unfold finiteMatrixBlockBaseEnergy finiteMatrixQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [c13OddAdjacentDyadicShellBuilderMatrix_inl_inl]

theorem c13OddAdjacentDyadicShellTailEnergy_eq
    (old : ℕ) (y : Fin (2 * old) → ℝ) :
    finiteMatrixBlockTailEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) y =
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
            (finGlobalShellPositiveMode (2 * old) (2 * old))) y := by
  unfold finiteMatrixBlockTailEnergy finiteMatrixQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [c13OddAdjacentDyadicShellBuilderMatrix_inr_inr]

theorem c13EvenAdjacentDyadicShellBuilder_offdiag_eq_error
    (old : ℕ) (u v : Fin old ⊕ Fin (2 * old)) (huv : u ≠ v) :
    c13EvenAdjacentDyadicShellBuilderMatrix old u v =
      c13EvenAdjacentDyadicShellErrorMatrix old u v := by
  let e := c13AdjacentDyadicShellSplitEquiv old
  have hIndex : e.symm u ≠ e.symm v := by
    intro h
    exact huv (e.symm.injective h)
  change c13EvenTriadicShellBuilderMatrix old (e.symm u) (e.symm v) =
    c13EvenShellTotalErrorMatrix old (3 * old) (e.symm u) (e.symm v)
  rw [c13EvenTriadicShellBuilderMatrix,
    logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition]
  simp [logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    hIndex, c13EvenShellTotalErrorMatrix]

theorem c13OddAdjacentDyadicShellBuilder_offdiag_eq_error
    (old : ℕ) (u v : Fin old ⊕ Fin (2 * old)) (huv : u ≠ v) :
    c13OddAdjacentDyadicShellBuilderMatrix old u v =
      c13OddAdjacentDyadicShellErrorMatrix old u v := by
  let e := c13AdjacentDyadicShellSplitEquiv old
  have hIndex : e.symm u ≠ e.symm v := by
    intro h
    exact huv (e.symm.injective h)
  change c13OddTriadicShellBuilderMatrix old (e.symm u) (e.symm v) =
    c13OddShellTotalErrorMatrix old (3 * old) (e.symm u) (e.symm v)
  rw [c13OddTriadicShellBuilderMatrix,
    logarithmicCvSBuilderOddPositiveModeMatrix_decomposition]
  simp [logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    hIndex, c13OddShellTotalErrorMatrix]

theorem c13EvenAdjacentDyadicShellCrossEnergy_eq_error
    (old : ℕ) (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) x y =
      finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellErrorMatrix old) x y := by
  unfold finiteMatrixBlockCrossEnergy
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [c13EvenAdjacentDyadicShellBuilder_offdiag_eq_error old
      (Sum.inl i) (Sum.inr j) (by simp)]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [c13EvenAdjacentDyadicShellBuilder_offdiag_eq_error old
      (Sum.inr i) (Sum.inl j) (by simp)]

theorem c13OddAdjacentDyadicShellCrossEnergy_eq_error
    (old : ℕ) (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) x y =
      finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellErrorMatrix old) x y := by
  unfold finiteMatrixBlockCrossEnergy
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [c13OddAdjacentDyadicShellBuilder_offdiag_eq_error old
      (Sum.inl i) (Sum.inr j) (by simp)]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [c13OddAdjacentDyadicShellBuilder_offdiag_eq_error old
      (Sum.inr i) (Sum.inl j) (by simp)]

theorem c13EvenAdjacentDyadicShellError_energy_abs_le_fourHundredEightyOneHundredths
    (old : ℕ) (hOld : 960 ≤ old)
    (z : Fin old ⊕ Fin (2 * old) → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13EvenAdjacentDyadicShellErrorMatrix old) z| ≤
      (481 / 100 : ℝ) * finiteVectorEuclideanNormSq z := by
  unfold c13EvenAdjacentDyadicShellErrorMatrix
  apply finiteMatrixQuadraticEnergy_pullback_abs_le
  intro x
  exact c13EvenShellTotalError_energy_abs_le_fourHundredEightyOneHundredths
    old (3 * old) hOld (by omega) x

theorem c13OddAdjacentDyadicShellError_energy_abs_le_fourHundredEightyOneHundredths
    (old : ℕ) (hOld : 960 ≤ old)
    (z : Fin old ⊕ Fin (2 * old) → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddAdjacentDyadicShellErrorMatrix old) z| ≤
      (481 / 100 : ℝ) * finiteVectorEuclideanNormSq z := by
  unfold c13OddAdjacentDyadicShellErrorMatrix
  apply finiteMatrixQuadraticEnergy_pullback_abs_le
  intro x
  exact c13OddShellTotalError_energy_abs_le_fourHundredEightyOneHundredths
    old (3 * old) hOld (by omega) x

/-- Concrete operator-norm cross budget for adjacent cutoff-13 even shells. -/
theorem c13EvenAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget
    (old : ℕ) (hOld : 960 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      (481 / 100 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenAdjacentDyadicShellCrossEnergy_eq_error]
  exact finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13EvenAdjacentDyadicShellErrorMatrix old) x y (481 / 100)
      (by norm_num)
      (c13EvenAdjacentDyadicShellError_energy_abs_le_fourHundredEightyOneHundredths
        old hOld)

/-- Concrete operator-norm cross budget for adjacent cutoff-13 odd shells. -/
theorem c13OddAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget
    (old : ℕ) (hOld : 960 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      (481 / 100 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddAdjacentDyadicShellCrossEnergy_eq_error]
  exact finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13OddAdjacentDyadicShellErrorMatrix old) x y (481 / 100)
      (by norm_num)
      (c13OddAdjacentDyadicShellError_energy_abs_le_fourHundredEightyOneHundredths
        old hOld)

/-- The dynamic gap keeps the exact logarithmic gain; the three losses total
at most five once the pole tail is bounded by `13/60`. -/
theorem c13ShellDynamicGap_ge_log_sub_five
    (old : ℕ) (hOld : 960 ≤ old) :
    Real.log (old : ℝ) - 5 ≤ c13ShellDynamicGap old := by
  have hPole := c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld
  unfold c13ShellDynamicGap
  nlinarith

lemma sixtyFourFifths_lt_log_nat_of_ge_371293
    (old : ℕ) (hOld : 371293 ≤ old) :
    (64 / 5 : ℝ) < Real.log (old : ℝ) := by
  have hOldReal : (371293 : ℝ) ≤ (old : ℝ) := by exact_mod_cast hOld
  have hLogMono : Real.log (371293 : ℝ) ≤ Real.log (old : ℝ) :=
    Real.log_le_log (by norm_num) hOldReal
  have hLogPower : Real.log (371293 : ℝ) = 5 * Real.log 13 := by
    rw [show (371293 : ℝ) = 13 ^ (5 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [hLogPower] at hLogMono
  nlinarith [sixtyFourTwentyFive_lt_log_thirteen]

theorem c13ShellDynamicGap_ge_thirtyNineFifths_of_ge_371293
    (old : ℕ) (hOld : 371293 ≤ old) :
    (39 / 5 : ℝ) ≤ c13ShellDynamicGap old := by
  have hOld960 : 960 ≤ old := by omega
  have hGap := c13ShellDynamicGap_ge_log_sub_five old hOld960
  have hLog := sixtyFourFifths_lt_log_nat_of_ge_371293 old hOld
  nlinarith

/-- From `13^5 = 371293` onward, the operator budget already fits inside the
balanced relative-coupling coefficient `4/9` for two adjacent dyadic shells. -/
theorem c13_operatorBudget_le_fourNinth_dynamicGap_product
    (old : ℕ) (hOld : 371293 ≤ old) :
    (481 / 100 : ℝ) ^ 2 ≤
      (4 / 9 : ℝ) * c13ShellDynamicGap old * c13ShellDynamicGap (2 * old) := by
  have hLow := c13ShellDynamicGap_ge_thirtyNineFifths_of_ge_371293 old hOld
  have hOld2 : 371293 ≤ 2 * old := by omega
  have hHigh :=
    c13ShellDynamicGap_ge_thirtyNineFifths_of_ge_371293 (2 * old) hOld2
  have hGapNonneg : 0 ≤ c13ShellDynamicGap old := by
    exact c13ShellDynamicGap_nonneg old (by omega)
  calc
    (481 / 100 : ℝ) ^ 2 ≤
        (4 / 9 : ℝ) * (39 / 5) * (39 / 5) := by norm_num
    _ ≤ (4 / 9 : ℝ) * c13ShellDynamicGap old * (39 / 5) := by
      nlinarith
    _ ≤ (4 / 9 : ℝ) * c13ShellDynamicGap old *
        c13ShellDynamicGap (2 * old) :=
      mul_le_mul_of_nonneg_left hHigh (by positivity)

/-- Actual even adjacent-shell relative coupling from the operator budget and
the two dynamic coercive gaps. -/
theorem c13EvenAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    (old : ℕ) (hOld : 960 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (481 / 100 : ℝ) ^ 2 ≤
      q * c13ShellDynamicGap old * c13ShellDynamicGap (2 * old)) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix old) x *
        finiteMatrixBlockTailEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix old) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy
      (c13EvenAdjacentDyadicShellBuilderMatrix old) x)
    (finiteMatrixBlockTailEnergy
      (c13EvenAdjacentDyadicShellBuilderMatrix old) y)
    (finiteMatrixBlockCrossEnergy
      (c13EvenAdjacentDyadicShellBuilderMatrix old) x y)
    (c13ShellDynamicGap old) (c13ShellDynamicGap (2 * old))
    ((481 / 100 : ℝ) ^ 2) q
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (c13ShellDynamicGap_nonneg old hOld)
    (c13ShellDynamicGap_nonneg (2 * old) (by omega)) hq
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  · rw [c13EvenAdjacentDyadicShellBaseEnergy_eq]
    exact c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      old old hOld le_rfl x
  · rw [c13EvenAdjacentDyadicShellTailEnergy_eq]
    exact c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
      (2 * old) (2 * old) (by omega) le_rfl y
  · exact c13EvenAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget
      old hOld x y
  · exact hBudget

/-- Actual odd adjacent-shell relative coupling from the operator budget and
the two dynamic coercive gaps. -/
theorem c13OddAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    (old : ℕ) (hOld : 960 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (481 / 100 : ℝ) ^ 2 ≤
      q * c13ShellDynamicGap old * c13ShellDynamicGap (2 * old)) :
    (finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix old) x *
        finiteMatrixBlockTailEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix old) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy
      (c13OddAdjacentDyadicShellBuilderMatrix old) x)
    (finiteMatrixBlockTailEnergy
      (c13OddAdjacentDyadicShellBuilderMatrix old) y)
    (finiteMatrixBlockCrossEnergy
      (c13OddAdjacentDyadicShellBuilderMatrix old) x y)
    (c13ShellDynamicGap old) (c13ShellDynamicGap (2 * old))
    ((481 / 100 : ℝ) ^ 2) q
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (c13ShellDynamicGap_nonneg old hOld)
    (c13ShellDynamicGap_nonneg (2 * old) (by omega)) hq
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  · rw [c13OddAdjacentDyadicShellBaseEnergy_eq]
    exact c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      old old hOld le_rfl x
  · rw [c13OddAdjacentDyadicShellTailEnergy_eq]
    exact c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
      (2 * old) (2 * old) (by omega) le_rfl y
  · exact c13OddAdjacentDyadicShellCrossEnergy_sq_le_operatorBudget
      old hOld x y
  · exact hBudget

/-- Premise-free balanced coupling for actual adjacent even shells from
`13^5` onward. -/
theorem c13EvenAdjacentDyadicShellCrossEnergy_relative_fourNinth_of_ge_371293
    (old : ℕ) (hOld : 371293 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      (4 / 9 : ℝ) * finiteMatrixBlockBaseEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix old) x *
        finiteMatrixBlockTailEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix old) y := by
  exact c13EvenAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    old (by omega) x y (4 / 9) (by norm_num)
      (c13_operatorBudget_le_fourNinth_dynamicGap_product old hOld)

/-- Premise-free balanced coupling for actual adjacent odd shells from
`13^5` onward. -/
theorem c13OddAdjacentDyadicShellCrossEnergy_relative_fourNinth_of_ge_371293
    (old : ℕ) (hOld : 371293 ≤ old)
    (x : Fin old → ℝ) (y : Fin (2 * old) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix old) x y) ^ 2 ≤
      (4 / 9 : ℝ) * finiteMatrixBlockBaseEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix old) x *
        finiteMatrixBlockTailEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix old) y := by
  exact c13OddAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    old (by omega) x y (4 / 9) (by norm_num)
      (c13_operatorBudget_le_fourNinth_dynamicGap_product old hOld)

noncomputable def c13DyadicShellBase (n : ℕ) : ℕ :=
  371293 * 2 ^ n

noncomputable def c13DyadicGapLower (n : ℕ) : ℝ :=
  39 / 5 + (69 / 100) * (n : ℝ)

noncomputable def c13DyadicRelativeEnvelope (n : ℕ) : ℝ :=
  (481 / 100 : ℝ) ^ 2 / c13DyadicGapLower n ^ 2

theorem c13DyadicShellBase_ge_371293 (n : ℕ) :
    371293 ≤ c13DyadicShellBase n := by
  have hPow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  unfold c13DyadicShellBase
  nlinarith

theorem c13DyadicShellBase_succ (n : ℕ) :
    c13DyadicShellBase (n + 1) = 2 * c13DyadicShellBase n := by
  simp [c13DyadicShellBase, pow_succ]
  ring

lemma c13_log_dyadicShellBase
    (n : ℕ) :
    Real.log (c13DyadicShellBase n : ℝ) =
      5 * Real.log 13 + (n : ℝ) * Real.log 2 := by
  rw [c13DyadicShellBase, Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by norm_num) (by positivity)]
  change Real.log (371293 : ℝ) + Real.log ((2 : ℝ) ^ n) =
    5 * Real.log 13 + (n : ℝ) * Real.log 2
  rw [show (371293 : ℝ) = 13 ^ (5 : ℕ) by norm_num,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem c13DyadicGapLower_le_dynamicGap
    (n : ℕ) :
    c13DyadicGapLower n ≤ c13ShellDynamicGap (c13DyadicShellBase n) := by
  have hBase := c13DyadicShellBase_ge_371293 n
  have hGap := c13ShellDynamicGap_ge_log_sub_five
    (c13DyadicShellBase n) (by omega)
  have hLog13 := sixtyFourTwentyFive_lt_log_thirteen
  have hLog2 := log_two_gt_sixtyNineHundredths
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hNLog2 : (69 / 100 : ℝ) * (n : ℝ) ≤
      (n : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hLog2.le hn
    nlinarith
  rw [c13_log_dyadicShellBase] at hGap
  unfold c13DyadicGapLower
  nlinarith

theorem c13DyadicGapLower_pos (n : ℕ) :
    0 < c13DyadicGapLower n := by
  unfold c13DyadicGapLower
  positivity

theorem c13DyadicRelativeEnvelope_nonneg (n : ℕ) :
    0 ≤ c13DyadicRelativeEnvelope n := by
  unfold c13DyadicRelativeEnvelope
  positivity

theorem c13DyadicRelativeEnvelope_budget
    (n : ℕ) :
    (481 / 100 : ℝ) ^ 2 ≤
      c13DyadicRelativeEnvelope n *
        c13ShellDynamicGap (c13DyadicShellBase n) *
          c13ShellDynamicGap (2 * c13DyadicShellBase n) := by
  let L := c13DyadicGapLower n
  let g₀ := c13ShellDynamicGap (c13DyadicShellBase n)
  let g₁ := c13ShellDynamicGap (2 * c13DyadicShellBase n)
  have hL : 0 < L := c13DyadicGapLower_pos n
  have hL0 : L ≤ g₀ := c13DyadicGapLower_le_dynamicGap n
  have hL1 : L ≤ g₁ := by
    have hNext := c13DyadicGapLower_le_dynamicGap (n + 1)
    have hMonotone : L ≤ c13DyadicGapLower (n + 1) := by
      dsimp only [L]
      unfold c13DyadicGapLower
      push_cast
      norm_num
    rw [c13DyadicShellBase_succ] at hNext
    exact hMonotone.trans hNext
  have hg₀ : 0 ≤ g₀ := hL.le.trans hL0
  have hProduct : L ^ 2 ≤ g₀ * g₁ := by
    calc
      L ^ 2 = L * L := by ring
      _ ≤ g₀ * L := mul_le_mul_of_nonneg_right hL0 hL.le
      _ ≤ g₀ * g₁ := mul_le_mul_of_nonneg_left hL1 hg₀
  have hEnvelopeIdentity :
      c13DyadicRelativeEnvelope n * L ^ 2 = (481 / 100 : ℝ) ^ 2 := by
    unfold c13DyadicRelativeEnvelope
    dsimp only [L]
    field_simp [ne_of_gt (c13DyadicGapLower_pos n)]
  calc
    (481 / 100 : ℝ) ^ 2 =
        c13DyadicRelativeEnvelope n * L ^ 2 := hEnvelopeIdentity.symm
    _ ≤ c13DyadicRelativeEnvelope n * (g₀ * g₁) :=
      mul_le_mul_of_nonneg_left hProduct (c13DyadicRelativeEnvelope_nonneg n)
    _ = c13DyadicRelativeEnvelope n * g₀ * g₁ := by ring

theorem summable_c13DyadicRelativeEnvelope :
    Summable c13DyadicRelativeEnvelope := by
  have hSeries :=
    (Real.summable_one_div_nat_add_rpow (260 / 23) 2).2 (by norm_num)
  have hScaled := hSeries.mul_left
    (((481 / 100 : ℝ) ^ 2) / (69 / 100 : ℝ) ^ 2)
  apply hScaled.congr
  intro n
  rw [show |(n : ℝ) + 260 / 23| = (n : ℝ) + 260 / 23 by
    rw [abs_of_pos]
    positivity]
  rw [Real.rpow_two]
  unfold c13DyadicRelativeEnvelope c13DyadicGapLower
  field_simp
  ring

theorem c13EvenDyadicShellCrossEnergy_relative_summableEnvelope
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n) → ℝ)
    (y : Fin (2 * c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) x y) ^ 2 ≤
      c13DyadicRelativeEnvelope n *
        finiteMatrixBlockBaseEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) y := by
  exact c13EvenAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    (c13DyadicShellBase n) (by
      have := c13DyadicShellBase_ge_371293 n
      omega) x y (c13DyadicRelativeEnvelope n)
    (c13DyadicRelativeEnvelope_nonneg n)
    (c13DyadicRelativeEnvelope_budget n)

theorem c13OddDyadicShellCrossEnergy_relative_summableEnvelope
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n) → ℝ)
    (y : Fin (2 * c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) x y) ^ 2 ≤
      c13DyadicRelativeEnvelope n *
        finiteMatrixBlockBaseEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddAdjacentDyadicShellBuilderMatrix (c13DyadicShellBase n)) y := by
  exact c13OddAdjacentDyadicShellCrossEnergy_relative_of_dynamicBudget
    (c13DyadicShellBase n) (by
      have := c13DyadicShellBase_ge_371293 n
      omega) x y (c13DyadicRelativeEnvelope n)
    (c13DyadicRelativeEnvelope_nonneg n)
    (c13DyadicRelativeEnvelope_budget n)

end RiemannCvs.V23BoundaryWeylMainline
