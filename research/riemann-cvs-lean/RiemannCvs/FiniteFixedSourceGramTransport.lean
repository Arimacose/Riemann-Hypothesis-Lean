import RiemannCvs.FiniteResidualBandTransport

/-!
# Source-preconditioned transport for the exceptional fixed block

Instead of replacing the shifted fixed source energy by its tiny Euclidean
gap, retain the complete source Gram geometry and use only the analytic
Euclidean floor on the remote target shell.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def c13OddFixedReferenceEnergy
    (F : ℕ) (x : Fin F → ℝ) : ℝ :=
  (249 / 250 : ℝ) *
    (c13OddBuilderFiniteIntervalEnergy 0 F x +
      (1 / 1024 : ℝ) * ∑ i, x i ^ 2)

noncomputable def c13OddFixedRemoteColumnEnergy
    (F N : ℕ) (x : Fin F → ℝ) : ℝ :=
  ∑ j : Fin N,
    (∑ i : Fin F,
      c13OddFiniteIntervalBuilderLoewnerRemoteEntry 0 F N i j * x i) ^ 2

theorem c13OddFixedRemote_crossEnergy_sq_le_columnEnergy_mul_norm
    (F N : ℕ) (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteOddBuilderMatrix 0 F N) x y) ^ 2 ≤
      c13OddFixedRemoteColumnEnergy F N x * (∑ j, y j ^ 2) := by
  rw [c13FiniteIntervalRemoteOddBuilderMatrix_crossEnergy_eq_fullLoewner]
  unfold c13OddFiniteIntervalBuilderLoewnerRemoteCrossEnergy
    c13OddFixedRemoteColumnEnergy
  rw [Finset.sum_product]
  have hRewrite :
      (∑ i : Fin F, ∑ j : Fin N,
        c13OddFiniteIntervalBuilderLoewnerRemoteEntry 0 F N i j *
          (x i * y j)) =
        ∑ j : Fin N,
          (∑ i : Fin F,
            c13OddFiniteIntervalBuilderLoewnerRemoteEntry 0 F N i j * x i) *
            y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hRewrite]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin N))
    (fun j => ∑ i : Fin F,
      c13OddFiniteIntervalBuilderLoewnerRemoteEntry 0 F N i j * x i)
    y

theorem c13OddFixedRemote_relative_of_sourceGram
    (F N : ℕ) (hN : 15360 ≤ N)
    (beta q : ℝ) (hBeta : 0 < beta) (hq : 0 ≤ q)
    (hBudget : beta ≤ q * (24 / 5 : ℝ))
    (hGram : ∀ x : Fin F → ℝ,
      c13OddFixedRemoteColumnEnergy F N x ≤
        beta * c13OddFixedReferenceEnergy F x)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteOddBuilderMatrix 0 F N) x y) ^ 2 ≤
      q * c13OddFixedReferenceEnergy F x *
        c13OddBuilderShellEnergy N N y := by
  have hColumnNonneg : 0 ≤ c13OddFixedRemoteColumnEnergy F N x := by
    unfold c13OddFixedRemoteColumnEnergy
    positivity
  have hSourceNonneg : 0 ≤ c13OddFixedReferenceEnergy F x := by
    have h := hGram x
    nlinarith
  have hNormNonneg : 0 ≤ ∑ j : Fin N, y j ^ 2 := by positivity
  have hCross := c13OddFixedRemote_crossEnergy_sq_le_columnEnergy_mul_norm
    F N x y
  have hGramScaled := mul_le_mul_of_nonneg_right (hGram x) hNormNonneg
  have hBudgetScaled := mul_le_mul_of_nonneg_right hBudget hSourceNonneg
  have hTarget := c13OddBuilderShellEnergy_ge_twentyFourFifths_of_ge15360
    N hN y
  calc
    (finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteOddBuilderMatrix 0 F N) x y) ^ 2 ≤
        c13OddFixedRemoteColumnEnergy F N x * (∑ j, y j ^ 2) := hCross
    _ ≤ beta * c13OddFixedReferenceEnergy F x * (∑ j, y j ^ 2) := by
      simpa [mul_assoc] using hGramScaled
    _ ≤ (q * (24 / 5 : ℝ)) * c13OddFixedReferenceEnergy F x *
          (∑ j, y j ^ 2) := by
      exact mul_le_mul_of_nonneg_right hBudgetScaled hNormNonneg
    _ = q * c13OddFixedReferenceEnergy F x *
          ((24 / 5 : ℝ) * ∑ j, y j ^ 2) := by ring
    _ ≤ q * c13OddFixedReferenceEnergy F x *
          c13OddBuilderShellEnergy N N y := by
      exact mul_le_mul_of_nonneg_left hTarget
        (mul_nonneg hq hSourceNonneg)

structure C13OddFixedSourceGramCertificate
    (F N : ℕ) (beta : ℝ) : Prop where
  sourceGram : ∀ x : Fin F → ℝ,
    c13OddFixedRemoteColumnEnergy F N x ≤
      beta * c13OddFixedReferenceEnergy F x

lemma c13OddFixedRemoteBudget_20_15360 :
    (3 / 1250 : ℝ) = (1 / 2000 : ℝ) * (24 / 5) := by
  norm_num

lemma v23_lowFrontier_afterFixedGramChannel :
    (2 / 27 : ℝ) - 7 / 120 - 1 / 350 - 1 / 500 - 1 / 795 -
        3 * (1 / 900) - 1 / 2000 = 23209 / 4006800 := by
  norm_num

theorem c13OddFixedRemoteBuilder_20_15360_relative_oneOver2000
    (hSource : C13OddFixedSourceGramCertificate 20 15360 (3 / 1250 : ℝ))
    (x : Fin 20 → ℝ) (y : Fin 15360 → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FiniteIntervalRemoteOddBuilderMatrix 0 20 15360) x y) ^ 2 ≤
      (1 / 2000 : ℝ) * c13OddFixedReferenceEnergy 20 x *
        c13OddBuilderShellEnergy 15360 15360 y := by
  exact c13OddFixedRemote_relative_of_sourceGram
    20 15360 (by norm_num) (3 / 1250) (1 / 2000)
    (by norm_num) (by norm_num) (by norm_num)
    hSource.sourceGram x y

end RiemannCvs.V23BoundaryWeylMainline
