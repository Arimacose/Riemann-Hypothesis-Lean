import RiemannCvs.AdjacentArchimedeanHilbertSchmidt

/-!
# Sharp reserve for the adjacent analytic bridge

`AdjacentArchimedeanHilbertSchmidt` closed the first adjacent analytic
rectangle with coefficient `24/25`.  This file keeps the same three-channel
operator estimate but recovers reserve that was hidden by coarse constants:

* `log 3840 = 8 log 2 + log 3 + log 5 > 20633/2500`;
* the pole amplitudes at `M` and `2M` are at most `229/5000` and
  `229/10000`, using the kernel-checked bound `3.14 < pi`;
* the two diagonal gaps are therefore at least `428/125` and `207/50`.

The full pole--Archimedean--prime amplitude is `27151/7500`.  Exact rational
arithmetic then improves the even and odd adjacent relative coefficient to
`37/40`.  Thus every analytic scale beginning at `M = 3840` carries a strict
`3/40` local reserve before any non-adjacent transport channels are charged.
No floating-point datum or external numerical oracle enters the proof.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.PoleSeparatedBands

lemma c13_log_nat_ge_3840_gt_20633Over2500
    (M : ℕ) (hM : 3840 ≤ M) :
    (20633 / 2500 : ℝ) < Real.log (M : ℝ) := by
  have hMReal : (3840 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLogMono : Real.log (3840 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMReal
  have hLog3840 :
      Real.log (3840 : ℝ) =
        8 * Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (3840 : ℝ) = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3 * 5 by
      norm_num]
    repeat' rw [Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLog3840] at hLogMono
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
    Real.log_five_gt_d9]

lemma c13_logarithmicCvSPoleTail_le_229Over5000
    (M : ℕ) (hM : 3840 ≤ M) :
    logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (M : ℝ)) ≤ (229 / 5000 : ℝ) := by
  have hMReal : (3840 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hPiSq : (314 / 100 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2]
  have hDenLower :
      (8 * (314 / 100 : ℝ) ^ 2 * 3840) ≤
        8 * Real.pi ^ 2 * (M : ℝ) := by
    calc
      8 * (314 / 100 : ℝ) ^ 2 * 3840 ≤ 8 * Real.pi ^ 2 * 3840 := by
        nlinarith
      _ ≤ 8 * Real.pi ^ 2 * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hMReal (by positivity)
  have hDenPos : 0 < 8 * Real.pi ^ 2 * (M : ℝ) := by positivity
  rw [div_le_iff₀ hDenPos]
  nlinarith [c13_logarithmicCvSPoleScale_le_13872]

lemma c13_logarithmicCvSPoleTail_le_229Over10000_of_ge_7680
    (M : ℕ) (hM : 7680 ≤ M) :
    logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (M : ℝ)) ≤ (229 / 10000 : ℝ) := by
  have hMReal : (7680 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hPiSq : (314 / 100 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2]
  have hDenLower :
      (8 * (314 / 100 : ℝ) ^ 2 * 7680) ≤
        8 * Real.pi ^ 2 * (M : ℝ) := by
    calc
      8 * (314 / 100 : ℝ) ^ 2 * 7680 ≤ 8 * Real.pi ^ 2 * 7680 := by
        nlinarith
      _ ≤ 8 * Real.pi ^ 2 * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hMReal (by positivity)
  have hDenPos : 0 < 8 * Real.pi ^ 2 * (M : ℝ) := by positivity
  rw [div_le_iff₀ hDenPos]
  nlinarith [c13_logarithmicCvSPoleScale_le_13872]

theorem c13EvenPoleCoreNewestCrossEnergy_sq_le_229Over5000
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (229 / 5000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13EvenPoleCoreNewestBlock M N) x y (229 / 5000 : ℝ) (by norm_num)
  intro z
  exact (c13EvenPoleCoreNewestEnergy_abs_le_poleTail M N (by omega) hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_229Over5000 M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

theorem c13OddPoleCoreNewestCrossEnergy_sq_le_229Over5000
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (229 / 5000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13OddPoleCoreNewestBlock M N) x y (229 / 5000 : ℝ) (by norm_num)
  intro z
  exact (c13OddPoleCoreNewestEnergy_abs_le_poleTail M N (by omega) hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_229Over5000 M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

theorem c13EvenCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_27151Over7500
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenCoreNewestTotalErrorBlock M (2 * M)) x y) ^ 2 ≤
      (27151 / 7500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy
    (c13EvenPoleCoreNewestBlock M (2 * M)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13EvenArchimedeanCoreNewestBlock M (2 * M)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13EvenPrimeCoreNewestBlock M (2 * M)) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hPole : pole ^ 2 ≤ (229 / 5000 : ℝ) ^ 2 * E :=
    c13EvenPoleCoreNewestCrossEnergy_sq_le_229Over5000
      M (2 * M) hM (by omega) x y
  have hArch : arch ^ 2 ≤ (241 / 1000 : ℝ) ^ 2 * E :=
    c13EvenArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths M hM x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird M (2 * M) (by omega)
      (by omega) x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (229 / 5000 : ℝ) (241 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (27151 / 7500 : ℝ) = 229 / 5000 + 241 / 1000 + 10 / 3 by
    norm_num]
  rw [c13EvenCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13OddCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_27151Over7500
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddCoreNewestTotalErrorBlock M (2 * M)) x y) ^ 2 ≤
      (27151 / 7500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy
    (c13OddPoleCoreNewestBlock M (2 * M)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13OddArchimedeanCoreNewestBlock M (2 * M)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13OddPrimeCoreNewestBlock M (2 * M)) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hPole : pole ^ 2 ≤ (229 / 5000 : ℝ) ^ 2 * E :=
    c13OddPoleCoreNewestCrossEnergy_sq_le_229Over5000
      M (2 * M) hM (by omega) x y
  have hArch : arch ^ 2 ≤ (241 / 1000 : ℝ) ^ 2 * E :=
    c13OddArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths M hM x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird M (2 * M) (by omega)
      (by omega) x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (229 / 5000 : ℝ) (241 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (27151 / 7500 : ℝ) = 229 / 5000 + 241 / 1000 + 10 / 3 by
    norm_num]
  rw [c13OddCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13EvenBuilderAdjacentCrossEnergy_sq_le_27151Over7500
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (27151 / 7500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13EvenCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_27151Over7500
    M hM x y

theorem c13OddBuilderAdjacentCrossEnergy_sq_le_27151Over7500
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (27151 / 7500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13OddCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_27151Over7500
    M hM x y

lemma c13ShellDynamicGap_ge_428Over125_of_ge_3840
    (M : ℕ) (hM : 3840 ≤ M) :
    (428 / 125 : ℝ) ≤ c13ShellDynamicGap M := by
  have hLog := c13_log_nat_ge_3840_gt_20633Over2500 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_229Over5000 M hM
  unfold c13ShellDynamicGap
  nlinarith

lemma c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840
    (M : ℕ) (hM : 3840 ≤ M) :
    (207 / 50 : ℝ) ≤ c13ShellDynamicGap (2 * M) := by
  have hLogM :=
    c13_log_nat_ge_3840_gt_20633Over2500 M hM
  have hLogTwo := Real.log_two_gt_d9
  have hMPos : (0 : ℝ) < M := by positivity
  have hLogMul : Real.log ((2 * M : ℕ) : ℝ) =
      Real.log 2 + Real.log (M : ℝ) := by
    rw [show ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) by norm_num,
      Real.log_mul (by norm_num) (ne_of_gt hMPos)]
  have hPole :=
    c13_logarithmicCvSPoleTail_le_229Over10000_of_ge_7680
      (2 * M) (by omega)
  unfold c13ShellDynamicGap
  rw [hLogMul]
  nlinarith

theorem c13EvenBuilderAdjacentBaseEnergy_ge_428Over125
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin (2 * M - M) → ℝ) :
    (428 / 125 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x := by
  have hShell := c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
    M (2 * M - M) (by omega) (by omega) x
  have hGap := c13ShellDynamicGap_ge_428Over125_of_ge_3840 M hM
  have hScaled := mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg x)
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using hScaled.trans hShell

theorem c13OddBuilderAdjacentBaseEnergy_ge_428Over125
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin (2 * M - M) → ℝ) :
    (428 / 125 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x := by
  have hShell := c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
    M (2 * M - M) (by omega) (by omega) x
  have hGap := c13ShellDynamicGap_ge_428Over125_of_ge_3840 M hM
  have hScaled := mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg x)
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using hScaled.trans hShell

theorem c13EvenBuilderAdjacentTailEnergy_ge_207Over50
    (M : ℕ) (hM : 3840 ≤ M) (y : Fin (2 * M) → ℝ) :
    (207 / 50 : ℝ) * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    M (2 * M) (by omega) y
  have hGap := c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840 M hM
  exact (mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg y)).trans hTail

theorem c13OddBuilderAdjacentTailEnergy_ge_207Over50
    (M : ℕ) (hM : 3840 ≤ M) (y : Fin (2 * M) → ℝ) :
    (207 / 50 : ℝ) * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    M (2 * M) (by omega) y
  have hGap := c13ShellDynamicGap_two_mul_ge_207Over50_of_ge_3840 M hM
  exact (mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg y)).trans hTail

lemma c13_adjacentSharpCrossBudget_le_37Over40_gapProduct :
    (27151 / 7500 : ℝ) ^ 2 ≤
      (37 / 40 : ℝ) * (428 / 125 : ℝ) * (207 / 50 : ℝ) := by
  norm_num

/-- The adjacent analytic bridge has coefficient `37/40`: precise certified
lower bounds for `log 2`, `log 3`, `log 5`, and `pi` recover the reserve lost
by the coarser decimal estimates. -/
theorem c13EvenBuilderAdjacent_relative_37Over40
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (37 / 40 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) y)
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) x y)
    (428 / 125) (207 / 50) ((27151 / 7500) ^ 2) (37 / 40)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (by norm_num) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    (c13EvenBuilderAdjacentBaseEnergy_ge_428Over125 M hM x)
    (c13EvenBuilderAdjacentTailEnergy_ge_207Over50 M hM y)
    (c13EvenBuilderAdjacentCrossEnergy_sq_le_27151Over7500 M hM x y)
    c13_adjacentSharpCrossBudget_le_37Over40_gapProduct

/-- Odd-parity companion of the sharpened adjacent analytic bridge. -/
theorem c13OddBuilderAdjacent_relative_37Over40
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (37 / 40 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) y)
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) x y)
    (428 / 125) (207 / 50) ((27151 / 7500) ^ 2) (37 / 40)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (by norm_num) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    (c13OddBuilderAdjacentBaseEnergy_ge_428Over125 M hM x)
    (c13OddBuilderAdjacentTailEnergy_ge_207Over50 M hM y)
    (c13OddBuilderAdjacentCrossEnergy_sq_le_27151Over7500 M hM x y)
    c13_adjacentSharpCrossBudget_le_37Over40_gapProduct

end RiemannCvs.V23BoundaryWeylMainline
