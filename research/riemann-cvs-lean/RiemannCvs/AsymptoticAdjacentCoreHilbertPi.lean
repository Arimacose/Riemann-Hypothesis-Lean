import RiemannCvs.AsymptoticCoreHilbertPi

/-!
# Adjacent historical half-block at the first analytic scale

The uniform historical-core estimate starts at mode `960`, so its smallest
diagonal reserve remains fixed while the newest shell moves outward.  That
loss is artificial for the part of the core adjacent to the new shell.

This module splits off the adjacent half-block `(floor (N/2), N]`.  Already at
`N = 13^5`, its left endpoint exceeds `6 * 13^4`; elementary logarithm bounds
therefore give a `59/10` core gap.  Combining this with the existing `39/5`
newest-shell gap and the complete `4217/1000` cross amplitude proves a
relative coefficient `2/5` at every dyadic scale, with no lower bound on the
scale index `n`.

This is the first analytic component of a multiband route: the immediately
adjacent half consumes only `2/5`, while earlier bands can be assigned
distance-decaying budgets instead of being charged the mode-`960` floor.
-/

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2

noncomputable section

lemma twelve_lt_log_nat_of_ge_six_mul_thirteenPowFour
    (M : ℕ) (hM : 6 * 13 ^ 4 ≤ M) :
    (12 : ℝ) < Real.log (M : ℝ) := by
  have hMReal : (6 * 13 ^ 4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLogMono : Real.log (6 * 13 ^ 4 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by positivity) hMReal
  have hFactor :
      Real.log (6 * 13 ^ 4 : ℝ) =
        Real.log 2 + Real.log 3 + 4 * Real.log 13 := by
    rw [show (6 * 13 ^ 4 : ℝ) = 2 * 3 * 13 ^ (4 : ℕ) by norm_num]
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hFactor] at hLogMono
  nlinarith [log_two_gt_sixtyNineHundredths,
    log_three_gt_oneHundredNineHundredths,
    sixtyFourTwentyFive_lt_log_thirteen]

lemma c13DyadicHalf_ge_six_mul_thirteenPowFour (n : ℕ) :
    6 * 13 ^ 4 ≤ c13DyadicShellBase n / 2 := by
  have hBase := c13DyadicShellBase_ge_371293 n
  norm_num at hBase ⊢
  omega

lemma c13_adjacentPiCore_scalar_reserve_ge_fiftyNineTenths
    (M : ℕ) (hM : 6 * 13 ^ 4 ≤ M) :
    (59 / 10 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) +
        42541 / 26880 + 10 / 3) := by
  have hM960 : 960 ≤ M := by norm_num at hM ⊢; omega
  have hLog := twelve_lt_log_nat_of_ge_six_mul_thirteenPowFour M hM
  have hPole := c13_logarithmicCvSPoleTail_le_thirteenSixtieth M hM960
  nlinarith

theorem c13_logarithmicCvSBuilderEvenAdjacentCore_energy_ge_fiftyNineTenths
    (M L : ℕ) (hM : 6 * 13 ^ 4 ≤ M) (x : Fin L → ℝ) :
    (59 / 10 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hM960 : 960 ≤ M := by norm_num at hM ⊢; omega
  have hArch :=
    c13EvenCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM960 x
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (59 / 10) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM960)
    hArch
    (by simpa using
      c13_adjacentPiCore_scalar_reserve_ge_fiftyNineTenths M hM)
  simpa using h

theorem c13_logarithmicCvSBuilderOddAdjacentCore_energy_ge_fiftyNineTenths
    (M L : ℕ) (hM : 6 * 13 ^ 4 ≤ M) (x : Fin L → ℝ) :
    (59 / 10 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hM960 : 960 ≤ M := by norm_num at hM ⊢; omega
  have hArch :=
    c13OddCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM960 x
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (59 / 10) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM960)
    hArch
    (by simpa using
      c13_adjacentPiCore_scalar_reserve_ge_fiftyNineTenths M hM)
  simpa using h

theorem c13EvenBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
    (M N : ℕ) (hM : 6 * 13 ^ 4 ≤ M)
    (x : Fin (N - M) → ℝ) :
    (59 / 10 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderEvenAdjacentCore_energy_ge_fiftyNineTenths
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13OddBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
    (M N : ℕ) (hM : 6 * 13 ^ 4 ≤ M)
    (x : Fin (N - M) → ℝ) :
    (59 / 10 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderOddAdjacentCore_energy_ge_fiftyNineTenths
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

lemma c13_completeCrossBudget_le_twoFifths_adjacentGapProduct :
    (4217 / 1000 : ℝ) ^ 2 ≤
      (2 / 5 : ℝ) * (59 / 10 : ℝ) * (39 / 5 : ℝ) := by
  norm_num

/-- The complete even coupling between the adjacent historical half and the
newest shell has coefficient `2/5` from the first analytic dyadic scale on. -/
theorem c13EvenBuilderDyadicAdjacentCoreNewest_relative_twoFifths
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n - c13DyadicShellBase n / 2) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock
          (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) x y) ^ 2 ≤
      (2 / 5 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock
            (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock
            (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) y := by
  let N := c13DyadicShellBase n
  let M := N / 2
  have hMStrong : 6 * 13 ^ 4 ≤ M := by
    simpa [M, N] using c13DyadicHalf_ge_six_mul_thirteenPowFour n
  have hM960 : 960 ≤ M := by norm_num at hMStrong ⊢; omega
  have hMN : M ≤ N := Nat.div_le_self N 2
  have hCore :=
    c13EvenBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
      M N hMStrong x
  have hGap := c13DyadicGapLower_le_dynamicGap n
  have hGap39 : (39 / 5 : ℝ) ≤ c13ShellDynamicGap N := by
    unfold c13DyadicGapLower at hGap
    have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [N] at hGap ⊢
    nlinarith
  apply c13EvenBuilderCoreNewest_relative_of_coreFloor
    M N hM960 hMN x y (59 / 10) (2 / 5) (by norm_num) (by norm_num)
    hCore
  exact c13_completeCrossBudget_le_twoFifths_adjacentGapProduct.trans
    (mul_le_mul_of_nonneg_left hGap39 (by norm_num))

/-- Odd-parity companion of the scale-free adjacent-half certificate. -/
theorem c13OddBuilderDyadicAdjacentCoreNewest_relative_twoFifths
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n - c13DyadicShellBase n / 2) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock
          (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) x y) ^ 2 ≤
      (2 / 5 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock
            (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock
            (c13DyadicShellBase n / 2) (c13DyadicShellBase n)) y := by
  let N := c13DyadicShellBase n
  let M := N / 2
  have hMStrong : 6 * 13 ^ 4 ≤ M := by
    simpa [M, N] using c13DyadicHalf_ge_six_mul_thirteenPowFour n
  have hM960 : 960 ≤ M := by norm_num at hMStrong ⊢; omega
  have hMN : M ≤ N := Nat.div_le_self N 2
  have hCore :=
    c13OddBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
      M N hMStrong x
  have hGap := c13DyadicGapLower_le_dynamicGap n
  have hGap39 : (39 / 5 : ℝ) ≤ c13ShellDynamicGap N := by
    unfold c13DyadicGapLower at hGap
    have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [N] at hGap ⊢
    nlinarith
  apply c13OddBuilderCoreNewest_relative_of_coreFloor
    M N hM960 hMN x y (59 / 10) (2 / 5) (by norm_num) (by norm_num)
    hCore
  exact c13_completeCrossBudget_le_twoFifths_adjacentGapProduct.trans
    (mul_le_mul_of_nonneg_left hGap39 (by norm_num))

/-!
## Analytic core anchored at the certified cutoff `3840`

The pole allowance used by the uniform `M >= 960` argument scales exactly as
`1/M`.  Retaining that decay at `M = 3840`, instead of reusing `13/60`, aligns
the analytic full-core theorem with the current rigorous finite frontier.
-/

lemma eightHundredTwentyOneHundredths_lt_log_nat_of_ge_3840
    (M : ℕ) (hM : 3840 ≤ M) :
    (821 / 100 : ℝ) < Real.log (M : ℝ) := by
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
  nlinarith [log_two_gt_sixtyNineHundredths,
    log_three_gt_oneHundredNineHundredths,
    log_five_gt_eightFifths]

theorem c13_logarithmicCvSPoleTail_le_fiftyOneThousandths
    (M : ℕ) (hM : 3840 ≤ M) :
    logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (M : ℝ)) ≤ (51 / 1000 : ℝ) := by
  have hMReal : (3840 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMPos : 0 < (M : ℝ) := by positivity
  have hPiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hDenLower : (276480 : ℝ) ≤ 8 * Real.pi ^ 2 * (M : ℝ) := by
    calc
      (276480 : ℝ) = 8 * 9 * 3840 := by norm_num
      _ ≤ 8 * Real.pi ^ 2 * 3840 := by nlinarith
      _ ≤ 8 * Real.pi ^ 2 * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hMReal (by positivity)
  have hDenPos : 0 < 8 * Real.pi ^ 2 * (M : ℝ) := by positivity
  rw [div_le_iff₀ hDenPos]
  nlinarith [c13_logarithmicCvSPoleScale_le_13872]

lemma c13_anchor3840PiCore_scalar_reserve_ge_twoHundredTwentyNineHundredths
    (M : ℕ) (hM : 3840 ≤ M) :
    (229 / 100 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) +
        42541 / 26880 + 10 / 3) := by
  have hLog := eightHundredTwentyOneHundredths_lt_log_nat_of_ge_3840 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_fiftyOneThousandths M hM
  nlinarith

theorem c13_logarithmicCvSBuilderEvenAnchor3840Core_energy_ge_229Over100
    (M L : ℕ) (hM : 3840 ≤ M) (x : Fin L → ℝ) :
    (229 / 100 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hM960 : 960 ≤ M := by omega
  have hArch :=
    c13EvenCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM960 x
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (229 / 100) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM960)
    hArch
    (by simpa using
      c13_anchor3840PiCore_scalar_reserve_ge_twoHundredTwentyNineHundredths M hM)
  simpa using h

theorem c13_logarithmicCvSBuilderOddAnchor3840Core_energy_ge_229Over100
    (M L : ℕ) (hM : 3840 ≤ M) (x : Fin L → ℝ) :
    (229 / 100 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hM960 : 960 ≤ M := by omega
  have hArch :=
    c13OddCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM960 x
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (229 / 100) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM960)
    hArch
    (by simpa using
      c13_anchor3840PiCore_scalar_reserve_ge_twoHundredTwentyNineHundredths M hM)
  simpa using h

theorem c13EvenBuilderAnchor3840CoreNewestBaseEnergy_ge_229Over100
    (M N : ℕ) (hM : 3840 ≤ M) (x : Fin (N - M) → ℝ) :
    (229 / 100 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderEvenAnchor3840Core_energy_ge_229Over100
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13OddBuilderAnchor3840CoreNewestBaseEnergy_ge_229Over100
    (M N : ℕ) (hM : 3840 ≤ M) (x : Fin (N - M) → ℝ) :
    (229 / 100 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderOddAnchor3840Core_energy_ge_229Over100
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13EvenPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (51 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13EvenPoleCoreNewestBlock M N) x y (51 / 1000 : ℝ) (by norm_num)
  intro z
  exact (c13EvenPoleCoreNewestEnergy_abs_le_poleTail M N (by omega) hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_fiftyOneThousandths M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

theorem c13OddPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (51 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13OddPoleCoreNewestBlock M N) x y (51 / 1000 : ℝ) (by norm_num)
  intro z
  exact (c13OddPoleCoreNewestEnergy_abs_le_poleTail M N (by omega) hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_fiftyOneThousandths M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

theorem c13EvenCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenCoreNewestTotalErrorBlock M N) x y) ^ 2 ≤
      (6077 / 1500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy (c13EvenPoleCoreNewestBlock M N) x y
  let arch := finiteMatrixBlockCrossEnergy (c13EvenArchimedeanCoreNewestBlock M N) x y
  let prime := finiteMatrixBlockCrossEnergy (c13EvenPrimeCoreNewestBlock M N) x y
  have hPole : pole ^ 2 ≤ (51 / 1000 : ℝ) ^ 2 * E :=
    c13EvenPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths M N hM hMN x y
  have hArch : arch ^ 2 ≤ (667 / 1000 : ℝ) ^ 2 * E :=
    c13EvenArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
      M N (by omega) hMN x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird M N (by omega) hMN x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (51 / 1000 : ℝ) (667 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y))
    hPole hArch hPrime
  rw [show (6077 / 1500 : ℝ) = 51 / 1000 + 667 / 1000 + 10 / 3 by
    norm_num]
  rw [c13EvenCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13OddCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddCoreNewestTotalErrorBlock M N) x y) ^ 2 ≤
      (6077 / 1500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy (c13OddPoleCoreNewestBlock M N) x y
  let arch := finiteMatrixBlockCrossEnergy (c13OddArchimedeanCoreNewestBlock M N) x y
  let prime := finiteMatrixBlockCrossEnergy (c13OddPrimeCoreNewestBlock M N) x y
  have hPole : pole ^ 2 ≤ (51 / 1000 : ℝ) ^ 2 * E :=
    c13OddPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths M N hM hMN x y
  have hArch : arch ^ 2 ≤ (667 / 1000 : ℝ) ^ 2 * E :=
    c13OddArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
      M N (by omega) hMN x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird M N (by omega) hMN x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (51 / 1000 : ℝ) (667 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y))
    hPole hArch hPrime
  rw [show (6077 / 1500 : ℝ) = 51 / 1000 + 667 / 1000 + 10 / 3 by
    norm_num]
  rw [c13OddCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13EvenBuilderCoreNewestCrossEnergy_sq_le_6077Over1500
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      (6077 / 1500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13EvenCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500
    M N hM hMN x y

theorem c13OddBuilderCoreNewestCrossEnergy_sq_le_6077Over1500
    (M N : ℕ) (hM : 3840 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      (6077 / 1500 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13OddCoreNewestTotalErrorCrossEnergy_sq_le_6077Over1500
    M N hM hMN x y

lemma c13_anchor3840_completeCrossBudget_le_twentyThreeTwentyFifths_gapProduct :
    (6077 / 1500 : ℝ) ^ 2 ≤
      (23 / 25 : ℝ) * (229 / 100 : ℝ) * (39 / 5 : ℝ) := by
  norm_num

/-- From the current rigorous finite frontier onward, the complete analytic
historical core/newest-shell channel has a fixed coefficient strictly below
one at every dyadic scale. -/
theorem c13EvenBuilderDyadicAnchor3840CoreNewest_relative_23Over25
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n - 3840) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (23 / 25 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) y := by
  let N := c13DyadicShellBase n
  have hMN : 3840 ≤ N := by
    have h := c13DyadicShellBase_ge_371293 n
    dsimp [N]
    omega
  have hN960 : 960 ≤ N := by omega
  have hCore := c13EvenBuilderAnchor3840CoreNewestBaseEnergy_ge_229Over100
    3840 N (by norm_num) x
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    3840 N hN960 y
  have hGap := c13DyadicGapLower_le_dynamicGap n
  have hGap39 : (39 / 5 : ℝ) ≤ c13ShellDynamicGap N := by
    unfold c13DyadicGapLower at hGap
    have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [N] at hGap ⊢
    nlinarith
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock 3840 N) x)
    (finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock 3840 N) y)
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock 3840 N) x y)
    (229 / 100) (c13ShellDynamicGap N) ((6077 / 1500) ^ 2) (23 / 25)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (c13ShellDynamicGap_nonneg N hN960) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    hCore hTail
  · exact c13EvenBuilderCoreNewestCrossEnergy_sq_le_6077Over1500
      3840 N (by norm_num) hMN x y
  · exact c13_anchor3840_completeCrossBudget_le_twentyThreeTwentyFifths_gapProduct.trans
      (mul_le_mul_of_nonneg_left hGap39 (by norm_num))

theorem c13OddBuilderDyadicAnchor3840CoreNewest_relative_23Over25
    (n : ℕ)
    (x : Fin (c13DyadicShellBase n - 3840) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (23 / 25 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock 3840 (c13DyadicShellBase n)) y := by
  let N := c13DyadicShellBase n
  have hMN : 3840 ≤ N := by
    have h := c13DyadicShellBase_ge_371293 n
    dsimp [N]
    omega
  have hN960 : 960 ≤ N := by omega
  have hCore := c13OddBuilderAnchor3840CoreNewestBaseEnergy_ge_229Over100
    3840 N (by norm_num) x
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    3840 N hN960 y
  have hGap := c13DyadicGapLower_le_dynamicGap n
  have hGap39 : (39 / 5 : ℝ) ≤ c13ShellDynamicGap N := by
    unfold c13DyadicGapLower at hGap
    have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [N] at hGap ⊢
    nlinarith
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock 3840 N) x)
    (finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock 3840 N) y)
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock 3840 N) x y)
    (229 / 100) (c13ShellDynamicGap N) ((6077 / 1500) ^ 2) (23 / 25)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (c13ShellDynamicGap_nonneg N hN960) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    hCore hTail
  · exact c13OddBuilderCoreNewestCrossEnergy_sq_le_6077Over1500
      3840 N (by norm_num) hMN x y
  · exact c13_anchor3840_completeCrossBudget_le_twentyThreeTwentyFifths_gapProduct.trans
      (mul_le_mul_of_nonneg_left hGap39 (by norm_num))

end


end RiemannCvs.V23BoundaryWeylMainline
