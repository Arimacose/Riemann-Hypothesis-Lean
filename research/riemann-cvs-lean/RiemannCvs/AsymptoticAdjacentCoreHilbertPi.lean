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
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
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
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    dsimp [N] at hGap ⊢
    nlinarith
  apply c13OddBuilderCoreNewest_relative_of_coreFloor
    M N hM960 hMN x y (59 / 10) (2 / 5) (by norm_num) (by norm_num)
    hCore
  exact c13_completeCrossBudget_le_twoFifths_adjacentGapProduct.trans
    (mul_le_mul_of_nonneg_left hGap39 (by norm_num))

end


end RiemannCvs.V23BoundaryWeylMainline
