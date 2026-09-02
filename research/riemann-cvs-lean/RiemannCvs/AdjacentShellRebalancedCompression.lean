import RiemannCvs.AdjacentLoewnerCompression
import RiemannCvs.CvSLoewnerAdiInstantiation
import RiemannCvs.AsymptoticCoreHilbert
import RiemannCvs.AdjacentArchimedeanSharpGap

/-!
# Rebalanced first adjacent-shell compression

The first open middle bridge has source modes `(1920,3840]` and target modes
`(3840,7680]`.  Two losses in the generic tail package are avoidable at this
single geometry:

* on a square adjacent shell, every entry of the reflected Hilbert kernel is
  at most `1 / (2 * (M+1))`, so the half-Hilbert leading matrix costs `1/4`
  rather than the dimension-free historical-core constant `2`;
* the two reference channels need only have coefficients whose *sum* is
  `4/27`.  Tight small-Gram caps permit the natural split
  `1/15 + 11/135 = 4/27`, leaving a larger target for the old-core channel.

The resulting scalar ledger accepts the explicit rank-86 ADI posterior at
`K=1920`.  The compressed Gram bounds and the old-core `1/15` estimate remain
explicit premises; no floating-point diagnostic is promoted to a theorem.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2

/-- Every entry of the square adjacent Hilbert kernel is bounded by the
reciprocal of twice the first possible mode. -/
lemma c13CoreHilbertKernel_adjacent_entry_le
    (M : ℕ) (i j : Fin M) :
    c13CoreHilbertKernel M M i j ≤
      1 / (2 * ((M : ℝ) + 1)) := by
  have hLower : 0 < 2 * ((M : ℝ) + 1) := by positivity
  have hDenom :
      2 * ((M : ℝ) + 1) ≤
        ((M + (i : ℕ) + 1 : ℕ) : ℝ) +
          ((M + (j : ℕ) + 1 : ℕ) : ℝ) := by
    push_cast
    have hi : (0 : ℝ) ≤ (i : ℕ) := by positivity
    have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
    nlinarith
  unfold c13CoreHilbertKernel
  exact one_div_le_one_div_of_le hLower hDenom

/-- The ordinary row sum of the square adjacent Hilbert kernel is at most
`1/2`. -/
lemma c13CoreHilbertKernel_adjacent_row_le_half
    (M : ℕ) (i : Fin M) :
    (∑ j, c13CoreHilbertKernel M M i j) ≤ (1 / 2 : ℝ) := by
  calc
    (∑ j, c13CoreHilbertKernel M M i j) ≤
        ∑ _j : Fin M, 1 / (2 * ((M : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact c13CoreHilbertKernel_adjacent_entry_le M i j
    _ = (M : ℝ) * (1 / (2 * ((M : ℝ) + 1))) := by simp
    _ ≤ 1 / 2 := by
      have hDen : 0 < 2 * ((M : ℝ) + 1) := by positivity
      rw [show (M : ℝ) * (1 / (2 * ((M : ℝ) + 1))) =
          (M : ℝ) / (2 * ((M : ℝ) + 1)) by ring]
      rw [div_le_iff₀ hDen]
      nlinarith

/-- Ordinary Schur on the square adjacent geometry gives norm `1/2` for the
unscaled Hilbert kernel. -/
theorem c13CoreHilbertKernel_adjacent_energy_abs_le_half
    (M : ℕ) (x : Fin M → ℝ) :
    |finiteMatrixQuadraticEnergy (c13CoreHilbertKernel M M) x| ≤
      (1 / 2 : ℝ) * finiteVectorEuclideanNormSq x := by
  let oneWeight : Fin M → ℝ := fun _ => 1
  have h := RiemannCvs.WeightedSchurSupersolution.weightedSchur_quadratic
    (c13CoreHilbertKernel M M) x oneWeight (1 / 2 : ℝ)
    (c13CoreHilbertKernel_nonneg M M)
    (c13CoreHilbertKernel_symm M M)
    (by intro i; simp [oneWeight])
    (by
      intro i
      simpa [oneWeight] using c13CoreHilbertKernel_adjacent_row_le_half M i)
  simpa only [weightedSchurEnergy_eq_finiteMatrixQuadraticEnergy,
    weightedSchurNormSq_eq_finiteVectorEuclideanNormSq] using h

/-- The leading reflected half-Hilbert matrix therefore costs only `1/4` on
an adjacent square shell. -/
theorem c13CoreReflectedHilbertLeading_adjacent_energy_abs_le_quarter
    (M : ℕ) (x : Fin M → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreReflectedHilbertLeadingMatrix M M) x| ≤
      (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  have h := c13CoreHilbertKernel_adjacent_energy_abs_le_half M x
  have heq :
      finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M M) x =
        (1 / 2 : ℝ) * finiteMatrixQuadraticEnergy
          (c13CoreHilbertKernel M M) x := by
    unfold c13CoreReflectedHilbertLeadingMatrix finiteMatrixQuadraticEnergy
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, abs_mul]
  norm_num at h ⊢
  linarith

/-- Odd parity changes only the sign of the leading matrix. -/
theorem c13OddCoreReflectedHilbertLeading_adjacent_energy_abs_le_quarter
    (M : ℕ) (x : Fin M → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddCoreReflectedHilbertLeadingMatrix M M) x| ≤
      (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [show finiteMatrixQuadraticEnergy
      (c13OddCoreReflectedHilbertLeadingMatrix M M) x =
        -finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M M) x by
    unfold c13OddCoreReflectedHilbertLeadingMatrix
    exact finiteMatrixQuadraticEnergy_neg
      (c13CoreReflectedHilbertLeadingMatrix M M) x]
  rw [abs_neg]
  exact c13CoreReflectedHilbertLeading_adjacent_energy_abs_le_quarter M x

/-- On a square shell the complete even Archimedean remainder costs
`1/4 + 43/3840 = 1003/3840`. -/
theorem c13EvenCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
    (M : ℕ) (hM : 960 ≤ M) (x : Fin M → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M M)) x| ≤
      (1003 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M M) x +
        finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M M) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M M) x| +
        |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M M) x| :=
      abs_add_le _ _
    _ ≤ (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreReflectedHilbertLeading_adjacent_energy_abs_le_quarter M x)
        (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M M hM x)
    _ = (1003 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

/-- Odd-parity companion of the adjacent Archimedean bound. -/
theorem c13OddCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
    (M : ℕ) (hM : 960 ≤ M) (x : Fin M → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M M)) x| ≤
      (1003 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M M) x +
        finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M M) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M M) x| +
        |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M M) x| :=
      abs_add_le _ _
    _ ≤ (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13OddCoreReflectedHilbertLeading_adjacent_energy_abs_le_quarter M x)
        (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M M hM x)
    _ = (1003 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

/-- Replacing the generic `1/2` Archimedean loss by `1003/3840` adds exactly
`917/3840` to every dynamic shell gap. -/
lemma c13_adjacentSharpGap_gain :
    (1 / 2 : ℝ) - 1003 / 3840 = 917 / 3840 := by
  norm_num

/-- Source energy floor at the first open adjacent bridge. -/
theorem c13EvenBuilderAdjacentShell_energy_ge_2257Over768
    (M : ℕ) (hM : 1920 ≤ M) (x : Fin M → ℝ) :
    (2257 / 768 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M M)) x := by
  have hM960 : 960 ≤ M := by omega
  have hGap := c13ShellDynamicGap_ge_twentySevenTenths_of_ge_1920 M hM
  have hFloor :
      (2257 / 768 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
        (logarithmicCvSPoleScale 13 /
            (8 * Real.pi ^ 2 * (M : ℝ)) +
          1003 / 3840 + 10 / 3) := by
    unfold c13ShellDynamicGap at hGap
    nlinarith
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M M (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (2257 / 768) (1003 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M M hM960)
    (c13EvenCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
      M hM960 x)
    (by simpa using hFloor)
  simpa using h

/-- Odd source energy floor at the first open adjacent bridge. -/
theorem c13OddBuilderAdjacentShell_energy_ge_2257Over768
    (M : ℕ) (hM : 1920 ≤ M) (x : Fin M → ℝ) :
    (2257 / 768 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M M)) x := by
  have hM960 : 960 ≤ M := by omega
  have hGap := c13ShellDynamicGap_ge_twentySevenTenths_of_ge_1920 M hM
  have hFloor :
      (2257 / 768 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
        (logarithmicCvSPoleScale 13 /
            (8 * Real.pi ^ 2 * (M : ℝ)) +
          1003 / 3840 + 10 / 3) := by
    unfold c13ShellDynamicGap at hGap
    nlinarith
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M M (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (2257 / 768) (1003 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M M hM960)
    (c13OddCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
      M hM960 x)
    (by simpa using hFloor)
  simpa using h

/-- Target energy floor, using the existing `M>=3840` logarithmic bound plus
the adjacent `917/3840` gain. -/
theorem c13EvenBuilderAdjacentShell_energy_ge_351629Over96000
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin M → ℝ) :
    (351629 / 96000 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M M)) x := by
  have hM960 : 960 ≤ M := by omega
  have hGap := c13ShellDynamicGap_ge_428Over125_of_ge_3840 M hM
  have hFloor :
      (351629 / 96000 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
        (logarithmicCvSPoleScale 13 /
            (8 * Real.pi ^ 2 * (M : ℝ)) +
          1003 / 3840 + 10 / 3) := by
    unfold c13ShellDynamicGap at hGap
    nlinarith
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M M (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
      (351629 / 96000) (1003 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M M hM960)
    (c13EvenCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
      M hM960 x)
    (by simpa using hFloor)
  simpa using h

/-- Odd target energy floor. -/
theorem c13OddBuilderAdjacentShell_energy_ge_351629Over96000
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin M → ℝ) :
    (351629 / 96000 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M M)) x := by
  have hM960 : 960 ≤ M := by omega
  have hGap := c13ShellDynamicGap_ge_428Over125_of_ge_3840 M hM
  have hFloor :
      (351629 / 96000 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
        (logarithmicCvSPoleScale 13 /
            (8 * Real.pi ^ 2 * (M : ℝ)) +
          1003 / 3840 + 10 / 3) := by
    unfold c13ShellDynamicGap at hGap
    nlinarith
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M M (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
      (351629 / 96000) (1003 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M M hM960)
    (c13OddCoreArchimedeanRemainder_adjacent_energy_abs_le_1003Over3840
      M hM960 x)
    (by simpa using hFloor)
  simpa using h

/-- Adaptive first-bridge compression uses 31 same-sign factors and 12
reflected factors, hence combined displacement-rank cap 86. -/
lemma v23_k1920_adjacentLoewnerCompression_rankLedger :
    2 * 31 + 2 * 12 = 86 := by
  norm_num

lemma nineteenOverFourThousand_posteriorInflation :
    (19 / 4000 : ℝ) / (1 - 19 / 4000) = 19 / 3981 := by
  norm_num

lemma threeOverSixteenThousand_posteriorInflation :
    (3 / 16000 : ℝ) / (1 - 3 / 16000) = 3 / 15997 := by
  norm_num

/-- Exact posterior assembled from the planned small Gram bounds. -/
lemma v23_k1920_compressionPosteriorLedger :
    (93223 / 100000 : ℝ) + (19 / 3981) * (8881 / 10000) +
        (3 / 15997) * (22301 / 100000) =
      186377448887 / 199012678125 := by
  norm_num

/-- The rational rank-86 posterior fits the rebalanced adjacent budget. -/
lemma v23_k1920_compressionPosterior_fits_elevenOver135 :
    (23413 / 25000 : ℝ) ^ 2 ≤
      (11 / 135 : ℝ) * (2257 / 768) * (351629 / 96000) := by
  norm_num

/-- Specialize the generic two-Loewner posterior to the first bridge.  The
three compressed bounds are precisely the small-Gram outputs; all relations
between the full, compressed, and residual blocks remain explicit premises. -/
theorem v23_k1920_twoLoewnerCompression_posterior
    (sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (19 / 4000 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (3 / 16000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (8881 / 10000 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (22301 / 100000 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (93223 / 100000 : ℝ)) :
    totalNorm ≤ 23413 / 25000 := by
  have hPosterior := twoLoewnerCompression_posterior
    sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
    residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
    (19 / 4000 : ℝ) (3 / 16000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSameSplit hReflectedSplit hSameResidual hReflectedResidual hTotalSplit
  calc
    totalNorm ≤ compressedTotalNorm +
        ((19 / 4000 : ℝ) / (1 - 19 / 4000)) * compressedSameNorm +
        ((3 / 16000 : ℝ) / (1 - 3 / 16000)) *
          compressedReflectedNorm := hPosterior
    _ = compressedTotalNorm + (19 / 3981 : ℝ) * compressedSameNorm +
        (3 / 15997 : ℝ) * compressedReflectedNorm := by norm_num
    _ ≤ (93223 / 100000 : ℝ) + (19 / 3981) * (8881 / 10000) +
        (3 / 15997) * (22301 / 100000) := by
      gcongr
    _ = 186377448887 / 199012678125 :=
      v23_k1920_compressionPosteriorLedger
    _ ≤ 23413 / 25000 := by norm_num

/-- End-to-end adjacent-channel consequence of the rank-86 posterior.  The
large matrices occur only through norm/split premises; the coercive floors and
the final `11/135` arithmetic are internal theorems. -/
theorem relativeCoupling_of_k1920_rank86Compression
    (lowEnergy highEnergy cross lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hLowNorm : 0 ≤ lowNorm) (hHighNorm : 0 ≤ highNorm)
    (hLowEnergy :
      (2257 / 768 : ℝ) * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy :
      (351629 / 96000 : ℝ) * highNorm ^ 2 ≤ highEnergy)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (19 / 4000 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (3 / 16000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (8881 / 10000 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (22301 / 100000 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (93223 / 100000 : ℝ))
    (hCross : |cross| ≤ totalNorm * lowNorm * highNorm) :
    cross ^ 2 ≤ (11 / 135 : ℝ) * lowEnergy * highEnergy := by
  let epsilon : ℝ := 23413 / 25000
  have hTotalEpsilon : totalNorm ≤ epsilon := by
    simpa [epsilon] using v23_k1920_twoLoewnerCompression_posterior
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
      hSameSplit hReflectedSplit hSameResidual hReflectedResidual hTotalSplit
      hCompressedSame hCompressedReflected hCompressedTotal
  have hCross' : |cross| ≤ epsilon * lowNorm * highNorm := by
    calc
      |cross| ≤ totalNorm * lowNorm * highNorm := hCross
      _ ≤ epsilon * lowNorm * highNorm := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hTotalEpsilon hLowNorm)
          hHighNorm
  exact relativeCoupling_of_coerciveNormBounds
    lowEnergy highEnergy cross
    (2257 / 768) (351629 / 96000) epsilon (11 / 135)
    lowNorm highNorm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hLowEnergy hHighEnergy hCross' hLowNorm hHighNorm
    (by
      simpa [epsilon] using
        v23_k1920_compressionPosterior_fits_elevenOver135)

/-- The rebalanced old-core and adjacent coefficients exactly renew the
steady reference budget. -/
lemma v23_k1920_rebalancedBudget :
    (1 / 15 : ℝ) + 11 / 135 = 4 / 27 := by
  norm_num

/-- Weighted two-channel Cauchy for the rebalanced first bridge. -/
theorem relativeCoupling_of_oneFifteenth_and_elevenOver135
    (oldEnergy adjacentEnergy tail oldCross adjacentCross : ℝ)
    (hOld : oldCross ^ 2 ≤
      (1 / 15 : ℝ) * oldEnergy * tail)
    (hAdjacent : adjacentCross ^ 2 ≤
      (11 / 135 : ℝ) * adjacentEnergy * tail) :
    (oldCross + adjacentCross) ^ 2 ≤
      (4 / 27 : ℝ) * (oldEnergy + adjacentEnergy) * tail := by
  have hOldScaled := mul_le_mul_of_nonneg_left hOld
    (show (0 : ℝ) ≤ 11 / 135 by norm_num)
  have hAdjacentScaled := mul_le_mul_of_nonneg_left hAdjacent
    (show (0 : ℝ) ≤ 1 / 15 by norm_num)
  have hWeighted := sq_nonneg
    ((11 / 135 : ℝ) * oldCross - (1 / 15 : ℝ) * adjacentCross)
  nlinarith

end RiemannCvs.V23BoundaryWeylMainline
