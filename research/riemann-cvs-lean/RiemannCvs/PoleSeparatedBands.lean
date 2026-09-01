import RiemannCvs.PrimeTranslationSeparatedBands
import RiemannCvs.ArchimedeanRemainderSchur

/-!
# Fixed-prefix / remote-shell pole channel

The rational pole parity blocks are rank one.  Keeping that factorization,
rather than charging their full quadratic-form norm to both bands, separates
the fixed-prefix and remote-shell weight masses.  The prefix mass is bounded
by the elementary reciprocal-square sum `<= 2`; the remote mass is `O(1/N)`.
At the first analytic scale this closes a common squared coupling coefficient
`1/5`, with exact one-half dyadic transport thereafter.
-/

noncomputable section

open scoped BigOperators Real

namespace RiemannCvs.PoleSeparatedBands

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.PrimeTranslationSeparatedBands

/-- The fixed-prefix mode map enumerates exactly the natural interval
`(0,F+1)`. -/
lemma fixedPrefix_inv_sq_sum_eq_Ioo (F N : ℕ) :
    (∑ i : Fin F,
      (((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) =
      ∑ n ∈ Finset.Ioo 0 (F + 1), (((n : ℝ) ^ 2)⁻¹) := by
  have hIoo : Finset.Ioo 0 (F + 1) = Finset.Ico 1 (F + 1) := by
    ext n
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hIoo, Finset.sum_Ico_eq_sum_range]
  have hLength : F + 1 - 1 = F := by omega
  rw [hLength]
  simpa [fixedRemotePositiveMode, add_comm] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹)) F)

/-- Uniform elementary reciprocal-square mass of every finite positive
prefix. -/
theorem fixedPrefix_inv_sq_sum_le_two (F N : ℕ) :
    (∑ i : Fin F,
      (((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) ≤
      (2 : ℝ) := by
  rw [fixedPrefix_inv_sq_sum_eq_Ioo]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (F + 1))

theorem fixedPrefixPoleOddWeight_sq_sum_le_invEightPiSq
    (F N : ℕ) :
    (∑ i : Fin F,
      logarithmicCvSPoleOddWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
      1 / (8 * Real.pi ^ 2) := by
  have hPoint : ∀ i : Fin F,
      logarithmicCvSPoleOddWeight 13
          (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2 ≤
        (16 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
    intro i
    have hMode := fixedRemotePositiveMode_inl_pos F N i
    have hModeReal : 0 <
        ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) := by
      exact_mod_cast hMode
    have h := logarithmicCvSPoleOddWeight_sq_le 13
      (fixedRemotePositiveMode F N (Sum.inl i)) hMode
    calc
      logarithmicCvSPoleOddWeight 13
          (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2 ≤
          1 / (16 * Real.pi ^ 2 *
            ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2) := h
      _ = (16 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
        field_simp [Real.pi_ne_zero, ne_of_gt hModeReal]
  calc
    (∑ i : Fin F,
      logarithmicCvSPoleOddWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
        ∑ i : Fin F, (16 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum (fun i _hi => hPoint i)
    _ = (16 * Real.pi ^ 2)⁻¹ *
        ∑ i : Fin F,
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (16 * Real.pi ^ 2)⁻¹ * 2 := by
      exact mul_le_mul_of_nonneg_left
        (fixedPrefix_inv_sq_sum_le_two F N) (by positivity)
    _ = 1 / (8 * Real.pi ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring

theorem fixedPrefixPoleEvenWeight_sq_sum_le_invThirtyTwoPiSq
    (F N : ℕ) :
    (∑ i : Fin F,
      logarithmicCvSPoleEvenWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
      1 / (32 * Real.pi ^ 2) := by
  have hPoint : ∀ i : Fin F,
      logarithmicCvSPoleEvenWeight 13
          (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2 ≤
        (64 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
    intro i
    have hMode := fixedRemotePositiveMode_inl_pos F N i
    have hModeReal : 0 <
        ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) := by
      exact_mod_cast hMode
    have h := logarithmicCvSPoleEvenWeight_sq_le 13
      (fixedRemotePositiveMode F N (Sum.inl i)) hMode
    calc
      logarithmicCvSPoleEvenWeight 13
          (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2 ≤
          1 / (64 * Real.pi ^ 2 *
            ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2) := h
      _ = (64 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
        field_simp [Real.pi_ne_zero, ne_of_gt hModeReal]
  calc
    (∑ i : Fin F,
      logarithmicCvSPoleEvenWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
        ∑ i : Fin F, (64 * Real.pi ^ 2)⁻¹ *
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum (fun i _hi => hPoint i)
    _ = (64 * Real.pi ^ 2)⁻¹ *
        ∑ i : Fin F,
          ((((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (64 * Real.pi ^ 2)⁻¹ * 2 := by
      exact mul_le_mul_of_nonneg_left
        (fixedPrefix_inv_sq_sum_le_two F N) (by positivity)
    _ = 1 / (32 * Real.pi ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring

lemma invEightPiSq_le_oneSeventySecond :
    1 / (8 * Real.pi ^ 2) ≤ (1 / 72 : ℝ) := by
  have hPi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2) (by norm_num)]
  nlinarith [sq_pos_of_pos Real.pi_pos]

theorem fixedPrefixPoleOddWeight_sq_sum_le_oneSeventySecond
    (F N : ℕ) :
    (∑ i : Fin F,
      logarithmicCvSPoleOddWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
      (1 / 72 : ℝ) :=
  (fixedPrefixPoleOddWeight_sq_sum_le_invEightPiSq F N).trans
    invEightPiSq_le_oneSeventySecond

theorem fixedPrefixPoleEvenWeight_sq_sum_le_oneSeventySecond
    (F N : ℕ) :
    (∑ i : Fin F,
      logarithmicCvSPoleEvenWeight 13
        (fixedRemotePositiveMode F N (Sum.inl i)) ^ 2) ≤
      (1 / 72 : ℝ) := by
  calc
    _ ≤ 1 / (32 * Real.pi ^ 2) :=
      fixedPrefixPoleEvenWeight_sq_sum_le_invThirtyTwoPiSq F N
    _ ≤ 1 / (8 * Real.pi ^ 2) := by
      have hPiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      rw [div_le_div_iff₀ (by positivity : 0 < 32 * Real.pi ^ 2)
        (by positivity : 0 < 8 * Real.pi ^ 2)]
      nlinarith
    _ ≤ 1 / 72 := invEightPiSq_le_oneSeventySecond

@[simp] lemma fixedRemotePositiveMode_inr_eq_globalShell
    (F N : ℕ) (j : Fin N) :
    fixedRemotePositiveMode F N (Sum.inr j) =
      finGlobalShellPositiveMode N N j := by
  simp [fixedRemotePositiveMode, finGlobalShellPositiveMode]
  ring

theorem remotePoleOddWeight_sq_sum_le
    (F N : ℕ) (hN : N ≠ 0) :
    (∑ j : Fin N,
      logarithmicCvSPoleOddWeight 13
        (fixedRemotePositiveMode F N (Sum.inr j)) ^ 2) ≤
      1 / (16 * Real.pi ^ 2 * (N : ℝ)) := by
  simpa only [fixedRemotePositiveMode_inr_eq_globalShell] using
    logarithmicCvSPoleOddWeight_shell_sum_le 13 N N hN

theorem remotePoleEvenWeight_sq_sum_le
    (F N : ℕ) (hN : N ≠ 0) :
    (∑ j : Fin N,
      logarithmicCvSPoleEvenWeight 13
        (fixedRemotePositiveMode F N (Sum.inr j)) ^ 2) ≤
      1 / (64 * Real.pi ^ 2 * (N : ℝ)) := by
  simpa only [fixedRemotePositiveMode_inr_eq_globalShell] using
    logarithmicCvSPoleEvenWeight_shell_sum_le_strong 13 N N hN

theorem remotePoleOddWeight_sq_sum_le_oneOver144N
    (F N : ℕ) (hN : 1 ≤ N) :
    (∑ j : Fin N,
      logarithmicCvSPoleOddWeight 13
        (fixedRemotePositiveMode F N (Sum.inr j)) ^ 2) ≤
      1 / (144 * (N : ℝ)) := by
  have hN0 : N ≠ 0 := by omega
  have hRaw := remotePoleOddWeight_sq_sum_le F N hN0
  refine hRaw.trans ?_
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hPi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hCoeff : (144 : ℝ) ≤ 16 * Real.pi ^ 2 := by nlinarith
  have hDen := mul_le_mul_of_nonneg_right hCoeff hNReal.le
  rw [div_le_div_iff₀ (by positivity : 0 < 16 * Real.pi ^ 2 * (N : ℝ))
    (by positivity : 0 < 144 * (N : ℝ))]
  simpa only [one_mul] using hDen

theorem remotePoleEvenWeight_sq_sum_le_oneOver144N
    (F N : ℕ) (hN : 1 ≤ N) :
    (∑ j : Fin N,
      logarithmicCvSPoleEvenWeight 13
        (fixedRemotePositiveMode F N (Sum.inr j)) ^ 2) ≤
      1 / (144 * (N : ℝ)) := by
  have hN0 : N ≠ 0 := by omega
  have hRaw := remotePoleEvenWeight_sq_sum_le F N hN0
  refine hRaw.trans ?_
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hPi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hCoeff : (144 : ℝ) ≤ 64 * Real.pi ^ 2 := by nlinarith
  have hDen := mul_le_mul_of_nonneg_right hCoeff hNReal.le
  rw [div_le_div_iff₀ (by positivity : 0 < 64 * Real.pi ^ 2 * (N : ℝ))
    (by positivity : 0 < 144 * (N : ℝ))]
  simpa only [one_mul] using hDen

/-- Exact rectangular cross coordinate of a symmetric rank-one matrix.  This
keeps the low- and high-band Cauchy factors separate instead of paying a
global operator norm. -/
theorem finiteMatrixBlockCrossEnergy_rankOne
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ) (u : ι ⊕ κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    finiteMatrixBlockCrossEnergy (fun i j => a * u i * u j) x y =
      a * (∑ i, u (Sum.inl i) * x i) *
        (∑ j, u (Sum.inr j) * y j) := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (fun i j => a * u i * u j) x y (by intro i j; ring)]
  calc
    (∑ i, ∑ j,
      x i * (a * u (Sum.inl i) * u (Sum.inr j)) * y j) =
        ∑ i, (a * u (Sum.inl i) * x i) *
          (∑ j, u (Sum.inr j) * y j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = a * (∑ i, u (Sum.inl i) * x i) *
        (∑ j, u (Sum.inr j) * y j) := by
      have hLeft : (∑ i, a * u (Sum.inl i) * x i) =
          a * ∑ i, u (Sum.inl i) * x i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      rw [← Finset.sum_mul, hLeft]

/-- Two independent finite Cauchy inequalities turn a rank-one cross block
into the product of its low/high squared weight masses. -/
theorem finiteMatrixBlockCrossEnergy_rankOne_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ) (u : ι ⊕ κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (finiteMatrixBlockCrossEnergy (fun i j => a * u i * u j) x y) ^ 2 ≤
      a ^ 2 * (∑ i, u (Sum.inl i) ^ 2) *
        (∑ j, u (Sum.inr j) ^ 2) *
          (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [finiteMatrixBlockCrossEnergy_rankOne]
  have hLow := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ι) (fun i => u (Sum.inl i)) x
  have hHigh := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset κ) (fun j => u (Sum.inr j)) y
  have hProduct := mul_le_mul hLow hHigh (sq_nonneg _) (by positivity)
  have hScaled := mul_le_mul_of_nonneg_left hProduct (sq_nonneg a)
  simpa only [finiteVectorEuclideanNormSq, pow_two,
    mul_assoc, mul_left_comm, mul_comm] using hScaled

/-- The actual even pole block on a fixed prefix and a remote band. -/
noncomputable def c13FixedRemoteEvenPoleMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSPoleEvenPositiveModeMatrix 13
    (fixedRemotePositiveMode F N)

/-- The actual odd pole block on the same separated bands. -/
noncomputable def c13FixedRemoteOddPoleMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSPoleOddPositiveModeMatrix 13
    (fixedRemotePositiveMode F N)

/-- The matrix is literally component zero of the even CvS builder error
vector, so the separated estimate plugs into the existing three-source
decomposition without a representation hypothesis. -/
@[simp] lemma c13_fixedRemoteEvenBuilderError_zero (F N : ℕ) :
    logarithmicCvSBuilderEvenPositiveModeErrorMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) 0 =
      c13FixedRemoteEvenPoleMatrix F N := by
  rfl

/-- Odd-parity builder identification. -/
@[simp] lemma c13_fixedRemoteOddBuilderError_zero (F N : ℕ) :
    logarithmicCvSBuilderOddPositiveModeErrorMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) 0 =
      c13FixedRemoteOddPoleMatrix F N := by
  rfl

/-- Common Euclidean squared-cross coefficient supplied by the rank-one pole
factorization and the separated reciprocal-square masses. -/
noncomputable def c13FixedRemotePoleCoefficient (N : ℕ) : ℝ :=
  (2 * logarithmicCvSPoleScale 13) ^ 2 * (1 / 72) *
    (1 / (144 * (N : ℝ)))

theorem c13_fixedRemoteEvenPoleCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hN : 1 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPoleMatrix F N) x y) ^ 2 ≤
      c13FixedRemotePoleCoefficient N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13FixedRemoteEvenPoleMatrix,
    logarithmicCvSPoleEvenPositiveModeMatrix_eq_rankOne]
  have hRank := finiteMatrixBlockCrossEnergy_rankOne_sq_le
    (2 * logarithmicCvSPoleScale 13)
    (fun q => logarithmicCvSPoleEvenWeight 13
      (fixedRemotePositiveMode F N q)) x y
  refine hRank.trans ?_
  unfold c13FixedRemotePoleCoefficient
  have hLow := fixedPrefixPoleEvenWeight_sq_sum_le_oneSeventySecond F N
  have hHigh := remotePoleEvenWeight_sq_sum_le_oneOver144N F N hN
  gcongr
  exact mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)

theorem c13_fixedRemoteOddPoleCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hN : 1 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPoleMatrix F N) x y) ^ 2 ≤
      c13FixedRemotePoleCoefficient N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13FixedRemoteOddPoleMatrix,
    logarithmicCvSPoleOddPositiveModeMatrix_eq_rankOne]
  have hRank := finiteMatrixBlockCrossEnergy_rankOne_sq_le
    (-(2 * logarithmicCvSPoleScale 13))
    (fun q => logarithmicCvSPoleOddWeight 13
      (fixedRemotePositiveMode F N q)) x y
  refine hRank.trans ?_
  unfold c13FixedRemotePoleCoefficient
  have hLow := fixedPrefixPoleOddWeight_sq_sum_le_oneSeventySecond F N
  have hHigh := remotePoleOddWeight_sq_sum_le_oneOver144N F N hN
  rw [neg_sq]
  gcongr
  exact mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)

/-- At the first analytic remote scale the complete pole cross coefficient is
strictly below `1/5`; unlike the older global pole estimate, this is a
fixed-prefix/remote-band statement. -/
theorem c13_fixedRemotePoleCoefficient_le_oneFifth
    (N : ℕ) (hN : 371293 ≤ N) :
    c13FixedRemotePoleCoefficient N ≤ (1 / 5 : ℝ) := by
  have hNPos : 0 < N := by omega
  have hNReal : (371293 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hInv : 1 / (N : ℝ) ≤ (1 / 371293 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hNReal
  have hScale0 : 0 ≤ logarithmicCvSPoleScale 13 :=
    logarithmicCvSPoleScale_nonneg 13 (by norm_num)
  have hScaleSq : (2 * logarithmicCvSPoleScale 13) ^ 2 ≤
      (2 * (13872 : ℝ)) ^ 2 := by
    nlinarith [c13_logarithmicCvSPoleScale_le_13872]
  have hNReal0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNPos)
  calc
    c13FixedRemotePoleCoefficient N =
        ((2 * logarithmicCvSPoleScale 13) ^ 2 / (72 * 144)) *
          (1 / (N : ℝ)) := by
      unfold c13FixedRemotePoleCoefficient
      field_simp [hNReal0]
    _ ≤ ((2 * (13872 : ℝ)) ^ 2 / (72 * 144)) *
          (1 / (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hScaleSq (by norm_num)) (by positivity)
    _ ≤ ((2 * (13872 : ℝ)) ^ 2 / (72 * 144)) *
          (1 / 371293 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hInv (by positivity)
    _ ≤ 1 / 5 := by norm_num

/-- Doubling the remote band halves the separated pole coefficient exactly. -/
lemma c13FixedRemotePoleCoefficient_two_mul (N : ℕ) :
    c13FixedRemotePoleCoefficient (2 * N) =
      (1 / 2 : ℝ) * c13FixedRemotePoleCoefficient N := by
  by_cases hN : N = 0
  · subst N
    simp [c13FixedRemotePoleCoefficient]
  · have hNReal : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    unfold c13FixedRemotePoleCoefficient
    push_cast
    field_simp [hNReal]

/-- Exact transport of the pole coefficient along a dyadic tower. -/
theorem c13FixedRemotePoleCoefficient_dyadic_eq (N k : ℕ) :
    c13FixedRemotePoleCoefficient (N * 2 ^ k) =
      (1 / 2 : ℝ) ^ k * c13FixedRemotePoleCoefficient N := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hNat : N * (2 ^ k * 2) = 2 * (N * 2 ^ k) := by
        ac_rfl
      rw [hNat, c13FixedRemotePoleCoefficient_two_mul, ih, pow_succ]
      ring

theorem c13_fixed3840_remotePoleCoefficient_dyadic_le
    (k : ℕ) :
    c13FixedRemotePoleCoefficient (371293 * 2 ^ k) ≤
      (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ k := by
  rw [c13FixedRemotePoleCoefficient_dyadic_eq]
  have hBase := c13_fixedRemotePoleCoefficient_le_oneFifth 371293 (by omega)
  have hPow : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hBase hPow
  nlinarith

theorem c13_fixed3840_remoteEvenPoleCrossEnergy_sq_le_oneFifth
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPoleMatrix 3840 N) x y) ^ 2 ≤
      (1 / 5 : ℝ) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13_fixedRemoteEvenPoleCrossEnergy_sq_le_coefficient
    3840 N (by omega) x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixedRemotePoleCoefficient_le_oneFifth N hN)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

theorem c13_fixed3840_remoteOddPoleCrossEnergy_sq_le_oneFifth
    (N : ℕ) (hN : 371293 ≤ N)
    (x : Fin 3840 → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPoleMatrix 3840 N) x y) ^ 2 ≤
      (1 / 5 : ℝ) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13_fixedRemoteOddPoleCrossEnergy_sq_le_coefficient
    3840 N (by omega) x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixedRemotePoleCoefficient_le_oneFifth N hN)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

/-- Even-parity pole cross budget on every dyadic remote band. -/
theorem c13_fixed3840_remoteEvenPoleCrossEnergy_sq_le_dyadic
    (k : ℕ)
    (x : Fin 3840 → ℝ) (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenPoleMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : 1 ≤ 371293 * 2 ^ k := by
    have hNPos : 0 < 371293 * 2 ^ k := by positivity
    omega
  have hRaw := c13_fixedRemoteEvenPoleCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) hN x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixed3840_remotePoleCoefficient_dyadic_le k)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

/-- Odd-parity pole cross budget on every dyadic remote band. -/
theorem c13_fixed3840_remoteOddPoleCrossEnergy_sq_le_dyadic
    (k : ℕ)
    (x : Fin 3840 → ℝ) (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddPoleMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : 1 ≤ 371293 * 2 ^ k := by
    have hNPos : 0 < 371293 * 2 ^ k := by positivity
    omega
  have hRaw := c13_fixedRemoteOddPoleCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) hN x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixed3840_remotePoleCoefficient_dyadic_le k)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

end RiemannCvs.PoleSeparatedBands
