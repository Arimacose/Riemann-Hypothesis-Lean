import RiemannCvs.AsymptoticCoreNewestArchimedean

noncomputable section

/-!
# Full-core/newest-shell total-error compression

This module adds the pole and prime-translation pieces to the uniform
Archimedean historical-core estimate.  The sum-type coordinates represent the
literal consecutive interval `(M,2N]` split as

`(M,N] ⊕ (N,2N]`.

The prime component retains its global `10/3` form bound.  An exact finite
equivalence identifies the sum-type pole weights with the already proved
consecutive-shell sum, retaining `13/60` rather than paying twice for the two
subintervals.  These are the remaining source components needed to bound the
complete old-core/new-shell error channel.
-/

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

lemma c13CoreNewestPositiveMode_injective
    (M N : ℕ) (hMN : M ≤ N) :
    Function.Injective (c13CoreNewestPositiveMode M N) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hijFin : i = j := by
            apply Fin.ext
            simp only [c13CoreNewestPositiveMode, Sum.elim_inl,
              c13CoreMode, Int.ofNat_inj] at hij
            omega
          exact congrArg Sum.inl hijFin
      | inr j =>
          simp only [c13CoreNewestPositiveMode, Sum.elim_inl, Sum.elim_inr,
            c13CoreMode, c13NewestMode, Int.ofNat_inj] at hij
          have hi : (i : ℕ) < N - M := i.isLt
          omega
  | inr i =>
      cases j with
      | inl j =>
          simp only [c13CoreNewestPositiveMode, Sum.elim_inl, Sum.elim_inr,
            c13CoreMode, c13NewestMode, Int.ofNat_inj] at hij
          have hj : (j : ℕ) < N - M := j.isLt
          omega
      | inr j =>
          have hijFin : i = j := by
            apply Fin.ext
            simp only [c13CoreNewestPositiveMode, Sum.elim_inr,
              c13NewestMode, Int.ofNat_inj] at hij
            omega
          exact congrArg Sum.inr hijFin

noncomputable def c13EvenPrimeCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  finiteLogarithmicPrimeEvenPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N)

noncomputable def c13OddPrimeCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  finiteLogarithmicPrimeOddPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N)

 theorem c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenPrimeCoreNewestBlock M N) x y) ^ 2 ≤
      (10 / 3 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13EvenPrimeCoreNewestBlock M N) x y (10 / 3 : ℝ) (by norm_num)
  intro z
  exact c13_finiteLogarithmicPrimeEvenPositiveModeErrorEnergy_abs_le_tenThird_closed
    (c13CoreNewestPositiveMode M N) z
    (c13CoreNewestPositiveMode_injective M N hMN)
    (c13CoreNewestPositiveMode_pos M N hM)

 theorem c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddPrimeCoreNewestBlock M N) x y) ^ 2 ≤
      (10 / 3 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13OddPrimeCoreNewestBlock M N) x y (10 / 3 : ℝ) (by norm_num)
  intro z
  exact c13_finiteLogarithmicPrimeOddPositiveModeErrorEnergy_abs_le_tenThird_closed
    (c13CoreNewestPositiveMode M N) z
    (c13CoreNewestPositiveMode_injective M N hMN)
    (c13CoreNewestPositiveMode_pos M N hM)

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline

noncomputable def c13CoreNewestShellEquiv
    (M N : ℕ) (hMN : M ≤ N) :
    Fin (2 * N - M) ≃ Fin (N - M) ⊕ Fin N :=
  finBlockSplitEquiv (by omega)

lemma finGlobalShellPositiveMode_coreNewestEquiv_symm_inl
    (M N : ℕ) (hMN : M ≤ N) (i : Fin (N - M)) :
    finGlobalShellPositiveMode M (2 * N - M)
        ((c13CoreNewestShellEquiv M N hMN).symm (Sum.inl i)) =
      (c13CoreMode M N i : ℤ) := by
  simp [c13CoreNewestShellEquiv, finBlockSplitEquiv,
    finGlobalShellPositiveMode, c13CoreMode]

lemma finGlobalShellPositiveMode_coreNewestEquiv_symm_inr
    (M N : ℕ) (hMN : M ≤ N) (j : Fin N) :
    finGlobalShellPositiveMode M (2 * N - M)
        ((c13CoreNewestShellEquiv M N hMN).symm (Sum.inr j)) =
      (c13NewestMode N j : ℤ) := by
  simp [c13CoreNewestShellEquiv, finBlockSplitEquiv,
    finGlobalShellPositiveMode, c13NewestMode]
  omega

lemma finGlobalShellPositiveMode_coreNewestEquiv_symm
    (M N : ℕ) (hMN : M ≤ N)
    (i : Fin (N - M) ⊕ Fin N) :
    finGlobalShellPositiveMode M (2 * N - M)
        ((c13CoreNewestShellEquiv M N hMN).symm i) =
      c13CoreNewestPositiveMode M N i := by
  cases i with
  | inl i =>
      simpa [c13CoreNewestPositiveMode] using
        finGlobalShellPositiveMode_coreNewestEquiv_symm_inl M N hMN i
  | inr j =>
      simpa [c13CoreNewestPositiveMode] using
        finGlobalShellPositiveMode_coreNewestEquiv_symm_inr M N hMN j

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline

lemma c13CoreNewestPoleEvenWeight_sum_eq_shell
    (M N : ℕ) (hMN : M ≤ N) :
    (∑ i : Fin (N - M) ⊕ Fin N,
        logarithmicCvSPoleEvenWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) =
      ∑ k : Fin (2 * N - M),
        logarithmicCvSPoleEvenWeight 13
          (finGlobalShellPositiveMode M (2 * N - M) k) ^ 2 := by
  symm
  apply Fintype.sum_equiv (c13CoreNewestShellEquiv M N hMN)
  intro k
  have hMode := finGlobalShellPositiveMode_coreNewestEquiv_symm M N hMN
    ((c13CoreNewestShellEquiv M N hMN) k)
  rw [(c13CoreNewestShellEquiv M N hMN).symm_apply_apply] at hMode
  rw [hMode]

lemma c13CoreNewestPoleOddWeight_sum_eq_shell
    (M N : ℕ) (hMN : M ≤ N) :
    (∑ i : Fin (N - M) ⊕ Fin N,
        logarithmicCvSPoleOddWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) =
      ∑ k : Fin (2 * N - M),
        logarithmicCvSPoleOddWeight 13
          (finGlobalShellPositiveMode M (2 * N - M) k) ^ 2 := by
  symm
  apply Fintype.sum_equiv (c13CoreNewestShellEquiv M N hMN)
  intro k
  have hMode := finGlobalShellPositiveMode_coreNewestEquiv_symm M N hMN
    ((c13CoreNewestShellEquiv M N hMN) k)
  rw [(c13CoreNewestShellEquiv M N hMN).symm_apply_apply] at hMode
  rw [hMode]

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def c13EvenPoleCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) 0

noncomputable def c13OddPoleCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderOddPositiveModeErrorMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) 0

lemma c13EvenPoleCoreNewestEnergy_abs_le_poleTail
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (z : Fin (N - M) ⊕ Fin N → ℝ) :
    |finiteMatrixQuadraticEnergy (c13EvenPoleCoreNewestBlock M N) z| ≤
      logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) *
        finiteVectorEuclideanNormSq z := by
  have hRaw := logarithmicCvSBuilderEvenPositiveModePoleError_abs_le
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) z
  have hWeightsShell := logarithmicCvSPoleEvenWeight_shell_sum_le
    13 M (2 * N - M) (by omega)
  have hWeights :
      (∑ i : Fin (N - M) ⊕ Fin N,
        logarithmicCvSPoleEvenWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) ≤
          1 / (16 * Real.pi ^ 2 * (M : ℝ)) := by
    rw [c13CoreNewestPoleEvenWeight_sum_eq_shell M N hMN]
    exact hWeightsShell
  calc
    |finiteMatrixQuadraticEnergy (c13EvenPoleCoreNewestBlock M N) z| ≤
      |2 * logarithmicCvSPoleScale 13| *
        (∑ i : Fin (N - M) ⊕ Fin N,
          logarithmicCvSPoleEvenWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) *
        finiteVectorEuclideanNormSq z := hRaw
    _ ≤ |2 * logarithmicCvSPoleScale 13| *
        (1 / (16 * Real.pi ^ 2 * (M : ℝ))) *
          finiteVectorEuclideanNormSq z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWeights (abs_nonneg _))
        (finiteVectorEuclideanNormSq_nonneg z)
    _ = logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) *
        finiteVectorEuclideanNormSq z := by
      have hMReal : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (logarithmicCvSPoleScale_nonneg 13 (by norm_num))]
      field_simp [Real.pi_ne_zero, hMReal]
      ring

lemma c13OddPoleCoreNewestEnergy_abs_le_poleTail
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (z : Fin (N - M) ⊕ Fin N → ℝ) :
    |finiteMatrixQuadraticEnergy (c13OddPoleCoreNewestBlock M N) z| ≤
      logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) *
        finiteVectorEuclideanNormSq z := by
  have hRaw := logarithmicCvSBuilderOddPositiveModePoleError_abs_le
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) z
  have hWeightsShell := logarithmicCvSPoleOddWeight_shell_sum_le
    13 M (2 * N - M) (by omega)
  have hWeights :
      (∑ i : Fin (N - M) ⊕ Fin N,
        logarithmicCvSPoleOddWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) ≤
          1 / (16 * Real.pi ^ 2 * (M : ℝ)) := by
    rw [c13CoreNewestPoleOddWeight_sum_eq_shell M N hMN]
    exact hWeightsShell
  calc
    |finiteMatrixQuadraticEnergy (c13OddPoleCoreNewestBlock M N) z| ≤
      |2 * logarithmicCvSPoleScale 13| *
        (∑ i : Fin (N - M) ⊕ Fin N,
          logarithmicCvSPoleOddWeight 13 (c13CoreNewestPositiveMode M N i) ^ 2) *
        finiteVectorEuclideanNormSq z := hRaw
    _ ≤ |2 * logarithmicCvSPoleScale 13| *
        (1 / (16 * Real.pi ^ 2 * (M : ℝ))) *
          finiteVectorEuclideanNormSq z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWeights (abs_nonneg _))
        (finiteVectorEuclideanNormSq_nonneg z)
    _ = logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) *
        finiteVectorEuclideanNormSq z := by
      have hMReal : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (logarithmicCvSPoleScale_nonneg 13 (by norm_num))]
      field_simp [Real.pi_ne_zero, hMReal]
      ring

 theorem c13EvenPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (13 / 60 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13EvenPoleCoreNewestBlock M N) x y (13 / 60 : ℝ) (by norm_num)
  intro z
  exact (c13EvenPoleCoreNewestEnergy_abs_le_poleTail M N hM hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_thirteenSixtieth M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

 theorem c13OddPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddPoleCoreNewestBlock M N) x y) ^ 2 ≤
      (13 / 60 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  apply finiteMatrixBlockCrossEnergy_sq_le_of_quadratic_abs_bound
    (c13OddPoleCoreNewestBlock M N) x y (13 / 60 : ℝ) (by norm_num)
  intro z
  exact (c13OddPoleCoreNewestEnergy_abs_le_poleTail M N hM hMN z).trans
    (mul_le_mul_of_nonneg_right
      (c13_logarithmicCvSPoleTail_le_thirteenSixtieth M hM)
      (finiteVectorEuclideanNormSq_nonneg z))

end RiemannCvs.V23BoundaryWeylMainline
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2
open Finset

lemma finiteMatrixBlockCrossEnergy_add
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    finiteMatrixBlockCrossEnergy (A + B) x y =
      finiteMatrixBlockCrossEnergy A x y +
        finiteMatrixBlockCrossEnergy B x y := by
  unfold finiteMatrixBlockCrossEnergy
  simp_rw [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma three_cross_sq_le_sum_amplitudes
    (a b c A B C E : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (ha : a ^ 2 ≤ A ^ 2 * E)
    (hb : b ^ 2 ≤ B ^ 2 * E)
    (hc : c ^ 2 ≤ C ^ 2 * E) :
    (a + b + c) ^ 2 ≤ (A + B + C) ^ 2 * E := by
  let cross : Fin 3 → ℝ := ![a, b, c]
  let amp : Fin 3 → ℝ := ![A, B, C]
  have hAmp : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ amp i := by
    intro i hi
    fin_cases i <;> simp [amp, hA, hB, hC]
  have hAmpE : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ amp i * E := by
    intro i hi
    exact mul_nonneg (hAmp i hi) hE
  have hCross : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      cross i ^ 2 ≤ amp i * (amp i * E) := by
    intro i hi
    fin_cases i
    · simpa [cross, amp, pow_two, mul_assoc] using ha
    · simpa [cross, amp, pow_two, mul_assoc] using hb
    · simpa [cross, amp, pow_two, mul_assoc] using hc
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin 3)) hAmp hAmpE hCross
  simp [Fin.sum_univ_three, cross, amp] at h
  calc
    (a + b + c) ^ 2 ≤
        (A + B + C) * (A * E + B * E + C * E) := h
    _ = (A + B + C) ^ 2 * E := by ring

noncomputable def c13EvenCoreNewestTotalErrorBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  c13EvenPoleCoreNewestBlock M N +
    c13EvenArchimedeanCoreNewestBlock M N +
      c13EvenPrimeCoreNewestBlock M N

noncomputable def c13OddCoreNewestTotalErrorBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  c13OddPoleCoreNewestBlock M N +
    c13OddArchimedeanCoreNewestBlock M N +
      c13OddPrimeCoreNewestBlock M N

 theorem c13EvenCoreNewestTotalErrorCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenCoreNewestTotalErrorBlock M N) x y) ^ 2 ≤
      (4217 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy (c13EvenPoleCoreNewestBlock M N) x y
  let arch := finiteMatrixBlockCrossEnergy (c13EvenArchimedeanCoreNewestBlock M N) x y
  let prime := finiteMatrixBlockCrossEnergy (c13EvenPrimeCoreNewestBlock M N) x y
  have hPole : pole ^ 2 ≤ (13 / 60 : ℝ) ^ 2 * E :=
    c13EvenPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth M N hM hMN x y
  have hArch : arch ^ 2 ≤ (667 / 1000 : ℝ) ^ 2 * E :=
    c13EvenArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
      M N hM hMN x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird M N hM hMN x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (13 / 60 : ℝ) (667 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y))
    hPole hArch hPrime
  rw [show (4217 / 1000 : ℝ) = 13 / 60 + 667 / 1000 + 10 / 3 by norm_num]
  rw [c13EvenCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add,
    finiteMatrixBlockCrossEnergy_add]
  exact hTotal

 theorem c13OddCoreNewestTotalErrorCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddCoreNewestTotalErrorBlock M N) x y) ^ 2 ≤
      (4217 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy (c13OddPoleCoreNewestBlock M N) x y
  let arch := finiteMatrixBlockCrossEnergy (c13OddArchimedeanCoreNewestBlock M N) x y
  let prime := finiteMatrixBlockCrossEnergy (c13OddPrimeCoreNewestBlock M N) x y
  have hPole : pole ^ 2 ≤ (13 / 60 : ℝ) ^ 2 * E :=
    c13OddPoleCoreNewestCrossEnergy_sq_le_thirteenSixtieth M N hM hMN x y
  have hArch : arch ^ 2 ≤ (667 / 1000 : ℝ) ^ 2 * E :=
    c13OddArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
      M N hM hMN x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird M N hM hMN x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (13 / 60 : ℝ) (667 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y))
    hPole hArch hPrime
  rw [show (4217 / 1000 : ℝ) = 13 / 60 + 667 / 1000 + 10 / 3 by norm_num]
  rw [c13OddCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add,
    finiteMatrixBlockCrossEnergy_add]
  exact hTotal

end RiemannCvs.V23BoundaryWeylMainline
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

lemma logarithmicCvSBuilderEvenPositiveModeMatrix_symm
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ)
    (i j : κ) :
    logarithmicCvSBuilderEvenPositiveModeMatrix c location base mode i j =
      logarithmicCvSBuilderEvenPositiveModeMatrix c location base mode j i := by
  unfold logarithmicCvSBuilderEvenPositiveModeMatrix
  rw [logarithmicCvSBuilderEntry_symm c location base (mode i) (mode j),
    logarithmicCvSBuilderEntry_symm c location base (mode j) (-mode i)]
  have hNeg := logarithmicCvSBuilderEntry_neg_neg
    c location base (mode i) (-mode j)
  simp only [neg_neg] at hNeg
  rw [hNeg]

lemma logarithmicCvSBuilderOddPositiveModeMatrix_symm
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ)
    (i j : κ) :
    logarithmicCvSBuilderOddPositiveModeMatrix c location base mode i j =
      logarithmicCvSBuilderOddPositiveModeMatrix c location base mode j i := by
  unfold logarithmicCvSBuilderOddPositiveModeMatrix
  rw [logarithmicCvSBuilderEntry_symm c location base (mode i) (mode j),
    logarithmicCvSBuilderEntry_symm c location base (mode j) (-mode i)]
  have hNeg := logarithmicCvSBuilderEntry_neg_neg
    c location base (mode i) (-mode j)
  simp only [neg_neg] at hNeg
  rw [hNeg]

noncomputable def c13EvenBuilderCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N)

noncomputable def c13OddBuilderCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderOddPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N)

lemma c13EvenBuilderCoreNewestBlock_inl_inr_eq_totalError
    (M N : ℕ) (i : Fin (N - M)) (j : Fin N) :
    c13EvenBuilderCoreNewestBlock M N (Sum.inl i) (Sum.inr j) =
      c13EvenCoreNewestTotalErrorBlock M N (Sum.inl i) (Sum.inr j) := by
  rw [c13EvenBuilderCoreNewestBlock,
    logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition]
  simp [c13EvenCoreNewestTotalErrorBlock, c13EvenPoleCoreNewestBlock,
    c13EvenArchimedeanCoreNewestBlock, c13EvenPrimeCoreNewestBlock,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderEvenPositiveModeErrorMatrix]

lemma c13OddBuilderCoreNewestBlock_inl_inr_eq_totalError
    (M N : ℕ) (i : Fin (N - M)) (j : Fin N) :
    c13OddBuilderCoreNewestBlock M N (Sum.inl i) (Sum.inr j) =
      c13OddCoreNewestTotalErrorBlock M N (Sum.inl i) (Sum.inr j) := by
  rw [c13OddBuilderCoreNewestBlock,
    logarithmicCvSBuilderOddPositiveModeMatrix_decomposition]
  simp [c13OddCoreNewestTotalErrorBlock, c13OddPoleCoreNewestBlock,
    c13OddArchimedeanCoreNewestBlock, c13OddPrimeCoreNewestBlock,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderOddPositiveModeErrorMatrix]

lemma c13EvenBuilderCoreNewestBlock_inr_inl_eq_totalError
    (M N : ℕ) (j : Fin N) (i : Fin (N - M)) :
    c13EvenBuilderCoreNewestBlock M N (Sum.inr j) (Sum.inl i) =
      c13EvenCoreNewestTotalErrorBlock M N (Sum.inr j) (Sum.inl i) := by
  rw [c13EvenBuilderCoreNewestBlock,
    logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition]
  simp [c13EvenCoreNewestTotalErrorBlock, c13EvenPoleCoreNewestBlock,
    c13EvenArchimedeanCoreNewestBlock, c13EvenPrimeCoreNewestBlock,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderEvenPositiveModeErrorMatrix]

lemma c13OddBuilderCoreNewestBlock_inr_inl_eq_totalError
    (M N : ℕ) (j : Fin N) (i : Fin (N - M)) :
    c13OddBuilderCoreNewestBlock M N (Sum.inr j) (Sum.inl i) =
      c13OddCoreNewestTotalErrorBlock M N (Sum.inr j) (Sum.inl i) := by
  rw [c13OddBuilderCoreNewestBlock,
    logarithmicCvSBuilderOddPositiveModeMatrix_decomposition]
  simp [c13OddCoreNewestTotalErrorBlock, c13OddPoleCoreNewestBlock,
    c13OddArchimedeanCoreNewestBlock, c13OddPrimeCoreNewestBlock,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderOddPositiveModeErrorMatrix]

lemma c13EvenBuilderCoreNewestBlock_crossEnergy_eq_totalError
    (M N : ℕ) (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y =
      finiteMatrixBlockCrossEnergy (c13EvenCoreNewestTotalErrorBlock M N) x y := by
  unfold finiteMatrixBlockCrossEnergy
  simp_rw [c13EvenBuilderCoreNewestBlock_inl_inr_eq_totalError,
    c13EvenBuilderCoreNewestBlock_inr_inl_eq_totalError]

lemma c13OddBuilderCoreNewestBlock_crossEnergy_eq_totalError
    (M N : ℕ) (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y =
      finiteMatrixBlockCrossEnergy (c13OddCoreNewestTotalErrorBlock M N) x y := by
  unfold finiteMatrixBlockCrossEnergy
  simp_rw [c13OddBuilderCoreNewestBlock_inl_inr_eq_totalError,
    c13OddBuilderCoreNewestBlock_inr_inl_eq_totalError]

theorem c13EvenBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      (4217 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13EvenCoreNewestTotalErrorCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    M N hM hMN x y

theorem c13OddBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      (4217 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13OddCoreNewestTotalErrorCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
    M N hM hMN x y

end RiemannCvs.V23BoundaryWeylMainline
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail

lemma c13NewestMode_eq_finGlobalShellPositiveMode
    (N : ℕ) (j : Fin N) :
    (c13NewestMode N j : ℤ) = finGlobalShellPositiveMode N N j := by
  simp [c13NewestMode, finGlobalShellPositiveMode]

@[simp] lemma c13EvenBuilderCoreNewestBlock_inr_inr
    (M N : ℕ) (i j : Fin N) :
    c13EvenBuilderCoreNewestBlock M N (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode N N) i j := by
  simp only [c13EvenBuilderCoreNewestBlock,
    logarithmicCvSBuilderEvenPositiveModeMatrix,
    c13CoreNewestPositiveMode, Sum.elim_inr,
    c13NewestMode_eq_finGlobalShellPositiveMode]

@[simp] lemma c13OddBuilderCoreNewestBlock_inr_inr
    (M N : ℕ) (i j : Fin N) :
    c13OddBuilderCoreNewestBlock M N (Sum.inr i) (Sum.inr j) =
      logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode N N) i j := by
  simp only [c13OddBuilderCoreNewestBlock,
    logarithmicCvSBuilderOddPositiveModeMatrix,
    c13CoreNewestPositiveMode, Sum.elim_inr,
    c13NewestMode_eq_finGlobalShellPositiveMode]

 theorem c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    (M N : ℕ) (hN : 960 ≤ N) (y : Fin N → ℝ) :
    c13ShellDynamicGap N * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  have h := c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
    N N hN le_rfl y
  unfold finiteMatrixBlockTailEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inr_inr,
    finiteMatrixQuadraticEnergy] using h

 theorem c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    (M N : ℕ) (hN : 960 ≤ N) (y : Fin N → ℝ) :
    c13ShellDynamicGap N * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  have h := c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
    N N hN le_rfl y
  unfold finiteMatrixBlockTailEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inr_inr,
    finiteMatrixQuadraticEnergy] using h

 theorem c13EvenBuilderCoreNewest_relative_of_coreFloor
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ)
    (coreGap q : ℝ) (hCoreGap : 0 ≤ coreGap) (hq : 0 ≤ q)
    (hCore : coreGap * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * coreGap * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  have hN : 960 ≤ N := hM.trans hMN
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x)
    (finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y)
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y)
    coreGap (c13ShellDynamicGap N) ((4217 / 1000 : ℝ) ^ 2) q
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    hCoreGap (c13ShellDynamicGap_nonneg N hN) hq
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    hCore (c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq M N hN y)
  · exact c13EvenBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
      M N hM hMN x y
  · exact hBudget

 theorem c13OddBuilderCoreNewest_relative_of_coreFloor
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ)
    (coreGap q : ℝ) (hCoreGap : 0 ≤ coreGap) (hq : 0 ≤ q)
    (hCore : coreGap * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * coreGap * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  have hN : 960 ≤ N := hM.trans hMN
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x)
    (finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y)
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y)
    coreGap (c13ShellDynamicGap N) ((4217 / 1000 : ℝ) ^ 2) q
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    hCoreGap (c13ShellDynamicGap_nonneg N hN) hq
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    hCore (c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq M N hN y)
  · exact c13OddBuilderCoreNewestCrossEnergy_sq_le_fourThousandTwoHundredSeventeenThousandths
      M N hM hMN x y
  · exact hBudget

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail
open Filter
open scoped Topology

noncomputable def c13CoreNewestRelativeEnvelope
    (coreGap : ℝ) (n : ℕ) : ℝ :=
  (4217 / 1000 : ℝ) ^ 2 /
    (coreGap * c13DyadicGapLower n)

lemma c13CoreNewestRelativeEnvelope_nonneg
    (coreGap : ℝ) (hCoreGap : 0 ≤ coreGap) (n : ℕ) :
    0 ≤ c13CoreNewestRelativeEnvelope coreGap n := by
  unfold c13CoreNewestRelativeEnvelope
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg hCoreGap (c13DyadicGapLower_pos n).le)

lemma c13CoreNewestRelativeEnvelope_budget
    (coreGap : ℝ) (hCoreGap : 0 < coreGap) (n : ℕ) :
    (4217 / 1000 : ℝ) ^ 2 ≤
      c13CoreNewestRelativeEnvelope coreGap n * coreGap *
        c13ShellDynamicGap (c13DyadicShellBase n) := by
  let L := c13DyadicGapLower n
  let g := c13ShellDynamicGap (c13DyadicShellBase n)
  have hL : 0 < L := c13DyadicGapLower_pos n
  have hLg : L ≤ g := c13DyadicGapLower_le_dynamicGap n
  have hq : 0 ≤ c13CoreNewestRelativeEnvelope coreGap n :=
    c13CoreNewestRelativeEnvelope_nonneg coreGap hCoreGap.le n
  have hIdentity :
      c13CoreNewestRelativeEnvelope coreGap n * coreGap * L =
        (4217 / 1000 : ℝ) ^ 2 := by
    unfold c13CoreNewestRelativeEnvelope
    dsimp only [L]
    have hLne : c13DyadicGapLower n ≠ 0 :=
      ne_of_gt (c13DyadicGapLower_pos n)
    field_simp [ne_of_gt hCoreGap, hLne]
  calc
    (4217 / 1000 : ℝ) ^ 2 =
        c13CoreNewestRelativeEnvelope coreGap n * coreGap * L := hIdentity.symm
    _ ≤ c13CoreNewestRelativeEnvelope coreGap n * coreGap * g := by
      exact mul_le_mul_of_nonneg_left hLg
        (mul_nonneg hq hCoreGap.le)

 theorem tendsto_c13CoreNewestRelativeEnvelope_zero
    (coreGap : ℝ) (hCoreGap : 0 < coreGap) :
    Tendsto (c13CoreNewestRelativeEnvelope coreGap) atTop (𝓝 0) := by
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLinear : Tendsto (fun n : ℕ => (69 / 100 : ℝ) * (n : ℝ)) atTop atTop :=
    hNat.const_mul_atTop (by norm_num)
  have hGap : Tendsto c13DyadicGapLower atTop atTop := by
    unfold c13DyadicGapLower
    exact tendsto_const_nhds.add_atTop hLinear
  have hDenominator : Tendsto
      (fun n => coreGap * c13DyadicGapLower n) atTop atTop :=
    hGap.const_mul_atTop hCoreGap
  change Tendsto
    (fun n => (4217 / 1000 : ℝ) ^ 2 /
      (coreGap * c13DyadicGapLower n)) atTop (nhds 0)
  exact hDenominator.const_div_atTop ((4217 / 1000 : ℝ) ^ 2)

 theorem c13EvenBuilderDyadicCoreNewest_relative_vanishingEnvelope
    (M n : ℕ) (hM : 960 ≤ M) (hMN : M ≤ c13DyadicShellBase n)
    (x : Fin (c13DyadicShellBase n - M) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ)
    (coreGap : ℝ) (hCoreGap : 0 < coreGap)
    (hCore : coreGap * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13EvenBuilderCoreNewestBlock M (c13DyadicShellBase n)) x) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (c13DyadicShellBase n)) x y) ^ 2 ≤
      c13CoreNewestRelativeEnvelope coreGap n *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock M (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (c13DyadicShellBase n)) y := by
  exact c13EvenBuilderCoreNewest_relative_of_coreFloor
    M (c13DyadicShellBase n) hM hMN x y coreGap
      (c13CoreNewestRelativeEnvelope coreGap n) hCoreGap.le
      (c13CoreNewestRelativeEnvelope_nonneg coreGap hCoreGap.le n)
      hCore (c13CoreNewestRelativeEnvelope_budget coreGap hCoreGap n)

 theorem c13OddBuilderDyadicCoreNewest_relative_vanishingEnvelope
    (M n : ℕ) (hM : 960 ≤ M) (hMN : M ≤ c13DyadicShellBase n)
    (x : Fin (c13DyadicShellBase n - M) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ)
    (coreGap : ℝ) (hCoreGap : 0 < coreGap)
    (hCore : coreGap * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13OddBuilderCoreNewestBlock M (c13DyadicShellBase n)) x) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (c13DyadicShellBase n)) x y) ^ 2 ≤
      c13CoreNewestRelativeEnvelope coreGap n *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock M (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (c13DyadicShellBase n)) y := by
  exact c13OddBuilderCoreNewest_relative_of_coreFloor
    M (c13DyadicShellBase n) hM hMN x y coreGap
      (c13CoreNewestRelativeEnvelope coreGap n) hCoreGap.le
      (c13CoreNewestRelativeEnvelope_nonneg coreGap hCoreGap.le n)
      hCore (c13CoreNewestRelativeEnvelope_budget coreGap hCoreGap n)

end RiemannCvs.V23BoundaryWeylMainline


namespace RiemannCvs.V23BoundaryWeylMainline

/-- Any positive target coefficient is eventually reached by the full
historical-core/newest-shell envelope, provided the historical core retains one
fixed positive Euclidean energy floor. -/
theorem exists_c13CoreNewestRelativeEnvelope_lt
    (coreGap rho : ℝ) (hCoreGap : 0 < coreGap) (hRho : 0 < rho) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      c13CoreNewestRelativeEnvelope coreGap n < rho := by
  have hEventually : ∀ᶠ n in Filter.atTop,
      c13CoreNewestRelativeEnvelope coreGap n < rho :=
    (tendsto_c13CoreNewestRelativeEnvelope_zero coreGap hCoreGap).eventually_lt_const
      hRho
  exact Filter.eventually_atTop.mp hEventually

/-- In particular, the optimized V23 recursive threshold `4/9` is eventually
strictly available for the complete old-core/new-shell channel. -/
theorem exists_c13CoreNewestRelativeEnvelope_lt_fourNinth
    (coreGap : ℝ) (hCoreGap : 0 < coreGap) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      c13CoreNewestRelativeEnvelope coreGap n < 4 / 9 := by
  exact exists_c13CoreNewestRelativeEnvelope_lt
    coreGap (4 / 9 : ℝ) hCoreGap (by norm_num)

end RiemannCvs.V23BoundaryWeylMainline
