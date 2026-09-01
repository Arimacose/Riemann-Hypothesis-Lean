import RiemannCvs.AsymptoticAdjacentCoreHilbertPi

/-!
# Finite CvS matrices as boundary-Weyl energy forms

This module closes a type-level gap between the concrete coordinate estimates
for the literal CvS matrices and the abstract Hilbert-space boundary-Weyl
monotonicity theorem.

For a symmetric matrix on `ι ⊕ κ`, the left and right diagonal blocks become
bilinear forms on `EuclideanSpace ℝ ι` and `EuclideanSpace ℝ κ`.  The coupling
is the symmetrized rectangular block already used by
`finiteMatrixBlockCrossEnergy`.  The coordinate equalities are exact, so a
finite relative-energy certificate transfers without a norm or normalization
loss.

The final theorems instantiate this adapter for the literal even and odd
`c = 13` historical-core/newest-shell matrices.  The complete `(960,N]`
historical core supplies `q = 4/9` from the sharp uniform-envelope cutoff
`n = 70`; the adjacent half `(floor(N/2),N]` supplies the stronger `q = 2/5`
certificate already at `n = 0`.  Only the actual weak resolvent equations and
the finite response remain as explicit boundary-Weyl inputs.
-/

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2
open scoped InnerProductSpace

noncomputable section

def finiteMatrixLowBlock
    {ι κ : Type*}
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  fun i j => A (Sum.inl i) (Sum.inl j)

def finiteMatrixHighBlock
    {ι κ : Type*}
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix κ κ ℝ :=
  fun i j => A (Sum.inr i) (Sum.inr j)

def finiteMatrixAverageCrossBlock
    {ι κ : Type*}
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι κ ℝ :=
  fun i j => (1 / 2 : ℝ) *
    (A (Sum.inl i) (Sum.inr j) + A (Sum.inr j) (Sum.inl i))

noncomputable def finiteMatrixLowForm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toBilin' (finiteMatrixLowBlock A)

noncomputable def finiteMatrixHighForm
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (κ → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toBilin' (finiteMatrixHighBlock A)

noncomputable def finiteMatrixCouplingForm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (ι → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ (finiteMatrixAverageCrossBlock A)

theorem finiteMatrixLowForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x y : ι → ℝ) :
    finiteMatrixLowForm A x y =
      ∑ i, ∑ j, x i * A (Sum.inl i) (Sum.inl j) * y j := by
  simp [finiteMatrixLowForm, finiteMatrixLowBlock, Matrix.toBilin'_apply]

theorem finiteMatrixHighForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x y : κ → ℝ) :
    finiteMatrixHighForm A x y =
      ∑ i, ∑ j, x i * A (Sum.inr i) (Sum.inr j) * y j := by
  simp [finiteMatrixHighForm, finiteMatrixHighBlock, Matrix.toBilin'_apply]

theorem finiteMatrixLowForm_self
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x : ι → ℝ) :
    finiteMatrixLowForm A x x = finiteMatrixBlockBaseEnergy A x := by
  simp [finiteMatrixLowForm_apply, finiteMatrixBlockBaseEnergy]

theorem finiteMatrixHighForm_self
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (y : κ → ℝ) :
    finiteMatrixHighForm A y y = finiteMatrixBlockTailEnergy A y := by
  simp [finiteMatrixHighForm_apply, finiteMatrixBlockTailEnergy]

theorem finiteMatrixCouplingForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    finiteMatrixCouplingForm A x y =
      finiteMatrixBlockCrossEnergy A x y := by
  rw [finiteMatrixBlockCrossEnergy]
  simp only [finiteMatrixCouplingForm, Matrix.toLinearMap₂'_apply,
    finiteMatrixAverageCrossBlock, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring

theorem finiteMatrixLowForm_symm_of_matrix_symm
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hSymm : ∀ i j, A i j = A j i)
    (x y : ι → ℝ) :
    finiteMatrixLowForm A x y = finiteMatrixLowForm A y x := by
  rw [finiteMatrixLowForm_apply, finiteMatrixLowForm_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hSymm (Sum.inl j) (Sum.inl i)]
  ring

noncomputable def finiteMatrixLowEuclideanForm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι →ₗ[ℝ] ℝ :=
  (finiteMatrixLowForm A).compl₁₂
    (EuclideanSpace.equiv ι ℝ).toLinearMap
    (EuclideanSpace.equiv ι ℝ).toLinearMap

noncomputable def finiteMatrixHighEuclideanForm
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ κ →ₗ[ℝ] ℝ :=
  (finiteMatrixHighForm A).compl₁₂
    (EuclideanSpace.equiv κ ℝ).toLinearMap
    (EuclideanSpace.equiv κ ℝ).toLinearMap

noncomputable def finiteMatrixCouplingEuclideanForm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ →ₗ[ℝ] ℝ :=
  (finiteMatrixCouplingForm A).compl₁₂
    (EuclideanSpace.equiv ι ℝ).toLinearMap
    (EuclideanSpace.equiv κ ℝ).toLinearMap

@[simp] theorem finiteMatrixLowEuclideanForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x y : EuclideanSpace ℝ ι) :
    finiteMatrixLowEuclideanForm A x y = finiteMatrixLowForm A x.ofLp y.ofLp :=
  rfl

@[simp] theorem finiteMatrixHighEuclideanForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x y : EuclideanSpace ℝ κ) :
    finiteMatrixHighEuclideanForm A x y = finiteMatrixHighForm A x.ofLp y.ofLp :=
  rfl

@[simp] theorem finiteMatrixCouplingEuclideanForm_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    finiteMatrixCouplingEuclideanForm A x y =
      finiteMatrixCouplingForm A x.ofLp y.ofLp :=
  rfl

theorem finiteMatrixLowEuclideanForm_self
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : EuclideanSpace ℝ ι) :
    finiteMatrixLowEuclideanForm A x x =
      finiteMatrixBlockBaseEnergy A x.ofLp := by
  rw [finiteMatrixLowEuclideanForm_apply, finiteMatrixLowForm_self]

theorem finiteMatrixHighEuclideanForm_self
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (y : EuclideanSpace ℝ κ) :
    finiteMatrixHighEuclideanForm A y y =
      finiteMatrixBlockTailEnergy A y.ofLp := by
  rw [finiteMatrixHighEuclideanForm_apply, finiteMatrixHighForm_self]

theorem finiteMatrixCouplingEuclideanForm_eq_crossEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    finiteMatrixCouplingEuclideanForm A x y =
      finiteMatrixBlockCrossEnergy A x.ofLp y.ofLp := by
  rw [finiteMatrixCouplingEuclideanForm_apply,
    finiteMatrixCouplingForm_apply]

/-- A coordinate-level relative-energy certificate for one finite block split.
The form adapter below turns this data into the exact algebraic hypotheses used
by the abstract boundary-Weyl response theorem. -/
structure FiniteMatrixRelativeEnergyCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (q : ℝ) : Prop where
  symmetric : ∀ i j, A i j = A j i
  base_nonnegative : ∀ x : ι → ℝ, 0 ≤ finiteMatrixBlockBaseEnergy A x
  tail_nonnegative : ∀ y : κ → ℝ, 0 ≤ finiteMatrixBlockTailEnergy A y
  relative : ∀ (x : ι → ℝ) (y : κ → ℝ),
    (finiteMatrixBlockCrossEnergy A x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy A x *
        finiteMatrixBlockTailEnergy A y

theorem finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (q : ℝ) (hCert : FiniteMatrixRelativeEnergyCertificate A q)
    (eta u0 u : EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ κ)
    (hq : 0 ≤ q) (hqLt : q < 1)
    (hFiniteEquation : ∀ w, finiteMatrixLowEuclideanForm A u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm A (u - u0) w +
        finiteMatrixCouplingEuclideanForm A w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm A v z +
        finiteMatrixCouplingEuclideanForm A u z = 0) :
    ⟪eta, u0⟫_ℝ ≤ ⟪eta, u⟫_ℝ := by
  apply boundaryWeyl_mono_of_relativeEnergyCoupling
    (finiteMatrixLowEuclideanForm A) (finiteMatrixHighEuclideanForm A)
    (finiteMatrixCouplingEuclideanForm A) eta u0 u v q hq hqLt
  · intro x y
    simp only [finiteMatrixLowEuclideanForm_apply]
    exact finiteMatrixLowForm_symm_of_matrix_symm A hCert.symmetric _ _
  · intro w
    rw [finiteMatrixLowEuclideanForm_self]
    exact hCert.base_nonnegative w.ofLp
  · intro z
    rw [finiteMatrixHighEuclideanForm_self]
    exact hCert.tail_nonnegative z.ofLp
  · intro w z
    rw [finiteMatrixCouplingEuclideanForm_eq_crossEnergy,
      finiteMatrixLowEuclideanForm_self,
      finiteMatrixHighEuclideanForm_self]
    exact hCert.relative w.ofLp z.ofLp
  · exact hFiniteEquation
  · exact hLowEquation
  · exact hHighEquation

theorem finiteMatrixBoundaryWeyl_pos_of_relativeEnergyCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (q : ℝ) (hCert : FiniteMatrixRelativeEnergyCertificate A q)
    (eta u0 u : EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ κ)
    (hq : 0 ≤ q) (hqLt : q < 1)
    (hFinitePos : 0 < ⟪eta, u0⟫_ℝ)
    (hFiniteEquation : ∀ w, finiteMatrixLowEuclideanForm A u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm A (u - u0) w +
        finiteMatrixCouplingEuclideanForm A w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm A v z +
        finiteMatrixCouplingEuclideanForm A u z = 0) :
    0 < ⟪eta, u⟫_ℝ := by
  exact hFinitePos.trans_le
    (finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate
      A q hCert eta u0 u v hq hqLt
      hFiniteEquation hLowEquation hHighEquation)

/-- At every dyadic scale from `n = 70` onward, the literal even CvS
historical-core/newest-shell matrix supplies all algebraic hypotheses needed
by the energy-normalized boundary-Weyl theorem, with `q = 4/9`. -/
theorem c13EvenBuilderDyadicCoreNewest_relativeEnergyCertificate_of_ge_70
    (n : ℕ) (hn : 70 ≤ n) :
    FiniteMatrixRelativeEnergyCertificate
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
      (4 / 9 : ℝ) := by
  have hN : 960 ≤ c13DyadicShellBase n := by
    have h := c13DyadicShellBase_ge_371293 n
    omega
  constructor
  · intro i j
    exact logarithmicCvSBuilderEvenPositiveModeMatrix_symm
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode 960 (c13DyadicShellBase n)) i j
  · intro x
    have hCore := c13EvenBuilderCoreNewestBaseEnergy_ge_19283Over26880
      960 (c13DyadicShellBase n) (by norm_num) x
    exact (mul_nonneg (by norm_num)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  · intro y
    have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
      960 (c13DyadicShellBase n) hN y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg _ hN)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  · exact c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70 n hn

/-- Odd-parity companion of the eventual `q = 4/9` form certificate. -/
theorem c13OddBuilderDyadicCoreNewest_relativeEnergyCertificate_of_ge_70
    (n : ℕ) (hn : 70 ≤ n) :
    FiniteMatrixRelativeEnergyCertificate
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
      (4 / 9 : ℝ) := by
  have hN : 960 ≤ c13DyadicShellBase n := by
    have h := c13DyadicShellBase_ge_371293 n
    omega
  constructor
  · intro i j
    exact logarithmicCvSBuilderOddPositiveModeMatrix_symm
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode 960 (c13DyadicShellBase n)) i j
  · intro x
    have hCore := c13OddBuilderCoreNewestBaseEnergy_ge_19283Over26880
      960 (c13DyadicShellBase n) (by norm_num) x
    exact (mul_nonneg (by norm_num)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  · intro y
    have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
      960 (c13DyadicShellBase n) hN y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg _ hN)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  · exact c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70 n hn

/-- Stronger scale-free certificate for the historical half immediately
adjacent to the newest shell.  This is the local block used by the multiband
route; unlike the full `(960,N]` certificate it is valid already at `n = 0`. -/
theorem c13EvenBuilderDyadicAdjacentCoreNewest_relativeEnergyCertificate
    (n : ℕ) :
    FiniteMatrixRelativeEnergyCertificate
      (c13EvenBuilderCoreNewestBlock
        (c13DyadicShellBase n / 2) (c13DyadicShellBase n))
      (2 / 5 : ℝ) := by
  let N := c13DyadicShellBase n
  let M := N / 2
  have hMStrong : 6 * 13 ^ 4 ≤ M := by
    simpa [M, N] using c13DyadicHalf_ge_six_mul_thirteenPowFour n
  have hN : 960 ≤ N := by
    have h := c13DyadicShellBase_ge_371293 n
    dsimp [N]
    omega
  constructor
  · intro i j
    exact logarithmicCvSBuilderEvenPositiveModeMatrix_symm
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) i j
  · intro x
    have hCore :=
      c13EvenBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
        M N hMStrong x
    exact (mul_nonneg (by norm_num)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  · intro y
    have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
      M N hN y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg N hN)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  · simpa [M, N] using
      c13EvenBuilderDyadicAdjacentCoreNewest_relative_twoFifths n

theorem c13OddBuilderDyadicAdjacentCoreNewest_relativeEnergyCertificate
    (n : ℕ) :
    FiniteMatrixRelativeEnergyCertificate
      (c13OddBuilderCoreNewestBlock
        (c13DyadicShellBase n / 2) (c13DyadicShellBase n))
      (2 / 5 : ℝ) := by
  let N := c13DyadicShellBase n
  let M := N / 2
  have hMStrong : 6 * 13 ^ 4 ≤ M := by
    simpa [M, N] using c13DyadicHalf_ge_six_mul_thirteenPowFour n
  have hN : 960 ≤ N := by
    have h := c13DyadicShellBase_ge_371293 n
    dsimp [N]
    omega
  constructor
  · intro i j
    exact logarithmicCvSBuilderOddPositiveModeMatrix_symm
      13 c13PrimePowerLocation c13PrimePowerBase
      (c13CoreNewestPositiveMode M N) i j
  · intro x
    have hCore :=
      c13OddBuilderAdjacentCoreNewestBaseEnergy_ge_fiftyNineTenths
        M N hMStrong x
    exact (mul_nonneg (by norm_num)
      (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  · intro y
    have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
      M N hN y
    exact (mul_nonneg (c13ShellDynamicGap_nonneg N hN)
      (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  · simpa [M, N] using
      c13OddBuilderDyadicAdjacentCoreNewest_relative_twoFifths n

/-- The even finite matrix certificate now reaches the abstract
boundary-Weyl response without any untyped matrix/form conversion left over.
The three remaining assumptions are precisely the finite and split weak
resolvent equations. -/
theorem c13EvenBuilderDyadic_boundaryWeyl_mono_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (eta u0 u :
      EuclideanSpace ℝ (Fin (c13DyadicShellBase n - 960)))
    (v : EuclideanSpace ℝ (Fin (c13DyadicShellBase n)))
    (hFiniteEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          (u - u0) w +
        finiteMatrixCouplingEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          v z +
        finiteMatrixCouplingEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u z = 0) :
    ⟪eta, u0⟫_ℝ ≤ ⟪eta, u⟫_ℝ := by
  exact finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate
    (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
    (4 / 9) (c13EvenBuilderDyadicCoreNewest_relativeEnergyCertificate_of_ge_70
      n hn)
    eta u0 u v (by norm_num) (by norm_num)
    hFiniteEquation hLowEquation hHighEquation

/-- Odd-parity boundary-Weyl monotonicity at the same sharp eventual cutoff. -/
theorem c13OddBuilderDyadic_boundaryWeyl_mono_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (eta u0 u :
      EuclideanSpace ℝ (Fin (c13DyadicShellBase n - 960)))
    (v : EuclideanSpace ℝ (Fin (c13DyadicShellBase n)))
    (hFiniteEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          (u - u0) w +
        finiteMatrixCouplingEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          v z +
        finiteMatrixCouplingEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u z = 0) :
    ⟪eta, u0⟫_ℝ ≤ ⟪eta, u⟫_ℝ := by
  exact finiteMatrixBoundaryWeyl_mono_of_relativeEnergyCertificate
    (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
    (4 / 9) (c13OddBuilderDyadicCoreNewest_relativeEnergyCertificate_of_ge_70
      n hn)
    eta u0 u v (by norm_num) (by norm_num)
    hFiniteEquation hLowEquation hHighEquation

theorem c13EvenBuilderDyadic_boundaryWeyl_pos_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (eta u0 u :
      EuclideanSpace ℝ (Fin (c13DyadicShellBase n - 960)))
    (v : EuclideanSpace ℝ (Fin (c13DyadicShellBase n)))
    (hFinitePos : 0 < ⟪eta, u0⟫_ℝ)
    (hFiniteEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          (u - u0) w +
        finiteMatrixCouplingEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          v z +
        finiteMatrixCouplingEuclideanForm
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u z = 0) :
    0 < ⟪eta, u⟫_ℝ := by
  exact hFinitePos.trans_le
    (c13EvenBuilderDyadic_boundaryWeyl_mono_of_ge_70 n hn eta u0 u v
      hFiniteEquation hLowEquation hHighEquation)

theorem c13OddBuilderDyadic_boundaryWeyl_pos_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (eta u0 u :
      EuclideanSpace ℝ (Fin (c13DyadicShellBase n - 960)))
    (v : EuclideanSpace ℝ (Fin (c13DyadicShellBase n)))
    (hFinitePos : 0 < ⟪eta, u0⟫_ℝ)
    (hFiniteEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      finiteMatrixLowEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          (u - u0) w +
        finiteMatrixCouplingEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          w v = 0)
    (hHighEquation : ∀ z,
      finiteMatrixHighEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          v z +
        finiteMatrixCouplingEuclideanForm
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n))
          u z = 0) :
    0 < ⟪eta, u⟫_ℝ := by
  exact hFinitePos.trans_le
    (c13OddBuilderDyadic_boundaryWeyl_mono_of_ge_70 n hn eta u0 u v
      hFiniteEquation hLowEquation hHighEquation)

end

end RiemannCvs.V23BoundaryWeylMainline
