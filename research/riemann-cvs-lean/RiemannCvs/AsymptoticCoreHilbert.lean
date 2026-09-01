import RiemannCvs.AsymptoticCoreNewestTotalError

/-!
# Uniform historical-core coercivity from a weighted Hilbert split

This module closes the fixed-core premise left by the asymptotic
core/newest-shell analysis.  The Archimedean remainder on an arbitrarily long
consecutive positive-mode core is split into

* the reflected half-Hilbert kernel `1 / (2 * (p + q))`;
* a centered reflected rank-one correction; and
* the centered same-sign divided-difference kernel.

Two elementary telescoping square-root estimates give a dimension-free
weighted-Schur constant `4` for `1 / (p + q)`, hence constant `2` for the
half-Hilbert quadratic form.  The centered reflected term costs only
`1 / 11520` above cutoff `960`.  A reciprocal-square distance-kernel estimate
and finite Hilbert--Schmidt argument first bound the same-sign term by `1 / 8`
and then sharpen it to `1 / 90`.  Thus the complete centered residual costs
only `43 / 3840` in both parity channels.

Combining this operator estimate with the diagonal, pole, and prime budgets
proves a uniform `1109 / 3840` coercivity floor for every historical core
beginning at `M >= 960`, without restricting its length.  As a concrete no-crossing
consequence, the actual even and odd CvS builder blocks satisfy the full
historical-core/newest-shell relative `4 / 9` bound on the dyadic tail for
every `n >= 190`.
-/

noncomputable section

namespace RiemannCvs.V23BoundaryWeylMainline

open scoped BigOperators
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2

lemma inv_sqrt_le_two_mul_sqrt_sub
    (x : ℝ) (hx : 1 ≤ x) :
    1 / Real.sqrt x ≤
      2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hxm0 : 0 ≤ x - 1 := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsxm0 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg _
  have hsxm_le : Real.sqrt (x - 1) ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt (by linarith)
  have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  have hsxm_sq : (Real.sqrt (x - 1)) ^ 2 = x - 1 := Real.sq_sqrt hxm0
  apply (div_le_iff₀ hsx0).2
  nlinarith

lemma inv_mul_sqrt_le_two_mul_inv_sqrt_sub
    (x : ℝ) (hx : 1 < x) :
    1 / (x * Real.sqrt x) ≤
      2 * (1 / Real.sqrt (x - 1) - 1 / Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hxm0 : 0 < x - 1 := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsxm0 : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.2 hxm0
  have hsxm_le : Real.sqrt (x - 1) ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt (by linarith)
  have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  have hsxm_sq : (Real.sqrt (x - 1)) ^ 2 = x - 1 := Real.sq_sqrt hxm0.le
  field_simp [ne_of_gt hx0, ne_of_gt hsx0, ne_of_gt hsxm0]
  nlinarith [mul_nonneg hsxm0.le (sub_nonneg.mpr hsxm_le)]

lemma sum_inv_sqrt_shift_le_two_sqrt
    (M r : ℕ) :
    (∑ j ∈ Finset.range r,
        1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((M + r : ℕ) : ℝ) := by
  calc
    (∑ j ∈ Finset.range r,
        1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range r,
          2 * (Real.sqrt ((M + j + 1 : ℕ) : ℝ) -
            Real.sqrt ((M + j : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := inv_sqrt_le_two_mul_sqrt_sub
        (((M + j + 1 : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ M + j + 1 by omega))
      push_cast at h
      push_cast
      ring_nf at h ⊢
      exact h
    _ = 2 * (Real.sqrt ((M + r : ℕ) : ℝ) - Real.sqrt (M : ℝ)) := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_range_sub
        (fun j : ℕ => Real.sqrt ((M + j : ℕ) : ℝ)) r
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero] using
        congrArg (2 * ·) htel
    _ ≤ 2 * Real.sqrt ((M + r : ℕ) : ℝ) := by
      nlinarith [Real.sqrt_nonneg (M : ℝ)]

lemma sum_inv_mul_sqrt_shift_succ_le_two_div_sqrt
    (M r : ℕ) (hM : 1 ≤ M) :
    (∑ j ∈ Finset.range r,
        1 / (((M + j + 1 : ℕ) : ℝ) *
          Real.sqrt ((M + j + 1 : ℕ) : ℝ))) ≤
      2 / Real.sqrt (M : ℝ) := by
  calc
    (∑ j ∈ Finset.range r,
        1 / (((M + j + 1 : ℕ) : ℝ) *
          Real.sqrt ((M + j + 1 : ℕ) : ℝ))) ≤
        ∑ j ∈ Finset.range r,
          2 * (1 / Real.sqrt ((M + j : ℕ) : ℝ) -
            1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := inv_mul_sqrt_le_two_mul_inv_sqrt_sub
        (((M + j + 1 : ℕ) : ℝ))
        (by exact_mod_cast (show 1 < M + j + 1 by omega))
      push_cast at h
      push_cast
      ring_nf at h ⊢
      exact h
    _ = 2 * (1 / Real.sqrt (M : ℝ) -
        1 / Real.sqrt ((M + r : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_range_sub'
        (fun j : ℕ => 1 / Real.sqrt ((M + j : ℕ) : ℝ)) r
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero] using
        congrArg (2 * ·) htel
    _ ≤ 2 / Real.sqrt (M : ℝ) := by
      have hnonneg : 0 ≤ 1 / Real.sqrt ((M + r : ℕ) : ℝ) := by positivity
      calc
        2 * (1 / Real.sqrt (M : ℝ) -
            1 / Real.sqrt ((M + r : ℕ) : ℝ)) ≤
            2 * (1 / Real.sqrt (M : ℝ)) := by linarith
        _ = 2 / Real.sqrt (M : ℝ) := by ring

lemma hilbert_mul_inv_sqrt_le_left
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (1 / (p + q)) * (1 / Real.sqrt q) ≤
      (1 / p) * (1 / Real.sqrt q) := by
  have hinv : 1 / (p + q) ≤ 1 / p :=
    one_div_le_one_div_of_le hp (by linarith)
  exact mul_le_mul_of_nonneg_right hinv (by positivity)

lemma hilbert_mul_inv_sqrt_le_right
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (1 / (p + q)) * (1 / Real.sqrt q) ≤
      1 / (q * Real.sqrt q) := by
  have hinv : 1 / (p + q) ≤ 1 / q :=
    one_div_le_one_div_of_le hq (by linarith)
  calc
    (1 / (p + q)) * (1 / Real.sqrt q) ≤
        (1 / q) * (1 / Real.sqrt q) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 1 / (q * Real.sqrt q) := by ring

noncomputable def c13CoreHilbertKernel (M L : ℕ) :
    Matrix (Fin L) (Fin L) ℝ :=
  fun i j => 1 / (((M + (i : ℕ) + 1 : ℕ) : ℝ) +
    ((M + (j : ℕ) + 1 : ℕ) : ℝ))

noncomputable def c13CoreHilbertWeight (M L : ℕ) : Fin L → ℝ :=
  fun i => 1 / Real.sqrt ((M + (i : ℕ) + 1 : ℕ) : ℝ)

lemma c13CoreHilbertWeight_pos
    (M L : ℕ) (i : Fin L) :
    0 < c13CoreHilbertWeight M L i := by
  unfold c13CoreHilbertWeight
  positivity

lemma c13CoreHilbertKernel_row_le_four
    (M L : ℕ) (i : Fin L) :
    (∑ j, c13CoreHilbertKernel M L i j * c13CoreHilbertWeight M L j) ≤
      4 * c13CoreHilbertWeight M L i := by
  let p : ℕ := M + (i : ℕ) + 1
  let f : ℕ → ℝ := fun j =>
    (1 / ((p : ℝ) + ((M + j + 1 : ℕ) : ℝ))) *
      (1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ))
  have hp : 1 ≤ p := by simp [p]
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hiL : (i : ℕ) + 1 ≤ L := i.isLt
  have hLow :
      (∑ j ∈ Finset.range ((i : ℕ) + 1), f j) ≤
        2 / Real.sqrt (p : ℝ) := by
    calc
      (∑ j ∈ Finset.range ((i : ℕ) + 1), f j) ≤
          ∑ j ∈ Finset.range ((i : ℕ) + 1),
            (1 / (p : ℝ)) *
              (1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hilbert_mul_inv_sqrt_le_left
          (p : ℝ) ((M + j + 1 : ℕ) : ℝ) hpR (by positivity)
      _ = (1 / (p : ℝ)) *
          (∑ j ∈ Finset.range ((i : ℕ) + 1),
            1 / Real.sqrt ((M + j + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / (p : ℝ)) * (2 * Real.sqrt (p : ℝ)) := by
        have hsum := sum_inv_sqrt_shift_le_two_sqrt M ((i : ℕ) + 1)
        have hpCast : ((M + ((i : ℕ) + 1) : ℕ) : ℝ) = (p : ℝ) := by
          push_cast
          simp [p]
          ring_nf
        rw [hpCast] at hsum
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 / Real.sqrt (p : ℝ) := by
        have hspos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
        have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hpR.le
        field_simp [ne_of_gt hpR, ne_of_gt hspos]
        nlinarith
  have hHigh :
      (∑ j ∈ Finset.range (L - ((i : ℕ) + 1)),
          f (((i : ℕ) + 1) + j)) ≤
        2 / Real.sqrt (p : ℝ) := by
    calc
      (∑ j ∈ Finset.range (L - ((i : ℕ) + 1)),
          f (((i : ℕ) + 1) + j)) ≤
          ∑ j ∈ Finset.range (L - ((i : ℕ) + 1)),
            1 / (((p + j + 1 : ℕ) : ℝ) *
              Real.sqrt ((p + j + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := hilbert_mul_inv_sqrt_le_right
          (p : ℝ) ((p + j + 1 : ℕ) : ℝ) hpR (by positivity)
        dsimp [f]
        have hq : M + (((i : ℕ) + 1) + j) + 1 = p + j + 1 := by
          simp [p]
          omega
        rw [hq]
        exact h
      _ ≤ 2 / Real.sqrt (p : ℝ) :=
        sum_inv_mul_sqrt_shift_succ_le_two_div_sqrt
          p (L - ((i : ℕ) + 1)) hp
  change (∑ j : Fin L, f j) ≤ 4 * (1 / Real.sqrt (p : ℝ))
  rw [Fin.sum_univ_eq_sum_range f L]
  rw [← Nat.add_sub_of_le hiL, Finset.sum_range_add]
  calc
    (∑ x ∈ Finset.range ((i : ℕ) + 1), f x) +
        ∑ x ∈ Finset.range (L - ((i : ℕ) + 1)),
          f ((i : ℕ) + 1 + x) ≤
        2 / Real.sqrt (p : ℝ) + 2 / Real.sqrt (p : ℝ) :=
      add_le_add hLow hHigh
    _ = 4 * (1 / Real.sqrt (p : ℝ)) := by ring

lemma c13CoreHilbertKernel_nonneg
    (M L : ℕ) (i j : Fin L) :
    0 ≤ c13CoreHilbertKernel M L i j := by
  unfold c13CoreHilbertKernel
  positivity

lemma c13CoreHilbertKernel_symm
    (M L : ℕ) (i j : Fin L) :
    c13CoreHilbertKernel M L i j = c13CoreHilbertKernel M L j i := by
  unfold c13CoreHilbertKernel
  congr 1
  ring

lemma weightedSchurEnergy_eq_finiteMatrixQuadraticEnergy
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    RiemannCvs.WeightedSchurSupersolution.weightedSchurEnergy A x =
      finiteMatrixQuadraticEnergy A x := by
  unfold RiemannCvs.WeightedSchurSupersolution.weightedSchurEnergy
    finiteMatrixQuadraticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma weightedSchurNormSq_eq_finiteVectorEuclideanNormSq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    RiemannCvs.WeightedSchurSupersolution.weightedSchurNormSq x =
      finiteVectorEuclideanNormSq x := by
  rfl

/-- A dimension-free, fully elementary weighted-Schur estimate for the
positive Hilbert kernel on every finite consecutive interval above `M`.
The constant `4` comes from two telescoping square-root tails. -/
theorem c13CoreHilbertKernel_energy_abs_le_four
    (M L : ℕ) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy (c13CoreHilbertKernel M L) x| ≤
      4 * finiteVectorEuclideanNormSq x := by
  have h := RiemannCvs.WeightedSchurSupersolution.weightedSchur_quadratic
    (c13CoreHilbertKernel M L) x (c13CoreHilbertWeight M L) 4
    (c13CoreHilbertKernel_nonneg M L)
    (c13CoreHilbertKernel_symm M L)
    (c13CoreHilbertWeight_pos M L)
    (c13CoreHilbertKernel_row_le_four M L)
  simpa only [weightedSchurEnergy_eq_finiteMatrixQuadraticEnergy,
    weightedSchurNormSq_eq_finiteVectorEuclideanNormSq] using h

noncomputable def c13CoreReflectedHilbertLeadingMatrix (M L : ℕ) :
    Matrix (Fin L) (Fin L) ℝ :=
  (1 / 2 : ℝ) • c13CoreHilbertKernel M L

theorem c13CoreReflectedHilbertLeading_energy_abs_le_two
    (M L : ℕ) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreReflectedHilbertLeadingMatrix M L) x| ≤
      2 * finiteVectorEuclideanNormSq x := by
  have h := c13CoreHilbertKernel_energy_abs_le_four M L x
  have heq :
      finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x =
        (1 / 2 : ℝ) * finiteMatrixQuadraticEnergy
          (c13CoreHilbertKernel M L) x := by
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

noncomputable def c13OddCoreReflectedHilbertLeadingMatrix (M L : ℕ) :
    Matrix (Fin L) (Fin L) ℝ :=
  -c13CoreReflectedHilbertLeadingMatrix M L

theorem c13OddCoreReflectedHilbertLeading_energy_abs_le_two
    (M L : ℕ) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddCoreReflectedHilbertLeadingMatrix M L) x| ≤
      2 * finiteVectorEuclideanNormSq x := by
  have h := c13CoreReflectedHilbertLeading_energy_abs_le_two M L x
  have heq :
      finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x =
        -finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x := by
    unfold c13OddCoreReflectedHilbertLeadingMatrix finiteMatrixQuadraticEnergy
    simp only [Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  rw [heq, abs_neg]
  exact h

noncomputable def c13EvenCoreArchimedeanCenteredResidualMatrix
    (M L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
      13 (finGlobalShellPositiveMode M L) -
    c13CoreReflectedHilbertLeadingMatrix M L

noncomputable def c13OddCoreArchimedeanCenteredResidualMatrix
    (M L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
      13 (finGlobalShellPositiveMode M L) -
    c13OddCoreReflectedHilbertLeadingMatrix M L

lemma c13EvenCoreArchimedeanRemainder_eq_leading_add_centered
    (M L : ℕ) :
    logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
        13 (finGlobalShellPositiveMode M L) =
      c13CoreReflectedHilbertLeadingMatrix M L +
        c13EvenCoreArchimedeanCenteredResidualMatrix M L := by
  ext i j
  simp [c13EvenCoreArchimedeanCenteredResidualMatrix]

lemma c13OddCoreArchimedeanRemainder_eq_leading_add_centered
    (M L : ℕ) :
    logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
        13 (finGlobalShellPositiveMode M L) =
      c13OddCoreReflectedHilbertLeadingMatrix M L +
        c13OddCoreArchimedeanCenteredResidualMatrix M L := by
  ext i j
  simp [c13OddCoreArchimedeanCenteredResidualMatrix]

theorem c13EvenCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
    (M L : ℕ) (x : Fin L → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ 2 * finiteVectorEuclideanNormSq x +
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add (c13CoreReflectedHilbertLeading_energy_abs_le_two M L x) hCentered
    _ = (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13OddCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
    (M L : ℕ) (x : Fin L → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ 2 * finiteVectorEuclideanNormSq x +
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add (c13OddCoreReflectedHilbertLeading_energy_abs_le_two M L x) hCentered
    _ = (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by ring

lemma c13_globalCore_scalar_reserve_ge_oneTwentieth
    (M : ℕ) (hM : 960 ≤ M) :
    (1 / 20 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) +
        9 / 4 + 10 / 3) := by
  nlinarith [c13_shell_complete_scalar_reserve_ge_nineFifths M hM]

theorem c13_logarithmicCvSBuilderEvenCore_energy_ge_oneTwentieth_of_centered
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch :=
    c13EvenCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
      M L x hCentered
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (1 / 20) (9 / 4)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_oneTwentieth M hM)
  simpa using h

theorem c13_logarithmicCvSBuilderOddCore_energy_ge_oneTwentieth_of_centered
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch :=
    c13OddCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
      M L x hCentered
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (1 / 20) (9 / 4)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_oneTwentieth M hM)
  simpa using h

lemma c13CoreMode_eq_finGlobalShellPositiveMode
    (M N : ℕ) (i : Fin (N - M)) :
    (c13CoreMode M N i : ℤ) =
      finGlobalShellPositiveMode M (N - M) i := by
  simp [c13CoreMode, finGlobalShellPositiveMode]

@[simp] lemma c13EvenBuilderCoreNewestBlock_inl_inl
    (M N : ℕ) (i j : Fin (N - M)) :
    c13EvenBuilderCoreNewestBlock M N (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M (N - M)) i j := by
  simp only [c13EvenBuilderCoreNewestBlock,
    logarithmicCvSBuilderEvenPositiveModeMatrix,
    c13CoreNewestPositiveMode, Sum.elim_inl,
    c13CoreMode_eq_finGlobalShellPositiveMode]

@[simp] lemma c13OddBuilderCoreNewestBlock_inl_inl
    (M N : ℕ) (i j : Fin (N - M)) :
    c13OddBuilderCoreNewestBlock M N (Sum.inl i) (Sum.inl j) =
      logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M (N - M)) i j := by
  simp only [c13OddBuilderCoreNewestBlock,
    logarithmicCvSBuilderOddPositiveModeMatrix,
    c13CoreNewestPositiveMode, Sum.elim_inl,
    c13CoreMode_eq_finGlobalShellPositiveMode]

theorem c13EvenBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M (N - M)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderEvenCore_energy_ge_oneTwentieth_of_centered
    M (N - M) hM x hCentered
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13OddBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M (N - M)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderOddCore_energy_ge_oneTwentieth_of_centered
    M (N - M) hM x hCentered
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13EvenBuilderCoreNewest_relative_of_centeredResidual
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M (N - M)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1 / 20 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  exact c13EvenBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (1 / 20) q (by norm_num) hq
    (c13EvenBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
      M N hM x hCentered)
    hBudget

theorem c13OddBuilderCoreNewest_relative_of_centeredResidual
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M (N - M)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1 / 20 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  exact c13OddBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (1 / 20) q (by norm_num) hq
    (c13OddBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
      M N hM x hCentered)
    hBudget

theorem c13CoreNewestRelativeEnvelope_oneTwentieth_lt_fourNinth
    (n : ℕ) (hn : 1150 ≤ n) :
    c13CoreNewestRelativeEnvelope (1 / 20) n < (4 / 9 : ℝ) := by
  have hnR : (1150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < c13DyadicGapLower n := c13DyadicGapLower_pos n
  unfold c13CoreNewestRelativeEnvelope
  apply (div_lt_iff₀ (mul_pos (by norm_num) hgap)).2
  have hscaled : (1150 : ℝ) * (69 / 100 : ℝ) ≤
      (n : ℝ) * (69 / 100 : ℝ) :=
    mul_le_mul_of_nonneg_right hnR (by norm_num)
  unfold c13DyadicGapLower
  norm_num at hscaled ⊢
  nlinarith

theorem c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_centeredResidual
    (n : ℕ) (hn : 1150 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix
            960 (c13DyadicShellBase n - 960)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13EvenBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    960 (c13DyadicShellBase n) (by norm_num) x hCentered
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13EvenBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (1 / 20) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt (c13CoreNewestRelativeEnvelope_oneTwentieth_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

theorem c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_centeredResidual
    (n : ℕ) (hn : 1150 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ)
    (hCentered :
      |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix
            960 (c13DyadicShellBase n - 960)) x| ≤
        (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13OddBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    960 (c13DyadicShellBase n) (by norm_num) x hCentered
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13OddBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (1 / 20) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt (c13CoreNewestRelativeEnvelope_oneTwentieth_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

lemma one_div_sq_le_inv_sub_inv
    (x : ℝ) (hx : 1 < x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hxm0 : 0 < x - 1 := by linarith
  field_simp [ne_of_gt hx0, ne_of_gt hxm0]
  nlinarith

lemma sum_shifted_inv_sq_le_inv
    (M L : ℕ) (hM : 1 ≤ M) :
    (∑ j ∈ Finset.range L,
        1 / (((M + j + 1 : ℕ) : ℝ) ^ 2)) ≤
      1 / (M : ℝ) := by
  calc
    (∑ j ∈ Finset.range L,
        1 / (((M + j + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ j ∈ Finset.range L,
          (1 / ((M + j : ℕ) : ℝ) -
            1 / ((M + j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := one_div_sq_le_inv_sub_inv
        (((M + j + 1 : ℕ) : ℝ))
        (by exact_mod_cast (show 1 < M + j + 1 by omega))
      push_cast at h ⊢
      ring_nf at h ⊢
      exact h
    _ = 1 / (M : ℝ) - 1 / ((M + L : ℕ) : ℝ) := by
      have htel := Finset.sum_range_sub'
        (fun j : ℕ => 1 / ((M + j : ℕ) : ℝ)) L
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero] using htel
    _ ≤ 1 / (M : ℝ) := by
      have hnonneg : 0 ≤ 1 / ((M + L : ℕ) : ℝ) := by positivity
      linarith

lemma fin_sum_shifted_inv_sq_le_inv
    (M L : ℕ) (hM : 1 ≤ M) :
    (∑ i : Fin L, (1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)) ^ 2) ≤
      1 / (M : ℝ) := by
  change (∑ i : Fin L,
      (fun j : ℕ => (1 / ((M + j + 1 : ℕ) : ℝ)) ^ 2) i) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (1 / ((M + j + 1 : ℕ) : ℝ)) ^ 2) L]
  simpa only [one_div, inv_pow] using sum_shifted_inv_sq_le_inv M L hM

/-- A pointwise rank-one envelope controls a finite quadratic form with the
same Cauchy--Schwarz coefficient as the exact rank-one matrix. -/
theorem finiteMatrixQuadraticEnergy_abs_le_rankOneEnvelope
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (C : ℝ) (u x : ι → ℝ)
    (hC : 0 ≤ C)
    (hEntry : ∀ i j, |A i j| ≤ C * u i * u j) :
    |finiteMatrixQuadraticEnergy A x| ≤
      C * (∑ i, u i ^ 2) * finiteVectorEuclideanNormSq x := by
  unfold finiteMatrixQuadraticEnergy
  calc
    |∑ i, ∑ j, x i * A i j * x j| ≤
        ∑ i, |∑ j, x i * A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * x j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j,
        |x i| * (C * u i * u j) * |x j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hEntry i j) (abs_nonneg (x i)))
        (abs_nonneg (x j))
    _ = C * (∑ i, u i * |x i|) ^ 2 := by
      rw [← finiteMatrixQuadraticEnergy_rankOne]
      unfold finiteMatrixQuadraticEnergy
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ C * (∑ i, u i ^ 2) * finiteVectorEuclideanNormSq x := by
      have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset ι) u (fun i => |x i|)
      have hScaled := mul_le_mul_of_nonneg_left hCauchy hC
      simpa only [sq_abs, finiteVectorEuclideanNormSq, mul_assoc] using hScaled

noncomputable def c13CoreArchimedeanReflectedCenteredMatrix
    (M L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  fun i j =>
    (centeredArchimedeanSymbol 13
        ((M + (i : ℕ) + 1 : ℕ) : ℤ) +
      centeredArchimedeanSymbol 13
        ((M + (j : ℕ) + 1 : ℕ) : ℤ)) /
      (Real.pi *
        (((M + (i : ℕ) + 1 : ℕ) : ℝ) +
          ((M + (j : ℕ) + 1 : ℕ) : ℝ)))

lemma c13CoreArchimedeanReflectedCentered_entry_abs_le
    (M L : ℕ) (hM : 960 ≤ M) (i j : Fin L) :
    |c13CoreArchimedeanReflectedCenteredMatrix M L i j| ≤
      1 / (12 * ((M + (i : ℕ) + 1 : ℕ) : ℝ) *
        ((M + (j : ℕ) + 1 : ℕ) : ℝ)) := by
  let p : ℕ := M + (i : ℕ) + 1
  let q : ℕ := M + (j : ℕ) + 1
  have hp : 960 ≤ p := by simp [p]; omega
  have hq : 960 ≤ q := by simp [q]; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcp := c13_centeredArchimedeanSymbol_nat_abs_le p hp
  have hcq := c13_centeredArchimedeanSymbol_nat_abs_le q hq
  have hnum :
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
        1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by
    calc
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
          |centeredArchimedeanSymbol 13 (p : ℤ)| +
            |centeredArchimedeanSymbol 13 (q : ℤ)| := abs_add_le _ _
      _ ≤ (1 / 4 : ℝ) / (p : ℝ) + (1 / 4 : ℝ) / (q : ℝ) :=
        add_le_add hcp hcq
      _ = 1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by ring
  have hsum : (0 : ℝ) < (p : ℝ) + (q : ℝ) := by positivity
  have hden : 3 * ((p : ℝ) + (q : ℝ)) ≤
      Real.pi * ((p : ℝ) + (q : ℝ)) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le hsum.le
  change |(centeredArchimedeanSymbol 13 (p : ℤ) +
      centeredArchimedeanSymbol 13 (q : ℤ)) /
        (Real.pi * ((p : ℝ) + (q : ℝ)))| ≤ _
  rw [abs_div, abs_of_pos (mul_pos Real.pi_pos hsum)]
  calc
    |centeredArchimedeanSymbol 13 (p : ℤ) +
        centeredArchimedeanSymbol 13 (q : ℤ)| /
        (Real.pi * ((p : ℝ) + (q : ℝ))) ≤
      (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
        (Real.pi * ((p : ℝ) + (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
        (3 * ((p : ℝ) + (q : ℝ))) := by
      gcongr
    _ ≤ 1 / (12 * (p : ℝ) * (q : ℝ)) :=
      centered_reflected_scalar_le (p : ℝ) (q : ℝ) (p : ℝ) (q : ℝ)
        hpR le_rfl hqR le_rfl

theorem c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreArchimedeanReflectedCenteredMatrix M L) x| ≤
      (1 / 11520 : ℝ) * finiteVectorEuclideanNormSq x := by
  let u : Fin L → ℝ := fun i =>
    1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)
  have hEnvelope := finiteMatrixQuadraticEnergy_abs_le_rankOneEnvelope
    (c13CoreArchimedeanReflectedCenteredMatrix M L) (1 / 12) u x
    (by norm_num) (by
      intro i j
      have h := c13CoreArchimedeanReflectedCentered_entry_abs_le M L hM i j
      dsimp only [u]
      exact h.trans_eq (by ring))
  have hSum : (∑ i, u i ^ 2) ≤ 1 / (M : ℝ) := by
    simpa only [u] using fin_sum_shifted_inv_sq_le_inv M L (by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMInv : 1 / (M : ℝ) ≤ 1 / (960 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)
  have hCoeff : (1 / 12 : ℝ) * (∑ i, u i ^ 2) ≤ 1 / 11520 := by
    calc
      (1 / 12 : ℝ) * (∑ i, u i ^ 2) ≤ (1 / 12 : ℝ) * (1 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hSum (by norm_num)
      _ ≤ (1 / 12 : ℝ) * (1 / 960 : ℝ) :=
        mul_le_mul_of_nonneg_left hMInv (by norm_num)
      _ = 1 / 11520 := by norm_num
  exact hEnvelope.trans
    (mul_le_mul_of_nonneg_right hCoeff (finiteVectorEuclideanNormSq_nonneg x))

lemma sum_range_one_div_succ_sq_le_two (r : ℕ) :
    (∑ k ∈ Finset.range r, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) ≤ 2 := by
  cases r with
  | zero => norm_num
  | succ r =>
      rw [Finset.sum_range_succ']
      have htail := sum_shifted_inv_sq_le_inv 1 r (by norm_num)
      norm_num at htail ⊢
      ring_nf at htail ⊢
      linarith

noncomputable def natDistanceSqKernel (a b : ℕ) : ℝ :=
  if a = b then 0 else 1 / ((Nat.dist a b : ℝ) ^ 2)

lemma natDistanceSqKernel_nonneg (a b : ℕ) :
    0 ≤ natDistanceSqKernel a b := by
  unfold natDistanceSqKernel
  split_ifs <;> positivity

lemma natDistanceSqKernel_symm (a b : ℕ) :
    natDistanceSqKernel a b = natDistanceSqKernel b a := by
  unfold natDistanceSqKernel
  rw [Nat.dist_comm]
  by_cases h : a = b
  · subst b
    simp
  · simp [h, Ne.symm h]

lemma sum_range_natDistanceSqKernel_le_four
    (L a : ℕ) (ha : a < L) :
    (∑ b ∈ Finset.range L, natDistanceSqKernel a b) ≤ 4 := by
  have haL : a + 1 ≤ L := by omega
  have hLowEq :
      (∑ b ∈ Finset.range a, natDistanceSqKernel a b) =
        ∑ k ∈ Finset.range a, 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      (∑ b ∈ Finset.range a, natDistanceSqKernel a b) =
          ∑ b ∈ Finset.range a,
            1 / ((((a - 1 - b) + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hba : b < a := Finset.mem_range.mp hb
        have hdist : Nat.dist a b = a - b := by
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt hba)]
        unfold natDistanceSqKernel
        rw [if_neg (by omega : a ≠ b), hdist]
        congr 3
        omega
      _ = ∑ k ∈ Finset.range a, 1 / (((k + 1 : ℕ) : ℝ) ^ 2) :=
        Finset.sum_range_reflect
          (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) a
  have hHighEq :
      (∑ k ∈ Finset.range (L - (a + 1)),
          natDistanceSqKernel a (a + 1 + k)) =
        ∑ k ∈ Finset.range (L - (a + 1)),
          1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : a ≠ a + 1 + k := by omega
    have hdist : Nat.dist a (a + 1 + k) = k + 1 := by
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    simp [natDistanceSqKernel, hne, hdist]
  rw [← Nat.add_sub_of_le haL, Finset.sum_range_add]
  rw [Finset.sum_range_succ]
  rw [show natDistanceSqKernel a a = 0 by simp [natDistanceSqKernel]]
  simp only [add_zero]
  rw [hLowEq, hHighEq]
  have h := add_le_add (sum_range_one_div_succ_sq_le_two a)
    (sum_range_one_div_succ_sq_le_two (L - (a + 1)))
  norm_num at h ⊢
  exact h

lemma add_reciprocal_div_sq_le
    (a b t : ℝ) (ht : 0 < t) :
    ((a + b) / (12 * t)) ^ 2 ≤
      (1 / 72 : ℝ) * (a ^ 2 + b ^ 2) * (1 / t ^ 2) := by
  field_simp [ne_of_gt ht]
  nlinarith [sq_nonneg (a - b)]

noncomputable def c13CoreArchimedeanSameSignMatrix
    (M L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  fun i j =>
    if i = j then 0 else
      logarithmicCvSArchimedeanEntry 13
        ((M + (i : ℕ) + 1 : ℕ) : ℤ)
        ((M + (j : ℕ) + 1 : ℕ) : ℤ)

lemma c13CoreArchimedeanSameSignMatrix_sq_le
    (M L : ℕ) (hM : 960 ≤ M) (i j : Fin L) :
    (c13CoreArchimedeanSameSignMatrix M L i j) ^ 2 ≤
      (1 / 72 : ℝ) *
        ((1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)) ^ 2 +
          (1 / ((M + (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2) *
        natDistanceSqKernel (i : ℕ) (j : ℕ) := by
  by_cases hij : i = j
  · subst j
    simp [c13CoreArchimedeanSameSignMatrix, natDistanceSqKernel]
  · have hnatne : (i : ℕ) ≠ (j : ℕ) := by
      intro h
      exact hij (Fin.ext h)
    let p : ℕ := M + (i : ℕ) + 1
    let q : ℕ := M + (j : ℕ) + 1
    have hp : 960 ≤ p := by simp [p]; omega
    have hq : 960 ≤ q := by simp [q]; omega
    have hdistNat : 0 < Nat.dist (i : ℕ) (j : ℕ) := by
      by_cases hle : (i : ℕ) ≤ (j : ℕ)
      · rw [Nat.dist_eq_sub_of_le hle]
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_not_ge hle)]
        omega
    have hdistPos : (0 : ℝ) < Nat.dist (i : ℕ) (j : ℕ) := by exact_mod_cast hdistNat
    have hTargetScalar := add_reciprocal_div_sq_le
      (1 / (p : ℝ)) (1 / (q : ℝ)) (Nat.dist (i : ℕ) (j : ℕ) : ℝ) hdistPos
    by_cases hijlt : (i : ℕ) < (j : ℕ)
    · have hpq : p < q := by simp [p, q]; omega
      have hAbs := c13_archimedean_sameSign_nat_abs_le p q hp hpq
      have hdist : Nat.dist (i : ℕ) (j : ℕ) = (j : ℕ) - (i : ℕ) :=
        Nat.dist_eq_sub_of_le (Nat.le_of_lt hijlt)
      have hpqsub : q - p = (j : ℕ) - (i : ℕ) := by simp [p, q]; omega
      have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
      have hdiffR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by linarith
      have hBoundNonneg : 0 ≤
          (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
            (3 * ((q : ℝ) - (p : ℝ))) := by positivity
      have hSq := (sq_le_sq₀ (abs_nonneg
        (logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)))
          hBoundNonneg).2 hAbs
      unfold c13CoreArchimedeanSameSignMatrix
      rw [if_neg hij]
      change (logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)) ^ 2 ≤ _
      have hRewrite :
          (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
              (3 * ((q : ℝ) - (p : ℝ))) =
            (1 / (p : ℝ) + 1 / (q : ℝ)) /
              (12 * (Nat.dist (i : ℕ) (j : ℕ) : ℝ)) := by
        rw [hdist]
        have hcast : ((q : ℝ) - (p : ℝ)) =
            (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
          rw [← hpqsub]
          exact (Nat.cast_sub (R := ℝ) (Nat.le_of_lt hpq)).symm
        rw [hcast]
        ring
      rw [sq_abs] at hSq
      rw [hRewrite] at hSq
      have hTarget :
          ((1 / (p : ℝ) + 1 / (q : ℝ)) /
              (12 * (Nat.dist (i : ℕ) (j : ℕ) : ℝ))) ^ 2 ≤
            (1 / 72 : ℝ) *
              ((1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)) ^ 2 +
                (1 / ((M + (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2) *
              natDistanceSqKernel (i : ℕ) (j : ℕ) := by
        simpa only [p, q, natDistanceSqKernel, if_neg hnatne] using hTargetScalar
      exact hSq.trans hTarget
    · have hjilt : (j : ℕ) < (i : ℕ) := by omega
      have hqp : q < p := by simp [p, q]; omega
      have hAbs := c13_archimedean_sameSign_nat_abs_le q p hq hqp
      have hdist : Nat.dist (i : ℕ) (j : ℕ) = (i : ℕ) - (j : ℕ) := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le (Nat.le_of_lt hjilt)
      have hqpsub : p - q = (i : ℕ) - (j : ℕ) := by simp [p, q]; omega
      have hqpR : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
      have hdiffR : (0 : ℝ) < (p : ℝ) - (q : ℝ) := by linarith
      have hBoundNonneg : 0 ≤
          (1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ))) /
            (3 * ((p : ℝ) - (q : ℝ))) := by positivity
      have hSq := (sq_le_sq₀ (abs_nonneg
        (logarithmicCvSArchimedeanEntry 13 (q : ℤ) (p : ℤ)))
          hBoundNonneg).2 hAbs
      unfold c13CoreArchimedeanSameSignMatrix
      rw [if_neg hij]
      rw [logarithmicCvSArchimedeanEntry_symm]
      change (logarithmicCvSArchimedeanEntry 13 (q : ℤ) (p : ℤ)) ^ 2 ≤ _
      have hRewrite :
          (1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ))) /
              (3 * ((p : ℝ) - (q : ℝ))) =
            (1 / (q : ℝ) + 1 / (p : ℝ)) /
              (12 * (Nat.dist (i : ℕ) (j : ℕ) : ℝ)) := by
        rw [hdist]
        have hcast : ((p : ℝ) - (q : ℝ)) =
            (((i : ℕ) - (j : ℕ) : ℕ) : ℝ) := by
          rw [← hqpsub]
          exact (Nat.cast_sub (R := ℝ) (Nat.le_of_lt hqp)).symm
        rw [hcast]
        ring
      rw [sq_abs] at hSq
      rw [hRewrite] at hSq
      have hTargetSwap := add_reciprocal_div_sq_le
        (1 / (q : ℝ)) (1 / (p : ℝ))
        (Nat.dist (i : ℕ) (j : ℕ) : ℝ) hdistPos
      have hTarget :
          ((1 / (q : ℝ) + 1 / (p : ℝ)) /
              (12 * (Nat.dist (i : ℕ) (j : ℕ) : ℝ))) ^ 2 ≤
            (1 / 72 : ℝ) *
              ((1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)) ^ 2 +
                (1 / ((M + (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2) *
              natDistanceSqKernel (i : ℕ) (j : ℕ) := by
        simpa only [p, q, natDistanceSqKernel, if_neg hnatne, add_comm] using hTargetSwap
      exact hSq.trans hTarget

theorem c13CoreArchimedeanSameSign_entry_sq_sum_le_oneOverNineM
    (M L : ℕ) (hM : 960 ≤ M) :
    (∑ i : Fin L, ∑ j : Fin L,
        (c13CoreArchimedeanSameSignMatrix M L i j) ^ 2) ≤
      1 / (9 * (M : ℝ)) := by
  let u : Fin L → ℝ := fun i =>
    1 / ((M + (i : ℕ) + 1 : ℕ) : ℝ)
  let D : Fin L → Fin L → ℝ := fun i j =>
    natDistanceSqKernel (i : ℕ) (j : ℕ)
  have hDnonneg : ∀ i j, 0 ≤ D i j := by
    intro i j
    exact natDistanceSqKernel_nonneg _ _
  have hDsymm : ∀ i j, D i j = D j i := by
    intro i j
    exact natDistanceSqKernel_symm _ _
  have hDrow : ∀ i : Fin L, (∑ j : Fin L, D i j) ≤ 4 := by
    intro i
    change (∑ j : Fin L,
      (fun b : ℕ => natDistanceSqKernel (i : ℕ) b) j) ≤ 4
    rw [Fin.sum_univ_eq_sum_range
      (fun b : ℕ => natDistanceSqKernel (i : ℕ) b) L]
    exact sum_range_natDistanceSqKernel_le_four L (i : ℕ) i.isLt
  let S₁ : ℝ := ∑ i : Fin L, ∑ j : Fin L, u i ^ 2 * D i j
  let S₂ : ℝ := ∑ i : Fin L, ∑ j : Fin L, u j ^ 2 * D i j
  have hS₁ : S₁ ≤ 4 * ∑ i : Fin L, u i ^ 2 := by
    dsimp only [S₁]
    calc
      (∑ i : Fin L, ∑ j : Fin L, u i ^ 2 * D i j) =
          ∑ i : Fin L, u i ^ 2 * ∑ j : Fin L, D i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin L, u i ^ 2 * 4 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hDrow i) (sq_nonneg (u i))
      _ = 4 * ∑ i : Fin L, u i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hS₂ : S₂ ≤ 4 * ∑ i : Fin L, u i ^ 2 := by
    dsimp only [S₂]
    rw [Finset.sum_comm]
    calc
      (∑ j : Fin L, ∑ i : Fin L, u j ^ 2 * D i j) =
          ∑ j : Fin L, u j ^ 2 * ∑ i : Fin L, D j i := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hDsymm i j]
      _ ≤ ∑ j : Fin L, u j ^ 2 * 4 := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hDrow j) (sq_nonneg (u j))
      _ = 4 * ∑ j : Fin L, u j ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hEntrySum :
      (∑ i : Fin L, ∑ j : Fin L,
          (c13CoreArchimedeanSameSignMatrix M L i j) ^ 2) ≤
        (1 / 72 : ℝ) * (S₁ + S₂) := by
    calc
      (∑ i : Fin L, ∑ j : Fin L,
          (c13CoreArchimedeanSameSignMatrix M L i j) ^ 2) ≤
          ∑ i : Fin L, ∑ j : Fin L,
            (1 / 72 : ℝ) * (u i ^ 2 + u j ^ 2) * D i j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        simpa only [u, D] using c13CoreArchimedeanSameSignMatrix_sq_le M L hM i j
      _ = (1 / 72 : ℝ) * (S₁ + S₂) := by
        have hExpand :
            (∑ i : Fin L, ∑ j : Fin L,
              (1 / 72 : ℝ) * (u i ^ 2 + u j ^ 2) * D i j) =
              (1 / 72 : ℝ) * S₁ + (1 / 72 : ℝ) * S₂ := by
          dsimp only [S₁, S₂]
          simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
          ring_nf
        rw [hExpand]
        ring_nf
  have hUSum : (∑ i : Fin L, u i ^ 2) ≤ 1 / (M : ℝ) := by
    simpa only [u] using fin_sum_shifted_inv_sq_le_inv M L (by omega)
  calc
    (∑ i : Fin L, ∑ j : Fin L,
        (c13CoreArchimedeanSameSignMatrix M L i j) ^ 2) ≤
        (1 / 72 : ℝ) * (S₁ + S₂) := hEntrySum
    _ ≤ (1 / 72 : ℝ) *
        (4 * (∑ i : Fin L, u i ^ 2) + 4 * (∑ i : Fin L, u i ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hS₁ hS₂) (by norm_num)
    _ = (1 / 9 : ℝ) * (∑ i : Fin L, u i ^ 2) := by ring
    _ ≤ (1 / 9 : ℝ) * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hUSum (by norm_num)
    _ = 1 / (9 * (M : ℝ)) := by ring

/-- Hilbert--Schmidt control of a finite quadratic form, stated in the exact
coordinate conventions used by the CvS matrices. -/
theorem finiteMatrixQuadraticEnergy_sq_le_entrySqSum_mul_normSq_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    (finiteMatrixQuadraticEnergy A x) ^ 2 ≤
      (∑ i : ι, ∑ j : ι, (A i j) ^ 2) *
        (finiteVectorEuclideanNormSq x) ^ 2 := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset ι) (Finset.univ : Finset ι) A x x
  have hEnergy :
      (∑ ij ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι),
          A ij.1 ij.2 * (x ij.1 * x ij.2)) =
        finiteMatrixQuadraticEnergy A x := by
    rw [← finiteRectangularBilinearEnergy_eq_product_sum A x x]
    rfl
  rw [hEnergy] at hCauchy
  rw [Finset.sum_product] at hCauchy
  simpa [finiteVectorEuclideanNormSq, pow_two] using hCauchy

theorem c13CoreArchimedeanSameSign_energy_abs_le_oneEighth
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreArchimedeanSameSignMatrix M L) x| ≤
      (1 / 8 : ℝ) * finiteVectorEuclideanNormSq x := by
  have hSqBase := finiteMatrixQuadraticEnergy_sq_le_entrySqSum_mul_normSq_sq
    (c13CoreArchimedeanSameSignMatrix M L) x
  have hEntries :=
    c13CoreArchimedeanSameSign_entry_sq_sum_le_oneOverNineM M L hM
  have hNormSq : 0 ≤ (finiteVectorEuclideanNormSq x) ^ 2 := sq_nonneg _
  have hSq :
      (finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x) ^ 2 ≤
        (1 / (9 * (M : ℝ))) *
          (finiteVectorEuclideanNormSq x) ^ 2 :=
    hSqBase.trans (mul_le_mul_of_nonneg_right hEntries hNormSq)
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hCoeff : 1 / (9 * (M : ℝ)) ≤ (1 / 8 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * (M : ℝ))]
    have hMR : (960 : ℝ) ≤ M := by exact_mod_cast hM
    norm_num
    linarith
  have hSqTarget :
      (finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x) ^ 2 ≤
        ((1 / 8 : ℝ) * finiteVectorEuclideanNormSq x) ^ 2 := by
    calc
      _ ≤ (1 / (9 * (M : ℝ))) *
          (finiteVectorEuclideanNormSq x) ^ 2 := hSq
      _ ≤ (1 / 8 : ℝ) ^ 2 *
          (finiteVectorEuclideanNormSq x) ^ 2 :=
        mul_le_mul_of_nonneg_right hCoeff hNormSq
      _ = ((1 / 8 : ℝ) * finiteVectorEuclideanNormSq x) ^ 2 := by ring
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x))).1
  simpa only [sq_abs] using hSqTarget

lemma c13EvenCoreArchimedeanCenteredResidualMatrix_entry_eq
    (M L : ℕ) (i j : Fin L) :
    c13EvenCoreArchimedeanCenteredResidualMatrix M L i j =
      -c13CoreArchimedeanSameSignMatrix M L i j +
        c13CoreArchimedeanReflectedCenteredMatrix M L i j := by
  have href := logarithmicCvSArchimedeanEntry_reflected_eq 13
    (finGlobalShellPositiveMode M L i)
    (finGlobalShellPositiveMode M L j)
    (finGlobalShellPositiveMode_pos M L i)
    (finGlobalShellPositiveMode_pos M L j)
  simp only [c13EvenCoreArchimedeanCenteredResidualMatrix,
    Matrix.sub_apply]
  simp only [logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
    c13CoreReflectedHilbertLeadingMatrix, c13CoreHilbertKernel,
    c13CoreArchimedeanSameSignMatrix,
    c13CoreArchimedeanReflectedCenteredMatrix,
    Matrix.smul_apply, smul_eq_mul]
  rw [href]
  simp only [finGlobalShellPositiveMode, Int.cast_natCast]
  have hsum : (0 : ℝ) <
      ((1 + M + (i : ℕ) : ℕ) : ℝ) +
        ((1 + M + (j : ℕ) : ℕ) : ℝ) := by positivity
  field_simp [ne_of_gt hsum, Real.pi_ne_zero]; ring_nf

lemma c13OddCoreArchimedeanCenteredResidualMatrix_entry_eq
    (M L : ℕ) (i j : Fin L) :
    c13OddCoreArchimedeanCenteredResidualMatrix M L i j =
      -c13CoreArchimedeanSameSignMatrix M L i j -
        c13CoreArchimedeanReflectedCenteredMatrix M L i j := by
  have href := logarithmicCvSArchimedeanEntry_reflected_eq 13
    (finGlobalShellPositiveMode M L i)
    (finGlobalShellPositiveMode M L j)
    (finGlobalShellPositiveMode_pos M L i)
    (finGlobalShellPositiveMode_pos M L j)
  simp only [c13OddCoreArchimedeanCenteredResidualMatrix,
    Matrix.sub_apply]
  simp only [logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
    c13OddCoreReflectedHilbertLeadingMatrix,
    c13CoreReflectedHilbertLeadingMatrix, c13CoreHilbertKernel,
    c13CoreArchimedeanSameSignMatrix,
    c13CoreArchimedeanReflectedCenteredMatrix,
    Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  rw [href]
  simp only [finGlobalShellPositiveMode, Int.cast_natCast]
  have hsum : (0 : ℝ) <
      ((1 + M + (i : ℕ) : ℕ) : ℝ) +
        ((1 + M + (j : ℕ) : ℕ) : ℝ) := by positivity
  field_simp [ne_of_gt hsum, Real.pi_ne_zero]; ring_nf

lemma c13EvenCoreArchimedeanCenteredResidualMatrix_eq
    (M L : ℕ) :
    c13EvenCoreArchimedeanCenteredResidualMatrix M L =
      -c13CoreArchimedeanSameSignMatrix M L +
        c13CoreArchimedeanReflectedCenteredMatrix M L := by
  ext i j
  exact c13EvenCoreArchimedeanCenteredResidualMatrix_entry_eq M L i j

lemma c13OddCoreArchimedeanCenteredResidualMatrix_eq
    (M L : ℕ) :
    c13OddCoreArchimedeanCenteredResidualMatrix M L =
      -c13CoreArchimedeanSameSignMatrix M L -
        c13CoreArchimedeanReflectedCenteredMatrix M L := by
  ext i j
  exact c13OddCoreArchimedeanCenteredResidualMatrix_entry_eq M L i j

lemma finiteMatrixQuadraticEnergy_neg
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteMatrixQuadraticEnergy (-A) x =
      -finiteMatrixQuadraticEnergy A x := by
  unfold finiteMatrixQuadraticEnergy
  simp only [Matrix.neg_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib]

/-- The part left after removing the half-Hilbert reflected kernel is smaller
than `1/4` uniformly in the length of the historical core. -/
theorem c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
      (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanCenteredResidualMatrix_eq,
    finiteMatrixQuadraticEnergy_add, finiteMatrixQuadraticEnergy_neg]
  calc
    |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| ≤
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| :=
      abs_add_le _ _
    _ = |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| := by
      rw [abs_neg]
    _ ≤ (1 / 8 : ℝ) * finiteVectorEuclideanNormSq x +
        (1 / 11520 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreArchimedeanSameSign_energy_abs_le_oneEighth M L hM x)
        (c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520
          M L hM x)
    _ ≤ (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
      nlinarith [finiteVectorEuclideanNormSq_nonneg x]

theorem c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
      (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanCenteredResidualMatrix_eq, sub_eq_add_neg,
    finiteMatrixQuadraticEnergy_add, finiteMatrixQuadraticEnergy_neg,
    finiteMatrixQuadraticEnergy_neg]
  calc
    |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x +
        -finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| ≤
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| :=
      abs_add_le _ _
    _ = |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| := by
      rw [abs_neg, abs_neg]
    _ ≤ (1 / 8 : ℝ) * finiteVectorEuclideanNormSq x +
        (1 / 11520 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreArchimedeanSameSign_energy_abs_le_oneEighth M L hM x)
        (c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520
          M L hM x)
    _ ≤ (1 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
      nlinarith [finiteVectorEuclideanNormSq_nonneg x]

theorem c13EvenCoreArchimedeanRemainder_energy_abs_le_nineFourths
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact c13EvenCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
    M L x
    (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter M L hM x)

theorem c13OddCoreArchimedeanRemainder_energy_abs_le_nineFourths
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (9 / 4 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact c13OddCoreArchimedeanRemainder_energy_abs_le_nineFourths_of_centered
    M L x
    (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter M L hM x)

/-- Uniform coercivity of every consecutive historical core beginning above
cutoff `960`; unlike the shell-local reserve, this has no upper bound on `L`. -/
theorem c13_logarithmicCvSBuilderEvenCore_energy_ge_oneTwentieth
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  exact c13_logarithmicCvSBuilderEvenCore_energy_ge_oneTwentieth_of_centered
    M L hM x
    (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter M L hM x)

theorem c13_logarithmicCvSBuilderOddCore_energy_ge_oneTwentieth
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  exact c13_logarithmicCvSBuilderOddCore_energy_ge_oneTwentieth_of_centered
    M L hM x
    (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter M L hM x)

theorem c13EvenBuilderCoreNewestBaseEnergy_ge_oneTwentieth
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  exact c13EvenBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    M N hM x
    (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      M (N - M) hM x)

theorem c13OddBuilderCoreNewestBaseEnergy_ge_oneTwentieth
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (1 / 20 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  exact c13OddBuilderCoreNewestBaseEnergy_ge_oneTwentieth_of_centered
    M N hM x
    (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      M (N - M) hM x)

theorem c13EvenBuilderCoreNewest_relative_oneTwentieth
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1 / 20 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  exact c13EvenBuilderCoreNewest_relative_of_centeredResidual
    M N hM hMN x y q hq
    (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      M (N - M) hM x)
    hBudget

theorem c13OddBuilderCoreNewest_relative_oneTwentieth
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1 / 20 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  exact c13OddBuilderCoreNewest_relative_of_centeredResidual
    M N hM hMN x y q hq
    (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      M (N - M) hM x)
    hBudget

/-- Unconditional full historical-core/newest-shell relative bound on the
explicit dyadic tail.  This is the actual matrix block, not a surrogate. -/
theorem c13EvenBuilderDyadicCoreNewest_relative_fourNinth
    (n : ℕ) (hn : 1150 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  exact c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_centeredResidual
    n hn x y
    (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      960 (c13DyadicShellBase n - 960) (by norm_num) x)

theorem c13OddBuilderDyadicCoreNewest_relative_fourNinth
    (n : ℕ) (hn : 1150 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  exact c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_centeredResidual
    n hn x y
    (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_quarter
      960 (c13DyadicShellBase n - 960) (by norm_num) x)

/-!
## Sharpened rational budget

The Hilbert--Schmidt square estimate contains substantially more information
than the coarse `1 / 8` adapter above.  At `M >= 960`, its square root is below
`1 / 90`.  Keeping this sharper rational constant improves the global core
floor and lowers the explicit dyadic no-crossing threshold.
-/

theorem c13CoreArchimedeanSameSign_energy_abs_le_oneNinetieth
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreArchimedeanSameSignMatrix M L) x| ≤
      (1 / 90 : ℝ) * finiteVectorEuclideanNormSq x := by
  have hSqBase := finiteMatrixQuadraticEnergy_sq_le_entrySqSum_mul_normSq_sq
    (c13CoreArchimedeanSameSignMatrix M L) x
  have hEntries :=
    c13CoreArchimedeanSameSign_entry_sq_sum_le_oneOverNineM M L hM
  have hNormSq : 0 ≤ (finiteVectorEuclideanNormSq x) ^ 2 := sq_nonneg _
  have hSq :
      (finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x) ^ 2 ≤
        (1 / (9 * (M : ℝ))) *
          (finiteVectorEuclideanNormSq x) ^ 2 :=
    hSqBase.trans (mul_le_mul_of_nonneg_right hEntries hNormSq)
  have hCoeff : 1 / (9 * (M : ℝ)) ≤ (1 / 90 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * (M : ℝ))]
    have hMR : (960 : ℝ) ≤ M := by exact_mod_cast hM
    norm_num
    linarith
  have hSqTarget :
      (finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x) ^ 2 ≤
        ((1 / 90 : ℝ) * finiteVectorEuclideanNormSq x) ^ 2 := by
    calc
      _ ≤ (1 / (9 * (M : ℝ))) *
          (finiteVectorEuclideanNormSq x) ^ 2 := hSq
      _ ≤ (1 / 90 : ℝ) ^ 2 *
          (finiteVectorEuclideanNormSq x) ^ 2 :=
        mul_le_mul_of_nonneg_right hCoeff hNormSq
      _ = ((1 / 90 : ℝ) * finiteVectorEuclideanNormSq x) ^ 2 := by ring
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x))).1
  simpa only [sq_abs] using hSqTarget

theorem c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
      (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanCenteredResidualMatrix_eq,
    finiteMatrixQuadraticEnergy_add, finiteMatrixQuadraticEnergy_neg]
  calc
    |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| ≤
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| :=
      abs_add_le _ _
    _ = |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| := by
      rw [abs_neg]
    _ ≤ (1 / 90 : ℝ) * finiteVectorEuclideanNormSq x +
        (1 / 11520 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreArchimedeanSameSign_energy_abs_le_oneNinetieth M L hM x)
        (c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520
          M L hM x)
    _ = (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13OddCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
      (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanCenteredResidualMatrix_eq, sub_eq_add_neg,
    finiteMatrixQuadraticEnergy_add, finiteMatrixQuadraticEnergy_neg,
    finiteMatrixQuadraticEnergy_neg]
  calc
    |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x +
        -finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| ≤
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |-finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| :=
      abs_add_le _ _
    _ = |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanSameSignMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13CoreArchimedeanReflectedCenteredMatrix M L) x| := by
      rw [abs_neg, abs_neg]
    _ ≤ (1 / 90 : ℝ) * finiteVectorEuclideanNormSq x +
        (1 / 11520 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreArchimedeanSameSign_energy_abs_le_oneNinetieth M L hM x)
        (c13CoreArchimedeanReflectedCentered_energy_abs_le_oneOver11520
          M L hM x)
    _ = (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13EvenCoreArchimedeanRemainder_energy_abs_le_7723Over3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (7723 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ 2 * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreReflectedHilbertLeading_energy_abs_le_two M L x)
        (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M L hM x)
    _ = (7723 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13OddCoreArchimedeanRemainder_energy_abs_le_7723Over3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (7723 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ 2 * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13OddCoreReflectedHilbertLeading_energy_abs_le_two M L x)
        (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M L hM x)
    _ = (7723 / 3840 : ℝ) * finiteVectorEuclideanNormSq x := by ring

lemma c13_globalCore_scalar_reserve_ge_1109Over3840
    (M : ℕ) (hM : 960 ≤ M) :
    (1109 / 3840 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) +
        7723 / 3840 + 10 / 3) := by
  nlinarith [c13_shell_complete_scalar_reserve_ge_nineFifths M hM]

theorem c13_logarithmicCvSBuilderEvenCore_energy_ge_1109Over3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (1109 / 3840 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch := c13EvenCoreArchimedeanRemainder_energy_abs_le_7723Over3840
    M L hM x
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (1109 / 3840) (7723 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_1109Over3840 M hM)
  simpa using h

theorem c13_logarithmicCvSBuilderOddCore_energy_ge_1109Over3840
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (1109 / 3840 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch := c13OddCoreArchimedeanRemainder_energy_abs_le_7723Over3840
    M L hM x
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0 (1109 / 3840) (7723 / 3840)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_1109Over3840 M hM)
  simpa using h

theorem c13EvenBuilderCoreNewestBaseEnergy_ge_1109Over3840
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (1109 / 3840 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderEvenCore_energy_ge_1109Over3840
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13OddBuilderCoreNewestBaseEnergy_ge_1109Over3840
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (1109 / 3840 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderOddCore_energy_ge_1109Over3840
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13EvenBuilderCoreNewest_relative_1109Over3840
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1109 / 3840 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  exact c13EvenBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (1109 / 3840) q (by norm_num) hq
    (c13EvenBuilderCoreNewestBaseEnergy_ge_1109Over3840 M N hM x)
    hBudget

theorem c13OddBuilderCoreNewest_relative_1109Over3840
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (1109 / 3840 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  exact c13OddBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (1109 / 3840) q (by norm_num) hq
    (c13OddBuilderCoreNewestBaseEnergy_ge_1109Over3840 M N hM x)
    hBudget

theorem c13CoreNewestRelativeEnvelope_1109Over3840_lt_fourNinth
    (n : ℕ) (hn : 190 ≤ n) :
    c13CoreNewestRelativeEnvelope (1109 / 3840) n < (4 / 9 : ℝ) := by
  have hnR : (190 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < c13DyadicGapLower n := c13DyadicGapLower_pos n
  unfold c13CoreNewestRelativeEnvelope
  apply (div_lt_iff₀ (mul_pos (by norm_num) hgap)).2
  have hscaled : (190 : ℝ) * (69 / 100 : ℝ) ≤
      (n : ℝ) * (69 / 100 : ℝ) :=
    mul_le_mul_of_nonneg_right hnR (by norm_num)
  unfold c13DyadicGapLower
  norm_num at hscaled ⊢
  nlinarith

/-- The cutoff `190` is the first integer certified by this exact rational
envelope: at `189` the same bound still lies at or above `4 / 9`. -/
theorem c13CoreNewestRelativeEnvelope_1109Over3840_ge_fourNinth_at_189 :
    (4 / 9 : ℝ) ≤
      c13CoreNewestRelativeEnvelope (1109 / 3840) 189 := by
  unfold c13CoreNewestRelativeEnvelope c13DyadicGapLower
  norm_num

theorem c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_ge_190
    (n : ℕ) (hn : 190 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13EvenBuilderCoreNewestBaseEnergy_ge_1109Over3840
    960 (c13DyadicShellBase n) (by norm_num) x
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13EvenBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (1109 / 3840) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt
          (c13CoreNewestRelativeEnvelope_1109Over3840_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

theorem c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_ge_190
    (n : ℕ) (hn : 190 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13OddBuilderCoreNewestBaseEnergy_ge_1109Over3840
    960 (c13DyadicShellBase n) (by norm_num) x
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13OddBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (1109 / 3840) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt
          (c13CoreNewestRelativeEnvelope_1109Over3840_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

end RiemannCvs.V23BoundaryWeylMainline
