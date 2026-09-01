import Mathlib

namespace RiemannCvs.WeightedSchurSupersolution

open scoped BigOperators

lemma weightedTwoMul_le (a b hi hj : ℝ) (hhi : 0 < hi) (hhj : 0 < hj) :
    2 * a * b ≤ (hj / hi) * a ^ 2 + (hi / hj) * b ^ 2 := by
  have hsq := sq_nonneg (hj * a - hi * b)
  field_simp [ne_of_gt hhi, ne_of_gt hhj]
  nlinarith

variable {ι : Type*} [Fintype ι]

noncomputable def weightedSchurEnergy (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

noncomputable def weightedSchurNormSq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

lemma firstWeightedSum
    (A : Matrix ι ι ℝ) (x h : ι → ℝ) :
    (∑ i, ∑ j, A i j * ((h j / h i) * x i ^ 2)) =
      ∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma secondWeightedSum
    (A : Matrix ι ι ℝ) (x h : ι → ℝ)
    (hSymm : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, A i j * ((h i / h j) * x j ^ 2)) =
      ∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hSymm i j]
  ring

lemma weightedRhs_eq_two
    (A : Matrix ι ι ℝ) (x h : ι → ℝ)
    (hSymm : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, A i j *
      ((h j / h i) * x i ^ 2 + (h i / h j) * x j ^ 2)) =
      2 * ∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [firstWeightedSum A x h, secondWeightedSum A x h hSymm]
  ring

lemma absEnergy_le_absKernel
    (A : Matrix ι ι ℝ) (x : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    |weightedSchurEnergy A x| ≤ ∑ i, ∑ j, A i j * |x i| * |x j| := by
  unfold weightedSchurEnergy
  calc
    |∑ i, ∑ j, A i j * x i * x j|
        ≤ ∑ i, |∑ j, A i j * x i * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * x i * x j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, A i j * |x i| * |x j| := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_mul, abs_of_nonneg (hA i j)]

lemma weightedKernelSum_le
    (A : Matrix ι ι ℝ) (x h : ι → ℝ) (B : ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hSymm : ∀ i j, A i j = A j i)
    (hH : ∀ i, 0 < h i)
    (hRow : ∀ i, ∑ j, A i j * h j ≤ B * h i) :
    ∑ i, ∑ j, A i j * |x i| * |x j| ≤ B * weightedSchurNormSq x := by
  let S : ℝ := ∑ i, ∑ j, A i j * |x i| * |x j|
  let P : ℝ := ∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j)
  have hPair : ∀ i j,
      2 * (A i j * |x i| * |x j|) ≤
        A i j * ((h j / h i) * x i ^ 2 + (h i / h j) * x j ^ 2) := by
    intro i j
    have hamgm := weightedTwoMul_le |x i| |x j| (h i) (h j) (hH i) (hH j)
    have hmul := mul_le_mul_of_nonneg_left hamgm (hA i j)
    calc
      2 * (A i j * |x i| * |x j|) =
          A i j * (2 * (|x i| * |x j|)) := by ring
      _ ≤ A i j * ((h j / h i) * x i ^ 2 + (h i / h j) * x j ^ 2) := by
        simp only [sq_abs] at hmul
        nlinarith [hmul]
  have hSum : 2 * S ≤ 2 * P := by
    dsimp [S, P]
    calc
      2 * (∑ i, ∑ j, A i j * |x i| * |x j|) =
          ∑ i, ∑ j, 2 * (A i j * |x i| * |x j|) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j,
          A i j * ((h j / h i) * x i ^ 2 + (h i / h j) * x j ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hPair i j
      _ = 2 * ∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j) :=
        weightedRhs_eq_two A x h hSymm
  have hP : P ≤ B * weightedSchurNormSq x := by
    dsimp [P, weightedSchurNormSq]
    calc
      (∑ i, (x i ^ 2 / h i) * (∑ j, A i j * h j))
          ≤ ∑ i, (x i ^ 2 / h i) * (B * h i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hRow i) (by positivity [hH i])
      _ = B * ∑ i, x i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [ne_of_gt (hH i)]
  nlinarith [hSum, hP]

/-- Finite weighted Schur test for a nonnegative symmetric real kernel. -/
theorem weightedSchur_quadratic
    (A : Matrix ι ι ℝ) (x h : ι → ℝ) (B : ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hSymm : ∀ i j, A i j = A j i)
    (hH : ∀ i, 0 < h i)
    (hRow : ∀ i, ∑ j, A i j * h j ≤ B * h i) :
    |weightedSchurEnergy A x| ≤ B * weightedSchurNormSq x := by
  exact (absEnergy_le_absKernel A x hA).trans
    (weightedKernelSum_le A x h B hA hSymm hH hRow)

end RiemannCvs.WeightedSchurSupersolution
