import RiemannCvs.PrimeTranslationFourierBridge
import RiemannCvs.PrimeTranslationContinuousSchur

/-!
# Continuous Fourier closure of the cutoff-13 prime form

This module identifies the finite prime-translation matrix quadratic form with
the physical-space cosine/sine correlation, proves the corresponding finite
Parseval identity, and discharges every interval-integrability obligation for
continuous Fourier polynomials.  The cutoff-13 positive supersolution then
gives the signed-space `10 / 3` bound for any finite injective positive mode
family, which is the exact input required by the even/odd parity compression.
-/

open scoped BigOperators Real Interval

noncomputable section

namespace RiemannCvs.PrimeTranslationContinuousFourier

open RiemannCvs.PrimeTranslationFourierBridge
open RiemannCvs.PrimeTranslationContinuousSchur
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.PrimeTranslationSupersolution

variable {κ : Type*} [Fintype κ]

noncomputable def finiteCosineModeSum
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, v i * Real.cos (2 * Real.pi * (mode i : ℝ) * x / L)

noncomputable def finiteSineModeSum
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, v i * Real.sin (2 * Real.pi * (mode i : ℝ) * x / L)

lemma continuous_finiteCosineModeSum
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ) :
    Continuous (finiteCosineModeSum L mode v) := by
  unfold finiteCosineModeSum
  fun_prop

lemma continuous_finiteSineModeSum
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ) :
    Continuous (finiteSineModeSum L mode v) := by
  unfold finiteSineModeSum
  fun_prop

lemma cosineSine_shift_product_eq_doubleSum
    (L y : ℝ) (mode : κ → ℤ) (v : κ → ℝ) (x : ℝ) :
    finiteCosineModeSum L mode v x * finiteCosineModeSum L mode v (x + y) +
      finiteSineModeSum L mode v x * finiteSineModeSum L mode v (x + y) =
    ∑ i, ∑ j, v i * v j *
      Real.cos (2 * Real.pi *
        (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L) := by
  unfold finiteCosineModeSum finiteSineModeSum
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show
      v i * Real.cos (2 * Real.pi * (mode i : ℝ) * x / L) *
          (v j * Real.cos (2 * Real.pi * (mode j : ℝ) * (x + y) / L)) +
        v i * Real.sin (2 * Real.pi * (mode i : ℝ) * x / L) *
          (v j * Real.sin (2 * Real.pi * (mode j : ℝ) * (x + y) / L)) =
        v i * v j *
          (Real.cos (2 * Real.pi * (mode i : ℝ) * x / L) *
              Real.cos (2 * Real.pi * (mode j : ℝ) * (x + y) / L) +
            Real.sin (2 * Real.pi * (mode i : ℝ) * x / L) *
              Real.sin (2 * Real.pi * (mode j : ℝ) * (x + y) / L)) by ring]
  rw [← Real.cos_sub]
  rw [show
      2 * Real.pi * (mode i : ℝ) * x / L -
          2 * Real.pi * (mode j : ℝ) * (x + y) / L =
        -(2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L) by
    ring]
  rw [Real.cos_neg]

/-- The quadratic form of one truncated-translation Fourier matrix is the
normalized physical-space correlation of the cosine and sine mode sums. -/
theorem truncatedTranslation_energy_eq_integral
    (L y : ℝ) (mode : κ → ℤ) (v : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (fun i j => truncatedTranslationFourierEntry L y (mode i) (mode j)) v =
      (2 / L) * ∫ x in 0..(L - y),
        (finiteCosineModeSum L mode v x *
            finiteCosineModeSum L mode v (x + y) +
          finiteSineModeSum L mode v x *
            finiteSineModeSum L mode v (x + y)) := by
  have hInt : ∀ i j, IntervalIntegrable
      (fun x => v i * v j *
        Real.cos (2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L))
      MeasureTheory.volume 0 (L - y) := by
    intro i j
    have hc : Continuous (fun x => v i * v j *
        Real.cos (2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L)) := by
      fun_prop
    exact hc.intervalIntegrable 0 (L - y)
  unfold finiteMatrixQuadraticEnergy truncatedTranslationFourierEntry
  calc
    (∑ i, ∑ j,
      v i * ((2 / L) * ∫ x in 0..(L - y),
        Real.cos (2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L)) *
        v j) =
      (2 / L) * ∑ i, ∑ j, ∫ x in 0..(L - y),
        v i * v j * Real.cos (2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [intervalIntegral.integral_const_mul]
        ring
    _ = (2 / L) * ∫ x in 0..(L - y), ∑ i, ∑ j,
        v i * v j * Real.cos (2 * Real.pi *
          (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L) := by
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_finsetSum]
        exact fun j hj => hInt i j
      · intro i hi
        have hfun := Finset.sum_induction (s := Finset.univ)
          (fun j => fun x => v i * v j *
            Real.cos (2 * Real.pi *
              (((mode j : ℝ) - (mode i : ℝ)) * x + (mode j : ℝ) * y) / L))
          (fun F => IntervalIntegrable F MeasureTheory.volume 0 (L - y))
          (fun _ _ hF hG => hF.add hG) IntervalIntegrable.zero
          (fun j hj => hInt i j)
        apply hfun.congr
        intro x hx
        simp
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      exact (cosineSine_shift_product_eq_doubleSum L y mode v x).symm

theorem finitePrimeTranslationModeMatrix_energy_eq_sum
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (v : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix c location base mode) v =
      ∑ q, logarithmicPrimeWeight (location q) (base q) *
        finiteMatrixQuadraticEnergy
          (fun i j => truncatedTranslationFourierEntry
            (Real.log c) (Real.log (location q)) (mode i) (mode j)) v := by
  unfold finiteMatrixQuadraticEnergy finitePrimeTranslationModeMatrix
    finitePrimeTranslationFourierEntry
  calc
    (∑ i, ∑ j, v i *
        (∑ q, logarithmicPrimeWeight (location q) (base q) *
          truncatedTranslationFourierEntry
            (Real.log c) (Real.log (location q)) (mode i) (mode j)) * v j) =
      ∑ i, ∑ j, ∑ q,
        logarithmicPrimeWeight (location q) (base q) *
          (v i * truncatedTranslationFourierEntry
            (Real.log c) (Real.log (location q)) (mode i) (mode j) * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ i, ∑ q, ∑ j,
        logarithmicPrimeWeight (location q) (base q) *
          (v i * truncatedTranslationFourierEntry
            (Real.log c) (Real.log (location q)) (mode i) (mode j) * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ q, ∑ i, ∑ j,
        logarithmicPrimeWeight (location q) (base q) *
          (v i * truncatedTranslationFourierEntry
            (Real.log c) (Real.log (location q)) (mode i) (mode j) * v j) := by
      rw [Finset.sum_comm]
    _ = ∑ q, logarithmicPrimeWeight (location q) (base q) *
        (∑ i, ∑ j, v i * truncatedTranslationFourierEntry
          (Real.log c) (Real.log (location q)) (mode i) (mode j) * v j) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

noncomputable def finitePrimeLogShift
    {ι : Type*} (location : ι → ℝ) (i : ι) : ℝ :=
  Real.log (location i)

noncomputable def finitePrimeLogWeight
    {ι : Type*} (location base : ι → ℝ) (i : ι) : ℝ :=
  logarithmicPrimeWeight (location i) (base i)

/-- Exact physical-space realization of the full finite prime-translation
matrix energy. -/
theorem finitePrimeTranslationModeMatrix_energy_eq_integralEnergies
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (v : κ → ℝ) :
    finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix c location base mode) v =
      (finiteTranslationIntegralEnergy (Real.log c)
          (finitePrimeLogShift location)
          (finitePrimeLogWeight location base)
          (finiteCosineModeSum (Real.log c) mode v) +
        finiteTranslationIntegralEnergy (Real.log c)
          (finitePrimeLogShift location)
          (finitePrimeLogWeight location base)
          (finiteSineModeSum (Real.log c) mode v)) / Real.log c := by
  rw [finitePrimeTranslationModeMatrix_energy_eq_sum]
  have hCos : ∀ q, IntervalIntegrable
      (fun x => finiteCosineModeSum (Real.log c) mode v x *
        finiteCosineModeSum (Real.log c) mode v
          (x + Real.log (location q)))
      MeasureTheory.volume 0 (Real.log c - Real.log (location q)) := by
    intro q
    have hc0 := continuous_finiteCosineModeSum (Real.log c) mode v
    have hc : Continuous (fun x =>
        finiteCosineModeSum (Real.log c) mode v x *
          finiteCosineModeSum (Real.log c) mode v
            (x + Real.log (location q))) :=
      hc0.mul (hc0.comp (continuous_id.add continuous_const))
    exact hc.intervalIntegrable 0 _
  have hSin : ∀ q, IntervalIntegrable
      (fun x => finiteSineModeSum (Real.log c) mode v x *
        finiteSineModeSum (Real.log c) mode v
          (x + Real.log (location q)))
      MeasureTheory.volume 0 (Real.log c - Real.log (location q)) := by
    intro q
    have hs0 := continuous_finiteSineModeSum (Real.log c) mode v
    have hs : Continuous (fun x =>
        finiteSineModeSum (Real.log c) mode v x *
          finiteSineModeSum (Real.log c) mode v
            (x + Real.log (location q))) :=
      hs0.mul (hs0.comp (continuous_id.add continuous_const))
    exact hs.intervalIntegrable 0 _
  calc
    (∑ q, logarithmicPrimeWeight (location q) (base q) *
      finiteMatrixQuadraticEnergy
        (fun i j => truncatedTranslationFourierEntry
          (Real.log c) (Real.log (location q)) (mode i) (mode j)) v) =
      ∑ q, logarithmicPrimeWeight (location q) (base q) *
        ((2 / Real.log c) * ∫ x in 0..(Real.log c - Real.log (location q)),
          (finiteCosineModeSum (Real.log c) mode v x *
              finiteCosineModeSum (Real.log c) mode v
                (x + Real.log (location q)) +
            finiteSineModeSum (Real.log c) mode v x *
              finiteSineModeSum (Real.log c) mode v
                (x + Real.log (location q)))) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [truncatedTranslation_energy_eq_integral]
    _ = ∑ q, (1 / Real.log c) *
        (2 * logarithmicPrimeWeight (location q) (base q) *
            (∫ x in 0..(Real.log c - Real.log (location q)),
              finiteCosineModeSum (Real.log c) mode v x *
                finiteCosineModeSum (Real.log c) mode v
                  (x + Real.log (location q))) +
          2 * logarithmicPrimeWeight (location q) (base q) *
            (∫ x in 0..(Real.log c - Real.log (location q)),
              finiteSineModeSum (Real.log c) mode v x *
                finiteSineModeSum (Real.log c) mode v
                  (x + Real.log (location q)))) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_add (hCos q) (hSin q)]
      ring
    _ = _ := by
      unfold finiteTranslationIntegralEnergy finitePrimeLogShift finitePrimeLogWeight
      rw [← Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, one_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring

lemma truncatedTranslationFourierEntry_zero
    (L : ℝ) (n m : ℤ) (hL : L ≠ 0) :
    truncatedTranslationFourierEntry L 0 n m = if n = m then 2 else 0 := by
  by_cases hnm : n = m
  · subst m
    rw [truncatedTranslationFourierEntry_diagonal L 0 n hL]
    simp
  · rw [truncatedTranslationFourierEntry_offDiagonal L 0 n m hL hnm]
    simp [hnm]

theorem truncatedTranslation_zero_energy
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ)
    (hL : L ≠ 0) (hmode : Function.Injective mode) :
    finiteMatrixQuadraticEnergy
        (fun i j => truncatedTranslationFourierEntry L 0 (mode i) (mode j)) v =
      2 * ∑ i, v i ^ 2 := by
  classical
  unfold finiteMatrixQuadraticEnergy
  simp_rw [truncatedTranslationFourierEntry_zero L _ _ hL]
  calc
    (∑ i, ∑ j, (v i * if mode i = mode j then 2 else 0) * v j) =
        ∑ i, ∑ j, if mode i = mode j then v i * v j * 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ =
        ∑ i, ∑ j, if i = j then v i * v j * 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp
      · have hm : mode i ≠ mode j := fun h => hij (hmode h)
        simp [hij, hm]
    _ = _ := by
      simp
      calc
        (∑ x, v x * v x * 2) = ∑ x, 2 * v x ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.mul_sum]

/-- Real Parseval identity for a finite family of distinct integer modes. -/
theorem finiteCosineSine_parseval
    (L : ℝ) (mode : κ → ℤ) (v : κ → ℝ)
    (hL : L ≠ 0) (hmode : Function.Injective mode) :
    (∫ x in 0..L,
      (finiteCosineModeSum L mode v x) ^ 2 +
        (finiteSineModeSum L mode v x) ^ 2) =
      L * ∑ i, v i ^ 2 := by
  have hEnergy := truncatedTranslation_energy_eq_integral L 0 mode v
  rw [truncatedTranslation_zero_energy L mode v hL hmode] at hEnergy
  simp only [sub_zero, add_zero] at hEnergy
  have hRewrite :
      (fun x => finiteCosineModeSum L mode v x *
          finiteCosineModeSum L mode v x +
        finiteSineModeSum L mode v x *
          finiteSineModeSum L mode v x) =
      (fun x => (finiteCosineModeSum L mode v x) ^ 2 +
        (finiteSineModeSum L mode v x) ^ 2) := by
    funext x
    ring
  rw [hRewrite] at hEnergy
  field_simp [hL] at hEnergy
  nlinarith [hEnergy]

/-- Exactly the two piecewise-row integrability obligations left after the
continuous cutoff-13 Schur theorem has discharged the row constant. -/
def C13PrimeSchurRowIntegrable (f : ℝ → ℝ) : Prop :=
  (∀ i : Fin 8, IntervalIntegrable
    (fun x => if x ≤ Real.log 13 - c13PrimeTranslationShift i then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 (Real.log 13)) ∧
  (∀ i : Fin 8, IntervalIntegrable
    (fun x => if c13PrimeTranslationShift i < x then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 (Real.log 13))

theorem c13PrimeTranslationSchur_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f)
    (hRowInt : C13PrimeSchurRowIntegrable f) :
    |finiteTranslationIntegralEnergy (Real.log 13)
        c13PrimeTranslationShift c13PrimeTranslationWeight f| ≤
      (10 / 3) * ∫ x in 0..(Real.log 13), f x ^ 2 := by
  apply c13PrimeTranslationSchur f
  · intro i
    have hprod : Continuous (fun x => f x * f (x + c13PrimeTranslationShift i)) :=
      hf.mul (hf.comp (continuous_id.add continuous_const))
    exact hprod.abs.intervalIntegrable 0 _
  · exact hRowInt.1
  · exact hRowInt.2
  · exact (hf.pow 2).intervalIntegrable 0 (Real.log 13)

@[simp] lemma c13_finitePrimeLogShift_eq :
    finitePrimeLogShift c13PrimePowerLocation = c13PrimeTranslationShift := by
  rfl

@[simp] lemma c13_finitePrimeLogWeight_eq :
    finitePrimeLogWeight c13PrimePowerLocation c13PrimePowerBase =
      c13PrimeTranslationWeight := by
  rfl

lemma measurable_c13LogSupersolutionHeight :
    Measurable c13LogSupersolutionHeight := by
  unfold c13LogSupersolutionHeight c13ContinuousSupersolutionHeight
  apply Measurable.ite
    (measurableSet_lt Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_lt Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_lt Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_lt Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_le Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_le Real.measurable_exp measurable_const) measurable_const
  apply Measurable.ite
    (measurableSet_le Real.measurable_exp measurable_const) measurable_const
  exact Measurable.ite
    (measurableSet_le Real.measurable_exp measurable_const)
    measurable_const measurable_const

lemma c13LogSupersolutionHeight_bounds (x : ℝ) :
    (9 / 13 : ℝ) ≤ c13LogSupersolutionHeight x ∧
      c13LogSupersolutionHeight x ≤ 1 := by
  unfold c13LogSupersolutionHeight c13ContinuousSupersolutionHeight
  split_ifs <;> norm_num

lemma c13PrimeTranslationWeight_le_one (i : Fin 8) :
    c13PrimeTranslationWeight i ≤ 1 := by
  have h := c13PrimeTranslationWeight_lt_upper i
  fin_cases i <;>
    norm_num [c13PrimeTranslationWeightUpper] at h ⊢ <;> linarith

lemma norm_c13WeightedHeightRatio_le_two (i : Fin 8) (x y : ℝ) :
    ‖c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight y / c13LogSupersolutionHeight x)‖ ≤ 2 := by
  have hw0 := c13PrimeTranslationWeight_nonneg i
  have hw1 := c13PrimeTranslationWeight_le_one i
  have hx := c13LogSupersolutionHeight_bounds x
  have hy := c13LogSupersolutionHeight_bounds y
  have hxpos : 0 < c13LogSupersolutionHeight x :=
    c13LogSupersolutionHeight_pos x
  have hratio0 : 0 ≤ c13LogSupersolutionHeight y /
      c13LogSupersolutionHeight x := div_nonneg (le_trans (by norm_num) hy.1) hxpos.le
  have hratio : c13LogSupersolutionHeight y /
      c13LogSupersolutionHeight x ≤ 13 / 9 := by
    rw [div_le_iff₀ hxpos]
    nlinarith [hx.1, hy.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hratio0)]
  nlinarith

lemma measurable_c13LeftRowCoefficient (i : Fin 8) :
    Measurable (fun x => if x ≤ Real.log 13 - c13PrimeTranslationShift i then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0) := by
  apply Measurable.ite
    (measurableSet_le measurable_id measurable_const)
  · exact measurable_const.mul
      ((measurable_c13LogSupersolutionHeight.comp
        (measurable_id.add measurable_const)).div
        measurable_c13LogSupersolutionHeight)
  · exact measurable_const

lemma measurable_c13RightRowCoefficient (i : Fin 8) :
    Measurable (fun x => if c13PrimeTranslationShift i < x then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0) := by
  apply Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
  · exact measurable_const.mul
      ((measurable_c13LogSupersolutionHeight.comp
        (measurable_id.sub measurable_const)).div
        measurable_c13LogSupersolutionHeight)
  · exact measurable_const

lemma c13LeftRowCoefficient_norm_le_two (i : Fin 8) (x : ℝ) :
    ‖(if x ≤ Real.log 13 - c13PrimeTranslationShift i then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0)‖ ≤ 2 := by
  split_ifs
  · exact norm_c13WeightedHeightRatio_le_two i x
      (x + c13PrimeTranslationShift i)
  · norm_num

lemma c13RightRowCoefficient_norm_le_two (i : Fin 8) (x : ℝ) :
    ‖(if c13PrimeTranslationShift i < x then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0)‖ ≤ 2 := by
  split_ifs
  · exact norm_c13WeightedHeightRatio_le_two i x
      (x - c13PrimeTranslationShift i)
  · norm_num

lemma intervalIntegrable_c13LeftRow_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) (i : Fin 8) :
    IntervalIntegrable
      (fun x => if x ≤ Real.log 13 - c13PrimeTranslationShift i then
        c13PrimeTranslationWeight i *
          (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
            c13LogSupersolutionHeight x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 (Real.log 13) := by
  have h0L : 0 ≤ Real.log 13 := Real.log_nonneg (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le h0L]
  let a : ℝ → ℝ := fun x =>
    if x ≤ Real.log 13 - c13PrimeTranslationShift i then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0
  have haMeas : Measurable a := measurable_c13LeftRowCoefficient i
  have hSq : MeasureTheory.IntegrableOn (fun x => f x ^ 2)
      (Set.Icc 0 (Real.log 13)) MeasureTheory.volume :=
    (hf.pow 2).integrableOn_Icc
  have hMul : MeasureTheory.IntegrableOn (fun x => a x * f x ^ 2)
      (Set.Icc 0 (Real.log 13)) MeasureTheory.volume := by
    exact hSq.bdd_mul haMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => c13LeftRowCoefficient_norm_le_two i x))
  apply hMul.congr_fun
  intro x hx
  dsimp only [a]
  split_ifs <;> ring
  exact measurableSet_Icc

lemma intervalIntegrable_c13RightRow_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) (i : Fin 8) :
    IntervalIntegrable
      (fun x => if c13PrimeTranslationShift i < x then
        c13PrimeTranslationWeight i *
          (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
            c13LogSupersolutionHeight x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 (Real.log 13) := by
  have h0L : 0 ≤ Real.log 13 := Real.log_nonneg (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le h0L]
  let a : ℝ → ℝ := fun x =>
    if c13PrimeTranslationShift i < x then
      c13PrimeTranslationWeight i *
        (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
          c13LogSupersolutionHeight x) else 0
  have haMeas : Measurable a := measurable_c13RightRowCoefficient i
  have hSq : MeasureTheory.IntegrableOn (fun x => f x ^ 2)
      (Set.Icc 0 (Real.log 13)) MeasureTheory.volume :=
    (hf.pow 2).integrableOn_Icc
  have hMul : MeasureTheory.IntegrableOn (fun x => a x * f x ^ 2)
      (Set.Icc 0 (Real.log 13)) MeasureTheory.volume := by
    exact hSq.bdd_mul haMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => c13RightRowCoefficient_norm_le_two i x))
  apply hMul.congr_fun
  intro x hx
  dsimp only [a]
  split_ifs <;> ring
  exact measurableSet_Icc

theorem c13PrimeSchurRowIntegrable_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    C13PrimeSchurRowIntegrable f := by
  constructor
  · exact fun i => intervalIntegrable_c13LeftRow_of_continuous f hf i
  · exact fun i => intervalIntegrable_c13RightRow_of_continuous f hf i

theorem c13PrimeTranslationSchur_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    |finiteTranslationIntegralEnergy (Real.log 13)
        c13PrimeTranslationShift c13PrimeTranslationWeight f| ≤
      (10 / 3) * ∫ x in 0..(Real.log 13), f x ^ 2 :=
  c13PrimeTranslationSchur_of_continuous f hf
    (c13PrimeSchurRowIntegrable_of_continuous f hf)

/-- The continuous positive-supersolution bound, exact Fourier energy
identity, and Parseval normalization combine to give the desired cutoff-13
finite prime-matrix quadratic-form bound. -/
theorem c13_finitePrimeTranslationModeMatrix_energy_abs_le_tenThird
    (mode : κ → ℤ) (v : κ → ℝ) (hmode : Function.Injective mode) :
    |finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix 13 c13PrimePowerLocation
          c13PrimePowerBase mode) v| ≤
      (10 / 3) * ∑ i, v i ^ 2 := by
  let C := finiteCosineModeSum (Real.log 13) mode v
  let S := finiteSineModeSum (Real.log 13) mode v
  let EC := finiteTranslationIntegralEnergy (Real.log 13)
    c13PrimeTranslationShift c13PrimeTranslationWeight C
  let ES := finiteTranslationIntegralEnergy (Real.log 13)
    c13PrimeTranslationShift c13PrimeTranslationWeight S
  have hLpos : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have hLne : Real.log 13 ≠ 0 := ne_of_gt hLpos
  have hCcont : Continuous C :=
    continuous_finiteCosineModeSum (Real.log 13) mode v
  have hScont : Continuous S :=
    continuous_finiteSineModeSum (Real.log 13) mode v
  have hEC : |EC| ≤ (10 / 3) * ∫ x in 0..(Real.log 13), C x ^ 2 := by
    exact c13PrimeTranslationSchur_continuous C hCcont
  have hES : |ES| ≤ (10 / 3) * ∫ x in 0..(Real.log 13), S x ^ 2 := by
    exact c13PrimeTranslationSchur_continuous S hScont
  have hEnergy := finitePrimeTranslationModeMatrix_energy_eq_integralEnergies
    (κ := κ) 13 c13PrimePowerLocation c13PrimePowerBase mode v
  rw [c13_finitePrimeLogShift_eq, c13_finitePrimeLogWeight_eq] at hEnergy
  change finiteMatrixQuadraticEnergy
      (finitePrimeTranslationModeMatrix 13 c13PrimePowerLocation
        c13PrimePowerBase mode) v = (EC + ES) / Real.log 13 at hEnergy
  have hCInt : IntervalIntegrable (fun x => C x ^ 2)
      MeasureTheory.volume 0 (Real.log 13) :=
    (hCcont.pow 2).intervalIntegrable 0 (Real.log 13)
  have hSInt : IntervalIntegrable (fun x => S x ^ 2)
      MeasureTheory.volume 0 (Real.log 13) :=
    (hScont.pow 2).intervalIntegrable 0 (Real.log 13)
  have hParseval :
      (∫ x in 0..(Real.log 13), C x ^ 2) +
          ∫ x in 0..(Real.log 13), S x ^ 2 =
        Real.log 13 * ∑ i, v i ^ 2 := by
    rw [← intervalIntegral.integral_add hCInt hSInt]
    exact finiteCosineSine_parseval (Real.log 13) mode v hLne hmode
  rw [hEnergy]
  calc
    |(EC + ES) / Real.log 13| = |EC + ES| / Real.log 13 := by
      rw [abs_div, abs_of_pos hLpos]
    _ ≤ (|EC| + |ES|) / Real.log 13 := by
      exact div_le_div_of_nonneg_right (abs_add_le EC ES) hLpos.le
    _ ≤ (((10 / 3) * ∫ x in 0..(Real.log 13), C x ^ 2) +
          (10 / 3) * ∫ x in 0..(Real.log 13), S x ^ 2) /
        Real.log 13 := by
      exact div_le_div_of_nonneg_right (add_le_add hEC hES) hLpos.le
    _ = (10 / 3) * ∑ i, v i ^ 2 := by
      rw [← mul_add, hParseval]
      field_simp [hLne]

omit [Fintype κ] in
theorem signedMode_injective_of_injective_pos
    (mode : κ → ℤ) (hmode : Function.Injective mode)
    (hpos : ∀ i, 0 < mode i) :
    Function.Injective (signedMode mode) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          apply congrArg Sum.inl
          apply hmode
          simpa [signedMode] using hab
      | inr j =>
          simp only [signedMode, Sum.elim_inl, Sum.elim_inr] at hab
          have hi := hpos i
          have hj := hpos j
          omega
  | inr i =>
      cases b with
      | inl j =>
          simp only [signedMode, Sum.elim_inl, Sum.elim_inr] at hab
          have hi := hpos i
          have hj := hpos j
          omega
      | inr j =>
          apply congrArg Sum.inr
          apply hmode
          simp only [signedMode, Sum.elim_inr] at hab
          omega

/-- Closed full signed-space prime bound for every finite injective family of
strictly positive integer modes. -/
theorem c13_signedModeEnergy_abs_le_tenThird
    (mode : κ → ℤ) (hmode : Function.Injective mode)
    (hpos : ∀ i, 0 < mode i) (v : κ ⊕ κ → ℝ) :
    |finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix 13 c13PrimePowerLocation
          c13PrimePowerBase (signedMode mode)) v| ≤
      (10 / 3) * finiteTranslationVectorNormSq v := by
  simpa [finiteTranslationVectorNormSq] using
    c13_finitePrimeTranslationModeMatrix_energy_abs_le_tenThird
      (signedMode mode) v
      (signedMode_injective_of_injective_pos mode hmode hpos)

end RiemannCvs.PrimeTranslationContinuousFourier
