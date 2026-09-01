import RiemannCvs.PrimeTranslationContinuousSupersolution
import RiemannCvs.WeightedSchurSupersolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Continuous weighted Schur bound for cutoff-13 prime translations

This module integrates the weighted AM--GM inequality over every truncated
translation overlap, reconstructs the normalized pointwise row on `[0,L]`,
and specializes the resulting continuous Schur theorem to the exact 61-cell
cutoff-13 supersolution.
-/

open scoped BigOperators Real Interval
open Set

noncomputable section

namespace RiemannCvs.PrimeTranslationContinuousSchur

open RiemannCvs.WeightedSchurSupersolution
open RiemannCvs.PrimeTranslationSupersolution
open RiemannCvs.CombinedSymbolDyadicL2

/-- One shifted overlap obeys the two weighted Schur halves. -/
theorem oneShift_abs_integral_le
    (L a w : ℝ) (f h : ℝ → ℝ)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (hw : 0 ≤ w)
    (hH : ∀ x ∈ Set.Ioo 0 L, 0 < h x)
    (hCross : IntervalIntegrable
      (fun x => |f x * f (x + a)|) MeasureTheory.volume 0 (L - a))
    (hLeft : IntervalIntegrable
      (fun x => w * (h (x + a) / h x) * f x ^ 2) MeasureTheory.volume 0 (L - a))
    (hRight : IntervalIntegrable
      (fun x => w * (h x / h (x + a)) * f (x + a) ^ 2)
        MeasureTheory.volume 0 (L - a)) :
    |2 * w * ∫ x in 0..(L - a), f x * f (x + a)| ≤
      (∫ x in 0..(L - a), w * (h (x + a) / h x) * f x ^ 2) +
      ∫ x in a..L, w * (h (x - a) / h x) * f x ^ 2 := by
  have hLa : 0 ≤ L - a := sub_nonneg.mpr haL
  have hPoint : ∀ x ∈ Set.Ioo 0 (L - a),
      2 * w * |f x * f (x + a)| ≤
        w * (h (x + a) / h x) * f x ^ 2 +
          w * (h x / h (x + a)) * f (x + a) ^ 2 := by
    intro x hx
    have hxL : x < L := lt_of_lt_of_le hx.2 (sub_le_self L ha0)
    have hxa0 : 0 < x + a := add_pos_of_pos_of_nonneg hx.1 ha0
    have hxaL : x + a < L := by
      calc
        x + a < (L - a) + a := by
          simpa [add_comm] using add_lt_add_right hx.2 a
        _ = L := sub_add_cancel L a
    have hxH : 0 < h x := hH x ⟨hx.1, hxL⟩
    have hxaH : 0 < h (x + a) := hH (x + a) ⟨hxa0, hxaL⟩
    have hamgm := weightedTwoMul_le |f x| |f (x + a)| (h x) (h (x + a)) hxH hxaH
    have hmul := mul_le_mul_of_nonneg_left hamgm hw
    rw [abs_mul]
    simp only [sq_abs] at hmul
    nlinarith
  have hCross' : IntervalIntegrable
      (fun x => 2 * w * |f x * f (x + a)|) MeasureTheory.volume 0 (L - a) := by
    exact hCross.const_mul (2 * w)
  have hPairInt :
      (∫ x in 0..(L - a), 2 * w * |f x * f (x + a)|) ≤
        ∫ x in 0..(L - a),
          (w * (h (x + a) / h x) * f x ^ 2 +
            w * (h x / h (x + a)) * f (x + a) ^ 2) := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo hLa hCross'
      (hLeft.add hRight) hPoint
  have hTranslate :
      (∫ x in 0..(L - a), w * (h x / h (x + a)) * f (x + a) ^ 2) =
        ∫ x in a..L, w * (h (x - a) / h x) * f x ^ 2 := by
    have ht := intervalIntegral.integral_comp_add_right
      (f := fun y => w * (h (y - a) / h y) * f y ^ 2)
      (a := 0) (b := L - a) a
    simpa only [zero_add, sub_add_cancel, add_sub_cancel_right] using ht
  calc
    |2 * w * ∫ x in 0..(L - a), f x * f (x + a)| =
        2 * w * |∫ x in 0..(L - a), f x * f (x + a)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg hw]
    _ ≤ 2 * w * ∫ x in 0..(L - a), |f x * f (x + a)| := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral.abs_integral_le_integral_abs hLa)
        (mul_nonneg (by norm_num) hw)
    _ = ∫ x in 0..(L - a), 2 * w * |f x * f (x + a)| := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x in 0..(L - a),
          (w * (h (x + a) / h x) * f x ^ 2 +
            w * (h x / h (x + a)) * f (x + a) ^ 2) := hPairInt
    _ = (∫ x in 0..(L - a), w * (h (x + a) / h x) * f x ^ 2) +
        ∫ x in 0..(L - a), w * (h x / h (x + a)) * f (x + a) ^ 2 := by
      exact intervalIntegral.integral_add hLeft hRight
    _ = _ := by rw [hTranslate]

variable {ι : Type*} [Fintype ι]

private lemma uIcc_zero_sub_subset_zero_L
    (L a : ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    [[(0 : ℝ), L - a]] ⊆ [[(0 : ℝ), L]] := by
  rw [Set.uIcc_of_le (sub_nonneg.mpr haL), Set.uIcc_of_le (le_trans ha0 haL)]
  intro x hx
  exact ⟨hx.1, le_trans hx.2 (sub_le_self L ha0)⟩

private lemma uIcc_sub_L_subset_zero_L
    (L a : ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    [[L - a, L]] ⊆ [[(0 : ℝ), L]] := by
  rw [Set.uIcc_of_le (sub_le_self L ha0), Set.uIcc_of_le (le_trans ha0 haL)]
  intro x hx
  exact ⟨le_trans (sub_nonneg.mpr haL) hx.1, hx.2⟩

/-- Integrating a right-truncated `if` over the full interval is the same as
integrating its live branch over the overlap interval. -/
lemma integral_ite_le_sub_eq
    (L a : ℝ) (φ : ℝ → ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hInt : IntervalIntegrable
      (fun x => if x ≤ L - a then φ x else 0)
      MeasureTheory.volume 0 L) :
    (∫ x in 0..L, if x ≤ L - a then φ x else 0) =
      ∫ x in 0..(L - a), φ x := by
  have hLa : 0 ≤ L - a := sub_nonneg.mpr haL
  have hsubL : L - a ≤ L := sub_le_self L ha0
  have hLeftInt := hInt.mono_set
    (uIcc_zero_sub_subset_zero_L L a ha0 haL)
  have hRightInt := hInt.mono_set
    (uIcc_sub_L_subset_zero_L L a ha0 haL)
  have hLeftEq :
      (∫ x in 0..(L - a), if x ≤ L - a then φ x else 0) =
        ∫ x in 0..(L - a), φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hx
    rw [Set.uIoc_of_le hLa] at hx
    simp [hx.2]
  have hRightEq :
      (∫ x in (L - a)..L, if x ≤ L - a then φ x else 0) = 0 := by
    calc
      _ = ∫ x in (L - a)..L, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with x
        intro hx
        rw [Set.uIoc_of_le hsubL] at hx
        simp [not_le.mpr hx.1]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hLeftInt hRightInt,
    hLeftEq, hRightEq, add_zero]

lemma intervalIntegrable_live_of_ite_le_sub
    (L a : ℝ) (φ : ℝ → ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hInt : IntervalIntegrable
      (fun x => if x ≤ L - a then φ x else 0)
      MeasureTheory.volume 0 L) :
    IntervalIntegrable φ MeasureTheory.volume 0 (L - a) := by
  have hLa : 0 ≤ L - a := sub_nonneg.mpr haL
  have hTruncated := hInt.mono_set
    (uIcc_zero_sub_subset_zero_L L a ha0 haL)
  apply hTruncated.congr
  intro x hx
  rw [Set.uIoc_of_le hLa] at hx
  simp [hx.2]

private lemma uIcc_zero_a_subset_zero_L
    (L a : ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    [[(0 : ℝ), a]] ⊆ [[(0 : ℝ), L]] := by
  rw [Set.uIcc_of_le ha0, Set.uIcc_of_le (le_trans ha0 haL)]
  intro x hx
  exact ⟨hx.1, le_trans hx.2 haL⟩

private lemma uIcc_a_L_subset_zero_L
    (L a : ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    [[a, L]] ⊆ [[(0 : ℝ), L]] := by
  rw [Set.uIcc_of_le haL, Set.uIcc_of_le (le_trans ha0 haL)]
  intro x hx
  exact ⟨le_trans ha0 hx.1, hx.2⟩

/-- Left truncation, with a strict test chosen so that the shared endpoint is
handled exactly by the oriented interval convention. -/
lemma integral_ite_lt_eq
    (L a : ℝ) (φ : ℝ → ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hInt : IntervalIntegrable
      (fun x => if a < x then φ x else 0)
      MeasureTheory.volume 0 L) :
    (∫ x in 0..L, if a < x then φ x else 0) =
      ∫ x in a..L, φ x := by
  have h0L : 0 ≤ L := le_trans ha0 haL
  have hLeftInt := hInt.mono_set
    (uIcc_zero_a_subset_zero_L L a ha0 haL)
  have hRightInt := hInt.mono_set
    (uIcc_a_L_subset_zero_L L a ha0 haL)
  have hLeftEq :
      (∫ x in 0..a, if a < x then φ x else 0) = 0 := by
    calc
      _ = ∫ x in 0..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with x
        intro hx
        rw [Set.uIoc_of_le ha0] at hx
        simp [not_lt.mpr hx.2]
      _ = 0 := by simp
  have hRightEq :
      (∫ x in a..L, if a < x then φ x else 0) =
        ∫ x in a..L, φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hx
    rw [Set.uIoc_of_le haL] at hx
    simp [hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hLeftInt hRightInt,
    hLeftEq, hRightEq, zero_add]

lemma intervalIntegrable_live_of_ite_lt
    (L a : ℝ) (φ : ℝ → ℝ) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hInt : IntervalIntegrable
      (fun x => if a < x then φ x else 0)
      MeasureTheory.volume 0 L) :
    IntervalIntegrable φ MeasureTheory.volume a L := by
  have hTruncated := hInt.mono_set
    (uIcc_a_L_subset_zero_L L a ha0 haL)
  apply hTruncated.congr
  intro x hx
  rw [Set.uIoc_of_le haL] at hx
  simp [hx.1]

/-- The finite self-adjoint partial-translation quadratic form. -/
noncomputable def finiteTranslationIntegralEnergy
    (L : ℝ) (a w : ι → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, 2 * w i * ∫ x in 0..(L - a i), f x * f (x + a i)

/-- The two integrated weighted-Schur row halves. -/
noncomputable def finiteTranslationIntegratedRows
    (L : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ) : ℝ :=
  ∑ i,
    ((∫ x in 0..(L - a i),
        w i * (h (x + a i) / h x) * f x ^ 2) +
      ∫ x in a i..L,
        w i * (h (x - a i) / h x) * f x ^ 2)

/-- Normalized pointwise Schur row on `[0,L]`.  The weak upper test and strict
lower test assign the two shared endpoints consistently with oriented
interval integration. -/
noncomputable def finiteTranslationNormalizedRow
    (L : ℝ) (a w : ι → ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i,
    ((if x ≤ L - a i then w i * (h (x + a i) / h x) else 0) +
      if a i < x then w i * (h (x - a i) / h x) else 0)

lemma finiteTranslationNormalizedRow_mul_sq_intervalIntegrable
    (L : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ)
    (hLeftExt : ∀ i, IntervalIntegrable
      (fun x => if x ≤ L - a i then
        w i * (h (x + a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hRightExt : ∀ i, IntervalIntegrable
      (fun x => if a i < x then
        w i * (h (x - a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L) :
    IntervalIntegrable
      (fun x => finiteTranslationNormalizedRow L a w h x * f x ^ 2)
      MeasureTheory.volume 0 L := by
  classical
  let g : ι → ℝ → ℝ := fun i x =>
    (if x ≤ L - a i then
      w i * (h (x + a i) / h x) * f x ^ 2 else 0) +
    (if a i < x then
      w i * (h (x - a i) / h x) * f x ^ 2 else 0)
  have hg : ∀ i, IntervalIntegrable (g i) MeasureTheory.volume 0 L := by
    intro i
    exact (hLeftExt i).add (hRightExt i)
  have hsum : IntervalIntegrable (fun x => ∑ i, g i x)
      MeasureTheory.volume 0 L := by
    have hfun := Finset.sum_induction (s := Finset.univ) (fun i => g i)
      (fun F => IntervalIntegrable F MeasureTheory.volume 0 L)
      (fun _ _ hF hG => hF.add hG) IntervalIntegrable.zero
      (fun i hi => hg i)
    apply hfun.congr
    intro x hx
    simp
  apply hsum.congr
  intro x hx
  dsimp only [g]
  simp only [finiteTranslationNormalizedRow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

/-- The two integrated row halves are exactly the integral of the normalized
pointwise row against `f²`. -/
theorem finiteTranslationIntegratedRows_eq_rowIntegral
    (L : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ L)
    (hLeftExt : ∀ i, IntervalIntegrable
      (fun x => if x ≤ L - a i then
        w i * (h (x + a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hRightExt : ∀ i, IntervalIntegrable
      (fun x => if a i < x then
        w i * (h (x - a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L) :
    finiteTranslationIntegratedRows L a w f h =
      ∫ x in 0..L, finiteTranslationNormalizedRow L a w h x * f x ^ 2 := by
  classical
  unfold finiteTranslationIntegratedRows
  calc
    (∑ i,
      ((∫ x in 0..(L - a i),
          w i * (h (x + a i) / h x) * f x ^ 2) +
        ∫ x in a i..L,
          w i * (h (x - a i) / h x) * f x ^ 2)) =
        ∑ i,
          ((∫ x in 0..L, if x ≤ L - a i then
              w i * (h (x + a i) / h x) * f x ^ 2 else 0) +
            ∫ x in 0..L, if a i < x then
              w i * (h (x - a i) / h x) * f x ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_ite_le_sub_eq L (a i)
          (fun x => w i * (h (x + a i) / h x) * f x ^ 2)
          (ha0 i) (haL i) (hLeftExt i),
        integral_ite_lt_eq L (a i)
          (fun x => w i * (h (x - a i) / h x) * f x ^ 2)
          (ha0 i) (haL i) (hRightExt i)]
    _ = ∑ i, ∫ x in 0..L,
          ((if x ≤ L - a i then
              w i * (h (x + a i) / h x) * f x ^ 2 else 0) +
            if a i < x then
              w i * (h (x - a i) / h x) * f x ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (intervalIntegral.integral_add (hLeftExt i) (hRightExt i)).symm
    _ = ∫ x in 0..L, ∑ i,
          ((if x ≤ L - a i then
              w i * (h (x + a i) / h x) * f x ^ 2 else 0) +
            if a i < x then
              w i * (h (x - a i) / h x) * f x ^ 2 else 0) := by
      exact (intervalIntegral.integral_finsetSum
        (fun i _ => (hLeftExt i).add (hRightExt i))).symm
    _ = ∫ x in 0..L,
        finiteTranslationNormalizedRow L a w h x * f x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [finiteTranslationNormalizedRow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring

/-- A finite family of partial translations is bounded by its two integrated
weighted-Schur row halves.  This is the continuous analogue of the finite
matrix Schur lemma, before inserting a pointwise supersolution budget. -/
theorem finiteTranslationEnergy_abs_le_integratedRows
    (L : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ L)
    (hw : ∀ i, 0 ≤ w i)
    (hH : ∀ x ∈ Set.Ioo 0 L, 0 < h x)
    (hCross : ∀ i, IntervalIntegrable
      (fun x => |f x * f (x + a i)|) MeasureTheory.volume 0 (L - a i))
    (hLeft : ∀ i, IntervalIntegrable
      (fun x => w i * (h (x + a i) / h x) * f x ^ 2)
        MeasureTheory.volume 0 (L - a i))
    (hRight : ∀ i, IntervalIntegrable
      (fun x => w i * (h x / h (x + a i)) * f (x + a i) ^ 2)
        MeasureTheory.volume 0 (L - a i)) :
    |finiteTranslationIntegralEnergy L a w f| ≤
      finiteTranslationIntegratedRows L a w f h := by
  unfold finiteTranslationIntegralEnergy finiteTranslationIntegratedRows
  calc
    |∑ i, 2 * w i * ∫ x in 0..(L - a i), f x * f (x + a i)| ≤
        ∑ i, |2 * w i * ∫ x in 0..(L - a i), f x * f (x + a i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,
        ((∫ x in 0..(L - a i),
            w i * (h (x + a i) / h x) * f x ^ 2) +
          ∫ x in a i..L,
            w i * (h (x - a i) / h x) * f x ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact oneShift_abs_integral_le L (a i) (w i) f h
        (ha0 i) (haL i) (hw i) hH (hCross i) (hLeft i) (hRight i)

/-- A pointwise bound for the normalized Schur row integrates to the same
`L²` bound. -/
theorem finiteTranslationIntegratedRows_le_of_pointwiseRow
    (L B : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ)
    (h0L : 0 ≤ L)
    (ha0 : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ L)
    (hLeftExt : ∀ i, IntervalIntegrable
      (fun x => if x ≤ L - a i then
        w i * (h (x + a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hRightExt : ∀ i, IntervalIntegrable
      (fun x => if a i < x then
        w i * (h (x - a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hSqIntegrable : IntervalIntegrable (fun x => f x ^ 2)
      MeasureTheory.volume 0 L)
    (hRow : ∀ x ∈ Set.Ioo 0 L,
      finiteTranslationNormalizedRow L a w h x ≤ B) :
    finiteTranslationIntegratedRows L a w f h ≤
      B * ∫ x in 0..L, f x ^ 2 := by
  rw [finiteTranslationIntegratedRows_eq_rowIntegral
    L a w f h ha0 haL hLeftExt hRightExt]
  calc
    (∫ x in 0..L,
        finiteTranslationNormalizedRow L a w h x * f x ^ 2) ≤
      ∫ x in 0..L, B * f x ^ 2 := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo h0L
          (finiteTranslationNormalizedRow_mul_sq_intervalIntegrable
            L a w f h hLeftExt hRightExt)
          (hSqIntegrable.const_mul B)
        intro x hx
        exact mul_le_mul_of_nonneg_right (hRow x hx) (sq_nonneg (f x))
    _ = B * ∫ x in 0..L, f x ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

/-- Continuous weighted Schur test for finitely many self-adjoint partial
translations on `[0,L]`.  The conclusion has the same constant as the
pointwise positive-supersolution row bound. -/
theorem finiteTranslationSchur
    (L B : ℝ) (a w : ι → ℝ) (f h : ℝ → ℝ)
    (h0L : 0 ≤ L)
    (ha0 : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ L)
    (hw : ∀ i, 0 ≤ w i)
    (hH : ∀ x ∈ Set.Ioo 0 L, 0 < h x)
    (hCross : ∀ i, IntervalIntegrable
      (fun x => |f x * f (x + a i)|) MeasureTheory.volume 0 (L - a i))
    (hLeftExt : ∀ i, IntervalIntegrable
      (fun x => if x ≤ L - a i then
        w i * (h (x + a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hRightExt : ∀ i, IntervalIntegrable
      (fun x => if a i < x then
        w i * (h (x - a i) / h x) * f x ^ 2 else 0)
      MeasureTheory.volume 0 L)
    (hSqIntegrable : IntervalIntegrable (fun x => f x ^ 2)
      MeasureTheory.volume 0 L)
    (hRow : ∀ x ∈ Set.Ioo 0 L,
      finiteTranslationNormalizedRow L a w h x ≤ B) :
    |finiteTranslationIntegralEnergy L a w f| ≤
      B * ∫ x in 0..L, f x ^ 2 := by
  have hLeft : ∀ i, IntervalIntegrable
      (fun x => w i * (h (x + a i) / h x) * f x ^ 2)
        MeasureTheory.volume 0 (L - a i) := by
    intro i
    exact intervalIntegrable_live_of_ite_le_sub L (a i)
      (fun x => w i * (h (x + a i) / h x) * f x ^ 2)
      (ha0 i) (haL i) (hLeftExt i)
  have hRight : ∀ i, IntervalIntegrable
      (fun x => w i * (h x / h (x + a i)) * f (x + a i) ^ 2)
        MeasureTheory.volume 0 (L - a i) := by
    intro i
    have hLive := intervalIntegrable_live_of_ite_lt L (a i)
      (fun x => w i * (h (x - a i) / h x) * f x ^ 2)
      (ha0 i) (haL i) (hRightExt i)
    have hShift := hLive.comp_add_right (a i)
    simpa only [sub_add_cancel, add_sub_cancel_right, sub_self] using hShift
  exact (finiteTranslationEnergy_abs_le_integratedRows
    L a w f h ha0 haL hw hH hCross hLeft hRight).trans
      (finiteTranslationIntegratedRows_le_of_pointwiseRow
        L B a w f h h0L ha0 haL hLeftExt hRightExt
        hSqIntegrable hRow)

/-! ## Cutoff-13 logarithmic specialization -/

/-- The certified multiplicative supersolution pulled back to logarithmic
coordinates. -/
noncomputable def c13LogSupersolutionHeight (x : ℝ) : ℝ :=
  c13ContinuousSupersolutionHeight (Real.exp x)

/-- The eight cutoff-13 prime-power translations in logarithmic coordinates. -/
noncomputable def c13PrimeTranslationShift (i : Fin 8) : ℝ :=
  Real.log (c13PrimePowerLocation i)

lemma c13LogSupersolutionHeight_pos (x : ℝ) :
    0 < c13LogSupersolutionHeight x :=
  c13ContinuousSupersolutionHeight_pos (Real.exp x)

lemma c13PrimeTranslationShift_nonneg (i : Fin 8) :
    0 ≤ c13PrimeTranslationShift i := by
  fin_cases i <;>
    simp [c13PrimeTranslationShift, c13PrimePowerLocation,
      Real.log_nonneg]

lemma c13PrimeTranslationShift_le_log_thirteen (i : Fin 8) :
    c13PrimeTranslationShift i ≤ Real.log 13 := by
  fin_cases i <;>
    simp [c13PrimeTranslationShift, c13PrimePowerLocation]
  all_goals exact Real.log_le_log (by norm_num) (by norm_num)

lemma c13PrimeTranslationWeight_nonneg (i : Fin 8) :
    0 ≤ c13PrimeTranslationWeight i := by
  fin_cases i <;>
    simp [c13PrimeTranslationWeight, c13PrimePowerBase,
      c13PrimePowerLocation] <;> positivity

lemma c13PrimePowerLocation_pos (i : Fin 8) :
    0 < c13PrimePowerLocation i := by
  fin_cases i <;> simp [c13PrimePowerLocation]

lemma exp_add_log_eq_mul (x q : ℝ) (hq : 0 < q) :
    Real.exp (x + Real.log q) = Real.exp x * q := by
  rw [Real.exp_add, Real.exp_log hq]

lemma exp_sub_log_eq_div (x q : ℝ) (hq : 0 < q) :
    Real.exp (x - Real.log q) = Real.exp x / q := by
  rw [Real.exp_sub, Real.exp_log hq]

lemma logCoordinate_upperShift_iff (x q : ℝ) (hq : 0 < q) :
    x ≤ Real.log 13 - Real.log q ↔ Real.exp x * q ≤ 13 := by
  have h13 : (0 : ℝ) < 13 := by norm_num
  constructor
  · intro hx
    have hadd : x + Real.log q ≤ Real.log 13 := by linarith
    have hexp := Real.exp_le_exp.mpr hadd
    simpa [exp_add_log_eq_mul x q hq, Real.exp_log h13] using hexp
  · intro hx
    have hexp : Real.exp (x + Real.log q) ≤ Real.exp (Real.log 13) := by
      simpa [exp_add_log_eq_mul x q hq, Real.exp_log h13] using hx
    have hadd := Real.exp_le_exp.mp hexp
    linarith

/-- The strict lower-overlap convention used by interval integration drops
at most the single equality point from the closed-support certified row. -/
lemma c13LogRowFactorNumerator_le
    (x q : ℝ) (hq : 0 < q) :
    (if x ≤ Real.log 13 - Real.log q then
        c13LogSupersolutionHeight (x + Real.log q) else 0) +
      (if Real.log q < x then
        c13LogSupersolutionHeight (x - Real.log q) else 0) ≤
      c13ContinuousPrimeTranslationRowFactor (Real.exp x) q := by
  have hplus := logCoordinate_upperShift_iff x q hq
  have hminus : Real.log q < x ↔ q < Real.exp x :=
    Real.log_lt_iff_lt_exp hq
  unfold c13LogSupersolutionHeight c13ContinuousPrimeTranslationRowFactor
  rw [exp_add_log_eq_mul x q hq, exp_sub_log_eq_div x q hq]
  by_cases hp : x ≤ Real.log 13 - Real.log q
  · have hp' : Real.exp x * q ≤ 13 := hplus.mp hp
    by_cases hm : Real.log q < x
    · have hm' : q ≤ Real.exp x := (hminus.mp hm).le
      simp [hp, hp', hm, hm']
    · by_cases hm' : q ≤ Real.exp x
      · simp [hp, hp', hm, hm',
          (c13ContinuousSupersolutionHeight_pos (Real.exp x / q)).le]
      · simp [hp, hp', hm, hm']
  · have hp' : ¬ Real.exp x * q ≤ 13 := fun h => hp (hplus.mpr h)
    by_cases hm : Real.log q < x
    · have hm' : q ≤ Real.exp x := (hminus.mp hm).le
      simp [hp, hp', hm, hm']
    · by_cases hm' : q ≤ Real.exp x
      · simp [hp, hp', hm, hm',
          (c13ContinuousSupersolutionHeight_pos (Real.exp x / q)).le]
      · simp [hp, hp', hm, hm']

lemma c13LogNormalizedEventRow_le
    (x q w : ℝ) (hq : 0 < q) (hw : 0 ≤ w) :
    (if x ≤ Real.log 13 - Real.log q then
        w * (c13LogSupersolutionHeight (x + Real.log q) /
          c13LogSupersolutionHeight x) else 0) +
      (if Real.log q < x then
        w * (c13LogSupersolutionHeight (x - Real.log q) /
          c13LogSupersolutionHeight x) else 0) ≤
      w * c13ContinuousPrimeTranslationRowFactor (Real.exp x) q /
        c13LogSupersolutionHeight x := by
  have hH := c13LogSupersolutionHeight_pos x
  have hnum := c13LogRowFactorNumerator_le x q hq
  have hscale : 0 ≤ w / c13LogSupersolutionHeight x :=
    div_nonneg hw hH.le
  have hmul := mul_le_mul_of_nonneg_left hnum hscale
  calc
    _ = (w / c13LogSupersolutionHeight x) *
        ((if x ≤ Real.log 13 - Real.log q then
            c13LogSupersolutionHeight (x + Real.log q) else 0) +
          if Real.log q < x then
            c13LogSupersolutionHeight (x - Real.log q) else 0) := by
      split_ifs <;> field_simp <;> ring
    _ ≤ (w / c13LogSupersolutionHeight x) *
        c13ContinuousPrimeTranslationRowFactor (Real.exp x) q := hmul
    _ = _ := by ring

lemma c13ActualPrimeTranslationRow_eq_fin_sum (t : ℝ) :
    c13ContinuousActualPrimeTranslationRow t =
      ∑ i : Fin 8, c13PrimeTranslationWeight i *
        c13ContinuousPrimeTranslationRowFactor t (c13PrimePowerLocation i) := by
  simp [c13ContinuousActualPrimeTranslationRow,
    c13PrimeTranslationWeight, c13PrimePowerBase, c13PrimePowerLocation,
    Fin.sum_univ_succ]
  ring

/-- The generated 61-cell real supersolution is now a literal pointwise Schur
row bound in logarithmic coordinates. -/
theorem c13_finiteTranslationNormalizedRow_lt_tenThird
    (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.log 13)) :
    finiteTranslationNormalizedRow (Real.log 13)
        c13PrimeTranslationShift c13PrimeTranslationWeight
        c13LogSupersolutionHeight x < 10 / 3 := by
  have hH : 0 < c13LogSupersolutionHeight x :=
    c13LogSupersolutionHeight_pos x
  have hsum :
      finiteTranslationNormalizedRow (Real.log 13)
          c13PrimeTranslationShift c13PrimeTranslationWeight
          c13LogSupersolutionHeight x ≤
        (∑ i : Fin 8, c13PrimeTranslationWeight i *
          c13ContinuousPrimeTranslationRowFactor (Real.exp x)
            (c13PrimePowerLocation i)) /
          c13LogSupersolutionHeight x := by
    unfold finiteTranslationNormalizedRow
    calc
      (∑ i : Fin 8,
        ((if x ≤ Real.log 13 - c13PrimeTranslationShift i then
            c13PrimeTranslationWeight i *
              (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
                c13LogSupersolutionHeight x) else 0) +
          if c13PrimeTranslationShift i < x then
            c13PrimeTranslationWeight i *
              (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
                c13LogSupersolutionHeight x) else 0)) ≤
        ∑ i : Fin 8,
          c13PrimeTranslationWeight i *
            c13ContinuousPrimeTranslationRowFactor (Real.exp x)
              (c13PrimePowerLocation i) /
            c13LogSupersolutionHeight x := by
        apply Finset.sum_le_sum
        intro i hi
        unfold c13PrimeTranslationShift
        exact c13LogNormalizedEventRow_le x (c13PrimePowerLocation i)
          (c13PrimeTranslationWeight i) (c13PrimePowerLocation_pos i)
          (c13PrimeTranslationWeight_nonneg i)
      _ = _ := by rw [Finset.sum_div]
  have hExpLower : 1 ≤ Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hx.1.le
  have hExpUpper : Real.exp x ≤ 13 := by
    have := Real.exp_le_exp.mpr hx.2.le
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 13)] using this
  have hActual := c13ContinuousActualPrimeTranslationRow_lt_tenThird
    (Real.exp x) hExpLower hExpUpper
  have hRatio :
      c13ContinuousActualPrimeTranslationRow (Real.exp x) /
          c13LogSupersolutionHeight x < 10 / 3 := by
    rw [div_lt_iff₀ hH]
    simpa [c13LogSupersolutionHeight] using hActual
  rw [← c13ActualPrimeTranslationRow_eq_fin_sum] at hsum
  exact lt_of_le_of_lt hsum hRatio

/-- Cutoff-13 continuous `L²` prime-translation bound.  The difficult
pointwise constant is discharged by the 61-cell certificate; the remaining
hypotheses are the standard interval-integrability obligations for the test
function. -/
theorem c13PrimeTranslationSchur
    (f : ℝ → ℝ)
    (hCross : ∀ i : Fin 8, IntervalIntegrable
      (fun x => |f x * f (x + c13PrimeTranslationShift i)|)
        MeasureTheory.volume 0 (Real.log 13 - c13PrimeTranslationShift i))
    (hLeftExt : ∀ i : Fin 8, IntervalIntegrable
      (fun x => if x ≤ Real.log 13 - c13PrimeTranslationShift i then
        c13PrimeTranslationWeight i *
          (c13LogSupersolutionHeight (x + c13PrimeTranslationShift i) /
            c13LogSupersolutionHeight x) * f x ^ 2 else 0)
        MeasureTheory.volume 0 (Real.log 13))
    (hRightExt : ∀ i : Fin 8, IntervalIntegrable
      (fun x => if c13PrimeTranslationShift i < x then
        c13PrimeTranslationWeight i *
          (c13LogSupersolutionHeight (x - c13PrimeTranslationShift i) /
            c13LogSupersolutionHeight x) * f x ^ 2 else 0)
        MeasureTheory.volume 0 (Real.log 13))
    (hSqIntegrable : IntervalIntegrable (fun x => f x ^ 2)
      MeasureTheory.volume 0 (Real.log 13)) :
    |finiteTranslationIntegralEnergy (Real.log 13)
        c13PrimeTranslationShift c13PrimeTranslationWeight f| ≤
      (10 / 3) * ∫ x in 0..(Real.log 13), f x ^ 2 := by
  apply finiteTranslationSchur (ι := Fin 8)
    (Real.log 13) (10 / 3) c13PrimeTranslationShift
    c13PrimeTranslationWeight f c13LogSupersolutionHeight
    (Real.log_nonneg (by norm_num))
    c13PrimeTranslationShift_nonneg
    c13PrimeTranslationShift_le_log_thirteen
    c13PrimeTranslationWeight_nonneg
    (fun x hx => c13LogSupersolutionHeight_pos x)
    hCross hLeftExt hRightExt hSqIntegrable
  intro x hx
  exact (c13_finiteTranslationNormalizedRow_lt_tenThird x hx).le

end RiemannCvs.PrimeTranslationContinuousSchur
