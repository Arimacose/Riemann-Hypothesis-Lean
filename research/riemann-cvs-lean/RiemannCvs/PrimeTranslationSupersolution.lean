import Mathlib
import RiemannCvs.CombinedSymbolDyadicL2

/-!
# A direct positive supersolution for the cutoff-13 prime translation

The earlier power-Schur certificate bounds the sixth power of the positive
prime-translation operator by enumerating all admissible paths of length six.
This module records a shorter route.  In multiplicative coordinates
`t = exp x ∈ [1,13]`, a symmetric rational step function has only four boundary
layers.  Its row ratio is below `10/3` after replacing each true
`log(p)/sqrt(q)` weight by a proved rational upper bound.

The exact finite table below checks the 61 atomic open cells and all 62
breakpoints.  A separate analytic layer must still connect the physical-space
supersolution to the L2 weighted Schur theorem and then to the Fourier
compression already identified in `PrimeTranslationFourierBridge`.
-/

namespace RiemannCvs.PrimeTranslationSupersolution

open scoped BigOperators
open RiemannCvs.CombinedSymbolDyadicL2

/-! ## Elementary certified bounds for the eight true weights -/

lemma log_two_lt : Real.log 2 < (347 / 500 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 8
  norm_num at h
  linarith

lemma log_three_lt : Real.log 3 < (1099 / 1000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 12
  norm_num at h
  linarith

lemma log_five_lt : Real.log 5 < (3219 / 2000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) 32
  norm_num at h
  linarith

lemma log_seven_lt : Real.log 7 < (3893 / 2000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (3 / 4 : ℝ)) (by norm_num) (by norm_num) 40
  norm_num at h
  linarith

lemma log_eleven_lt : Real.log 11 < (12 / 5 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (5 / 6 : ℝ)) (by norm_num) (by norm_num) 40
  norm_num at h
  linarith

lemma sqrt_two_lower : (707 / 500 : ℝ) < Real.sqrt 2 := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma sqrt_three_lower : (433 / 250 : ℝ) < Real.sqrt 3 := by
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

lemma sqrt_five_lower : (559 / 250 : ℝ) < Real.sqrt 5 := by
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

lemma sqrt_seven_lower : (529 / 200 : ℝ) < Real.sqrt 7 := by
  have hs0 := Real.sqrt_nonneg (7 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  nlinarith

lemma sqrt_eleven_lower : (829 / 250 : ℝ) < Real.sqrt 11 := by
  have hs0 := Real.sqrt_nonneg (11 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11)
  nlinarith

lemma sqrt_eight_lower : (707 / 250 : ℝ) < Real.sqrt 8 := by
  have hs0 := Real.sqrt_nonneg (8 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

lemma weight_two_lt :
    Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_two_lt, sqrt_two_lower]

lemma weight_four_lt :
    Real.log 2 / Real.sqrt 4 < (347 / 1000 : ℝ) := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hs]
  linarith [log_two_lt]

lemma weight_eight_lt :
    Real.log 2 / Real.sqrt 8 < (246 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_two_lt, sqrt_eight_lower]

lemma weight_three_lt :
    Real.log 3 / Real.sqrt 3 < (635 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_three_lt, sqrt_three_lower]

lemma weight_nine_lt :
    Real.log 3 / Real.sqrt 9 < (367 / 1000 : ℝ) := by
  have hs : Real.sqrt (9 : ℝ) = 3 := by norm_num
  rw [hs]
  linarith [log_three_lt]

lemma weight_five_lt :
    Real.log 5 / Real.sqrt 5 < (720 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_five_lt, sqrt_five_lower]

lemma weight_seven_lt :
    Real.log 7 / Real.sqrt 7 < (736 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (7 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_seven_lt, sqrt_seven_lower]

lemma weight_eleven_lt :
    Real.log 11 / Real.sqrt 11 < (724 / 1000 : ℝ) := by
  have hsPos : 0 < Real.sqrt (11 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsPos]
  nlinarith [log_eleven_lt, sqrt_eleven_lower]

/-- The true cutoff-13 weight in the existing prime-power ordering. -/
noncomputable def c13PrimeTranslationWeight (i : Fin 8) : ℝ :=
  Real.log (c13PrimePowerBase i) / Real.sqrt (c13PrimePowerLocation i)

/-- Simple rational upper weights, ordered by locations `2,3,4,5,7,8,9,11`. -/
noncomputable def c13PrimeTranslationWeightUpper : Fin 8 → ℝ :=
  ![491 / 1000, 635 / 1000, 347 / 1000, 720 / 1000,
    736 / 1000, 246 / 1000, 367 / 1000, 724 / 1000]

/-- Every transcendental prime weight is strictly below its rational envelope. -/
theorem c13PrimeTranslationWeight_lt_upper (i : Fin 8) :
    c13PrimeTranslationWeight i < c13PrimeTranslationWeightUpper i := by
  fin_cases i
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_two_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_three_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_four_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_five_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_seven_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_eight_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_nine_lt
  · simpa [c13PrimeTranslationWeight, c13PrimeTranslationWeightUpper,
      c13PrimePowerBase, c13PrimePowerLocation] using weight_eleven_lt

/-! ## Exact rational step supersolution and its finite atomic table -/

/-- Rational prime-power locations in the same ordering as the real data. -/
def c13PrimePowerLocationQ : Fin 8 → ℚ :=
  ![2, 3, 4, 5, 7, 8, 9, 11]

/-- Rational upper weights in exact computation form. -/
def c13PrimeTranslationWeightUpperQ : Fin 8 → ℚ :=
  ![491 / 1000, 635 / 1000, 347 / 1000, 720 / 1000,
    736 / 1000, 246 / 1000, 367 / 1000, 724 / 1000]

/-- Four symmetric multiplicative boundary layers and one central layer. -/
def c13SupersolutionHeightQ (t : ℚ) : ℚ :=
  if t < 6 / 5 then 1
  else if t < 3 / 2 then 5 / 6
  else if t < 5 / 3 then 10 / 13
  else if t < 15 / 8 then 5 / 7
  else if t ≤ 104 / 15 then 9 / 13
  else if t ≤ 39 / 5 then 5 / 7
  else if t ≤ 26 / 3 then 10 / 13
  else if t ≤ 65 / 6 then 5 / 6
  else 1

lemma c13SupersolutionHeightQ_pos (t : ℚ) :
    0 < c13SupersolutionHeightQ t := by
  simp only [c13SupersolutionHeightQ]
  split_ifs <;> norm_num

/-- One rational closed-support directed-pair row factor. -/
def c13RationalPrimeTranslationRowFactorQ (t q : ℚ) : ℚ :=
  (if t * q ≤ 13 then c13SupersolutionHeightQ (t * q) else 0) +
  (if q ≤ t then c13SupersolutionHeightQ (t / q) else 0)

/-- One rational closed-support directed-pair row contribution. -/
def c13RationalPrimeTranslationEventRow (t q weight : ℚ) : ℚ :=
  weight * c13RationalPrimeTranslationRowFactorQ t q

/-- Exact rational envelope for one closed-support prime-translation row. -/
def c13RationalPrimeTranslationRow (t : ℚ) : ℚ :=
  c13RationalPrimeTranslationEventRow t 2 (491 / 1000) +
  c13RationalPrimeTranslationEventRow t 3 (635 / 1000) +
  c13RationalPrimeTranslationEventRow t 4 (347 / 1000) +
  c13RationalPrimeTranslationEventRow t 5 (720 / 1000) +
  c13RationalPrimeTranslationEventRow t 7 (736 / 1000) +
  c13RationalPrimeTranslationEventRow t 8 (246 / 1000) +
  c13RationalPrimeTranslationEventRow t 9 (367 / 1000) +
  c13RationalPrimeTranslationEventRow t 11 (724 / 1000)

/-- The nonnegative physical row factor attached to one rational shift. -/
noncomputable def c13PrimeTranslationRowFactor (t q : ℚ) : ℝ :=
  (if t * q ≤ 13 then (c13SupersolutionHeightQ (t * q) : ℝ) else 0) +
  (if q ≤ t then (c13SupersolutionHeightQ (t / q) : ℝ) else 0)

lemma c13PrimeTranslationRowFactor_nonneg (t q : ℚ) :
    0 ≤ c13PrimeTranslationRowFactor t q := by
  unfold c13PrimeTranslationRowFactor
  apply add_nonneg
  · split_ifs
    · exact_mod_cast (c13SupersolutionHeightQ_pos (t * q)).le
    · norm_num
  · split_ifs
    · exact_mod_cast (c13SupersolutionHeightQ_pos (t / q)).le
    · norm_num

lemma c13PrimeTranslationRowFactor_eq_ratCast (t q : ℚ) :
    c13PrimeTranslationRowFactor t q =
      (c13RationalPrimeTranslationRowFactorQ t q : ℝ) := by
  by_cases hPlus : t * q ≤ 13 <;>
    by_cases hMinus : q ≤ t <;>
    simp [c13PrimeTranslationRowFactor,
      c13RationalPrimeTranslationRowFactorQ, hPlus, hMinus]

/-- The true row, with exact logarithmic weights and rational step geometry. -/
noncomputable def c13ActualPrimeTranslationRow (t : ℚ) : ℝ :=
  (Real.log 2 / Real.sqrt 2) * c13PrimeTranslationRowFactor t 2 +
  (Real.log 3 / Real.sqrt 3) * c13PrimeTranslationRowFactor t 3 +
  (Real.log 2 / Real.sqrt 4) * c13PrimeTranslationRowFactor t 4 +
  (Real.log 5 / Real.sqrt 5) * c13PrimeTranslationRowFactor t 5 +
  (Real.log 7 / Real.sqrt 7) * c13PrimeTranslationRowFactor t 7 +
  (Real.log 2 / Real.sqrt 8) * c13PrimeTranslationRowFactor t 8 +
  (Real.log 3 / Real.sqrt 9) * c13PrimeTranslationRowFactor t 9 +
  (Real.log 11 / Real.sqrt 11) * c13PrimeTranslationRowFactor t 11

/-- The real-valued row formed from the rational upper weights. -/
noncomputable def c13UpperPrimeTranslationRow (t : ℚ) : ℝ :=
  (491 / 1000) * c13PrimeTranslationRowFactor t 2 +
  (635 / 1000) * c13PrimeTranslationRowFactor t 3 +
  (347 / 1000) * c13PrimeTranslationRowFactor t 4 +
  (720 / 1000) * c13PrimeTranslationRowFactor t 5 +
  (736 / 1000) * c13PrimeTranslationRowFactor t 7 +
  (246 / 1000) * c13PrimeTranslationRowFactor t 8 +
  (367 / 1000) * c13PrimeTranslationRowFactor t 9 +
  (724 / 1000) * c13PrimeTranslationRowFactor t 11

/-- Weight monotonicity transfers the eight elementary bounds to the whole row. -/
theorem c13ActualPrimeTranslationRow_le_upper (t : ℚ) :
    c13ActualPrimeTranslationRow t ≤ c13UpperPrimeTranslationRow t := by
  unfold c13ActualPrimeTranslationRow c13UpperPrimeTranslationRow
  have h2 := mul_le_mul_of_nonneg_right weight_two_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 2)
  have h3 := mul_le_mul_of_nonneg_right weight_three_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 3)
  have h4 := mul_le_mul_of_nonneg_right weight_four_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 4)
  have h5 := mul_le_mul_of_nonneg_right weight_five_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 5)
  have h7 := mul_le_mul_of_nonneg_right weight_seven_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 7)
  have h8 := mul_le_mul_of_nonneg_right weight_eight_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 8)
  have h9 := mul_le_mul_of_nonneg_right weight_nine_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 9)
  have h11 := mul_le_mul_of_nonneg_right weight_eleven_lt.le
    (c13PrimeTranslationRowFactor_nonneg t 11)
  linarith

/-- Casting the exact rational computation gives precisely the upper real row. -/
theorem c13UpperPrimeTranslationRow_eq_ratCast (t : ℚ) :
    c13UpperPrimeTranslationRow t = (c13RationalPrimeTranslationRow t : ℝ) := by
  simp only [c13UpperPrimeTranslationRow, c13RationalPrimeTranslationRow,
    c13RationalPrimeTranslationEventRow]
  rw [c13PrimeTranslationRowFactor_eq_ratCast t 2,
    c13PrimeTranslationRowFactor_eq_ratCast t 3,
    c13PrimeTranslationRowFactor_eq_ratCast t 4,
    c13PrimeTranslationRowFactor_eq_ratCast t 5,
    c13PrimeTranslationRowFactor_eq_ratCast t 7,
    c13PrimeTranslationRowFactor_eq_ratCast t 8,
    c13PrimeTranslationRowFactor_eq_ratCast t 9,
    c13PrimeTranslationRowFactor_eq_ratCast t 11]
  push_cast
  norm_num

/-- All physical points at which the rational row signature can change. -/
def c13SupersolutionBreakpoints : List ℚ := [
  (1 : ℚ),
  (13 / 12 : ℚ),
  (39 / 35 : ℚ),
  (13 / 11 : ℚ),
  (6 / 5 : ℚ),
  (65 / 54 : ℚ),
  (26 / 21 : ℚ),
  (65 / 48 : ℚ),
  (104 / 75 : ℚ),
  (13 / 9 : ℚ),
  (3 / 2 : ℚ),
  (65 / 42 : ℚ),
  (39 / 25 : ℚ),
  (13 / 8 : ℚ),
  (5 / 3 : ℚ),
  (26 / 15 : ℚ),
  (13 / 7 : ℚ),
  (15 / 8 : ℚ),
  (39 / 20 : ℚ),
  (2 : ℚ),
  (13 / 6 : ℚ),
  (104 / 45 : ℚ),
  (12 / 5 : ℚ),
  (13 / 5 : ℚ),
  (65 / 24 : ℚ),
  (26 / 9 : ℚ),
  (3 : ℚ),
  (13 / 4 : ℚ),
  (10 / 3 : ℚ),
  (52 / 15 : ℚ),
  (18 / 5 : ℚ),
  (65 / 18 : ℚ),
  (15 / 4 : ℚ),
  (39 / 10 : ℚ),
  (4 : ℚ),
  (13 / 3 : ℚ),
  (9 / 2 : ℚ),
  (24 / 5 : ℚ),
  (5 : ℚ),
  (65 / 12 : ℚ),
  (45 / 8 : ℚ),
  (6 : ℚ),
  (13 / 2 : ℚ),
  (20 / 3 : ℚ),
  (104 / 15 : ℚ),
  (7 : ℚ),
  (15 / 2 : ℚ),
  (39 / 5 : ℚ),
  (8 : ℚ),
  (25 / 3 : ℚ),
  (42 / 5 : ℚ),
  (26 / 3 : ℚ),
  (9 : ℚ),
  (75 / 8 : ℚ),
  (48 / 5 : ℚ),
  (21 / 2 : ℚ),
  (54 / 5 : ℚ),
  (65 / 6 : ℚ),
  (11 : ℚ),
  (35 / 3 : ℚ),
  (12 : ℚ),
  (13 : ℚ)
]

/-- One exact rational sample from every open atomic cell. -/
def c13SupersolutionOpenSamples : List ℚ :=
  (c13SupersolutionBreakpoints.zip c13SupersolutionBreakpoints.tail).map
    (fun pair => (pair.1 + pair.2) / 2)

lemma c13SupersolutionBreakpoints_length :
    c13SupersolutionBreakpoints.length = 62 := by
  norm_num [c13SupersolutionBreakpoints]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c13SupersolutionBreakpoints_strict :
    c13SupersolutionBreakpoints.Pairwise (· < ·) := by
  rw [← List.isChain_iff_pairwise]
  norm_num [c13SupersolutionBreakpoints]

lemma c13SupersolutionOpenSamples_length :
    c13SupersolutionOpenSamples.length = 61 := by
  norm_num [c13SupersolutionOpenSamples, c13SupersolutionBreakpoints]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact computation on all 62 breakpoint rows. -/
theorem c13Supersolution_endpoint_rows_le :
    ∀ t ∈ c13SupersolutionBreakpoints,
      c13RationalPrimeTranslationRow t ≤
        (33223 / 10000 : ℚ) * c13SupersolutionHeightQ t := by
  norm_num [c13SupersolutionBreakpoints, c13RationalPrimeTranslationRow,
    c13RationalPrimeTranslationEventRow, c13RationalPrimeTranslationRowFactorQ,
    c13SupersolutionHeightQ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact computation on one representative of every open atomic row. -/
theorem c13Supersolution_open_rows_le :
    ∀ t ∈ c13SupersolutionOpenSamples,
      c13RationalPrimeTranslationRow t ≤
        (33223 / 10000 : ℚ) * c13SupersolutionHeightQ t := by
  norm_num [c13SupersolutionOpenSamples, c13SupersolutionBreakpoints,
    c13RationalPrimeTranslationRow, c13RationalPrimeTranslationEventRow,
    c13RationalPrimeTranslationRowFactorQ, c13SupersolutionHeightQ]

/-- The worst open-cell row is attained on `(39/25, 13/8)`. -/
theorem c13Supersolution_worst_sample_exact :
    c13RationalPrimeTranslationRow (637 / 400) =
      (33223 / 10000 : ℚ) * c13SupersolutionHeightQ (637 / 400) := by
  norm_num [c13RationalPrimeTranslationRow, c13RationalPrimeTranslationEventRow,
    c13RationalPrimeTranslationRowFactorQ, c13SupersolutionHeightQ]

/-- The exact rational envelope retains a positive margin below `10/3`. -/
theorem c13Supersolution_rational_margin :
    (10 / 3 : ℚ) - 33223 / 10000 = 331 / 30000 := by
  norm_num

lemma c13Supersolution_rational_max_lt_tenThird :
    (33223 / 10000 : ℚ) < 10 / 3 := by
  norm_num

/-- Any exact rational row certificate at one point transfers to the true
transcendental row with the strict `10/3` target. -/
theorem c13ActualPrimeTranslationRow_lt_tenThird_of_rationalRow_le
    (t : ℚ)
    (hRow : c13RationalPrimeTranslationRow t ≤
      (33223 / 10000 : ℚ) * c13SupersolutionHeightQ t) :
    c13ActualPrimeTranslationRow t <
      (10 / 3 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
  have hRowReal :
      (c13RationalPrimeTranslationRow t : ℝ) ≤
        (33223 / 10000 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
    calc
      (c13RationalPrimeTranslationRow t : ℝ) ≤
          (((33223 / 10000 : ℚ) * c13SupersolutionHeightQ t : ℚ) : ℝ) := by
        exact_mod_cast hRow
      _ = (33223 / 10000 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
        push_cast
        norm_num
  have hHeightReal : 0 < (c13SupersolutionHeightQ t : ℝ) := by
    exact_mod_cast c13SupersolutionHeightQ_pos t
  calc
    c13ActualPrimeTranslationRow t
        ≤ c13UpperPrimeTranslationRow t :=
      c13ActualPrimeTranslationRow_le_upper t
    _ = (c13RationalPrimeTranslationRow t : ℝ) :=
      c13UpperPrimeTranslationRow_eq_ratCast t
    _ ≤ (33223 / 10000 : ℝ) * (c13SupersolutionHeightQ t : ℝ) :=
      hRowReal
    _ < (10 / 3 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
      apply mul_lt_mul_of_pos_right _ hHeightReal
      norm_num

/-- The true row bound on every representative of an open atomic cell. -/
theorem c13ActualPrimeTranslationRow_openSamples_lt :
    ∀ t ∈ c13SupersolutionOpenSamples,
      c13ActualPrimeTranslationRow t <
        (10 / 3 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
  intro t ht
  exact c13ActualPrimeTranslationRow_lt_tenThird_of_rationalRow_le t
    (c13Supersolution_open_rows_le t ht)

/-- The true closed-support row bound on every rational breakpoint. -/
theorem c13ActualPrimeTranslationRow_breakpoints_lt :
    ∀ t ∈ c13SupersolutionBreakpoints,
      c13ActualPrimeTranslationRow t <
        (10 / 3 : ℝ) * (c13SupersolutionHeightQ t : ℝ) := by
  intro t ht
  exact c13ActualPrimeTranslationRow_lt_tenThird_of_rationalRow_le t
    (c13Supersolution_endpoint_rows_le t ht)

end RiemannCvs.PrimeTranslationSupersolution
