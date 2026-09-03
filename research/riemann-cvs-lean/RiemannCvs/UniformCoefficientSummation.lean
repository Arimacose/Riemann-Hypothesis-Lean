import Mathlib
import RiemannCvs.AsymptoticTailOperatorBound
import RiemannCvs.BoundaryWeylSchurTail

/-!
# Uniform coefficient summation for the dyadic shell recursion

The finite adjacent-compression layer supplies squared relative coefficients.
This file closes the scalar summation and product-reserve steps needed to use
summable coefficients through an infinite shell tower.

The squared coefficient envelope is

`q n = (1 / 30) * (1 / 2)^n`.

The recursive reserve-product theorem consumes amplitudes rather than squared
coefficients, so we use the slightly looser but summable envelope

`u n = (1 / 5) * (3 / 4)^n`.

The two envelopes satisfy `q n ≤ u n^2`, while the finite amplitude sums are
bounded by `4/5`.  Consequently every finite reserve product is at least
`1/5`.  The final theorems below combine this explicit floor with the existing
recursive shell-energy and finite-matrix-tower interfaces.

There are two complementary closures.  The explicit geometric envelope above
controls the full accumulated block-diagonal reference with the rational floor
`1/5`.  A sharper core-only Schur step works directly with any summable squared
coefficient sequence `q`; its infinite product `prod' n, (1-q n)` is strictly
positive.  This second route applies to the actual cutoff-13 adjacent-shell
envelope, which decays quadratically rather than geometrically.

The concrete full-prefix CvS source estimate is deliberately an explicit
hypothesis: the identification of an adjacent source-shell coefficient with a
recursive tower stage is an analytic/indexing obligation and is not replaced
here by an informal reindexing.
-/

open scoped BigOperators

namespace RiemannCvs.UniformCoefficientSummation

open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.V23BoundaryWeylMainline

noncomputable section

/-! ## Scalar envelopes -/

/-- The squared relative-coefficient envelope selected for the dyadic tower. -/
def oneThirtiethDyadicCoefficient (n : ℕ) : ℝ :=
  (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ n

/-- A summable amplitude envelope whose square dominates the coefficient. -/
def oneFifthThreeFourthsAmplitude (n : ℕ) : ℝ :=
  (1 / 5 : ℝ) * (3 / 4 : ℝ) ^ n

lemma half_pow_le_threeFourths_pow_sq (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ ((3 / 4 : ℝ) ^ n) ^ 2 := by
  have hPow : (1 / 2 : ℝ) ^ n ≤ (9 / 16 : ℝ) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  calc
    (1 / 2 : ℝ) ^ n ≤ (9 / 16 : ℝ) ^ n := hPow
    _ = ((3 / 4 : ℝ) ^ n) ^ 2 := by
      rw [pow_two, ← mul_pow]
      norm_num

theorem oneThirtiethDyadicCoefficient_nonnegative (n : ℕ) :
    0 ≤ oneThirtiethDyadicCoefficient n := by
  unfold oneThirtiethDyadicCoefficient
  positivity

theorem oneThirtiethDyadicCoefficient_le_one (n : ℕ) :
    oneThirtiethDyadicCoefficient n ≤ 1 := by
  unfold oneThirtiethDyadicCoefficient
  have hPow : (1 / 2 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ n ≤
        (1 / 30 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hPow (by norm_num)
    _ ≤ 1 := by norm_num

theorem oneFifthThreeFourthsAmplitude_nonnegative (n : ℕ) :
    0 ≤ oneFifthThreeFourthsAmplitude n := by
  unfold oneFifthThreeFourthsAmplitude
  positivity

theorem oneFifthThreeFourthsAmplitude_le_one (n : ℕ) :
    oneFifthThreeFourthsAmplitude n ≤ 1 := by
  unfold oneFifthThreeFourthsAmplitude
  have hPow : (3 / 4 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    (1 / 5 : ℝ) * (3 / 4 : ℝ) ^ n ≤
        (1 / 5 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hPow (by norm_num)
    _ ≤ 1 := by norm_num

/-- The one-thirtieth squared coefficient is dominated by the amplitude square. -/
theorem oneThirtieth_dyadic_le_summableAmplitude_sq (n : ℕ) :
    oneThirtiethDyadicCoefficient n ≤
      (oneFifthThreeFourthsAmplitude n) ^ 2 := by
  unfold oneThirtiethDyadicCoefficient oneFifthThreeFourthsAmplitude
  have hCoeff : (1 / 30 : ℝ) ≤ (1 / 5 : ℝ) ^ 2 := by
    norm_num
  have hDyadic := half_pow_le_threeFourths_pow_sq n
  have hScaled :
      (1 / 30 : ℝ) * (1 / 2 : ℝ) ^ n ≤
        (1 / 5 : ℝ) ^ 2 * ((3 / 4 : ℝ) ^ n) ^ 2 :=
    mul_le_mul hCoeff hDyadic (by positivity) (by positivity)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hScaled

/-! ## Infinite sums and finite tail bounds -/

theorem summable_oneThirtiethDyadicCoefficient :
    Summable oneThirtiethDyadicCoefficient := by
  unfold oneThirtiethDyadicCoefficient
  exact (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 30 : ℝ)

theorem tsum_oneThirtiethDyadicCoefficient :
    ∑' n : ℕ, oneThirtiethDyadicCoefficient n = (1 / 15 : ℝ) := by
  unfold oneThirtiethDyadicCoefficient
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

theorem summable_oneFifthThreeFourthsAmplitude :
    Summable oneFifthThreeFourthsAmplitude := by
  unfold oneFifthThreeFourthsAmplitude
  exact (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).mul_left (1 / 5 : ℝ)

theorem tsum_oneFifthThreeFourthsAmplitude :
    ∑' n : ℕ, oneFifthThreeFourthsAmplitude n = (4 / 5 : ℝ) := by
  unfold oneFifthThreeFourthsAmplitude
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)]
  norm_num

theorem oneFifth_threeFourths_partialSum_le_fourFifths (n : ℕ) :
    (∑ i ∈ Finset.range n, oneFifthThreeFourthsAmplitude i) ≤
      (4 / 5 : ℝ) := by
  have hSummable :
      Summable (fun i : ℕ => oneFifthThreeFourthsAmplitude i) :=
    summable_oneFifthThreeFourthsAmplitude
  have hNonnegative : ∀ i : ℕ, 0 ≤ oneFifthThreeFourthsAmplitude i :=
    oneFifthThreeFourthsAmplitude_nonnegative
  have hFinite := hSummable.sum_le_tsum (Finset.range n)
    (fun i _hi => hNonnegative i)
  rw [tsum_oneFifthThreeFourthsAmplitude] at hFinite
  exact hFinite

theorem oneThirtieth_dyadic_partialSum_le_oneFifteenth (n : ℕ) :
    (∑ i ∈ Finset.range n, oneThirtiethDyadicCoefficient i) ≤
      (1 / 15 : ℝ) := by
  have hSummable :
      Summable (fun i : ℕ => oneThirtiethDyadicCoefficient i) :=
    summable_oneThirtiethDyadicCoefficient
  have hNonnegative : ∀ i : ℕ, 0 ≤ oneThirtiethDyadicCoefficient i :=
    oneThirtiethDyadicCoefficient_nonnegative
  have hFinite := hSummable.sum_le_tsum (Finset.range n)
    (fun i _hi => hNonnegative i)
  rw [tsum_oneThirtiethDyadicCoefficient] at hFinite
  exact hFinite

theorem oneFifth_threeFourths_tail_sum (n : ℕ) :
    (∑' i : ℕ, oneFifthThreeFourthsAmplitude (n + i)) =
      (4 / 5 : ℝ) * (3 / 4 : ℝ) ^ n := by
  unfold oneFifthThreeFourthsAmplitude
  rw [tsum_mul_left]
  simp_rw [pow_add]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)]
  ring

theorem oneThirtieth_dyadic_tail_sum (n : ℕ) :
    (∑' i : ℕ, oneThirtiethDyadicCoefficient (n + i)) =
      (1 / 15 : ℝ) * (1 / 2 : ℝ) ^ n := by
  unfold oneThirtiethDyadicCoefficient
  rw [tsum_mul_left]
  simp_rw [pow_add]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)]
  ring

/-! ## Direct summable-coefficient product reserve -/

/-- A squared relative coefficient `q` retains `1-q` of the old core energy.

Unlike `sqShell_oneSubReserve`, this estimate does not retain the newly
added tail energy.  In exchange, it consumes `q` itself rather than `sqrt q`,
so a summable `O(n⁻²)` coefficient sequence gives a positive infinite reserve. -/
theorem relativeCoefficient_oneSubCoreReserve
    (core tail cross q : ℝ)
    (hCore : 0 ≤ core)
    (hTail : 0 ≤ tail)
    (hq : 0 ≤ q)
    (hRelative : cross ^ 2 ≤ q * core * tail) :
    (1 - q) * core ≤ core + 2 * cross + tail := by
  have hScaledCore : 0 ≤ q * core := mul_nonneg hq hCore
  have hGlue := twoBlockEnergy_nonnegative
    (q * core) tail cross hScaledCore hTail hRelative
  nlinarith

/-- Iterating the core-only Schur reserve keeps the finite product of the
actual squared coefficients in front of the initial energy. -/
theorem recursiveShellEnergy_ge_coefficientReserveProduct
    (energy tail cross q : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ q n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (∏ i ∈ Finset.range n, (1 - q i)) * energy 0 ≤ energy n := by
  have hEnergyNonnegative : ∀ n, 0 ≤ energy n :=
    recursiveShellEnergy_nonnegative_nat
      energy tail cross q hBase hTail hQOne hRelative hStep
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hOneSubQ : 0 ≤ 1 - q n := sub_nonneg.mpr (hQOne n)
      have hIHScaled :
          (1 - q n) *
              ((∏ i ∈ Finset.range n, (1 - q i)) * energy 0) ≤
            (1 - q n) * energy n :=
        mul_le_mul_of_nonneg_left ih hOneSubQ
      have hReserve :
          (1 - q n) * energy n ≤ energy (n + 1) := by
        rw [hStep n]
        exact relativeCoefficient_oneSubCoreReserve
          (energy n) (tail n) (cross n) (q n)
          (hEnergyNonnegative n) (hTail n) (hQNonnegative n) (hRelative n)
      calc
        (∏ i ∈ Finset.range (n + 1), (1 - q i)) * energy 0 =
            (1 - q n) *
              ((∏ i ∈ Finset.range n, (1 - q i)) * energy 0) := by
                rw [Finset.prod_range_succ]
                ring
        _ ≤ (1 - q n) * energy n := hIHScaled
        _ ≤ energy (n + 1) := hReserve

private theorem summable_nonnegative_norm_neg
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hSummable : Summable q) :
    Summable (fun n => ‖(-q n : ℝ)‖) := by
  simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (hQNonnegative _)]
    using hSummable

/-- Summability of nonnegative coefficients makes the reserve factors
`1-q n` multipliable. -/
theorem summableCoefficient_reserveMultipliable
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hSummable : Summable q) :
    Multipliable (fun n => 1 - q n) := by
  have hNorm := summable_nonnegative_norm_neg q hQNonnegative hSummable
  simpa only [sub_eq_add_neg] using
    (multipliable_one_add_of_summable hNorm)

/-- If every coefficient is strictly below one, the reserve infinite product
cannot vanish. -/
theorem summableCoefficient_reserveProduct_ne_zero
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q) :
    (∏' n : ℕ, (1 - q n)) ≠ 0 := by
  have hNorm := summable_nonnegative_norm_neg q hQNonnegative hSummable
  simpa only [sub_eq_add_neg] using
    (tprod_one_add_ne_zero_of_summable
      (f := fun n : ℕ => -q n)
      (fun n => by linarith [hQOne n]) hNorm)

/-- The reserve infinite product of a summable sequence in `[0,1)` is
strictly positive. -/
theorem summableCoefficient_reserveProduct_pos
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q) :
    0 < ∏' n : ℕ, (1 - q n) := by
  have hMultipliable :=
    summableCoefficient_reserveMultipliable q hQNonnegative hSummable
  have hTendsto := hMultipliable.tendsto_prod_tprod_nat
  have hNonnegative : 0 ≤ ∏' n : ℕ, (1 - q n) := by
    apply ge_of_tendsto hTendsto
    exact Filter.Eventually.of_forall (fun n =>
      Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hQOne i).le))
  exact lt_of_le_of_ne hNonnegative
    (summableCoefficient_reserveProduct_ne_zero
      q hQNonnegative hQOne hSummable).symm

/-- The positive infinite product is a uniform lower bound for every finite
reserve product. -/
theorem summableCoefficient_reserveProduct_le_finite
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q) :
    ∀ n,
      (∏' i : ℕ, (1 - q i)) ≤
        ∏ i ∈ Finset.range n, (1 - q i) := by
  have hMultipliable :=
    summableCoefficient_reserveMultipliable q hQNonnegative hSummable
  have hAntitone : Antitone
      (fun n => ∏ i ∈ Finset.range n, (1 - q i)) :=
    antitone_nat_of_succ_le (fun n => by
      rw [Finset.prod_range_succ]
      exact mul_le_of_le_one_right
        (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hQOne i).le))
        (by linarith [hQNonnegative n]))
  intro n
  exact hAntitone.le_of_tendsto hMultipliable.tendsto_prod_tprod_nat n

/-- Abstract existence form of the uniform product reserve. -/
theorem exists_pos_reserveFloor_of_summableCoefficient
    (q : ℕ → ℝ)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q) :
    ∃ reserveFloor : ℝ,
      0 < reserveFloor ∧
        ∀ n, reserveFloor ≤ ∏ i ∈ Finset.range n, (1 - q i) := by
  refine ⟨∏' i : ℕ, (1 - q i), ?_, ?_⟩
  · exact summableCoefficient_reserveProduct_pos
      q hQNonnegative hQOne hSummable
  · exact summableCoefficient_reserveProduct_le_finite
      q hQNonnegative hQOne hSummable

/-- The infinite reserve product itself uniformly controls every finite
recursive energy. -/
theorem recursiveShellEnergy_ge_summableCoefficientTprod
    (energy tail cross q : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ q n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (∏' i : ℕ, (1 - q i)) * energy 0 ≤ energy n := by
  have hFinite := recursiveShellEnergy_ge_coefficientReserveProduct
    energy tail cross q hBase hTail hQNonnegative (fun n => (hQOne n).le)
    hRelative hStep
  intro n
  have hFloor := summableCoefficient_reserveProduct_le_finite
    q hQNonnegative hQOne hSummable n
  exact (mul_le_mul_of_nonneg_right hFloor hBase).trans (hFinite n)

/-- A convergent recursive shell energy retains the positive infinite-product
fraction of its initial energy. -/
theorem recursiveShellEnergy_limit_ge_summableCoefficientTprod
    (energy tail cross q : ℕ → ℝ)
    (limit : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ q n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    (∏' i : ℕ, (1 - q i)) * energy 0 ≤ limit := by
  apply ge_of_tendsto hTendsto
  exact Filter.Eventually.of_forall
    (recursiveShellEnergy_ge_summableCoefficientTprod
      energy tail cross q hBase hTail hQNonnegative hQOne hSummable
      hRelative hStep)

/-- A positive initial energy therefore has a positive closed limit whenever
the actual squared stage coefficients are summable. -/
theorem recursiveShellEnergy_limit_pos_of_summableCoefficient
    (energy tail cross q : ℕ → ℝ)
    (limit : ℝ)
    (hBase : 0 < energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hQNonnegative : ∀ n, 0 ≤ q n)
    (hQOne : ∀ n, q n < 1)
    (hSummable : Summable q)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ q n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 < limit := by
  have hLower := recursiveShellEnergy_limit_ge_summableCoefficientTprod
    energy tail cross q limit (le_of_lt hBase) hTail hQNonnegative hQOne
    hSummable hRelative hStep hTendsto
  exact (mul_pos
    (summableCoefficient_reserveProduct_pos
      q hQNonnegative hQOne hSummable) hBase).trans_le hLower

/-! ## The actual cutoff-13 adjacent-shell envelope -/

theorem c13DyadicRelativeEnvelope_lt_one (n : ℕ) :
    c13DyadicRelativeEnvelope n < 1 := by
  have hGap : 0 < c13DyadicGapLower n := c13DyadicGapLower_pos n
  have hNumeratorGap : (481 / 100 : ℝ) < c13DyadicGapLower n := by
    unfold c13DyadicGapLower
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  unfold c13DyadicRelativeEnvelope
  rw [div_lt_one (sq_pos_of_pos hGap)]
  exact (sq_lt_sq₀ (by norm_num) hGap.le).2 hNumeratorGap

/-- Every finite cutoff-13 coefficient sum is bounded by the convergent total
sum.  This is the direct uniform partial-sum statement. -/
theorem c13DyadicRelativeEnvelope_partialSum_le_tsum (n : ℕ) :
    (∑ i ∈ Finset.range n, c13DyadicRelativeEnvelope i) ≤
      ∑' i : ℕ, c13DyadicRelativeEnvelope i := by
  exact summable_c13DyadicRelativeEnvelope.sum_le_tsum (Finset.range n)
    (fun i _ => c13DyadicRelativeEnvelope_nonneg i)

/-- The true cutoff-13 `O(n⁻²)` coefficient envelope has a strictly positive
infinite reserve product. -/
theorem c13DyadicReserveProduct_pos :
    0 < ∏' n : ℕ, (1 - c13DyadicRelativeEnvelope n) := by
  exact summableCoefficient_reserveProduct_pos
    c13DyadicRelativeEnvelope c13DyadicRelativeEnvelope_nonneg
    c13DyadicRelativeEnvelope_lt_one summable_c13DyadicRelativeEnvelope

/-- The true cutoff-13 infinite reserve is a uniform lower bound at every
finite adjacent-shell depth. -/
theorem c13DyadicReserveProduct_le_finite :
    ∀ n,
      (∏' i : ℕ, (1 - c13DyadicRelativeEnvelope i)) ≤
        ∏ i ∈ Finset.range n, (1 - c13DyadicRelativeEnvelope i) := by
  exact summableCoefficient_reserveProduct_le_finite
    c13DyadicRelativeEnvelope c13DyadicRelativeEnvelope_nonneg
    c13DyadicRelativeEnvelope_lt_one summable_c13DyadicRelativeEnvelope

/-- The scalar uniform coefficient summation/product obligation for the
cutoff-13 adjacent-shell envelope is closed without replacing it by a
geometric majorant. -/
theorem c13Dyadic_exists_pos_uniformReserveFloor :
    ∃ reserveFloor : ℝ,
      0 < reserveFloor ∧
        ∀ n,
          reserveFloor ≤
            ∏ i ∈ Finset.range n, (1 - c13DyadicRelativeEnvelope i) := by
  exact exists_pos_reserveFloor_of_summableCoefficient
    c13DyadicRelativeEnvelope c13DyadicRelativeEnvelope_nonneg
    c13DyadicRelativeEnvelope_lt_one summable_c13DyadicRelativeEnvelope

/-- A genuine stage-relative cutoff-13 coefficient bound retains the actual
positive infinite-product fraction of the initial core energy.  The stage
identification remains an explicit source-side premise. -/
theorem c13Dyadic_stageRelative_initialReserve
    (energy tail cross : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        c13DyadicRelativeEnvelope n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (∏' i : ℕ, (1 - c13DyadicRelativeEnvelope i)) * energy 0 ≤
        energy n := by
  exact recursiveShellEnergy_ge_summableCoefficientTprod
    energy tail cross c13DyadicRelativeEnvelope hBase hTail
    c13DyadicRelativeEnvelope_nonneg c13DyadicRelativeEnvelope_lt_one
    summable_c13DyadicRelativeEnvelope hStageRelative hStep

/-- The direct cutoff-13 coefficient product survives passage to any closed
limit of the recursive energy. -/
theorem c13Dyadic_limit_ge_initialReserve
    (energy tail cross : ℕ → ℝ) (limit : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        c13DyadicRelativeEnvelope n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    (∏' i : ℕ, (1 - c13DyadicRelativeEnvelope i)) * energy 0 ≤
      limit := by
  exact recursiveShellEnergy_limit_ge_summableCoefficientTprod
    energy tail cross c13DyadicRelativeEnvelope limit hBase hTail
    c13DyadicRelativeEnvelope_nonneg c13DyadicRelativeEnvelope_lt_one
    summable_c13DyadicRelativeEnvelope hStageRelative hStep hTendsto

/-- A positive initial energy and a genuine cutoff-13 stage-relative bound
force the closed recursive limit to be positive. -/
theorem c13Dyadic_limit_pos
    (energy tail cross : ℕ → ℝ) (limit : ℝ)
    (hBase : 0 < energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        c13DyadicRelativeEnvelope n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 < limit := by
  exact recursiveShellEnergy_limit_pos_of_summableCoefficient
    energy tail cross c13DyadicRelativeEnvelope limit hBase hTail
    c13DyadicRelativeEnvelope_nonneg c13DyadicRelativeEnvelope_lt_one
    summable_c13DyadicRelativeEnvelope hStageRelative hStep hTendsto

/-! ## Reserve-product floor -/

/-- Every finite reserve product has the explicit floor `1/5`. -/
theorem oneThirtiethDyadic_reserveProduct_ge_oneFifth :
    ∀ n,
      (1 / 5 : ℝ) ≤
        ∏ i ∈ Finset.range n, (1 - oneFifthThreeFourthsAmplitude i) := by
  intro n
  have h := reserveProduct_ge_one_sub_of_partialSumBound
    oneFifthThreeFourthsAmplitude (4 / 5 : ℝ)
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    oneFifth_threeFourths_partialSum_le_fourFifths n
  norm_num at h
  exact h

theorem oneThirtiethDyadic_reserveProduct_pos :
    ∀ n,
      0 < ∏ i ∈ Finset.range n, (1 - oneFifthThreeFourthsAmplitude i) := by
  intro n
  exact reserveProduct_pos_of_partialSum_lt_one
    oneFifthThreeFourthsAmplitude (4 / 5 : ℝ)
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    oneFifth_threeFourths_partialSum_le_fourFifths
    (by norm_num : (4 / 5 : ℝ) < 1) n

/-! ## Recursive shell-energy closure -/

/--
Upgrade a stage-relative squared-coefficient estimate to the summable
amplitude-square estimate used by the reserve-product recursion.
-/
theorem stageRelative_le_oneFifthThreeFourthsAmplitude_sq
    (energy tail cross : ℕ → ℝ)
    (hEnergy : ∀ n, 0 ≤ energy n)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n * energy n * tail n) :
    ∀ n,
      (cross n) ^ 2 ≤
        (oneFifthThreeFourthsAmplitude n) ^ 2 * energy n * tail n := by
  intro n
  have hReference : 0 ≤ energy n * tail n :=
    mul_nonneg (hEnergy n) (hTail n)
  have hScaled :=
    mul_le_mul_of_nonneg_right
      (oneThirtieth_dyadic_le_summableAmplitude_sq n) hReference
  calc
    (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n * energy n * tail n :=
      hStageRelative n
    _ = oneThirtiethDyadicCoefficient n * (energy n * tail n) := by
      ring
    _ ≤ (oneFifthThreeFourthsAmplitude n) ^ 2 *
        (energy n * tail n) := hScaled
    _ = (oneFifthThreeFourthsAmplitude n) ^ 2 * energy n * tail n := by
      ring

theorem oneThirtiethDyadic_stageRelative_blockSumReserve
    (energy tail cross : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (1 / 5 : ℝ) *
          (energy 0 + ∑ i ∈ Finset.range n, tail i) ≤ energy n := by
  have hEnergyNonnegative : ∀ n, 0 ≤ energy n :=
    recursiveShellEnergy_nonnegative_nat
      energy tail cross oneThirtiethDyadicCoefficient
      hBase hTail oneThirtiethDyadicCoefficient_le_one
      hStageRelative hStep
  have hRelativeAmplitude :=
    stageRelative_le_oneFifthThreeFourthsAmplitude_sq
      energy tail cross hEnergyNonnegative hTail hStageRelative
  intro n
  exact recursiveShellEnergy_ge_reserveFloor_mul_blockSum
    energy tail cross oneFifthThreeFourthsAmplitude (1 / 5 : ℝ)
    hBase hTail
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    hRelativeAmplitude hStep
    oneThirtiethDyadic_reserveProduct_ge_oneFifth n

theorem oneThirtiethDyadic_recursiveBlockEnergy_blockSumReserve
    (base : ℝ) (tail cross : ℕ → ℝ)
    (hBase : 0 ≤ base)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n *
          recursiveBlockEnergy base tail cross n * tail n) :
    ∀ n,
      (1 / 5 : ℝ) *
          (base + ∑ i ∈ Finset.range n, tail i) ≤
        recursiveBlockEnergy base tail cross n := by
  intro n
  have h := oneThirtiethDyadic_stageRelative_blockSumReserve
    (recursiveBlockEnergy base tail cross) tail cross
    (by simpa using hBase) hTail hStageRelative
    (fun j => recursiveBlockEnergy_succ base tail cross j) n
  simpa using h

/-! ## Next-shell and closed-limit adapters -/

/--
If a next-shell source estimate is measured against the full historical
block-diagonal reference, the `1/5` product floor converts it to the actual
recursive core energy.  The budget condition is intentionally written in the
same multiplication-only form consumed by the existing reserve adapter.
-/
theorem oneThirtiethDyadic_nextShell_relative
    (energy tail cross : ℕ → ℝ) (n : ℕ)
    (newTail newCross budget rho : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ j, 0 ≤ tail j)
    (hStageRelative : ∀ j,
      (cross j) ^ 2 ≤
        oneThirtiethDyadicCoefficient j * energy j * tail j)
    (hStep : ∀ j,
      energy (j + 1) = energy j + 2 * cross j + tail j)
    (hNewTail : 0 ≤ newTail)
    (hRho : 0 ≤ rho)
    (hBudget : budget ≤ rho * (1 / 5 : ℝ))
    (hNewCross :
      newCross ^ 2 ≤
        budget * (energy 0 + ∑ i ∈ Finset.range n, tail i) * newTail) :
    newCross ^ 2 ≤ rho * energy n * newTail := by
  exact relativeShell_of_recursiveBlockSumReserve
    energy tail cross oneFifthThreeFourthsAmplitude n
    newTail newCross (1 / 5 : ℝ) budget rho
    hBase hTail
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    (stageRelative_le_oneFifthThreeFourthsAmplitude_sq
      energy tail cross
      (recursiveShellEnergy_nonnegative_nat
        energy tail cross oneThirtiethDyadicCoefficient
        hBase hTail oneThirtiethDyadicCoefficient_le_one
        hStageRelative hStep)
      hTail hStageRelative)
    hStep
    oneThirtiethDyadic_reserveProduct_ge_oneFifth
    hNewTail hRho hBudget hNewCross

theorem oneThirtiethDyadic_limit_ge_initialReserve
    (energy tail cross : ℕ → ℝ) (limit : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    (1 / 5 : ℝ) * energy 0 ≤ limit := by
  exact recursiveShellEnergy_limit_ge_of_reserveProductLowerBound
    energy tail cross oneFifthThreeFourthsAmplitude (1 / 5 : ℝ) limit
    hBase hTail
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    (stageRelative_le_oneFifthThreeFourthsAmplitude_sq
      energy tail cross
      (recursiveShellEnergy_nonnegative_nat
        energy tail cross oneThirtiethDyadicCoefficient
        hBase hTail oneThirtiethDyadicCoefficient_le_one
        hStageRelative hStep)
      hTail hStageRelative)
    hStep oneThirtiethDyadic_reserveProduct_ge_oneFifth hTendsto

theorem oneThirtiethDyadic_limit_pos
    (energy tail cross : ℕ → ℝ) (limit : ℝ)
    (hBase : 0 < energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hStageRelative : ∀ n,
      (cross n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 < limit := by
  exact recursiveShellEnergy_limit_pos_of_reserveProductLowerBound
    energy tail cross oneFifthThreeFourthsAmplitude (1 / 5 : ℝ) limit
    (by norm_num) hBase hTail
    oneFifthThreeFourthsAmplitude_nonnegative
    oneFifthThreeFourthsAmplitude_le_one
    (stageRelative_le_oneFifthThreeFourthsAmplitude_sq
      energy tail cross
      (recursiveShellEnergy_nonnegative_nat
        energy tail cross oneThirtiethDyadicCoefficient
        (le_of_lt hBase) hTail oneThirtiethDyadicCoefficient_le_one
        hStageRelative hStep)
      hTail hStageRelative)
    hStep oneThirtiethDyadic_reserveProduct_ge_oneFifth hTendsto

/-! ## Honest finite-matrix-tower adapter -/

section FiniteMatrixTower

variable {I S : ℕ → Type*}
variable [∀ n, Fintype (I n)] [∀ n, Fintype (S n)]

/--
The scalar result applied to any compatible finite matrix tower.  The theorem
does not manufacture `hStageRelative`: that premise is exactly the source-side
uniform coefficient estimate that must be proved for a concrete CvS tower.
-/
theorem finiteMatrixTower_limit_pos_of_oneThirtiethDyadic
    (A : ∀ n, Matrix (I n) (I n) ℝ)
    (x : ∀ n, I n → ℝ) (y : ∀ n, S n → ℝ)
    (split : ∀ n, I (n + 1) ≃ I n ⊕ S n)
    (hVector : ∀ n,
      finiteVectorPullback (split n) (x (n + 1)) =
        finiteMatrixBlockVector (x n) (y n))
    (hCore : ∀ n i j,
      finiteMatrixPullback (split n) (A (n + 1))
          (Sum.inl i) (Sum.inl j) = A n i j)
    (hBase : 0 < finiteMatrixTowerEnergy A x 0)
    (hTail : ∀ n, 0 ≤ finiteMatrixTowerTailEnergy A y split n)
    (hStageRelative : ∀ n,
      (finiteMatrixTowerCrossEnergy A x y split n) ^ 2 ≤
        oneThirtiethDyadicCoefficient n *
          finiteMatrixTowerEnergy A x n *
          finiteMatrixTowerTailEnergy A y split n)
    (limit : ℝ)
    (hTendsto :
      Filter.Tendsto (finiteMatrixTowerEnergy A x)
        Filter.atTop (nhds limit)) :
    0 < limit := by
  let energy := finiteMatrixTowerEnergy A x
  let tail := finiteMatrixTowerTailEnergy A y split
  let cross := finiteMatrixTowerCrossEnergy A x y split
  have hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n := by
    intro n
    exact finiteMatrixTowerEnergy_succ A x y split hVector hCore n
  have hResult := oneThirtiethDyadic_limit_pos
    energy tail cross limit hBase hTail hStageRelative hStep hTendsto
  exact hResult

/-- The finite-matrix-tower adapter for the actual summable cutoff-13
coefficient envelope.  As above, the theorem deliberately requires the full
prefix-to-next-shell stage estimate rather than conflating it with the proved
adjacent-shell-to-adjacent-shell bound. -/
theorem finiteMatrixTower_limit_pos_of_c13DyadicRelativeEnvelope
    (A : ∀ n, Matrix (I n) (I n) ℝ)
    (x : ∀ n, I n → ℝ) (y : ∀ n, S n → ℝ)
    (split : ∀ n, I (n + 1) ≃ I n ⊕ S n)
    (hVector : ∀ n,
      finiteVectorPullback (split n) (x (n + 1)) =
        finiteMatrixBlockVector (x n) (y n))
    (hCore : ∀ n i j,
      finiteMatrixPullback (split n) (A (n + 1))
          (Sum.inl i) (Sum.inl j) = A n i j)
    (hBase : 0 < finiteMatrixTowerEnergy A x 0)
    (hTail : ∀ n, 0 ≤ finiteMatrixTowerTailEnergy A y split n)
    (hStageRelative : ∀ n,
      (finiteMatrixTowerCrossEnergy A x y split n) ^ 2 ≤
        c13DyadicRelativeEnvelope n *
          finiteMatrixTowerEnergy A x n *
          finiteMatrixTowerTailEnergy A y split n)
    (limit : ℝ)
    (hTendsto :
      Filter.Tendsto (finiteMatrixTowerEnergy A x)
        Filter.atTop (nhds limit)) :
    0 < limit := by
  let energy := finiteMatrixTowerEnergy A x
  let tail := finiteMatrixTowerTailEnergy A y split
  let cross := finiteMatrixTowerCrossEnergy A x y split
  have hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n := by
    intro n
    exact finiteMatrixTowerEnergy_succ A x y split hVector hCore n
  exact c13Dyadic_limit_pos
    energy tail cross limit hBase hTail hStageRelative hStep hTendsto

end FiniteMatrixTower

end

end RiemannCvs.UniformCoefficientSummation
