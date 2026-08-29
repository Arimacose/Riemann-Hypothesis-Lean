import RiemannCvs.BesselJ0IntegralRepresentation

namespace RiemannCvs.BesselJ0Dlmf

open Real

/-- The concrete repository function entering the DLMF remainder interface now
has a proved real oscillatory integral representation. -/
theorem concreteJ0_integral_representation (x : ℝ) :
    BesselJ0Series.besselJ0 x =
      Real.pi⁻¹ * ∫ t in (0 : ℝ)..Real.pi,
        Real.cos (x * Real.sin t) :=
  BesselJ0IntegralRepresentation.besselJ0_integral_representation x

/-!
# The order-zero DLMF large-argument remainder interface

For `ν = 0`, DLMF 10.17.1 and 10.17.3 split the Hankel expansion into
even and odd coefficient series. Keeping `a₀` in the even series and `a₁`
in the odd series leaves first-neglected-term bounds `|a₂| / z²` and
`|a₃| / z³`. This module formalizes the coefficient specialization and the
elementary step that combines those two remainder bounds into the exact
one-sided absolute-error interface used by `ExteriorLogMomentTransfer`.

The analytic construction of the two remainders is deliberately kept as the
next theorem boundary; all coefficient arithmetic and trigonometric error
combination below are proof-complete.
-/

/-- DLMF 10.17.1 specialized to order zero. -/
noncomputable def orderZeroCoefficient (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, -(2 * (j : ℝ) + 1) ^ 2) /
    ((k.factorial : ℝ) * 8 ^ k)

@[simp]
theorem orderZeroCoefficient_zero : orderZeroCoefficient 0 = 1 := by
  norm_num [orderZeroCoefficient]

@[simp]
theorem orderZeroCoefficient_one : orderZeroCoefficient 1 = -(1 / 8 : ℝ) := by
  norm_num [orderZeroCoefficient]

@[simp]
theorem orderZeroCoefficient_two : orderZeroCoefficient 2 = (9 / 128 : ℝ) := by
  norm_num [orderZeroCoefficient]

@[simp]
theorem orderZeroCoefficient_three :
    orderZeroCoefficient 3 = -(75 / 1024 : ℝ) := by
  norm_num [orderZeroCoefficient]

/-- The leading scale in DLMF 10.17.3 at order zero. -/
noncomputable def leadingScale (z : ℝ) : ℝ :=
  sqrt (2 / (π * z))

/-- The leading cosine approximation in DLMF 10.17.3 at order zero. -/
noncomputable def leadingCosine (z : ℝ) : ℝ :=
  leadingScale z * cos (z - π / 4)

/-- The combined first-neglected-term envelope after keeping `a₀` and `a₁`. -/
noncomputable def firstRemainderEnvelope (z : ℝ) : ℝ :=
  leadingScale z *
    (1 / (8 * z) + 9 / (128 * z ^ 2) + 75 / (1024 * z ^ 3))

theorem leadingScale_nonneg (z : ℝ) : 0 ≤ leadingScale z := by
  exact sqrt_nonneg _

theorem firstRemainderEnvelope_nonneg {z : ℝ} (hz : 0 < z) :
    0 ≤ firstRemainderEnvelope z := by
  unfold firstRemainderEnvelope
  apply mul_nonneg (leadingScale_nonneg z)
  have h8z : 0 ≤ 8 * z := mul_nonneg (by norm_num) hz.le
  have h128z2 : 0 ≤ 128 * z ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg z)
  have h1024z3 : 0 ≤ 1024 * z ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hz.le 3)
  exact add_nonneg
    (add_nonneg (div_nonneg (by norm_num) h8z)
      (div_nonneg (by norm_num) h128z2))
    (div_nonneg (by norm_num) h1024z3)

/-- The proof-complete algebraic specialization of the real-argument DLMF
remainder rule. Once the even and odd remainders for the concrete series are
constructed with the first-neglected-term bounds, this theorem gives precisely
the absolute error consumed by the PSWF source adapter. -/
theorem leadingCosine_error_of_separated_remainders
    (z evenRemainder oddRemainder : ℝ)
    (hz : 0 < z)
    (hExpansion :
      BesselJ0Series.besselJ0 z =
        leadingScale z *
          (cos (z - π / 4) * (1 + evenRemainder) -
            sin (z - π / 4) * (-(1 / (8 * z)) + oddRemainder)))
    (hEvenRemainder :
      |evenRemainder| ≤ 9 / (128 * z ^ 2))
    (hOddRemainder :
      |oddRemainder| ≤ 75 / (1024 * z ^ 3)) :
    |leadingCosine z - BesselJ0Series.besselJ0 z| ≤
      firstRemainderEnvelope z := by
  let w : ℝ := z - π / 4
  let scale : ℝ := leadingScale z
  let q : ℝ := 1 / (8 * z)
  have hscale : 0 ≤ scale := by
    exact leadingScale_nonneg z
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hEvenEnvelope : 0 ≤ 9 / (128 * z ^ 2) := by positivity
  have hOddEnvelope : 0 ≤ 75 / (1024 * z ^ 3) := by positivity
  have hCosEven : |cos w * evenRemainder| ≤ |evenRemainder| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg evenRemainder) (abs_cos_le_one w)
  have hSinQ : |sin w * q| ≤ q := by
    rw [abs_mul, abs_of_nonneg hq]
    exact mul_le_of_le_one_left hq (abs_sin_le_one w)
  have hSinOdd : |sin w * oddRemainder| ≤ |oddRemainder| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg oddRemainder) (abs_sin_le_one w)
  have hInner :
      |-(cos w * evenRemainder) - sin w * q +
          sin w * oddRemainder| ≤
        1 / (8 * z) + 9 / (128 * z ^ 2) + 75 / (1024 * z ^ 3) := by
    calc
      |-(cos w * evenRemainder) - sin w * q +
          sin w * oddRemainder| ≤
          |-(cos w * evenRemainder) - sin w * q| +
            |sin w * oddRemainder| := abs_add_le _ _
      _ ≤ (|cos w * evenRemainder| + |sin w * q|) +
            |sin w * oddRemainder| := by
          gcongr
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (-(cos w * evenRemainder)) (-(sin w * q)))
      _ ≤ (|evenRemainder| + q) + |oddRemainder| := by
          gcongr
      _ ≤ (9 / (128 * z ^ 2) + q) + 75 / (1024 * z ^ 3) := by
          gcongr
      _ = 1 / (8 * z) + 9 / (128 * z ^ 2) + 75 / (1024 * z ^ 3) := by
          dsimp [q]
          ring
  have hDifference :
      leadingCosine z - BesselJ0Series.besselJ0 z =
        scale * (-(cos w * evenRemainder) - sin w * q +
          sin w * oddRemainder) := by
    rw [hExpansion]
    dsimp [leadingCosine, scale, w, q]
    ring
  rw [hDifference, abs_mul, abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_left hInner hscale

/-- A single predicate naming the exact global real-axis theorem still needed
from the analytic DLMF development. -/
def HasFirstDlmfRemainderBound : Prop :=
  ∀ z : ℝ, 0 < z →
    |leadingCosine z - BesselJ0Series.besselJ0 z| ≤
      firstRemainderEnvelope z

end RiemannCvs.BesselJ0Dlmf
