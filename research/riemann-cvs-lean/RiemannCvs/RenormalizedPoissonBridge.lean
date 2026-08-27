import Mathlib

/-!
# A renormalized Poisson bridge for nonzero boundary values

For an even function, Poisson summation relates the positive-integer sums by

`S_f(u) + f(0)/2 = u⁻¹ * (S_fhat(u⁻¹) + fhat(0)/2)`.

The usual map `E f(u) = sqrt(u) * S_f(u)` intertwines Fourier grading with
multiplicative inversion only after imposing `f(0) = fhat(0) = 0`.  Without
those vanishing conditions there is a one-parameter family of corrected maps.

Writing `r = sqrt(u)`, define

`T_a(f; r) = r*S_f + a*r*f(0) + (a-1/2)*r⁻¹*fhat(0)`.

Poisson summation implies `T_a(fhat; r⁻¹) = T_a(f; r)`.  Moreover, changing the
parameter `a` changes the corrected value only by a linear combination of
`r*f(0)` and `r⁻¹*fhat(0)`.  In multiplicative coordinates these are precisely
the two pole-mode directions `u^(1/2)` and `u^(-1/2)`.

This file formalizes only the scalar algebra after assuming the Poisson
identity.  It does not formalize summability, Poisson summation, Fourier
analysis, the Weil form, or membership in a pole quotient.
-/

namespace RiemannCvs.RenormalizedPoissonBridge

/-- Scalar value of the one-parameter corrected Poisson transform.  The first
zero value belongs to the source function and the second to its Fourier
transform. -/
noncomputable def correctedValue
    (a r sum atZero fourierAtZero : ℝ) : ℝ :=
  r * sum + a * r * atZero +
    (a - 1 / 2) * (1 / r) * fourierAtZero

/-- The corrected transform is linear in all function data. -/
theorem correctedValue_smul
    (a r epsilon sum atZero fourierAtZero : ℝ) :
    correctedValue a r
        (epsilon * sum) (epsilon * atZero) (epsilon * fourierAtZero) =
      epsilon * correctedValue a r sum atZero fourierAtZero := by
  unfold correctedValue
  ring

/-- Scalar Poisson intertwining identity.

The hypothesis is the rearranged even Poisson formula

`S_fhat(u⁻¹) = u*S_f(u) + (u*f(0)-fhat(0))/2`

with `u = r²`. -/
theorem correctedPoissonIntertwining
    (a r sum sumHatInv atZero fourierAtZero : ℝ)
    (hr : r ≠ 0)
    (hPoisson :
      sumHatInv = r ^ 2 * sum +
        (r ^ 2 * atZero - fourierAtZero) / 2) :
    correctedValue a (1 / r)
        sumHatInv fourierAtZero atZero =
      correctedValue a r sum atZero fourierAtZero := by
  rw [hPoisson]
  unfold correctedValue
  field_simp [hr]
  ring

/-- If the Fourier data lie in an `epsilon` eigenspace and `epsilon² = 1`, the
corrected transform has exact multiplicative inversion parity `epsilon`.

The two scalar equalities express
`S_fhat(u⁻¹) = epsilon*S_f(u⁻¹)` and
`fhat(0) = epsilon*f(0)`. -/
theorem correctedFourierClassGivesInversionParity
    (a r sum sumInv sumHatInv atZero fourierAtZero epsilon : ℝ)
    (hr : r ≠ 0)
    (hEpsilonSq : epsilon ^ 2 = 1)
    (hPoisson :
      sumHatInv = r ^ 2 * sum +
        (r ^ 2 * atZero - fourierAtZero) / 2)
    (hSumClass : sumHatInv = epsilon * sumInv)
    (hZeroClass : fourierAtZero = epsilon * atZero) :
    correctedValue a (1 / r)
        sumInv atZero fourierAtZero =
      epsilon * correctedValue a r sum atZero fourierAtZero := by
  have hBackZero : atZero = epsilon * fourierAtZero := by
    rw [hZeroClass]
    nlinarith
  have hIntertwine := correctedPoissonIntertwining
    a r sum sumHatInv atZero fourierAtZero hr hPoisson
  have hClass :
      correctedValue a (1 / r)
          sumHatInv fourierAtZero atZero =
        epsilon * correctedValue a (1 / r)
          sumInv atZero fourierAtZero := by
    calc
      correctedValue a (1 / r)
          sumHatInv fourierAtZero atZero
          = correctedValue a (1 / r)
              (epsilon * sumInv)
              (epsilon * atZero)
              (epsilon * fourierAtZero) := by
                rw [hSumClass, hZeroClass, hBackZero]
      _ = epsilon * correctedValue a (1 / r)
            sumInv atZero fourierAtZero :=
          correctedValue_smul
            a (1 / r) epsilon sumInv atZero fourierAtZero
  have hEq :
      epsilon * correctedValue a (1 / r)
          sumInv atZero fourierAtZero =
        correctedValue a r sum atZero fourierAtZero := by
    exact hClass.symm.trans hIntertwine
  calc
    correctedValue a (1 / r)
        sumInv atZero fourierAtZero
        = epsilon ^ 2 * correctedValue a (1 / r)
            sumInv atZero fourierAtZero := by rw [hEpsilonSq, one_mul]
    _ = epsilon *
          (epsilon * correctedValue a (1 / r)
            sumInv atZero fourierAtZero) := by ring
    _ = epsilon * correctedValue a r sum atZero fourierAtZero := by
      rw [hEq]

/-- The `+1` Fourier class gives inversion-even corrected values. -/
theorem correctedPlusClassGivesInversionEven
    (a r sum sumInv sumHatInv atZero fourierAtZero : ℝ)
    (hr : r ≠ 0)
    (hPoisson :
      sumHatInv = r ^ 2 * sum +
        (r ^ 2 * atZero - fourierAtZero) / 2)
    (hSumClass : sumHatInv = sumInv)
    (hZeroClass : fourierAtZero = atZero) :
    correctedValue a (1 / r)
        sumInv atZero fourierAtZero =
      correctedValue a r sum atZero fourierAtZero := by
  have h := correctedFourierClassGivesInversionParity
    a r sum sumInv sumHatInv atZero fourierAtZero 1
    hr (by norm_num) hPoisson
    (by simpa using hSumClass) (by simpa using hZeroClass)
  simpa using h

/-- The `-1` Fourier class gives inversion-odd corrected values. -/
theorem correctedMinusClassGivesInversionOdd
    (a r sum sumInv sumHatInv atZero fourierAtZero : ℝ)
    (hr : r ≠ 0)
    (hPoisson :
      sumHatInv = r ^ 2 * sum +
        (r ^ 2 * atZero - fourierAtZero) / 2)
    (hSumClass : sumHatInv = -sumInv)
    (hZeroClass : fourierAtZero = -atZero) :
    correctedValue a (1 / r)
        sumInv atZero fourierAtZero =
      -correctedValue a r sum atZero fourierAtZero := by
  have h := correctedFourierClassGivesInversionParity
    a r sum sumInv sumHatInv atZero fourierAtZero (-1)
    hr (by norm_num) hPoisson
    (by simpa using hSumClass) (by simpa using hZeroClass)
  simpa using h

/-- Changing the renormalization parameter changes only the two-dimensional
pole-mode component. -/
theorem correctedValue_gaugeDifference
    (a b r sum atZero fourierAtZero : ℝ) :
    correctedValue b r sum atZero fourierAtZero -
        correctedValue a r sum atZero fourierAtZero =
      (b - a) *
        (r * atZero + (1 / r) * fourierAtZero) := by
  unfold correctedValue
  ring

/-- The symmetric correction `a = 1/2` is the half-weighted positive-integer
sum `r*(S_f + f(0)/2)`. -/
theorem correctedValue_half
    (r sum atZero fourierAtZero : ℝ) :
    correctedValue (1 / 2) r sum atZero fourierAtZero =
      r * (sum + atZero / 2) := by
  unfold correctedValue
  ring

/-- The correction `a = 0` subtracts the Fourier zero mode. -/
theorem correctedValue_zero
    (r sum atZero fourierAtZero : ℝ) :
    correctedValue 0 r sum atZero fourierAtZero =
      r * sum - (1 / (2 * r)) * fourierAtZero := by
  unfold correctedValue
  ring

/-- Difference between the two most useful gauges. -/
theorem half_minus_zero_is_poleMode
    (r sum atZero fourierAtZero : ℝ) :
    correctedValue (1 / 2) r sum atZero fourierAtZero -
        correctedValue 0 r sum atZero fourierAtZero =
      (1 / 2) *
        (r * atZero + (1 / r) * fourierAtZero) := by
  exact correctedValue_gaugeDifference
    0 (1 / 2) r sum atZero fourierAtZero

end RiemannCvs.RenormalizedPoissonBridge
