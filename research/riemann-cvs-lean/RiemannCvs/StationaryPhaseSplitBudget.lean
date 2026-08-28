import Mathlib

/-!
# Scalar budgets for a single-stationary-point decomposition

The analytic proof of the restricted prime-block estimate splits an
oscillatory integral into a short interval around the unique stationary point
and two monotone-derivative tails.  This file records the multiplication-only
algebra used after those analytic estimates have been established.

No oscillatory-integral theorem, PSWF asymptotic, von Mangoldt estimate, or RH
statement is hidden in these lemmas.
-/

namespace RiemannCvs.StationaryPhaseSplitBudget

/-- Convert the integration-by-parts denominator into the chosen stationary
width.  Analytically one takes `delta = (mu * kappa)^(-1/2)`. -/
theorem farBoundAtNaturalWidth
    (far mu kappa delta amplitude : ℝ)
    (hmu : 0 < mu)
    (hkappa : 0 < kappa)
    (hdelta : 0 < delta)
    (hunit : mu * kappa * delta ^ 2 = 1)
    (hfar : mu * kappa * delta * far ≤ amplitude) :
    far ≤ amplitude * delta := by
  have hden : 0 < mu * kappa * delta := by positivity
  have hrewrite :
      amplitude =
        (mu * kappa * delta) * (amplitude * delta) := by
    calc
      amplitude = amplitude * 1 := by ring
      _ = amplitude * (mu * kappa * delta ^ 2) := by rw [hunit]
      _ = (mu * kappa * delta) * (amplitude * delta) := by ring
  have hscaled :
      (mu * kappa * delta) * far ≤
        (mu * kappa * delta) * (amplitude * delta) := by
    calc
      (mu * kappa * delta) * far ≤ amplitude := hfar
      _ = (mu * kappa * delta) * (amplitude * delta) := hrewrite
  exact (mul_le_mul_left hden).mp hscaled

/-- Bookkeeping for the elementary one-critical-point proof.

The near interval has length at most `2 * delta`.  Each monotone tail is
bounded by `(3 * supNorm + variation) * delta`; the coefficient three allows
for the near boundary, the outer boundary, and the derivative of `1 / phi'`.
-/
theorem oneCriticalPointBudget
    (total near left right delta supNorm variation : ℝ)
    (hnear : near ≤ 2 * delta * supNorm)
    (hleft : left ≤ (3 * supNorm + variation) * delta)
    (hright : right ≤ (3 * supNorm + variation) * delta)
    (htotal : total ≤ near + left + right) :
    total ≤ (8 * supNorm + 2 * variation) * delta := by
  nlinarith

/-- The complete scalar consequence of choosing the natural stationary width.
The hypotheses `hleftScaled` and `hrightScaled` are the two integration-by-parts
estimates before replacing the denominator by `delta`. -/
theorem oneCriticalPointAtNaturalWidth
    (total near left right mu kappa delta supNorm variation : ℝ)
    (hmu : 0 < mu)
    (hkappa : 0 < kappa)
    (hdelta : 0 < delta)
    (hunit : mu * kappa * delta ^ 2 = 1)
    (hnear : near ≤ 2 * delta * supNorm)
    (hleftScaled :
      mu * kappa * delta * left ≤ 3 * supNorm + variation)
    (hrightScaled :
      mu * kappa * delta * right ≤ 3 * supNorm + variation)
    (htotal : total ≤ near + left + right) :
    total ≤ (8 * supNorm + 2 * variation) * delta := by
  have hleft := farBoundAtNaturalWidth
    left mu kappa delta (3 * supNorm + variation)
    hmu hkappa hdelta hunit hleftScaled
  have hright := farBoundAtNaturalWidth
    right mu kappa delta (3 * supNorm + variation)
    hmu hkappa hdelta hunit hrightScaled
  exact oneCriticalPointBudget
    total near left right delta supNorm variation
    hnear hleft hright htotal

/-- Main-plus-remainder aggregation.  This is useful because the explicit
Dunster remainder can be summed by Cauchy--Schwarz and a Chebyshev prime-weight
bound; it need not inherit the dilation decay of the stationary main term. -/
theorem mainRemainderAggregate
    (total main remainder rootC mainConstant remainderConstant : ℝ)
    (hroot : 0 < rootC)
    (hmain : rootC * main ≤ mainConstant)
    (hremainder : rootC * remainder ≤ remainderConstant)
    (htotal : total ≤ main + remainder) :
    rootC * total ≤ mainConstant + remainderConstant := by
  have hscaled := mul_le_mul_of_nonneg_left htotal (le_of_lt hroot)
  nlinarith

/-- A lower-order prime perturbation cannot destroy a logarithmic conductor
margin once its reciprocal-square-root bound is below that margin. -/
theorem conductorDominatesPrimeRemainder
    (conductor prime total defect logScale rootC A : ℝ)
    (hdefect : 0 ≤ defect)
    (hroot : 0 < rootC)
    (hconductor : 2 * logScale * defect ≤ conductor)
    (hprime : -(A / rootC * defect) ≤ prime)
    (htotal : total = conductor + prime) :
    (2 * logScale - A / rootC) * defect ≤ total := by
  rw [htotal]
  nlinarith

end RiemannCvs.StationaryPhaseSplitBudget
