import Mathlib
import RiemannCvs.BoundaryWeylUniformLimit

/-!
# Quantitative block-Schur tail for a boundary-Weyl response

This module replaces an abstract finite-to-limit error slot by a variational
estimate with source-level inputs.  The finite low-block solution `u0` and the
low/high components `(u,v)` of the full solution satisfy their weak resolvent
equations.  Low coercivity `a`, high coercivity `gamma`, and a coupling bound
`epsilon` then imply

`‖u-u0‖ <= epsilon² / (a*gamma-epsilon²) * ‖u0‖`

and hence

`|<eta,u>-<eta,u0>|
  <= ‖eta‖² epsilon² / (a * (a*gamma-epsilon²))`.

The division-free product budget and domain-uniform positivity theorem are
designed to accept interval-certified constants.  No CvS coercivity or
coupling estimate is postulated inside the module; each remains an explicit
hypothesis to be discharged by the log-tail or sharper prolate analysis.

The module also contains a stronger energy-normalized route.  If

`coupling(w,z)² <= q * lowForm(w,w) * highForm(z,z)` with `q < 1`,

then low-form symmetry and the two weak equations imply that adjoining the
high block can only increase the boundary response.  This conclusion has no
Euclidean `‖eta‖²` loss and is the preferred interface for a relative-form
tail certificate.
-/

namespace RiemannCvs.BoundaryWeylSchurTail

open scoped InnerProductSpace

variable {E H : Type*}
variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A centered multiplier of norm at most `delta` has commutator norm at most
twice `delta` against a contraction.  In the CvS tail application the
multiplier is `M_(S - π/4)` on the positive-positive Loewner block and the
contraction is the normalized discrete Hilbert transform.  The reflected
parity block has a separate leading Hankel kernel and is not erased by this
centering step. -/
theorem commutator_norm_le_two_mul_of_norm_bounds
    (A B : E →L[ℝ] E) (delta : ℝ)
    (hDelta : 0 ≤ delta)
    (hA : ‖A‖ ≤ delta)
    (hB : ‖B‖ ≤ 1) :
    ‖A.comp B - B.comp A‖ ≤ 2 * delta := by
  calc
    ‖A.comp B - B.comp A‖ ≤ ‖A.comp B‖ + ‖B.comp A‖ :=
      norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ :=
      add_le_add
        (ContinuousLinearMap.opNorm_comp_le A B)
        (ContinuousLinearMap.opNorm_comp_le B A)
    _ ≤ delta * 1 + 1 * delta := by
      exact add_le_add
        (mul_le_mul hA hB (norm_nonneg B) hDelta)
        (mul_le_mul hB hA (norm_nonneg A) (by norm_num))
    _ = 2 * delta := by ring

/-- Numerical specialization used by the same-sign part of the certified
Archimedean tail: a centered multiplier bound `1 / (4*N)` yields the
commutator bound `1 / (2*N)`. -/
theorem commutator_norm_le_one_div_two_mul
    (A B : E →L[ℝ] E) (N : ℝ)
    (hN : 0 < N)
    (hA : ‖A‖ ≤ 1 / (4 * N))
    (hB : ‖B‖ ≤ 1) :
    ‖A.comp B - B.comp A‖ ≤ 1 / (2 * N) := by
  calc
    ‖A.comp B - B.comp A‖ ≤ 2 * (1 / (4 * N)) :=
      commutator_norm_le_two_mul_of_norm_bounds A B (1 / (4 * N))
        (by positivity) hA hB
    _ = 1 / (2 * N) := by field_simp; norm_num

private theorem norm_le_of_coercive_variational_coupling
    (form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (w : E) (v : H) (gap epsilon : ℝ)
    (_hGap : 0 < gap)
    (hEpsilon : 0 ≤ epsilon)
    (hCoercive : gap * ‖w‖ ^ 2 ≤ form w w)
    (hEquation : form w w + coupling w v = 0)
    (hCoupling : |coupling w v| ≤ epsilon * ‖w‖ * ‖v‖) :
    gap * ‖w‖ ≤ epsilon * ‖v‖ := by
  have hForm : form w w = -coupling w v := by linarith
  have hNegLeAbs : -coupling w v ≤ |coupling w v| := neg_le_abs _
  have hProduct : gap * ‖w‖ ^ 2 ≤ epsilon * ‖w‖ * ‖v‖ := by
    calc
      gap * ‖w‖ ^ 2 ≤ form w w := hCoercive
      _ = -coupling w v := hForm
      _ ≤ |coupling w v| := hNegLeAbs
      _ ≤ epsilon * ‖w‖ * ‖v‖ := hCoupling
  by_cases hw : ‖w‖ = 0
  · simp [hw, mul_nonneg hEpsilon (norm_nonneg v)]
  · have hwPos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    nlinarith [hProduct]

private theorem finite_solution_norm_le
    (form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (eta u0 : E) (gap : ℝ)
    (_hGap : 0 < gap)
    (hCoercive : gap * ‖u0‖ ^ 2 ≤ form u0 u0)
    (hEquation : form u0 u0 = ⟪eta, u0⟫_ℝ) :
    gap * ‖u0‖ ≤ ‖eta‖ := by
  have hInnerAbs : form u0 u0 ≤ |⟪eta, u0⟫_ℝ| := by
    rw [hEquation]
    exact le_abs_self _
  have hCauchy : |⟪eta, u0⟫_ℝ| ≤ ‖eta‖ * ‖u0‖ :=
    abs_real_inner_le_norm eta u0
  have hProduct : gap * ‖u0‖ ^ 2 ≤ ‖eta‖ * ‖u0‖ :=
    hCoercive.trans (hInnerAbs.trans hCauchy)
  by_cases hu0 : ‖u0‖ = 0
  · simp [hu0]
  · have hu0Pos : 0 < ‖u0‖ := lt_of_le_of_ne (norm_nonneg u0) (Ne.symm hu0)
    nlinarith [hProduct]

/-- Variational block-Schur estimate for the low-component resolvent error. -/
theorem lowComponentError_norm_le
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (u0 u : E) (v : H)
    (lowGap highGap epsilon : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0) :
    ‖u - u0‖ ≤
      (epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * ‖u0‖ := by
  let d : E := u - u0
  have hD : lowGap * ‖d‖ ≤ epsilon * ‖v‖ :=
    norm_le_of_coercive_variational_coupling
      lowForm coupling d v lowGap epsilon hLowGap hEpsilon
      (hLowCoercive d) (hLowEquation d) (hCoupling d v)
  have hFlipCoupling :
      |coupling.flip v u| ≤ epsilon * ‖v‖ * ‖u‖ := by
    change |coupling u v| ≤ epsilon * ‖v‖ * ‖u‖
    calc
      |coupling u v| ≤ epsilon * ‖u‖ * ‖v‖ := hCoupling u v
      _ = epsilon * ‖v‖ * ‖u‖ := by ring
  have hV : highGap * ‖v‖ ≤ epsilon * ‖u‖ :=
    norm_le_of_coercive_variational_coupling
      highForm coupling.flip v u highGap epsilon hHighGap hEpsilon
      (hHighCoercive v) (by simpa using hHighEquation v) hFlipCoupling
  have hDProduct :
      lowGap * highGap * ‖d‖ ≤ epsilon ^ 2 * ‖u‖ := by
    have hD' := mul_le_mul_of_nonneg_left hD (le_of_lt hHighGap)
    have hV' := mul_le_mul_of_nonneg_left hV hEpsilon
    nlinarith
  have hTriangle : ‖u‖ ≤ ‖d‖ + ‖u0‖ := by
    have hu : u = d + u0 := by simp [d]
    rw [hu]
    exact norm_add_le d u0
  have hEpsSq : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
  have hTriangleScaled := mul_le_mul_of_nonneg_left hTriangle hEpsSq
  have hDenomMul :
      (lowGap * highGap - epsilon ^ 2) * ‖d‖ ≤ epsilon ^ 2 * ‖u0‖ := by
    nlinarith [hDProduct, hTriangleScaled]
  have hDenomPos : 0 < lowGap * highGap - epsilon ^ 2 := sub_pos.mpr hSmall
  change ‖d‖ ≤ (epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * ‖u0‖
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hDenomPos).2 (by simpa [mul_comm] using hDenomMul)

/-- The finite low-block resolvent solution is controlled by its coercivity. -/
theorem finiteResolvent_norm_le
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (eta u0 : E) (lowGap : ℝ)
    (hLowGap : 0 < lowGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ) :
    ‖u0‖ ≤ ‖eta‖ / lowGap := by
  have h := finite_solution_norm_le lowForm eta u0 lowGap hLowGap
    (hLowCoercive u0) (hFiniteEquation u0)
  exact (le_div_iff₀ hLowGap).2 (by simpa [mul_comm] using h)

/-- A coercive high block and a small low/high coupling give an explicit
boundary-Weyl (quadratic resolvent response) error. -/
theorem boundaryWeylError_le_of_blockSchur
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H)
    (lowGap highGap epsilon : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0) :
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤
      ‖eta‖ ^ 2 * epsilon ^ 2 /
        (lowGap * (lowGap * highGap - epsilon ^ 2)) := by
  have hError := lowComponentError_norm_le
    lowForm highForm coupling u0 u v
    lowGap highGap epsilon hLowGap hHighGap hEpsilon hSmall
    hLowCoercive hHighCoercive hCoupling hLowEquation hHighEquation
  have hFinite := finiteResolvent_norm_le
    lowForm eta u0 lowGap hLowGap hLowCoercive hFiniteEquation
  have hCauchy :
      |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤ ‖eta‖ * ‖u - u0‖ := by
    rw [← inner_sub_right]
    exact abs_real_inner_le_norm eta (u - u0)
  have hEta : 0 ≤ ‖eta‖ := norm_nonneg eta
  have hFactor : 0 ≤ epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2) := by
    positivity
  have h1 := mul_le_mul_of_nonneg_left hError hEta
  have h2 := mul_le_mul_of_nonneg_left hFinite hFactor
  calc
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤ ‖eta‖ * ‖u - u0‖ := hCauchy
    _ ≤ ‖eta‖ * ((epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * ‖u0‖) := h1
    _ ≤ ‖eta‖ * ((epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * (‖eta‖ / lowGap)) := by
      nlinarith [h2]
    _ = ‖eta‖ ^ 2 * epsilon ^ 2 /
        (lowGap * (lowGap * highGap - epsilon ^ 2)) := by
      field_simp [ne_of_gt hLowGap, ne_of_gt (sub_pos.mpr hSmall)]

omit [InnerProductSpace ℝ E] in
/-- The Schur product budget solved for the high-gap side.  This form is
convenient when `‖eta‖²`, `lowGap`, `epsilon`, and `margin` are already
certified and the remaining task is to make `highGap` sufficiently large. -/
theorem schurProductBudget_of_highGapBudget
    (eta : E) (etaNormSq lowGap highGap epsilon margin : ℝ)
    (hEtaNorm : ‖eta‖ ^ 2 ≤ etaNormSq)
    (hHighGapBudget :
      epsilon ^ 2 * (etaNormSq + margin * lowGap) ≤
        margin * lowGap ^ 2 * highGap) :
    ‖eta‖ ^ 2 * epsilon ^ 2 ≤
      margin * lowGap * (lowGap * highGap - epsilon ^ 2) := by
  have hScaled :=
    mul_le_mul_of_nonneg_right hEtaNorm (sq_nonneg epsilon)
  nlinarith [hScaled, hHighGapBudget]

/-- Structural obstruction for a coarse dimension-independent coupling bound.
If the boundary-vector mass grows at least like `2 * cutoff + 1`, the available
high gap grows no faster than `cutoff + shift`, and the right-side scale is
smaller in both slope and intercept than `epsilon²`, then the Schur high-gap
budget is contradictory.  The logarithmic CvS floor is even smaller than this
linear majorant, so the theorem cleanly detects when a sharper cutoff-decaying
coupling estimate is required. -/
theorem highGapBudget_false_of_linearBoundaryGrowth
    (cutoff etaNormSq highGap epsilon scale boundaryOffset shift : ℝ)
    (hCutoff : 0 ≤ cutoff)
    (hScale : 0 ≤ scale)
    (hBoundaryOffset : 0 ≤ boundaryOffset)
    (hEtaGrowth : 2 * cutoff + 1 ≤ etaNormSq)
    (hHighGrowth : highGap ≤ cutoff + shift)
    (hSlope : scale < 2 * epsilon ^ 2)
    (hIntercept : scale * shift < epsilon ^ 2)
    (hBudget :
      epsilon ^ 2 * (etaNormSq + boundaryOffset) ≤ scale * highGap) :
    False := by
  have hEtaPlus :
      2 * cutoff + 1 ≤ etaNormSq + boundaryOffset := by
    linarith
  have hLeft :=
    mul_le_mul_of_nonneg_left hEtaPlus (sq_nonneg epsilon)
  have hRight := mul_le_mul_of_nonneg_left hHighGrowth hScale
  have hCombined :
      epsilon ^ 2 * (2 * cutoff + 1) ≤
        scale * (cutoff + shift) :=
    hLeft.trans (hBudget.trans hRight)
  have hSlopePos : 0 < 2 * epsilon ^ 2 - scale :=
    sub_pos.mpr hSlope
  have hInterceptPos : 0 < epsilon ^ 2 - scale * shift :=
    sub_pos.mpr hIntercept
  nlinarith [mul_nonneg (le_of_lt hSlopePos) hCutoff]

/-- A squared relative coupling bound forces the low error energy below a
`q`-fraction of the high energy.  This cancellation is the scalar core of the
energy-normalized Schur route. -/
theorem lowEnergy_le_relativeHighEnergy
    (lowEnergy highEnergy q : ℝ)
    (hLowEnergy : 0 ≤ lowEnergy)
    (hHighEnergy : 0 ≤ highEnergy)
    (hq : 0 ≤ q)
    (hRelative :
      lowEnergy ^ 2 ≤ q * lowEnergy * highEnergy) :
    lowEnergy ≤ q * highEnergy := by
  by_cases hLowZero : lowEnergy = 0
  · rw [hLowZero]
    exact mul_nonneg hq hHighEnergy
  · have hLowPos : 0 < lowEnergy :=
      lt_of_le_of_ne hLowEnergy (Ne.symm hLowZero)
    have hMul :
        lowEnergy * lowEnergy ≤ lowEnergy * (q * highEnergy) := by
      nlinarith [hRelative]
    exact le_of_mul_le_mul_left hMul hLowPos

/-- If `q < 1`, the high energy dominates the low Schur-error energy. -/
theorem relativeSchurResponseNonnegative
    (lowEnergy highEnergy q : ℝ)
    (hLowEnergy : 0 ≤ lowEnergy)
    (hHighEnergy : 0 ≤ highEnergy)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hRelative :
      lowEnergy ^ 2 ≤ q * lowEnergy * highEnergy) :
    0 ≤ highEnergy - lowEnergy := by
  have hLowRelative := lowEnergy_le_relativeHighEnergy
    lowEnergy highEnergy q hLowEnergy hHighEnergy hq hRelative
  have hRelativeHigh : q * highEnergy ≤ highEnergy := by
    have := mul_le_mul_of_nonneg_right (le_of_lt hqLt) hHighEnergy
    simpa using this
  linarith

/-- Multiplication-only error budget for the energy-normalized Schur system.

Here `lowEnergy` is the energy of the low-component error, `highEnergy` is the
high-component energy, `sourceEnergy` is the finite resolvent energy, and
`cross = lowEnergy - highEnergy` is the source/high cross term forced by the
two block equations. -/
theorem relativeSchurResponseBudget
    (lowEnergy highEnergy sourceEnergy q cross : ℝ)
    (hLowEnergy : 0 ≤ lowEnergy)
    (hHighEnergy : 0 ≤ highEnergy)
    (hSourceEnergy : 0 ≤ sourceEnergy)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hCross : cross = lowEnergy - highEnergy)
    (hRelativeLow :
      lowEnergy ^ 2 ≤ q * lowEnergy * highEnergy)
    (hRelativeSource :
      cross ^ 2 ≤ q * sourceEnergy * highEnergy) :
    (1 - q) * |cross| ≤ q * sourceEnergy := by
  have hLowRelative := lowEnergy_le_relativeHighEnergy
    lowEnergy highEnergy q
    hLowEnergy hHighEnergy hq hRelativeLow
  have hRelativeHigh : q * highEnergy ≤ highEnergy := by
    have := mul_le_mul_of_nonneg_right (le_of_lt hqLt) hHighEnergy
    simpa using this
  have hCrossNonpos : cross ≤ 0 := by
    rw [hCross]
    linarith
  have hAbsCross : |cross| = highEnergy - lowEnergy := by
    rw [abs_of_nonpos hCrossNonpos, hCross]
    ring
  rw [hAbsCross]
  have hResponseNonneg : 0 ≤ highEnergy - lowEnergy := by
    linarith
  by_cases hResponseZero : highEnergy - lowEnergy = 0
  · rw [hResponseZero]
    simpa using mul_nonneg hq hSourceEnergy
  · have hResponsePos : 0 < highEnergy - lowEnergy :=
      lt_of_le_of_ne hResponseNonneg (Ne.symm hResponseZero)
    have hOneMinusQ : 0 < 1 - q := sub_pos.mpr hqLt
    have hRelativeResponse :
        (highEnergy - lowEnergy) ^ 2 ≤
          q * sourceEnergy * highEnergy := by
      rw [hCross] at hRelativeSource
      nlinarith [hRelativeSource]
    have hHighToResponse :
        (1 - q) * highEnergy ≤ highEnergy - lowEnergy := by
      nlinarith [hLowRelative]
    have hRelativeScaled := mul_le_mul_of_nonneg_left
      hRelativeResponse (le_of_lt hOneMinusQ)
    have hHighScaled := mul_le_mul_of_nonneg_left
      hHighToResponse (mul_nonneg hq hSourceEnergy)
    have hProduct :
        ((1 - q) * (highEnergy - lowEnergy)) *
            (highEnergy - lowEnergy) ≤
          (q * sourceEnergy) * (highEnergy - lowEnergy) := by
      calc
        ((1 - q) * (highEnergy - lowEnergy)) *
              (highEnergy - lowEnergy)
            = (1 - q) * (highEnergy - lowEnergy) ^ 2 := by ring
        _ ≤ (1 - q) * (q * sourceEnergy * highEnergy) :=
          hRelativeScaled
        _ = (q * sourceEnergy) * ((1 - q) * highEnergy) := by ring
        _ ≤ (q * sourceEnergy) * (highEnergy - lowEnergy) :=
          hHighScaled
    exact le_of_mul_le_mul_right hProduct hResponsePos

/-- A relative coupling certificate at one pair of nonnegative forms remains
valid after both forms grow.  For the CvS resolvent this propagates a right
endpoint certificate to every more negative spectral parameter, since both
diagonal blocks gain the same positive shift. -/
theorem relativeCoupling_of_formGrowth
    (couplingSq q low₀ low high₀ high : ℝ)
    (hq : 0 ≤ q)
    (hLow₀ : 0 ≤ low₀)
    (hHigh₀ : 0 ≤ high₀)
    (hLowGrowth : low₀ ≤ low)
    (hHighGrowth : high₀ ≤ high)
    (hRelative : couplingSq ≤ q * low₀ * high₀) :
    couplingSq ≤ q * low * high := by
  have hLowNonneg : 0 ≤ low := hLow₀.trans hLowGrowth
  have hLowProduct : low₀ * high₀ ≤ low * high₀ :=
    mul_le_mul_of_nonneg_right hLowGrowth hHigh₀
  have hHighProduct : low * high₀ ≤ low * high :=
    mul_le_mul_of_nonneg_left hHighGrowth hLowNonneg
  have hProduct := hLowProduct.trans hHighProduct
  have hScaled := mul_le_mul_of_nonneg_left hProduct hq
  calc
    couplingSq ≤ q * low₀ * high₀ := hRelative
    _ = q * (low₀ * high₀) := by ring
    _ ≤ q * (low * high) := hScaled
    _ = q * low * high := by ring

/-- Convert ordinary coercive norm bounds and an operator-norm coupling bound
into the dimensionless relative-energy inequality used by the recursive shell
route.  This is the direct adapter for analytic estimates of a shell floor and
of the corresponding rectangular block norm. -/
theorem relativeCoupling_of_coerciveNormBounds
    (lowEnergy highEnergy cross lowGap highGap epsilon q
      lowNorm highNorm : ℝ)
    (hLowGap : 0 ≤ lowGap)
    (hHighGap : 0 ≤ highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q)
    (hLowEnergy : lowGap * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy : highGap * highNorm ^ 2 ≤ highEnergy)
    (hCross : |cross| ≤ epsilon * lowNorm * highNorm)
    (hLowNorm : 0 ≤ lowNorm)
    (hHighNorm : 0 ≤ highNorm)
    (hBudget : epsilon ^ 2 ≤ q * lowGap * highGap) :
    cross ^ 2 ≤ q * lowEnergy * highEnergy := by
  have hCouplingNonnegative :
      0 ≤ epsilon * lowNorm * highNorm := by positivity
  have hCrossSq :
      cross ^ 2 ≤ (epsilon * lowNorm * highNorm) ^ 2 := by
    have hAbsSq := (sq_le_sq₀ (abs_nonneg cross) hCouplingNonnegative).2
      hCross
    simpa only [sq_abs] using hAbsSq
  have hLowReference : 0 ≤ lowGap * lowNorm ^ 2 := by positivity
  have hHighReference : 0 ≤ highGap * highNorm ^ 2 := by positivity
  have hLowEnergyNonnegative : 0 ≤ lowEnergy :=
    hLowReference.trans hLowEnergy
  have hReferenceProduct :
      (lowGap * lowNorm ^ 2) * (highGap * highNorm ^ 2) ≤
        lowEnergy * highEnergy := by
    calc
      (lowGap * lowNorm ^ 2) * (highGap * highNorm ^ 2) ≤
          lowEnergy * (highGap * highNorm ^ 2) :=
        mul_le_mul_of_nonneg_right hLowEnergy hHighReference
      _ ≤ lowEnergy * highEnergy :=
        mul_le_mul_of_nonneg_left hHighEnergy hLowEnergyNonnegative
  have hBudgetScaled := mul_le_mul_of_nonneg_right hBudget
    (mul_nonneg (sq_nonneg lowNorm) (sq_nonneg highNorm))
  have hScaledReference := mul_le_mul_of_nonneg_left hReferenceProduct hq
  calc
    cross ^ 2 ≤ (epsilon * lowNorm * highNorm) ^ 2 := hCrossSq
    _ = epsilon ^ 2 * (lowNorm ^ 2 * highNorm ^ 2) := by ring
    _ ≤ (q * lowGap * highGap) *
        (lowNorm ^ 2 * highNorm ^ 2) := hBudgetScaled
    _ = q * ((lowGap * lowNorm ^ 2) *
        (highGap * highNorm ^ 2)) := by ring
    _ ≤ q * (lowEnergy * highEnergy) := hScaledReference
    _ = q * lowEnergy * highEnergy := by ring

/-- Two nonnegative energy blocks glue whenever the square of their cross term
does not exceed the product of the diagonal energies.  This is the scalar
determinant step used by the recursive finite-shell certificate. -/
theorem twoBlockEnergy_nonnegative
    (coreEnergy tailEnergy cross : ℝ)
    (hCore : 0 ≤ coreEnergy)
    (hTail : 0 ≤ tailEnergy)
    (hDet : cross ^ 2 ≤ coreEnergy * tailEnergy) :
    0 ≤ coreEnergy + 2 * cross + tailEnergy := by
  rcases hCore.eq_or_lt with hCoreZero | hCorePos
  · have hCrossZero : cross = 0 := by
      rw [← sq_eq_zero_iff]
      nlinarith [sq_nonneg cross]
    rw [hCoreZero, hCrossZero]
    simpa using hTail
  · have hMul :
        coreEnergy * 0 ≤
          coreEnergy * (coreEnergy + 2 * cross + tailEnergy) := by
      nlinarith [sq_nonneg (coreEnergy + cross)]
    exact le_of_mul_le_mul_left hMul hCorePos

/-- A relative shell coefficient `u²` retains the balanced reserve `1-u`.

Unlike the fixed `rho = 4/9` specialization below, this form permits a
scale-dependent sequence `u n`.  It is the scalar input for retaining a
positive product of reserves along an infinite dyadic shell chain. -/
theorem sqShell_oneSubReserve
    (core tail cross u : ℝ)
    (hCore : 0 ≤ core)
    (hTail : 0 ≤ tail)
    (hU : 0 ≤ u)
    (hRelative : cross ^ 2 ≤ u ^ 2 * core * tail) :
    (1 - u) * (core + tail) ≤ core + 2 * cross + tail := by
  have hProduct : core * tail ≤ ((core + tail) / 2) ^ 2 := by
    nlinarith [sq_nonneg (core - tail)]
  have hScaled :
      u ^ 2 * (core * tail) ≤ u ^ 2 * (((core + tail) / 2) ^ 2) :=
    mul_le_mul_of_nonneg_left hProduct (sq_nonneg u)
  have hTargetSq :
      cross ^ 2 ≤ (u * ((core + tail) / 2)) ^ 2 := by
    calc
      cross ^ 2 ≤ u ^ 2 * core * tail := hRelative
      _ = u ^ 2 * (core * tail) := by ring
      _ ≤ u ^ 2 * (((core + tail) / 2) ^ 2) := hScaled
      _ = (u * ((core + tail) / 2)) ^ 2 := by ring
  have hTargetNonnegative : 0 ≤ u * ((core + tail) / 2) := by
    positivity
  have hAbs : |cross| ≤ |u * ((core + tail) / 2)| :=
    (sq_le_sq).mp hTargetSq
  rw [abs_of_nonneg hTargetNonnegative] at hAbs
  have hLower := (abs_le.mp hAbs).1
  nlinarith

/-- Exact reserve left by the V23 shell coefficient `rho = 1/12`.

The relative determinant bound implies that the glued energy controls two
thirds of the block-diagonal core-plus-tail reference.  This turns the next
dyadic-shell target into a reference coefficient of at most
`(1/12) * (2/3) = 1/18`, a much larger usable reserve than the independent
`1/666` gap between `q₀` and the final benchmark `q`. -/
theorem oneTwelfthShell_balancedReserve
    (core tail cross : ℝ)
    (hCore : 0 ≤ core)
    (hTail : 0 ≤ tail)
    (hRelative : cross ^ 2 ≤ (1 / 12 : ℝ) * core * tail) :
    (2 / 3 : ℝ) * (core + tail) ≤ core + 2 * cross + tail := by
  have hSum : 0 ≤ (core + tail) / 6 := by positivity
  have hTargetSq : cross ^ 2 ≤ ((core + tail) / 6) ^ 2 := by
    calc
      cross ^ 2 ≤ (1 / 12 : ℝ) * core * tail := hRelative
      _ ≤ ((core + tail) / 6) ^ 2 := by
        nlinarith [sq_nonneg (core - tail)]
  have hAbs : |cross| ≤ |(core + tail) / 6| :=
    (sq_le_sq).mp hTargetSq
  rw [abs_of_nonneg hSum] at hAbs
  have hLower := (abs_le.mp hAbs).1
  nlinarith

/-- The reusable balanced-shell budget `u² * (1-u)` is at most `4/27` for
every nonnegative `u`; equality is attained at `u = 2/3`.  This is the scalar
optimization behind the steady coefficient `rho = u² = 4/9`. -/
theorem balancedShellBudget_le_fourTwentySevenths
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 * (1 - u) ≤ (4 / 27 : ℝ) := by
  have hLinear : 0 ≤ u + 1 / 3 := by positivity
  have hFactor : 0 ≤ (u - 2 / 3) ^ 2 * (u + 1 / 3) :=
    mul_nonneg (sq_nonneg _) hLinear
  nlinarith

/-- The balanced rational shell coefficient `rho = 4/9` leaves exactly one
third of the block-diagonal core-plus-tail reference.

Among coefficients of the form `rho = u^2`, the corresponding balanced
reserve is `1-u`, so the reusable next-shell budget is `u^2 * (1-u)`.  Its
maximum occurs at `u = 2/3`, giving the exact rational pair

`rho = 4/9`, `reserve = 1/3`, `rho * reserve = 4/27`.

This coefficient is deliberately weaker than the rigorous finite
`rho = 1/12` bridge through `N = 1920`, but it leaves a substantially larger
repeatable budget for every later dyadic shell. -/
theorem fourNinthsShell_oneThirdReserve
    (core tail cross : ℝ)
    (hCore : 0 ≤ core)
    (hTail : 0 ≤ tail)
    (hRelative : cross ^ 2 ≤ (4 / 9 : ℝ) * core * tail) :
    (1 / 3 : ℝ) * (core + tail) ≤ core + 2 * cross + tail := by
  have hSum : 0 ≤ (core + tail) / 3 := by positivity
  have hTargetSq : cross ^ 2 ≤ ((core + tail) / 3) ^ 2 := by
    calc
      cross ^ 2 ≤ (4 / 9 : ℝ) * core * tail := hRelative
      _ ≤ ((core + tail) / 3) ^ 2 := by
        nlinarith [sq_nonneg (core - tail)]
  have hAbs : |cross| ≤ |(core + tail) / 3| :=
    (sq_le_sq).mp hTargetSq
  rw [abs_of_nonneg hSum] at hAbs
  have hLower := (abs_le.mp hAbs).1
  nlinarith

/-- A tighter relative coefficient `q₀` leaves a direct low-channel reserve
when the same form is evaluated with a larger coefficient `q`. -/
theorem relativeCouplingSlack_lowReserve
    (low high cross q₀ q : ℝ)
    (hLow : 0 ≤ low)
    (hHigh : 0 ≤ high)
    (hq₀ : 0 ≤ q₀)
    (hRelative : cross ^ 2 ≤ q₀ * low * high) :
    (q - q₀) * low ≤ q * low + 2 * cross + high := by
  have hCore : 0 ≤ q₀ * low := mul_nonneg hq₀ hLow
  have hBase := twoBlockEnergy_nonnegative
    (q₀ * low) high cross hCore hHigh hRelative
  nlinarith

/-- Division-free high-channel companion to
`relativeCouplingSlack_lowReserve`.  Multiplication by `q` avoids introducing
the quotient `q₀ / q` into an interval certificate. -/
theorem relativeCouplingSlack_highReserve
    (low high cross q₀ q : ℝ)
    (hLow : 0 ≤ low)
    (hHigh : 0 ≤ high)
    (hq₀ : 0 ≤ q₀)
    (hRelative : cross ^ 2 ≤ q₀ * low * high) :
    (q - q₀) * high ≤ q * (q * low + 2 * cross + high) := by
  have hCore : 0 ≤ q ^ 2 * low := mul_nonneg (sq_nonneg q) hLow
  have hTail : 0 ≤ q₀ * high := mul_nonneg hq₀ hHigh
  have hScaled := mul_le_mul_of_nonneg_left hRelative (sq_nonneg q)
  have hDet : (q * cross) ^ 2 ≤ (q ^ 2 * low) * (q₀ * high) := by
    calc
      (q * cross) ^ 2 = q ^ 2 * cross ^ 2 := by ring
      _ ≤ q ^ 2 * (q₀ * low * high) := hScaled
      _ = (q ^ 2 * low) * (q₀ * high) := by ring
  have hBase := twoBlockEnergy_nonnegative
    (q ^ 2 * low) (q₀ * high) (q * cross)
    hCore hTail hDet
  nlinarith

/-- Balanced division-free reserve from a strict coefficient gap `q₀ < q`.
It lower-bounds the `q`-scaled core simultaneously in its low and high
energies, which is the form needed to estimate the next dyadic shell. -/
theorem relativeCouplingSlack_balancedReserve
    (low high cross q₀ q : ℝ)
    (hLow : 0 ≤ low)
    (hHigh : 0 ≤ high)
    (hq₀ : 0 ≤ q₀)
    (hq₀Lt : q₀ < q)
    (hRelative : cross ^ 2 ≤ q₀ * low * high) :
    (q - q₀) * (q * low + high) ≤
      2 * q * (q * low + 2 * cross + high) := by
  have hq : 0 < q := lt_of_le_of_lt hq₀ hq₀Lt
  have hLowReserve := relativeCouplingSlack_lowReserve
    low high cross q₀ q hLow hHigh hq₀ hRelative
  have hHighReserve := relativeCouplingSlack_highReserve
    low high cross q₀ q hLow hHigh hq₀ hRelative
  have hLowScaled := mul_le_mul_of_nonneg_left hLowReserve (le_of_lt hq)
  nlinarith

/-- Quotient form of `relativeCouplingSlack_balancedReserve`.  For the concrete
V23 coefficients `q₀ = 249/250` and `q = 999/1000`, the prefactor on the left
is exactly `1/666`. -/
theorem relativeCouplingSlack_balancedLowerBound
    (low high cross q₀ q : ℝ)
    (hLow : 0 ≤ low)
    (hHigh : 0 ≤ high)
    (hq₀ : 0 ≤ q₀)
    (hq₀Lt : q₀ < q)
    (hRelative : cross ^ 2 ≤ q₀ * low * high) :
    ((q - q₀) / (2 * q)) * (q * low + high) ≤
      q * low + 2 * cross + high := by
  have hq : 0 < q := lt_of_le_of_lt hq₀ hq₀Lt
  have hTwoQ : 0 < 2 * q := by positivity
  have hReserve := relativeCouplingSlack_balancedReserve
    low high cross q₀ q hLow hHigh hq₀ hq₀Lt hRelative
  have hDiv :
      ((q - q₀) * (q * low + high)) / (2 * q) ≤
        q * low + 2 * cross + high := by
    apply (div_le_iff₀ hTwoQ).2
    nlinarith
  calc
    ((q - q₀) / (2 * q)) * (q * low + high) =
        ((q - q₀) * (q * low + high)) / (2 * q) := by ring
    _ ≤ q * low + 2 * cross + high := hDiv

/-- Concrete V23 specialization of the balanced reserve.  A certificate with
`q₀ = 249/250` supplies exactly `1/666` of the reference energy when the final
relative coefficient is `q = 999/1000`. -/
theorem relativeCouplingSlack_v23BalancedLowerBound
    (low high cross : ℝ)
    (hLow : 0 ≤ low)
    (hHigh : 0 ≤ high)
    (hRelative : cross ^ 2 ≤ (249 / 250 : ℝ) * low * high) :
    (1 / 666 : ℝ) * ((999 / 1000 : ℝ) * low + high) ≤
      (999 / 1000 : ℝ) * low + 2 * cross + high := by
  have h := relativeCouplingSlack_balancedLowerBound
    low high cross (249 / 250 : ℝ) (999 / 1000 : ℝ)
    hLow hHigh (by norm_num) (by norm_num) hRelative
  norm_num at h ⊢
  exact h

/-- Convert a coupling estimate measured against a simpler reference energy
into the core-relative form consumed by `relativeCoupling_of_recursiveShell`.
The scalar budget `budget ≤ rho * reserve` is the exact next-shell acceptance
condition once `reserve * reference ≤ core` has been established. -/
theorem relativeShell_of_referenceReserve
    (reference core tail cross reserve budget rho : ℝ)
    (hReference : 0 ≤ reference)
    (hTail : 0 ≤ tail)
    (hRho : 0 ≤ rho)
    (hReserveCore : reserve * reference ≤ core)
    (hBudget : budget ≤ rho * reserve)
    (hCross : cross ^ 2 ≤ budget * reference * tail) :
    cross ^ 2 ≤ rho * core * tail := by
  have hBudgetReference :
      budget * reference ≤ (rho * reserve) * reference :=
    mul_le_mul_of_nonneg_right hBudget hReference
  have hBudgetTail :
      budget * reference * tail ≤
        (rho * reserve) * reference * tail :=
    mul_le_mul_of_nonneg_right hBudgetReference hTail
  have hCoreRho : rho * (reserve * reference) ≤ rho * core :=
    mul_le_mul_of_nonneg_left hReserveCore hRho
  have hCoreTail :
      rho * (reserve * reference) * tail ≤ rho * core * tail :=
    mul_le_mul_of_nonneg_right hCoreRho hTail
  calc
    cross ^ 2 ≤ budget * reference * tail := hCross
    _ ≤ (rho * reserve) * reference * tail := hBudgetTail
    _ = rho * (reserve * reference) * tail := by ring
    _ ≤ rho * core * tail := hCoreTail

/-- Combine a finite family of shell channels using the sum of their relative
coefficients.  If channel `i` has cross term `cross i`, reference energy
`energy i`, and coefficient `budget i`, weighted Cauchy--Schwarz gives one
aggregate coefficient `sum budget` rather than a factor equal to the number of
channels.

This is the multiscale adapter for the previous-core channel: decompose the
old core into dyadic shells, prove a distance-dependent budget for each shell,
and add those budgets before applying the recursive reserve theorem. -/
theorem relativeCoupling_of_finsetChannelBudgets
    {ι : Type*}
    (s : Finset ι)
    (energy cross budget : ι → ℝ)
    (tail rho : ℝ)
    (hEnergy : ∀ i ∈ s, 0 ≤ energy i)
    (hBudget : ∀ i ∈ s, 0 ≤ budget i)
    (hTail : 0 ≤ tail)
    (hBudgetSum : (∑ i ∈ s, budget i) ≤ rho)
    (hRelative : ∀ i ∈ s,
      (cross i) ^ 2 ≤ budget i * energy i * tail) :
    (∑ i ∈ s, cross i) ^ 2 ≤
      rho * (∑ i ∈ s, energy i) * tail := by
  have hCauchy :
      (∑ i ∈ s, cross i) ^ 2 ≤
        (∑ i ∈ s, budget i) * ∑ i ∈ s, energy i * tail := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      s hBudget
      (fun i hi => mul_nonneg (hEnergy i hi) hTail)
      (fun i hi => by simpa [mul_assoc] using hRelative i hi)
  have hEnergySum : 0 ≤ ∑ i ∈ s, energy i :=
    Finset.sum_nonneg hEnergy
  have hEnergyTail :
      (∑ i ∈ s, energy i * tail) = (∑ i ∈ s, energy i) * tail := by
    exact (Finset.sum_mul s energy tail).symm
  have hScale :
      (∑ i ∈ s, budget i) * ((∑ i ∈ s, energy i) * tail) ≤
        rho * ((∑ i ∈ s, energy i) * tail) :=
    mul_le_mul_of_nonneg_right hBudgetSum (mul_nonneg hEnergySum hTail)
  calc
    (∑ i ∈ s, cross i) ^ 2 ≤
        (∑ i ∈ s, budget i) * ∑ i ∈ s, energy i * tail := hCauchy
    _ = (∑ i ∈ s, budget i) * ((∑ i ∈ s, energy i) * tail) := by
      rw [hEnergyTail]
    _ ≤ rho * ((∑ i ∈ s, energy i) * tail) := hScale
    _ = rho * (∑ i ∈ s, energy i) * tail := by ring

/-- Add one separately certified channel to an arbitrary finite channel family
without paying the factor-two loss from the elementary two-term square bound.
The exceptional channel and the regular family instead share the same weighted
Cauchy--Schwarz budget.  This is the interface used when a fixed low block does
not obey the eventual dyadic envelope. -/
theorem relativeCoupling_of_exception_and_finsetChannelBudgets
    {ι : Type*}
    (s : Finset ι)
    (energy cross budget : ι → ℝ)
    (tail rho exceptionEnergy exceptionCross exceptionBudget : ℝ)
    (hExceptionEnergy : 0 ≤ exceptionEnergy)
    (hExceptionBudget : 0 ≤ exceptionBudget)
    (hExceptionRelative :
      exceptionCross ^ 2 ≤ exceptionBudget * exceptionEnergy * tail)
    (hEnergy : ∀ i ∈ s, 0 ≤ energy i)
    (hBudget : ∀ i ∈ s, 0 ≤ budget i)
    (hTail : 0 ≤ tail)
    (hBudgetSum : exceptionBudget + (∑ i ∈ s, budget i) ≤ rho)
    (hRelative : ∀ i ∈ s,
      (cross i) ^ 2 ≤ budget i * energy i * tail) :
    (exceptionCross + ∑ i ∈ s, cross i) ^ 2 ≤
      rho * (exceptionEnergy + ∑ i ∈ s, energy i) * tail := by
  classical
  let channels : Finset (Option ι) := insert none (s.image some)
  let energy' : Option ι → ℝ := fun i => i.elim exceptionEnergy energy
  let cross' : Option ι → ℝ := fun i => i.elim exceptionCross cross
  let budget' : Option ι → ℝ := fun i => i.elim exceptionBudget budget
  have hEnergyAll : ∀ i ∈ channels, 0 ≤ energy' i := by
    intro i hi
    cases i with
    | none => simpa [energy'] using hExceptionEnergy
    | some i =>
        have hi' : i ∈ s := by simpa [channels] using hi
        simpa [energy'] using hEnergy i hi'
  have hBudgetAll : ∀ i ∈ channels, 0 ≤ budget' i := by
    intro i hi
    cases i with
    | none => simpa [budget'] using hExceptionBudget
    | some i =>
        have hi' : i ∈ s := by simpa [channels] using hi
        simpa [budget'] using hBudget i hi'
  have hBudgetSumAll : (∑ i ∈ channels, budget' i) ≤ rho := by
    simpa [channels, budget'] using hBudgetSum
  have hRelativeAll : ∀ i ∈ channels,
      (cross' i) ^ 2 ≤ budget' i * energy' i * tail := by
    intro i hi
    cases i with
    | none => simpa [cross', budget', energy'] using hExceptionRelative
    | some i =>
        have hi' : i ∈ s := by simpa [channels] using hi
        simpa [cross', budget', energy'] using hRelative i hi'
  have hAll := relativeCoupling_of_finsetChannelBudgets
    channels energy' cross' budget' tail rho
    hEnergyAll hBudgetAll hTail hBudgetSumAll hRelativeAll
  simpa [channels, cross', energy'] using hAll

/-- A dyadically decaying coefficient envelope has total budget at most twice
its leading coefficient.  This is the scalar summation needed when separated
shell norms lose one factor `1/2` per dyadic scale in squared norm. -/
theorem dyadicChannelBudget_sum_le_two
    (budget : ℕ → ℝ) (n : ℕ) (leading : ℝ)
    (hLeading : 0 ≤ leading)
    (hBudget : ∀ i ∈ Finset.range n,
      budget i ≤ leading * (1 / (2 : ℝ)) ^ i) :
    (∑ i ∈ Finset.range n, budget i) ≤ 2 * leading := by
  calc
    (∑ i ∈ Finset.range n, budget i) ≤
        ∑ i ∈ Finset.range n, leading * (1 / (2 : ℝ)) ^ i := by
      exact Finset.sum_le_sum hBudget
    _ = leading * ∑ i ∈ Finset.range n, (1 / (2 : ℝ)) ^ i := by
      rw [Finset.mul_sum]
    _ ≤ leading * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hLeading
    _ = 2 * leading := by ring

/-- Package the finite-channel Cauchy estimate with a dyadic coefficient
envelope.  A leading coefficient at most half the desired aggregate budget is
sufficient uniformly in the number of earlier shells. -/
theorem relativeCoupling_of_dyadicChannelBudgets
    (energy cross budget : ℕ → ℝ)
    (n : ℕ) (tail leading rho : ℝ)
    (hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i)
    (hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i)
    (hTail : 0 ≤ tail)
    (hLeading : 0 ≤ leading)
    (hBudgetEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ leading * (1 / (2 : ℝ)) ^ i)
    (hTotalBudget : 2 * leading ≤ rho)
    (hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i * tail) :
    (∑ i ∈ Finset.range n, cross i) ^ 2 ≤
      rho * (∑ i ∈ Finset.range n, energy i) * tail := by
  apply relativeCoupling_of_finsetChannelBudgets
    (Finset.range n) energy cross budget tail rho
    hEnergy hBudget hTail
  · exact (dyadicChannelBudget_sum_le_two
      budget n leading hLeading hBudgetEnvelope).trans hTotalBudget
  · exact hRelative

/-- Package one fixed exceptional channel together with a geometrically
decaying dyadic family.  The exception consumes `exceptionBudget`, while the
entire regular family consumes at most `2 * leading`; only their sum must fit
inside the final coefficient `rho`.  In particular, one fixed base block may
be interval-certified separately without weakening the dyadic tail envelope. -/
theorem relativeCoupling_of_finiteException_and_dyadicChannelBudgets
    (exceptionEnergy exceptionCross exceptionBudget : ℝ)
    (energy cross budget : ℕ → ℝ)
    (n : ℕ) (tail leading rho : ℝ)
    (hExceptionEnergy : 0 ≤ exceptionEnergy)
    (hExceptionBudget : 0 ≤ exceptionBudget)
    (hExceptionRelative :
      exceptionCross ^ 2 ≤ exceptionBudget * exceptionEnergy * tail)
    (hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i)
    (hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i)
    (hTail : 0 ≤ tail)
    (hLeading : 0 ≤ leading)
    (hBudgetEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ leading * (1 / (2 : ℝ)) ^ i)
    (hTotalBudget : exceptionBudget + 2 * leading ≤ rho)
    (hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i * tail) :
    (exceptionCross + ∑ i ∈ Finset.range n, cross i) ^ 2 ≤
      rho * (exceptionEnergy + ∑ i ∈ Finset.range n, energy i) * tail := by
  apply relativeCoupling_of_exception_and_finsetChannelBudgets
    (Finset.range n) energy cross budget tail rho
    exceptionEnergy exceptionCross exceptionBudget
    hExceptionEnergy hExceptionBudget hExceptionRelative
    hEnergy hBudget hTail
  · have hDyadic := add_le_add_left
      (dyadicChannelBudget_sum_le_two
        budget n leading hLeading hBudgetEnvelope)
      exceptionBudget
    have hCombined :
        exceptionBudget + (∑ i ∈ Finset.range n, budget i) ≤
          exceptionBudget + 2 * leading := by
      simpa [add_comm] using hDyadic
    exact hCombined.trans hTotalBudget
  · exact hRelative

/-- Exact scalar budget retained after assigning `1/384` to the exceptional
odd fixed base and `1/30` as the leading coefficient of the regular dyadic
family.  The positive remainder is the slack left inside the previous-channel
allocation `2/27`. -/
theorem v23OddFixedBaseBudget_allocation :
    (2 / 27 : ℝ) -
      ((1 / 384 : ℝ) + 2 * (1 / 30 : ℝ)) = 83 / 17280 := by
  norm_num

/-- Exact finite budget remaining after the five certified even regular
source bands at the first `1920 -> 3840` transition.  Their coefficients are
`1/30, 1/60, 1/120, 1/240, 1/480`. -/
theorem v23EvenFiniteRegularBudget_allocation :
    (2 / 27 : ℝ) -
      ((1 / 30 : ℝ) + 1 / 60 + 1 / 120 + 1 / 240 + 1 / 480) =
        41 / 4320 := by
  norm_num

/-- Exact finite budget remaining after the four certified odd regular source
bands and the separately certified `1/384` odd fixed base at the first
`1920 -> 3840` transition. -/
theorem v23OddFiniteRegularBudget_allocation :
    (2 / 27 : ℝ) -
      ((1 / 384 : ℝ) + 1 / 30 + 1 / 60 + 1 / 120 + 1 / 240) =
        31 / 3456 := by
  norm_num

/-- V23 specialization of the finite-exception/dyadic adapter.  A rigorous
`1/384` estimate for the odd fixed base and a regular envelope with leading
coefficient `1/30` combine strictly inside the previous-core budget `2/27`.

The finite interval certificate supplies `hExceptionRelative`; the remaining
source-level separated-band estimate supplies `hBudgetEnvelope` and
`hRelative`. -/
theorem relativeCoupling_of_v23OddFixedBaseAndDyadicBudgets
    (exceptionEnergy exceptionCross : ℝ)
    (energy cross budget : ℕ → ℝ)
    (n : ℕ) (tail : ℝ)
    (hExceptionEnergy : 0 ≤ exceptionEnergy)
    (hExceptionRelative :
      exceptionCross ^ 2 ≤ (1 / 384 : ℝ) * exceptionEnergy * tail)
    (hEnergy : ∀ i ∈ Finset.range n, 0 ≤ energy i)
    (hBudget : ∀ i ∈ Finset.range n, 0 ≤ budget i)
    (hTail : 0 ≤ tail)
    (hBudgetEnvelope : ∀ i ∈ Finset.range n,
      budget i ≤ (1 / 30 : ℝ) * (1 / (2 : ℝ)) ^ i)
    (hRelative : ∀ i ∈ Finset.range n,
      (cross i) ^ 2 ≤ budget i * energy i * tail) :
    (exceptionCross + ∑ i ∈ Finset.range n, cross i) ^ 2 ≤
      (2 / 27 : ℝ) *
        (exceptionEnergy + ∑ i ∈ Finset.range n, energy i) * tail := by
  apply relativeCoupling_of_finiteException_and_dyadicChannelBudgets
    exceptionEnergy exceptionCross (1 / 384 : ℝ)
    energy cross budget n tail (1 / 30 : ℝ) (2 / 27 : ℝ)
    hExceptionEnergy
  · norm_num
  · exact hExceptionRelative
  · exact hEnergy
  · exact hBudget
  · exact hTail
  · norm_num
  · exact hBudgetEnvelope
  · norm_num
  · exact hRelative

/-- Combine fixed-low/shell and high-core/shell estimates into one relative
coupling bound.  The factor two is the division-free inequality
`(a+b)^2 ≤ 2*a^2 + 2*b^2`; consequently each channel may consume at most half
of the desired final coefficient.

This is the component-wise interface for the post-N1920 analysis: estimate the
decaying coupling from the fixed low block separately from the adjacent
high-mode coupling, then reassemble the whole core/shell estimate required by
`relativeCoupling_of_recursiveShell`. -/
theorem relativeCoupling_of_twoChannelBudgets
    (coreLow coreHigh tail crossLow crossHigh rhoLow rhoHigh rho : ℝ)
    (hCoreLow : 0 ≤ coreLow)
    (hCoreHigh : 0 ≤ coreHigh)
    (hTail : 0 ≤ tail)
    (hLowBudget : 2 * rhoLow ≤ rho)
    (hHighBudget : 2 * rhoHigh ≤ rho)
    (hLowRelative : crossLow ^ 2 ≤ rhoLow * coreLow * tail)
    (hHighRelative : crossHigh ^ 2 ≤ rhoHigh * coreHigh * tail) :
    (crossLow + crossHigh) ^ 2 ≤
      rho * (coreLow + coreHigh) * tail := by
  have hSquare :
      (crossLow + crossHigh) ^ 2 ≤
        2 * crossLow ^ 2 + 2 * crossHigh ^ 2 := by
    nlinarith [sq_nonneg (crossLow - crossHigh)]
  have hLowScaled :
      2 * crossLow ^ 2 ≤ 2 * (rhoLow * coreLow * tail) :=
    mul_le_mul_of_nonneg_left hLowRelative (by norm_num)
  have hHighScaled :
      2 * crossHigh ^ 2 ≤ 2 * (rhoHigh * coreHigh * tail) :=
    mul_le_mul_of_nonneg_left hHighRelative (by norm_num)
  have hLowCore : 2 * rhoLow * coreLow ≤ rho * coreLow :=
    mul_le_mul_of_nonneg_right hLowBudget hCoreLow
  have hHighCore : 2 * rhoHigh * coreHigh ≤ rho * coreHigh :=
    mul_le_mul_of_nonneg_right hHighBudget hCoreHigh
  have hLowTail :
      2 * (rhoLow * coreLow * tail) ≤ rho * coreLow * tail := by
    have := mul_le_mul_of_nonneg_right hLowCore hTail
    nlinarith
  have hHighTail :
      2 * (rhoHigh * coreHigh * tail) ≤ rho * coreHigh * tail := by
    have := mul_le_mul_of_nonneg_right hHighCore hTail
    nlinarith
  calc
    (crossLow + crossHigh) ^ 2 ≤
        2 * crossLow ^ 2 + 2 * crossHigh ^ 2 := hSquare
    _ ≤ 2 * (rhoLow * coreLow * tail) +
        2 * (rhoHigh * coreHigh * tail) := by linarith
    _ ≤ rho * coreLow * tail + rho * coreHigh * tail := by linarith
    _ = rho * (coreLow + coreHigh) * tail := by ring

/-- Optimized steady-state dyadic shell package for the post-`N=1920` route.

Each of the two reference channels may spend `2/27`.  The generic two-channel
lemma combines them into the reference coefficient `4/27`; a one-third
reserve then converts that reference estimate into the direct coefficient
`4/9`.  The second conclusion renews the same one-third reserve, so the package
can be iterated without changing constants. -/
theorem fourNinthsShell_of_twoChannelReference
    (referenceLow referenceHigh core tail crossLow crossHigh : ℝ)
    (hReferenceLow : 0 ≤ referenceLow)
    (hReferenceHigh : 0 ≤ referenceHigh)
    (hTail : 0 ≤ tail)
    (hReserveCore :
      (1 / 3 : ℝ) * (referenceLow + referenceHigh) ≤ core)
    (hLowRelative :
      crossLow ^ 2 ≤ (2 / 27 : ℝ) * referenceLow * tail)
    (hHighRelative :
      crossHigh ^ 2 ≤ (2 / 27 : ℝ) * referenceHigh * tail) :
    (crossLow + crossHigh) ^ 2 ≤ (4 / 9 : ℝ) * core * tail ∧
      (1 / 3 : ℝ) * (core + tail) ≤
        core + 2 * (crossLow + crossHigh) + tail := by
  have hReference : 0 ≤ referenceLow + referenceHigh :=
    add_nonneg hReferenceLow hReferenceHigh
  have hReferenceRelative :
      (crossLow + crossHigh) ^ 2 ≤
        (4 / 27 : ℝ) * (referenceLow + referenceHigh) * tail :=
    relativeCoupling_of_twoChannelBudgets
      referenceLow referenceHigh tail crossLow crossHigh
      (2 / 27 : ℝ) (2 / 27 : ℝ) (4 / 27 : ℝ)
      hReferenceLow hReferenceHigh hTail (by norm_num) (by norm_num)
      hLowRelative hHighRelative
  have hRelative :
      (crossLow + crossHigh) ^ 2 ≤ (4 / 9 : ℝ) * core * tail :=
    relativeShell_of_referenceReserve
      (referenceLow + referenceHigh) core tail (crossLow + crossHigh)
      (1 / 3 : ℝ) (4 / 27 : ℝ) (4 / 9 : ℝ)
      hReference hTail (by norm_num) hReserveCore (by norm_num)
      hReferenceRelative
  have hReserveNonnegative :
      0 ≤ (1 / 3 : ℝ) * (referenceLow + referenceHigh) := by positivity
  have hCore : 0 ≤ core := hReserveNonnegative.trans hReserveCore
  exact ⟨hRelative,
    fourNinthsShell_oneThirdReserve
      core tail (crossLow + crossHigh) hCore hTail hRelative⟩

/-- Recover a relative coupling inequality from nonnegativity of the scaled
two-block form for every scalar multiple of the low vector.  Algebraically,
this is the converse discriminant direction to `twoBlockEnergy_nonnegative`. -/
theorem relativeCoupling_of_scaledFormNonnegative
    (scaledLow coupling high : ℝ)
    (hScaledLow : 0 < scaledLow)
    (hForm : ∀ r : ℝ,
      0 ≤ scaledLow * r ^ 2 + 2 * coupling * r + high) :
    coupling ^ 2 ≤ scaledLow * high := by
  have hNonzero : scaledLow ≠ 0 := ne_of_gt hScaledLow
  have hAtVertex := hForm (-coupling / scaledLow)
  have hIdentity :
      scaledLow * (-coupling / scaledLow) ^ 2 +
          2 * coupling * (-coupling / scaledLow) + high =
        high - coupling ^ 2 / scaledLow := by
    field_simp [hNonzero]
    ring
  rw [hIdentity] at hAtVertex
  have hDiv : coupling ^ 2 / scaledLow ≤ high := by linarith
  have hMul : coupling ^ 2 ≤ high * scaledLow :=
    (div_le_iff₀ hScaledLow).mp hDiv
  nlinarith

section RecursiveShell

variable {E₀ M T : Type*}
variable [AddCommGroup E₀] [Module ℝ E₀]
variable [AddCommGroup M] [Module ℝ M]
variable [AddCommGroup T] [Module ℝ T]

/-- Recursive three-block gluing for the relative-energy route.

The already certified core consists of the low block `E₀` and a middle block
`M`; its scaled energy uses the desired final coefficient `q`.  A new shell
`T` may be attached when its coupling to the whole core has relative
coefficient `rho ≤ 1`.  Nonnegativity of every scaled three-block form then
recovers the same coefficient `q` between the original low block and the
enlarged high block `M ⊕ T`.

This is the exact inductive adapter for certificates of
`[[rho * R_core, C], [Cᵀ, H_shell]]`, where
`R_core = [[q * L, B], [Bᵀ, H_middle]]`. -/
theorem relativeCoupling_of_recursiveShell
    (lowForm : E₀ →ₗ[ℝ] E₀ →ₗ[ℝ] ℝ)
    (middleForm : M →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    (tailForm : T →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (lowMiddle : E₀ →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    (lowTail : E₀ →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (middleTail : M →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (q rho : ℝ)
    (hq : 0 < q)
    (hrhoOne : rho ≤ 1)
    (hLowPos : ∀ w, w ≠ 0 → 0 < lowForm w w)
    (hCoreNonneg : ∀ w m,
      0 ≤ q * lowForm w w + 2 * lowMiddle w m + middleForm m m)
    (hTailNonneg : ∀ t, 0 ≤ tailForm t t)
    (hCoreTailRelative : ∀ w m t,
      (lowTail w t + middleTail m t) ^ 2 ≤
        rho *
          (q * lowForm w w + 2 * lowMiddle w m + middleForm m m) *
          tailForm t t) :
    ∀ w m t,
      (lowMiddle w m + lowTail w t) ^ 2 ≤
        q * lowForm w w *
          (middleForm m m + 2 * middleTail m t + tailForm t t) := by
  intro w m t
  by_cases hw : w = 0
  · subst w
    simp
  have hScaledLow : 0 < q * lowForm w w :=
    mul_pos hq (hLowPos w hw)
  apply relativeCoupling_of_scaledFormNonnegative
    (q * lowForm w w)
    (lowMiddle w m + lowTail w t)
    (middleForm m m + 2 * middleTail m t + tailForm t t)
    hScaledLow
  intro r
  let coreEnergy :=
    q * lowForm (r • w) (r • w) +
      2 * lowMiddle (r • w) m + middleForm m m
  let tailEnergy := tailForm t t
  let cross := lowTail (r • w) t + middleTail m t
  have hCore : 0 ≤ coreEnergy := hCoreNonneg (r • w) m
  have hTail : 0 ≤ tailEnergy := hTailNonneg t
  have hRelative : cross ^ 2 ≤ rho * coreEnergy * tailEnergy :=
    hCoreTailRelative (r • w) m t
  have hProduct : 0 ≤ coreEnergy * tailEnergy := mul_nonneg hCore hTail
  have hRhoProduct :
      rho * (coreEnergy * tailEnergy) ≤ coreEnergy * tailEnergy := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hrhoOne hProduct)
  have hDet : cross ^ 2 ≤ coreEnergy * tailEnergy := by
    calc
      cross ^ 2 ≤ rho * coreEnergy * tailEnergy := hRelative
      _ = rho * (coreEnergy * tailEnergy) := by ring
      _ ≤ coreEnergy * tailEnergy := hRhoProduct
  have hGlue := twoBlockEnergy_nonnegative
    coreEnergy tailEnergy cross hCore hTail hDet
  dsimp [coreEnergy, tailEnergy, cross] at hGlue
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hGlue
  nlinarith [hGlue]

end RecursiveShell

/-- Nonnegativity propagates through any finite chain of scalar shell energies
whose relative determinant coefficients are at most one.

For a concrete dyadic decomposition, `energy n` is the relative energy of the
core through the `n`-th shell, while `tail n` and `cross n` are the diagonal
and cross energies of the next shell.  This theorem packages the induction
that was previously implicit in repeated uses of
`relativeCoupling_of_recursiveShell`. -/
theorem recursiveShellEnergy_nonnegative_nat
    (energy tail cross rho : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hRho : ∀ n, rho n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ rho n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n, 0 ≤ energy n := by
  intro n
  induction n with
  | zero => exact hBase
  | succ n ih =>
      have hTailN : 0 ≤ tail n := hTail n
      have hProduct : 0 ≤ energy n * tail n := mul_nonneg ih hTailN
      have hRhoProduct :
          rho n * (energy n * tail n) ≤ energy n * tail n := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hRho n) hProduct)
      have hDet : (cross n) ^ 2 ≤ energy n * tail n := by
        calc
          (cross n) ^ 2 ≤ rho n * energy n * tail n := hRelative n
          _ = rho n * (energy n * tail n) := by ring
          _ ≤ energy n * tail n := hRhoProduct
      have hGlue := twoBlockEnergy_nonnegative
        (energy n) (tail n) (cross n) ih hTailN hDet
      rw [hStep n]
      exact hGlue

/-- Variable shell coefficients preserve the finite product of their balanced
reserves.  If the `n`-th relative coefficient is `(u n)²`, then after `n`
shells the glued energy controls

`(∏ i in range n, (1-u i)) * energy 0`.

This avoids the artificial exponential loss caused by replacing every actual
coefficient by the fixed worst-case value `4/9`. -/
theorem recursiveShellEnergy_ge_reserveProduct
    (energy tail cross u : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (∏ i ∈ Finset.range n, (1 - u i)) * energy 0 ≤ energy n := by
  have hUSq : ∀ n, (u n) ^ 2 ≤ 1 := by
    intro n
    have hProduct :=
      mul_nonneg (hUNonnegative n) (sub_nonneg.mpr (hUOne n))
    nlinarith
  have hEnergyNonnegative : ∀ n, 0 ≤ energy n :=
    recursiveShellEnergy_nonnegative_nat
      energy tail cross (fun n => (u n) ^ 2)
      hBase hTail hUSq hRelative hStep
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hOneSubU : 0 ≤ 1 - u n := sub_nonneg.mpr (hUOne n)
      have hReserve :
          (1 - u n) * (energy n + tail n) ≤ energy (n + 1) := by
        rw [hStep n]
        exact sqShell_oneSubReserve
          (energy n) (tail n) (cross n) (u n)
          (hEnergyNonnegative n) (hTail n) (hUNonnegative n) (hRelative n)
      have hTailScaled :
          (1 - u n) * energy n ≤
            (1 - u n) * (energy n + tail n) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (hTail n)) hOneSubU
      have hIHScaled :
          (1 - u n) *
              ((∏ i ∈ Finset.range n, (1 - u i)) * energy 0) ≤
            (1 - u n) * energy n :=
        mul_le_mul_of_nonneg_left ih hOneSubU
      calc
        (∏ i ∈ Finset.range (n + 1), (1 - u i)) * energy 0 =
            (1 - u n) *
              ((∏ i ∈ Finset.range n, (1 - u i)) * energy 0) := by
                rw [Finset.prod_range_succ]
                ring
        _ ≤ (1 - u n) * energy n := hIHScaled
        _ ≤ (1 - u n) * (energy n + tail n) := hTailScaled
        _ ≤ energy (n + 1) := hReserve

/-- Finite reserve products obey the elementary union-bound lower estimate

`1 - sum i in range n, u i ≤ prod i in range n, (1-u i)`

whenever every `u i` lies in `[0,1]`.  This is the scalar bridge from a
summable envelope for the actual shell coefficients to a positive uniform
reserve-product floor. -/
theorem reserveProduct_ge_one_sub_partialSum
    (u : ℕ → ℝ)
    (hUNonnegative : ∀ i, 0 ≤ u i)
    (hUOne : ∀ i, u i ≤ 1) :
    ∀ n,
      1 - (∑ i ∈ Finset.range n, u i) ≤
        ∏ i ∈ Finset.range n, (1 - u i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hSumNonnegative :
          0 ≤ ∑ i ∈ Finset.range n, u i :=
        Finset.sum_nonneg (fun i _ => hUNonnegative i)
      have hOneSubU : 0 ≤ 1 - u n := sub_nonneg.mpr (hUOne n)
      have hIHScaled :
          (1 - ∑ i ∈ Finset.range n, u i) * (1 - u n) ≤
            (∏ i ∈ Finset.range n, (1 - u i)) * (1 - u n) :=
        mul_le_mul_of_nonneg_right ih hOneSubU
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      calc
        1 - ((∑ i ∈ Finset.range n, u i) + u n) ≤
            (1 - ∑ i ∈ Finset.range n, u i) * (1 - u n) := by
          nlinarith [mul_nonneg hSumNonnegative (hUNonnegative n)]
        _ ≤ (∏ i ∈ Finset.range n, (1 - u i)) * (1 - u n) :=
          hIHScaled

/-- A uniform upper bound on all finite coefficient sums gives the explicit
uniform reserve-product floor `1-total`. -/
theorem reserveProduct_ge_one_sub_of_partialSumBound
    (u : ℕ → ℝ)
    (total : ℝ)
    (hUNonnegative : ∀ i, 0 ≤ u i)
    (hUOne : ∀ i, u i ≤ 1)
    (hPartialSum : ∀ n,
      (∑ i ∈ Finset.range n, u i) ≤ total) :
    ∀ n,
      1 - total ≤ ∏ i ∈ Finset.range n, (1 - u i) := by
  intro n
  have hOneSubSum :
      1 - total ≤ 1 - ∑ i ∈ Finset.range n, u i :=
    sub_le_sub_left (hPartialSum n) 1
  exact hOneSubSum.trans
    (reserveProduct_ge_one_sub_partialSum u hUNonnegative hUOne n)

/-- If the finite sums of the actual shell coefficients are uniformly bounded
by some `total < 1`, every finite reserve product has the same strictly
positive lower bound `1-total`. -/
theorem reserveProduct_pos_of_partialSum_lt_one
    (u : ℕ → ℝ)
    (total : ℝ)
    (hUNonnegative : ∀ i, 0 ≤ u i)
    (hUOne : ∀ i, u i ≤ 1)
    (hPartialSum : ∀ n,
      (∑ i ∈ Finset.range n, u i) ≤ total)
    (hTotalOne : total < 1) :
    ∀ n, 0 < ∏ i ∈ Finset.range n, (1 - u i) := by
  intro n
  exact (sub_pos.mpr hTotalOne).trans_le
    (reserveProduct_ge_one_sub_of_partialSumBound
      u total hUNonnegative hUOne hPartialSum n)

/-- The reserve product controls the entire block-diagonal reference accumulated
through the first `n` shells, not only the initial block.

More precisely, the common finite product

`prod i in range n, (1 - u i)`

may be placed in front of `energy 0 + sum i in range n, tail i`.  At the
induction step the already accumulated blocks use the induction hypothesis,
while the new tail uses that every earlier reserve factor lies in `[0,1]`.
This is the scalar normalization needed to compare a previous-core dyadic
channel sum with the recursively glued core energy. -/
theorem recursiveShellEnergy_ge_reserveProduct_mul_blockSum
    (energy tail cross u : ℕ → ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n) :
    ∀ n,
      (∏ i ∈ Finset.range n, (1 - u i)) *
          (energy 0 + ∑ i ∈ Finset.range n, tail i) ≤ energy n := by
  have hUSq : ∀ n, (u n) ^ 2 ≤ 1 := by
    intro n
    have hProduct :=
      mul_nonneg (hUNonnegative n) (sub_nonneg.mpr (hUOne n))
    nlinarith
  have hEnergyNonnegative : ∀ n, 0 ≤ energy n :=
    recursiveShellEnergy_nonnegative_nat
      energy tail cross (fun n => (u n) ^ 2)
      hBase hTail hUSq hRelative hStep
  intro n
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty,
        add_zero, one_mul]
      exact le_rfl
  | succ n ih =>
      have hOneSubU : 0 ≤ 1 - u n := sub_nonneg.mpr (hUOne n)
      have hProductOne :
          (∏ i ∈ Finset.range n, (1 - u i)) ≤ 1 :=
        Finset.prod_le_one
          (fun i _ => sub_nonneg.mpr (hUOne i))
          (fun i _ => by linarith [hUNonnegative i])
      have hReserve :
          (1 - u n) * (energy n + tail n) ≤ energy (n + 1) := by
        rw [hStep n]
        exact sqShell_oneSubReserve
          (energy n) (tail n) (cross n) (u n)
          (hEnergyNonnegative n) (hTail n) (hUNonnegative n) (hRelative n)
      have hIHScaled :
          (1 - u n) *
              ((∏ i ∈ Finset.range n, (1 - u i)) *
                (energy 0 + ∑ i ∈ Finset.range n, tail i)) ≤
            (1 - u n) * energy n :=
        mul_le_mul_of_nonneg_left ih hOneSubU
      have hTailProduct :
          (∏ i ∈ Finset.range n, (1 - u i)) * tail n ≤ tail n := by
        calc
          (∏ i ∈ Finset.range n, (1 - u i)) * tail n ≤ 1 * tail n :=
            mul_le_mul_of_nonneg_right hProductOne (hTail n)
          _ = tail n := one_mul _
      have hTailScaled :
          (1 - u n) *
              ((∏ i ∈ Finset.range n, (1 - u i)) * tail n) ≤
            (1 - u n) * tail n :=
        mul_le_mul_of_nonneg_left hTailProduct hOneSubU
      calc
        (∏ i ∈ Finset.range (n + 1), (1 - u i)) *
              (energy 0 + ∑ i ∈ Finset.range (n + 1), tail i) =
            (1 - u n) *
                ((∏ i ∈ Finset.range n, (1 - u i)) *
                  (energy 0 + ∑ i ∈ Finset.range n, tail i)) +
              (1 - u n) *
                ((∏ i ∈ Finset.range n, (1 - u i)) * tail n) := by
                  rw [Finset.prod_range_succ, Finset.sum_range_succ]
                  ring
        _ ≤ (1 - u n) * energy n + (1 - u n) * tail n :=
          add_le_add hIHScaled hTailScaled
        _ = (1 - u n) * (energy n + tail n) := by ring
        _ ≤ energy (n + 1) := hReserve

/-- A uniform lower bound on the finite reserve products therefore controls
the whole block-diagonal reference with the same floor.  This is the direct
finite-scale adapter for a sum of previous-core dyadic channel energies. -/
theorem recursiveShellEnergy_ge_reserveFloor_mul_blockSum
    (energy tail cross u : ℕ → ℝ)
    (reserveFloor : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hReserveProduct : ∀ n,
      reserveFloor ≤ ∏ i ∈ Finset.range n, (1 - u i)) :
    ∀ n,
      reserveFloor * (energy 0 + ∑ i ∈ Finset.range n, tail i) ≤
        energy n := by
  intro n
  have hBlockSumNonnegative :
      0 ≤ energy 0 + ∑ i ∈ Finset.range n, tail i :=
    add_nonneg hBase (Finset.sum_nonneg (fun i _ => hTail i))
  have hProductBound :=
    recursiveShellEnergy_ge_reserveProduct_mul_blockSum
      energy tail cross u hBase hTail hUNonnegative hUOne hRelative hStep n
  exact
    (mul_le_mul_of_nonneg_right (hReserveProduct n) hBlockSumNonnegative).trans
      hProductBound

/-- Compose the recursive block-sum normalization directly with a next-shell
coupling estimate measured against that block-diagonal reference.  Once the
analytic layer supplies a reserve-product floor and a source-channel budget
`budget ≤ rho * reserveFloor`, the resulting coupling is relative to the
actual recursively glued core energy. -/
theorem relativeShell_of_recursiveBlockSumReserve
    (energy tail cross u : ℕ → ℝ)
    (n : ℕ)
    (newTail newCross reserveFloor budget rho : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ j, 0 ≤ tail j)
    (hUNonnegative : ∀ j, 0 ≤ u j)
    (hUOne : ∀ j, u j ≤ 1)
    (hRelative : ∀ j,
      (cross j) ^ 2 ≤ (u j) ^ 2 * energy j * tail j)
    (hStep : ∀ j,
      energy (j + 1) = energy j + 2 * cross j + tail j)
    (hReserveProduct : ∀ j,
      reserveFloor ≤ ∏ i ∈ Finset.range j, (1 - u i))
    (hNewTail : 0 ≤ newTail)
    (hRho : 0 ≤ rho)
    (hBudget : budget ≤ rho * reserveFloor)
    (hNewCross :
      newCross ^ 2 ≤
        budget * (energy 0 + ∑ i ∈ Finset.range n, tail i) * newTail) :
    newCross ^ 2 ≤ rho * energy n * newTail := by
  apply relativeShell_of_referenceReserve
    (energy 0 + ∑ i ∈ Finset.range n, tail i)
    (energy n) newTail newCross reserveFloor budget rho
  · exact add_nonneg hBase (Finset.sum_nonneg (fun i _ => hTail i))
  · exact hNewTail
  · exact hRho
  · exact recursiveShellEnergy_ge_reserveFloor_mul_blockSum
      energy tail cross u reserveFloor hBase hTail hUNonnegative hUOne
      hRelative hStep hReserveProduct n
  · exact hBudget
  · exact hNewCross

/-- A uniform lower bound on the finite reserve products yields a uniform
lower bound on every recursively glued shell energy.  The analytic layer may
now prove a positive product floor separately from the finite shell algebra. -/
theorem recursiveShellEnergy_ge_of_reserveProductLowerBound
    (energy tail cross u : ℕ → ℝ)
    (reserveFloor : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hReserveProduct : ∀ n,
      reserveFloor ≤ ∏ i ∈ Finset.range n, (1 - u i)) :
    ∀ n, reserveFloor * energy 0 ≤ energy n := by
  intro n
  have hProductBound := recursiveShellEnergy_ge_reserveProduct
    energy tail cross u hBase hTail hUNonnegative hUOne hRelative hStep n
  exact (mul_le_mul_of_nonneg_right (hReserveProduct n) hBase).trans
    hProductBound

/-- The same uniform reserve-product floor passes to any closed-form limit of
the finite shell energies. -/
theorem recursiveShellEnergy_limit_ge_of_reserveProductLowerBound
    (energy tail cross u : ℕ → ℝ)
    (reserveFloor limit : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hReserveProduct : ∀ n,
      reserveFloor ≤ ∏ i ∈ Finset.range n, (1 - u i))
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    reserveFloor * energy 0 ≤ limit := by
  apply ge_of_tendsto hTendsto
  exact Filter.Eventually.of_forall
    (recursiveShellEnergy_ge_of_reserveProductLowerBound
      energy tail cross u reserveFloor hBase hTail hUNonnegative hUOne
      hRelative hStep hReserveProduct)

/-- A positive reserve-product floor and a positive initial energy force the
closed recursively glued energy to remain strictly positive. -/
theorem recursiveShellEnergy_limit_pos_of_reserveProductLowerBound
    (energy tail cross u : ℕ → ℝ)
    (reserveFloor limit : ℝ)
    (hReserveFloor : 0 < reserveFloor)
    (hBase : 0 < energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hUNonnegative : ∀ n, 0 ≤ u n)
    (hUOne : ∀ n, u n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ (u n) ^ 2 * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hReserveProduct : ∀ n,
      reserveFloor ≤ ∏ i ∈ Finset.range n, (1 - u i))
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 < limit := by
  have hLower := recursiveShellEnergy_limit_ge_of_reserveProductLowerBound
    energy tail cross u reserveFloor limit (le_of_lt hBase) hTail
    hUNonnegative hUOne hRelative hStep hReserveProduct hTendsto
  exact (mul_pos hReserveFloor hBase).trans_le hLower

/-- If recursively glued finite-support energies converge to a closed-form
energy, the closed value is nonnegative.  The analytic operator layer only has
to supply convergence of the finite-support form values; the order passage is
now internal. -/
theorem recursiveShellEnergy_limit_nonnegative
    (energy tail cross rho : ℕ → ℝ)
    (limit : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hRho : ∀ n, rho n ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ rho n * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 ≤ limit := by
  apply ge_of_tendsto hTendsto
  exact Filter.Eventually.of_forall
    (recursiveShellEnergy_nonnegative_nat
      energy tail cross rho hBase hTail hRho hRelative hStep)

/-- Uniform-coefficient specialization used by the post-N1920 dyadic-shell
target.  A single `rhoStar ≤ 1` estimate for every later shell, together with
convergence of the finite-support energies, proves nonnegativity of the closed
tail value. -/
theorem recursiveShellEnergy_limit_nonnegative_of_uniformRho
    (energy tail cross : ℕ → ℝ)
    (limit rhoStar : ℝ)
    (hBase : 0 ≤ energy 0)
    (hTail : ∀ n, 0 ≤ tail n)
    (hRhoStar : rhoStar ≤ 1)
    (hRelative : ∀ n,
      (cross n) ^ 2 ≤ rhoStar * energy n * tail n)
    (hStep : ∀ n,
      energy (n + 1) = energy n + 2 * cross n + tail n)
    (hTendsto : Filter.Tendsto energy Filter.atTop (nhds limit)) :
    0 ≤ limit := by
  exact recursiveShellEnergy_limit_nonnegative
    energy tail cross (fun _ => rhoStar) limit
    hBase hTail (fun _ => hRhoStar) hRelative hStep hTendsto

/-- Relative-energy boundary-Weyl error estimate.

Unlike the Euclidean Schur estimate, this bound contains neither `‖eta‖²` nor
a raw source norm.  Symmetry and the two weak block equations identify the
response error with the source/high cross term. -/
theorem boundaryWeylRelativeEnergyBudget
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H) (q : ℝ)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hLowSymm : ∀ w₁ w₂, lowForm w₁ w₂ = lowForm w₂ w₁)
    (hLowNonneg : ∀ w, 0 ≤ lowForm w w)
    (hHighNonneg : ∀ z, 0 ≤ highForm z z)
    (hRelative : ∀ w z,
      (coupling w z) ^ 2 ≤
        q * lowForm w w * highForm z z)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z,
      highForm v z + coupling u z = 0) :
    (1 - q) * |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤
      q * ⟪eta, u0⟫_ℝ := by
  let d : E := u - u0
  have hU : u = d + u0 := by
    simp [d]
  have hLowAtD : lowForm d d + coupling d v = 0 := by
    simpa [d] using hLowEquation d
  have hHighAtV :
      highForm v v + (coupling d v + coupling u0 v) = 0 := by
    have h := hHighEquation v
    rw [hU] at h
    simpa only [map_add, LinearMap.add_apply] using h
  have hCouplingRelation :
      coupling u0 v = lowForm d d - highForm v v := by
    linarith
  have hCouplingD : coupling d v = -lowForm d d := by
    linarith
  have hRelativeD := hRelative d v
  rw [hCouplingD] at hRelativeD
  have hLowSquare :
      (lowForm d d) ^ 2 ≤
        q * lowForm d d * highForm v v := by
    simpa using hRelativeD
  have hScalar := relativeSchurResponseBudget
    (lowForm d d) (highForm v v) (lowForm u0 u0) q (coupling u0 v)
    (hLowNonneg d) (hHighNonneg v) (hLowNonneg u0)
    hq hqLt hCouplingRelation hLowSquare (hRelative u0 v)
  have hResponse :
      ⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ = -coupling u0 v := by
    rw [← inner_sub_right]
    change ⟪eta, d⟫_ℝ = -coupling u0 v
    rw [← hFiniteEquation d, hLowSymm u0 d]
    linarith [hLowEquation u0]
  calc
    (1 - q) * |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ|
        = (1 - q) * |coupling u0 v| := by rw [hResponse, abs_neg]
    _ ≤ q * lowForm u0 u0 := hScalar
    _ = q * ⟪eta, u0⟫_ℝ := by rw [hFiniteEquation u0]

/-- Energy-normalized Schur monotonicity: adjoining a high block whose
relative coupling satisfies `q < 1` can only increase the boundary resolvent
response.  This is the key route around the linearly growing Euclidean
boundary-vector mass. -/
theorem boundaryWeyl_mono_of_relativeEnergyCoupling
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H) (q : ℝ)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hLowSymm : ∀ w₁ w₂, lowForm w₁ w₂ = lowForm w₂ w₁)
    (hLowNonneg : ∀ w, 0 ≤ lowForm w w)
    (hHighNonneg : ∀ z, 0 ≤ highForm z z)
    (hRelative : ∀ w z,
      (coupling w z) ^ 2 ≤
        q * lowForm w w * highForm z z)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z,
      highForm v z + coupling u z = 0) :
    ⟪eta, u0⟫_ℝ ≤ ⟪eta, u⟫_ℝ := by
  let d : E := u - u0
  have hLowAtD : lowForm d d + coupling d v = 0 := by
    simpa [d] using hLowEquation d
  have hCouplingD : coupling d v = -lowForm d d := by
    linarith
  have hRelativeD := hRelative d v
  rw [hCouplingD] at hRelativeD
  have hLowSquare :
      (lowForm d d) ^ 2 ≤
        q * lowForm d d * highForm v v := by
    simpa using hRelativeD
  have hResponseNonneg :
      0 ≤ highForm v v - lowForm d d :=
    relativeSchurResponseNonnegative
      (lowForm d d) (highForm v v) q
      (hLowNonneg d) (hHighNonneg v) hq hqLt hLowSquare
  have hU : u = d + u0 := by
    simp [d]
  have hHighAtV :
      highForm v v + (coupling d v + coupling u0 v) = 0 := by
    have h := hHighEquation v
    rw [hU] at h
    simpa only [map_add, LinearMap.add_apply] using h
  have hCouplingRelation :
      coupling u0 v = lowForm d d - highForm v v := by
    linarith
  have hResponse :
      ⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ = -coupling u0 v := by
    rw [← inner_sub_right]
    change ⟪eta, d⟫_ℝ = -coupling u0 v
    rw [← hFiniteEquation d, hLowSymm u0 d]
    linarith [hLowEquation u0]
  linarith

/-- Strict finite positivity transfers through the energy-normalized Schur
system as soon as its relative coupling coefficient is below one. -/
theorem boundaryWeyl_pos_of_relativeEnergyCoupling
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H) (q : ℝ)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hFinitePos : 0 < ⟪eta, u0⟫_ℝ)
    (hLowSymm : ∀ w₁ w₂, lowForm w₁ w₂ = lowForm w₂ w₁)
    (hLowNonneg : ∀ w, 0 ≤ lowForm w w)
    (hHighNonneg : ∀ z, 0 ≤ highForm z z)
    (hRelative : ∀ w z,
      (coupling w z) ^ 2 ≤
        q * lowForm w w * highForm z z)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w,
      lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z,
      highForm v z + coupling u z = 0) :
    0 < ⟪eta, u⟫_ℝ := by
  exact hFinitePos.trans_le
    (boundaryWeyl_mono_of_relativeEnergyCoupling
      lowForm highForm coupling eta u0 u v q
      hq hqLt hLowSymm hLowNonneg hHighNonneg hRelative
      hFiniteEquation hLowEquation hHighEquation)

/-- Replace the raw Euclidean boundary mass by two source-specific weights.

`sourceWeight` controls the actual finite resolvent solution `u0`, while
`observationWeight` controls the boundary functional only on the subspace that
contains the Schur error `u - u0`.  This is the interface needed by a weighted
boundary or prolate-tail estimate: neither weight has to be the global norm
`‖eta‖`, whose square grows linearly with the retained cutoff in the concrete
CvS boundary vector. -/
theorem boundaryWeylError_le_of_weightedBlockSchur
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (errorSpace : Set E)
    (eta u0 u : E) (v : H)
    (lowGap highGap epsilon sourceWeight observationWeight : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hObservationWeight : 0 ≤ observationWeight)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0)
    (hSource : ‖u0‖ ≤ sourceWeight)
    (hErrorMem : u - u0 ∈ errorSpace)
    (hObservation : ∀ w ∈ errorSpace,
      |⟪eta, w⟫_ℝ| ≤ observationWeight * ‖w‖) :
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤
      observationWeight * sourceWeight * epsilon ^ 2 /
        (lowGap * highGap - epsilon ^ 2) := by
  have hError := lowComponentError_norm_le
    lowForm highForm coupling u0 u v
    lowGap highGap epsilon hLowGap hHighGap hEpsilon hSmall
    hLowCoercive hHighCoercive hCoupling hLowEquation hHighEquation
  have hResponse :
      |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤
        observationWeight * ‖u - u0‖ := by
    rw [← inner_sub_right]
    exact hObservation (u - u0) hErrorMem
  have hDenomPos : 0 < lowGap * highGap - epsilon ^ 2 :=
    sub_pos.mpr hSmall
  have hFactor :
      0 ≤ epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2) := by
    positivity
  have hErrorScaled :=
    mul_le_mul_of_nonneg_left hError hObservationWeight
  have hSourceScaled := mul_le_mul_of_nonneg_left hSource hFactor
  have hSourceObserved :=
    mul_le_mul_of_nonneg_left hSourceScaled hObservationWeight
  calc
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤
        observationWeight * ‖u - u0‖ := hResponse
    _ ≤ observationWeight *
        ((epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * ‖u0‖) :=
      hErrorScaled
    _ ≤ observationWeight *
        ((epsilon ^ 2 / (lowGap * highGap - epsilon ^ 2)) * sourceWeight) :=
      hSourceObserved
    _ = observationWeight * sourceWeight * epsilon ^ 2 /
        (lowGap * highGap - epsilon ^ 2) := by ring

/-- Division-free weighted-boundary Schur budget.  Compared with the global
Euclidean estimate, the numerator is `observationWeight * sourceWeight` rather
than `‖eta‖²`. -/
theorem boundaryWeylError_le_margin_of_weightedBlockSchur
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (errorSpace : Set E)
    (eta u0 u : E) (v : H)
    (lowGap highGap epsilon sourceWeight observationWeight margin : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hObservationWeight : 0 ≤ observationWeight)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0)
    (hSource : ‖u0‖ ≤ sourceWeight)
    (hErrorMem : u - u0 ∈ errorSpace)
    (hObservation : ∀ w ∈ errorSpace,
      |⟪eta, w⟫_ℝ| ≤ observationWeight * ‖w‖)
    (hBudget :
      observationWeight * sourceWeight * epsilon ^ 2 ≤
        margin * (lowGap * highGap - epsilon ^ 2)) :
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤ margin := by
  have hRaw := boundaryWeylError_le_of_weightedBlockSchur
    lowForm highForm coupling errorSpace eta u0 u v
    lowGap highGap epsilon sourceWeight observationWeight
    hLowGap hHighGap hEpsilon hObservationWeight hSmall
    hLowCoercive hHighCoercive hCoupling hLowEquation hHighEquation
    hSource hErrorMem hObservation
  have hDenomPos : 0 < lowGap * highGap - epsilon ^ 2 :=
    sub_pos.mpr hSmall
  exact hRaw.trans ((div_le_iff₀ hDenomPos).2 hBudget)

/-- Monotone interval-certificate adapter for the weighted budget.  A certified
upper bound on the source/observation product and on `epsilon²` can be checked
without division. -/
theorem weightedSchurBudget_of_upperBounds
    (sourceWeight observationWeight boundaryProduct
      lowGap highGap epsilon couplingSq margin : ℝ)
    (hBoundaryProduct : 0 ≤ boundaryProduct)
    (hMargin : 0 ≤ margin)
    (hWeightProduct :
      observationWeight * sourceWeight ≤ boundaryProduct)
    (hCouplingSq : epsilon ^ 2 ≤ couplingSq)
    (hUpperBudget :
      boundaryProduct * couplingSq ≤
        margin * (lowGap * highGap - couplingSq)) :
    observationWeight * sourceWeight * epsilon ^ 2 ≤
      margin * (lowGap * highGap - epsilon ^ 2) := by
  have hWeightScaled :=
    mul_le_mul_of_nonneg_right hWeightProduct (sq_nonneg epsilon)
  have hCouplingScaled :=
    mul_le_mul_of_nonneg_left hCouplingSq hBoundaryProduct
  have hDenomMonotone :
      margin * (lowGap * highGap - couplingSq) ≤
        margin * (lowGap * highGap - epsilon ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hMargin
  exact hWeightScaled.trans
    (hCouplingScaled.trans (hUpperBudget.trans hDenomMonotone))


/-- Division-free budget form of `boundaryWeylError_le_of_blockSchur`.  This is
suited to interval certificates: only products of certified lower and upper
bounds occur in the acceptance inequality. -/
theorem boundaryWeylError_le_margin_of_blockSchur
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H)
    (lowGap highGap epsilon margin : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0)
    (hBudget :
      ‖eta‖ ^ 2 * epsilon ^ 2 ≤
        margin * lowGap * (lowGap * highGap - epsilon ^ 2)) :
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤ margin := by
  have hRaw := boundaryWeylError_le_of_blockSchur
    lowForm highForm coupling eta u0 u v
    lowGap highGap epsilon hLowGap hHighGap hEpsilon hSmall
    hLowCoercive hHighCoercive hCoupling
    hFiniteEquation hLowEquation hHighEquation
  have hDenomPos :
      0 < lowGap * (lowGap * highGap - epsilon ^ 2) :=
    mul_pos hLowGap (sub_pos.mpr hSmall)
  exact hRaw.trans ((div_le_iff₀ hDenomPos).2 (by
    simpa [mul_assoc] using hBudget))

/-- High-gap-oriented wrapper of the division-free error theorem. -/
theorem boundaryWeylError_le_margin_of_blockSchur_highGapBudget
    (lowForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta u0 u : E) (v : H)
    (etaNormSq lowGap highGap epsilon margin : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ w, lowGap * ‖w‖ ^ 2 ≤ lowForm w w)
    (hHighCoercive : ∀ z, highGap * ‖z‖ ^ 2 ≤ highForm z z)
    (hCoupling : ∀ w z, |coupling w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hFiniteEquation : ∀ w, lowForm u0 w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ w, lowForm (u - u0) w + coupling w v = 0)
    (hHighEquation : ∀ z, highForm v z + coupling u z = 0)
    (hEtaNorm : ‖eta‖ ^ 2 ≤ etaNormSq)
    (hHighGapBudget :
      epsilon ^ 2 * (etaNormSq + margin * lowGap) ≤
        margin * lowGap ^ 2 * highGap) :
    |⟪eta, u⟫_ℝ - ⟪eta, u0⟫_ℝ| ≤ margin := by
  apply boundaryWeylError_le_margin_of_blockSchur
    lowForm highForm coupling eta u0 u v
    lowGap highGap epsilon margin
    hLowGap hHighGap hEpsilon hSmall
    hLowCoercive hHighCoercive hCoupling
    hFiniteEquation hLowEquation hHighEquation
  exact schurProductBudget_of_highGapBudget
    eta etaNormSq lowGap highGap epsilon margin
    hEtaNorm hHighGapBudget

section UniformDomain

variable {X : Type*}

/-- Uniform compact/domain form of the Schur tail estimate.  At each spectral
parameter `x`, `u0 x` solves the finite low-block resolvent equation and
`(u x, v x)` solves the full low/high block system. -/
theorem boundaryWeylErrorOn_le_margin_of_blockSchur
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta : E) (u0 u : X → E) (v : X → H)
    (lowGap highGap epsilon margin : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ x ∈ domain, ∀ w,
      lowGap * ‖w‖ ^ 2 ≤ lowForm x w w)
    (hHighCoercive : ∀ x ∈ domain, ∀ z,
      highGap * ‖z‖ ^ 2 ≤ highForm x z z)
    (hCoupling : ∀ x ∈ domain, ∀ w z,
      |coupling x w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hFiniteEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u0 x) w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0)
    (hBudget :
      ‖eta‖ ^ 2 * epsilon ^ 2 ≤
        margin * lowGap * (lowGap * highGap - epsilon ^ 2)) :
    ∀ x ∈ domain,
      |⟪eta, u0 x⟫_ℝ - ⟪eta, u x⟫_ℝ| ≤ margin := by
  intro x hx
  rw [abs_sub_comm]
  exact boundaryWeylError_le_margin_of_blockSchur
    (lowForm x) (highForm x) (coupling x)
    eta (u0 x) (u x) (v x)
    lowGap highGap epsilon margin
    hLowGap hHighGap hEpsilon hSmall
    (hLowCoercive x hx) (hHighCoercive x hx)
    (hCoupling x hx) (hFiniteEquation x hx)
    (hLowEquation x hx) (hHighEquation x hx) hBudget

/-- Compact/domain-uniform weighted-boundary Schur estimate.  The analytic
adapter supplies, for every spectral parameter, a subspace containing the
actual low-block error together with a boundary-functional norm on that
subspace and a direct bound on the finite resolvent source. -/
theorem boundaryWeylErrorOn_le_margin_of_weightedBlockSchur
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (errorSpace : X → Set E)
    (eta : E) (u0 u : X → E) (v : X → H)
    (lowGap highGap epsilon sourceWeight observationWeight margin : ℝ)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hObservationWeight : 0 ≤ observationWeight)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hLowCoercive : ∀ x ∈ domain, ∀ w,
      lowGap * ‖w‖ ^ 2 ≤ lowForm x w w)
    (hHighCoercive : ∀ x ∈ domain, ∀ z,
      highGap * ‖z‖ ^ 2 ≤ highForm x z z)
    (hCoupling : ∀ x ∈ domain, ∀ w z,
      |coupling x w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0)
    (hSource : ∀ x ∈ domain, ‖u0 x‖ ≤ sourceWeight)
    (hErrorMem : ∀ x ∈ domain, u x - u0 x ∈ errorSpace x)
    (hObservation : ∀ x ∈ domain, ∀ w ∈ errorSpace x,
      |⟪eta, w⟫_ℝ| ≤ observationWeight * ‖w‖)
    (hBudget :
      observationWeight * sourceWeight * epsilon ^ 2 ≤
        margin * (lowGap * highGap - epsilon ^ 2)) :
    ∀ x ∈ domain,
      |⟪eta, u0 x⟫_ℝ - ⟪eta, u x⟫_ℝ| ≤ margin := by
  intro x hx
  rw [abs_sub_comm]
  exact boundaryWeylError_le_margin_of_weightedBlockSchur
    (lowForm x) (highForm x) (coupling x) (errorSpace x)
    eta (u0 x) (u x) (v x)
    lowGap highGap epsilon sourceWeight observationWeight margin
    hLowGap hHighGap hEpsilon hObservationWeight hSmall
    (hLowCoercive x hx) (hHighCoercive x hx) (hCoupling x hx)
    (hLowEquation x hx) (hHighEquation x hx)
    (hSource x hx) (hErrorMem x hx) (hObservation x hx) hBudget

/-- Domain-uniform energy-normalized Schur monotonicity.  A common `q < 1`
certificate makes every full boundary response dominate its finite retained
response on the domain. -/
theorem boundaryWeyl_monoOn_of_relativeEnergyCoupling
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta : E) (u0 u : X → E) (v : X → H) (q : ℝ)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hLowSymm : ∀ x ∈ domain, ∀ w₁ w₂,
      lowForm x w₁ w₂ = lowForm x w₂ w₁)
    (hLowNonneg : ∀ x ∈ domain, ∀ w,
      0 ≤ lowForm x w w)
    (hHighNonneg : ∀ x ∈ domain, ∀ z,
      0 ≤ highForm x z z)
    (hRelative : ∀ x ∈ domain, ∀ w z,
      (coupling x w z) ^ 2 ≤
        q * lowForm x w w * highForm x z z)
    (hFiniteEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u0 x) w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0) :
    ∀ x ∈ domain,
      ⟪eta, u0 x⟫_ℝ ≤ ⟪eta, u x⟫_ℝ := by
  intro x hx
  exact boundaryWeyl_mono_of_relativeEnergyCoupling
    (lowForm x) (highForm x) (coupling x)
    eta (u0 x) (u x) (v x) q hq hqLt
    (hLowSymm x hx) (hLowNonneg x hx) (hHighNonneg x hx)
    (hRelative x hx) (hFiniteEquation x hx)
    (hLowEquation x hx) (hHighEquation x hx)

/-- Pointwise finite positivity transfers to the full response throughout a
domain once the common relative-energy coupling coefficient is below one. -/
theorem positiveOn_of_relativeEnergyCoupling
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta : E) (u0 u : X → E) (v : X → H) (q : ℝ)
    (hq : 0 ≤ q)
    (hqLt : q < 1)
    (hFinitePos : ∀ x ∈ domain, 0 < ⟪eta, u0 x⟫_ℝ)
    (hLowSymm : ∀ x ∈ domain, ∀ w₁ w₂,
      lowForm x w₁ w₂ = lowForm x w₂ w₁)
    (hLowNonneg : ∀ x ∈ domain, ∀ w,
      0 ≤ lowForm x w w)
    (hHighNonneg : ∀ x ∈ domain, ∀ z,
      0 ≤ highForm x z z)
    (hRelative : ∀ x ∈ domain, ∀ w z,
      (coupling x w z) ^ 2 ≤
        q * lowForm x w w * highForm x z z)
    (hFiniteEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u0 x) w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0) :
    ∀ x ∈ domain, 0 < ⟪eta, u x⟫_ℝ := by
  have hMono := boundaryWeyl_monoOn_of_relativeEnergyCoupling
    domain lowForm highForm coupling eta u0 u v q hq hqLt
    hLowSymm hLowNonneg hHighNonneg hRelative
    hFiniteEquation hLowEquation hHighEquation
  intro x hx
  exact (hFinitePos x hx).trans_le (hMono x hx)

/-- Direct positivity bridge: a finite boundary response of at least twice the
margin stays positive for the full response once the block-Schur product
budget fits inside one margin. -/
theorem positiveOn_of_finiteMargin_and_blockSchur
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (eta : E) (u0 u : X → E) (v : X → H)
    (lowGap highGap epsilon margin : ℝ)
    (hMargin : 0 < margin)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hFiniteMargin : ∀ x ∈ domain, 2 * margin ≤ ⟪eta, u0 x⟫_ℝ)
    (hLowCoercive : ∀ x ∈ domain, ∀ w,
      lowGap * ‖w‖ ^ 2 ≤ lowForm x w w)
    (hHighCoercive : ∀ x ∈ domain, ∀ z,
      highGap * ‖z‖ ^ 2 ≤ highForm x z z)
    (hCoupling : ∀ x ∈ domain, ∀ w z,
      |coupling x w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hFiniteEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u0 x) w = ⟪eta, w⟫_ℝ)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0)
    (hBudget :
      ‖eta‖ ^ 2 * epsilon ^ 2 ≤
        margin * lowGap * (lowGap * highGap - epsilon ^ 2)) :
    ∀ x ∈ domain, 0 < ⟪eta, u x⟫_ℝ := by
  apply RiemannCvs.BoundaryWeylUniformLimit.positiveOn_of_finiteMargin_and_uniformError
    (fun x => ⟪eta, u0 x⟫_ℝ) (fun x => ⟪eta, u x⟫_ℝ)
    domain margin hMargin hFiniteMargin
  exact boundaryWeylErrorOn_le_margin_of_blockSchur
    domain lowForm highForm coupling eta u0 u v
    lowGap highGap epsilon margin
    hLowGap hHighGap hEpsilon hSmall
    hLowCoercive hHighCoercive hCoupling
    hFiniteEquation hLowEquation hHighEquation hBudget

/-- Positivity bridge for the weighted-boundary interface.  This is the final
compact-window API expected from a concrete CvS/prolate adapter: a finite
margin, uniform block equations, a restricted boundary observation bound, and
the weighted product budget imply positivity of the full boundary response. -/
theorem positiveOn_of_finiteMargin_and_weightedBlockSchur
    (domain : Set X)
    (lowForm : X → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (highForm : X → H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (coupling : X → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (errorSpace : X → Set E)
    (eta : E) (u0 u : X → E) (v : X → H)
    (lowGap highGap epsilon sourceWeight observationWeight margin : ℝ)
    (hMargin : 0 < margin)
    (hLowGap : 0 < lowGap)
    (hHighGap : 0 < highGap)
    (hEpsilon : 0 ≤ epsilon)
    (hObservationWeight : 0 ≤ observationWeight)
    (hSmall : epsilon ^ 2 < lowGap * highGap)
    (hFiniteMargin : ∀ x ∈ domain, 2 * margin ≤ ⟪eta, u0 x⟫_ℝ)
    (hLowCoercive : ∀ x ∈ domain, ∀ w,
      lowGap * ‖w‖ ^ 2 ≤ lowForm x w w)
    (hHighCoercive : ∀ x ∈ domain, ∀ z,
      highGap * ‖z‖ ^ 2 ≤ highForm x z z)
    (hCoupling : ∀ x ∈ domain, ∀ w z,
      |coupling x w z| ≤ epsilon * ‖w‖ * ‖z‖)
    (hLowEquation : ∀ x ∈ domain, ∀ w,
      lowForm x (u x - u0 x) w + coupling x w (v x) = 0)
    (hHighEquation : ∀ x ∈ domain, ∀ z,
      highForm x (v x) z + coupling x (u x) z = 0)
    (hSource : ∀ x ∈ domain, ‖u0 x‖ ≤ sourceWeight)
    (hErrorMem : ∀ x ∈ domain, u x - u0 x ∈ errorSpace x)
    (hObservation : ∀ x ∈ domain, ∀ w ∈ errorSpace x,
      |⟪eta, w⟫_ℝ| ≤ observationWeight * ‖w‖)
    (hBudget :
      observationWeight * sourceWeight * epsilon ^ 2 ≤
        margin * (lowGap * highGap - epsilon ^ 2)) :
    ∀ x ∈ domain, 0 < ⟪eta, u x⟫_ℝ := by
  apply RiemannCvs.BoundaryWeylUniformLimit.positiveOn_of_finiteMargin_and_uniformError
    (fun x => ⟪eta, u0 x⟫_ℝ) (fun x => ⟪eta, u x⟫_ℝ)
    domain margin hMargin hFiniteMargin
  exact boundaryWeylErrorOn_le_margin_of_weightedBlockSchur
    domain lowForm highForm coupling errorSpace eta u0 u v
    lowGap highGap epsilon sourceWeight observationWeight margin
    hLowGap hHighGap hEpsilon hObservationWeight hSmall
    hLowCoercive hHighCoercive hCoupling hLowEquation hHighEquation
    hSource hErrorMem hObservation hBudget

end UniformDomain

end RiemannCvs.BoundaryWeylSchurTail
