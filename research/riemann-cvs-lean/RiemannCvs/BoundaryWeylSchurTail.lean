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
