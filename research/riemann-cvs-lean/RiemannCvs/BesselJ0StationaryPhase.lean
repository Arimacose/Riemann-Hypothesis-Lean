import RiemannCvs.BesselJ0IntegralRepresentation

namespace RiemannCvs.BesselJ0StationaryPhase

open Real Set MeasureTheory
open scoped Interval

/-!
# Centered stationary-phase form of the concrete order-zero Bessel series

`BesselJ0IntegralRepresentation` identifies the repository power series with

`π⁻¹ ∫ t in 0..π, cos (x * sin t)`.

This module moves the interior stationary point `t = π / 2` to the origin,
uses the evenness of the centered integrand to reduce to one half-interval, and
records the exact geometry of the phase `cos u`.  In particular, the coordinate

`s = 2 * sin (u / 2)`

turns the phase into the exact quadratic `1 - s² / 2`.  These identities are
the starting data for constructing the even and odd large-argument remainders
required by `BesselJ0Dlmf.HasFirstDlmfRemainderBound`.
-/

/-- Translating by `π / 2` moves the unique interior stationary point of the
Poisson--Schlafli integral to the origin. -/
theorem integral_cos_sin_eq_centered (x : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin t)) =
      ∫ u in -(Real.pi / 2)..Real.pi / 2,
        Real.cos (x * Real.cos u) := by
  have h := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => Real.cos (x * Real.sin t)) (Real.pi / 2)
    (a := -(Real.pi / 2)) (b := Real.pi / 2)
  simpa [Real.sin_add_pi_div_two] using h.symm

/-- The centered integrand is continuous and hence integrable on every compact
interval. -/
theorem intervalIntegrable_centeredIntegrand (x a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.cos (x * Real.cos u))
      volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Evenness reduces the centered oscillatory integral to twice its right
half. -/
theorem integral_cos_cos_centered_eq_two_mul_half (x : ℝ) :
    (∫ u in -(Real.pi / 2)..Real.pi / 2,
        Real.cos (x * Real.cos u)) =
      2 * ∫ u in (0 : ℝ)..Real.pi / 2,
        Real.cos (x * Real.cos u) := by
  let g : ℝ → ℝ := fun u => Real.cos (x * Real.cos u)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hleft : IntervalIntegrable g volume (-(Real.pi / 2)) 0 :=
    hg.intervalIntegrable _ _
  have hright : IntervalIntegrable g volume 0 (Real.pi / 2) :=
    hg.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect := intervalIntegral.integral_comp_neg g
    (a := (0 : ℝ)) (b := Real.pi / 2)
  have heven :
      (∫ u in (0 : ℝ)..Real.pi / 2, g u) =
        ∫ u in -(Real.pi / 2)..(0 : ℝ), g u := by
    simpa [g, Real.cos_neg] using hreflect
  change (∫ u in -(Real.pi / 2)..Real.pi / 2, g u) =
    2 * ∫ u in (0 : ℝ)..Real.pi / 2, g u
  rw [← hsplit, ← heven]
  ring

/-- Centered full-interval representation of the concrete repository `J₀`. -/
theorem besselJ0_centered_integral_representation (x : ℝ) :
    BesselJ0Series.besselJ0 x =
      Real.pi⁻¹ * ∫ u in -(Real.pi / 2)..Real.pi / 2,
        Real.cos (x * Real.cos u) := by
  rw [BesselJ0IntegralRepresentation.besselJ0_integral_representation,
    integral_cos_sin_eq_centered]

/-- Half-interval stationary-phase representation, with the stationary point
at the left endpoint. -/
theorem besselJ0_half_interval_representation (x : ℝ) :
    BesselJ0Series.besselJ0 x =
      (2 / Real.pi) * ∫ u in (0 : ℝ)..Real.pi / 2,
        Real.cos (x * Real.cos u) := by
  rw [besselJ0_centered_integral_representation,
    integral_cos_cos_centered_eq_two_mul_half]
  field_simp [Real.pi_ne_zero]

/-- The centered oscillatory phase. -/
noncomputable def stationaryPhase (u : ℝ) : ℝ := Real.cos u

/-- Its first derivative, named separately for later integration-by-parts
arguments. -/
noncomputable def stationaryPhaseDerivative (u : ℝ) : ℝ := -Real.sin u

@[simp]
theorem stationaryPhase_zero : stationaryPhase 0 = 1 := by
  simp [stationaryPhase]

@[simp]
theorem stationaryPhase_pi_div_two :
    stationaryPhase (Real.pi / 2) = 0 := by
  simp [stationaryPhase]

@[simp]
theorem stationaryPhase_neg (u : ℝ) :
    stationaryPhase (-u) = stationaryPhase u := by
  simp [stationaryPhase]

theorem hasDerivAt_stationaryPhase (u : ℝ) :
    HasDerivAt stationaryPhase (stationaryPhaseDerivative u) u := by
  change HasDerivAt (fun v : ℝ => Real.cos v) (-Real.sin u) u
  exact Real.hasDerivAt_cos u

@[simp]
theorem stationaryPhaseDerivative_zero :
    stationaryPhaseDerivative 0 = 0 := by
  simp [stationaryPhaseDerivative]

theorem hasDerivAt_stationaryPhaseDerivative (u : ℝ) :
    HasDerivAt stationaryPhaseDerivative (-Real.cos u) u := by
  change HasDerivAt (fun v : ℝ => -Real.sin v) (-Real.cos u) u
  exact (Real.hasDerivAt_sin u).neg

/-- The stationary point is quadratically nondegenerate: its second derivative
is exactly `-1`. -/
theorem stationaryPhase_secondDerivative_at_zero :
    HasDerivAt stationaryPhaseDerivative (-1) 0 := by
  simpa using hasDerivAt_stationaryPhaseDerivative 0

/-- On the right half-interval, the phase decreases strictly from `1` to `0`. -/
theorem strictAntiOn_stationaryPhase_half :
    StrictAntiOn stationaryPhase (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  unfold stationaryPhase
  apply Real.strictAntiOn_cos.mono
  intro u hu
  exact ⟨hu.1, hu.2.trans (by linarith [Real.pi_pos])⟩

theorem stationaryPhaseDerivative_neg_of_mem_Ioo
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    stationaryPhaseDerivative u < 0 := by
  unfold stationaryPhaseDerivative
  exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi hu.1
    (hu.2.trans (by linarith [Real.pi_pos])))

theorem stationaryPhaseDerivative_pos_of_mem_Ioo
    {u : ℝ} (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ)) :
    0 < stationaryPhaseDerivative u := by
  unfold stationaryPhaseDerivative
  apply neg_pos.mpr
  apply Real.sin_neg_of_neg_of_neg_pi_lt hu.2
  have h : -Real.pi < -(Real.pi / 2) := by linarith [Real.pi_pos]
  exact h.trans hu.1

/-- The centered phase has exactly one critical point on its whole integration
interval. -/
theorem stationaryPhaseDerivative_eq_zero_iff
    {u : ℝ} (hu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    stationaryPhaseDerivative u = 0 ↔ u = 0 := by
  unfold stationaryPhaseDerivative
  rw [neg_eq_zero]
  exact Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hu.1, Real.pi_pos])
    (by linarith [hu.2, Real.pi_pos])

/-- Half-angle form of the nondegenerate stationary phase. -/
theorem stationaryPhase_quadratic_identity (u : ℝ) :
    stationaryPhase u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
  calc
    stationaryPhase u = Real.cos u := rfl
    _ = Real.cos (2 * (u / 2)) := by congr 1; ring
    _ = 2 * Real.cos (u / 2) ^ 2 - 1 := Real.cos_two_mul _
    _ = 1 - 2 * Real.sin (u / 2) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (u / 2)]

/-- Exact coordinate which turns the phase into a quadratic polynomial. -/
noncomputable def stationaryCoordinate (u : ℝ) : ℝ :=
  2 * Real.sin (u / 2)

@[simp]
theorem stationaryCoordinate_zero : stationaryCoordinate 0 = 0 := by
  simp [stationaryCoordinate]

@[simp]
theorem stationaryCoordinate_pi_div_two :
    stationaryCoordinate (Real.pi / 2) = Real.sqrt 2 := by
  rw [stationaryCoordinate]
  rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring,
    Real.sin_pi_div_four]
  ring

/-- In the stationary coordinate the phase is exactly `1 - s² / 2`, rather
than merely asymptotic to a quadratic. -/
theorem stationaryPhase_eq_one_sub_coordinate_sq_half (u : ℝ) :
    stationaryPhase u = 1 - stationaryCoordinate u ^ 2 / 2 := by
  rw [stationaryPhase_quadratic_identity]
  unfold stationaryCoordinate
  ring

theorem hasDerivAt_stationaryCoordinate (u : ℝ) :
    HasDerivAt stationaryCoordinate (Real.cos (u / 2)) u := by
  change HasDerivAt (fun v : ℝ => 2 * Real.sin (v / 2))
    (Real.cos (u / 2)) u
  have h := (Real.hasDerivAt_sin (u / 2)).comp u
    ((hasDerivAt_id u).div_const 2)
  have h' := h.const_mul (2 : ℝ)
  have hCoefficient :
      (2 : ℝ) * (Real.cos (u / 2) * (1 / 2)) = Real.cos (u / 2) := by
    ring
  rw [hCoefficient] at h'
  simpa [Function.comp_def] using h'

theorem stationaryCoordinate_derivative_pos
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos (u / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [hu.1, hu.2, Real.pi_pos]

/-- The exact quadratic coordinate is orientation-preserving on the reduced
integration interval. -/
theorem strictMonoOn_stationaryCoordinate :
    StrictMonoOn stationaryCoordinate (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  intro u hu v hv huv
  unfold stationaryCoordinate
  have huHalf : u / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hu.1, hu.2, Real.pi_pos]
  have hvHalf : v / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hv.1, hv.2, Real.pi_pos]
  have hSin : Real.sin (u / 2) < Real.sin (v / 2) :=
    Real.strictMonoOn_sin huHalf hvHalf (by linarith)
  linarith

/-- The cosine integrand becomes a Fresnel-type quadratic oscillation in the
stationary coordinate. -/
theorem oscillatoryIntegrand_quadratic (x u : ℝ) :
    Real.cos (x * stationaryPhase u) =
      Real.cos (x - (x / 2) * stationaryCoordinate u ^ 2) := by
  rw [stationaryPhase_eq_one_sub_coordinate_sq_half]
  congr 1
  ring

/-- Exact cosine/sine splitting which exposes the two parity sectors of the
large-argument expansion. -/
theorem oscillatoryIntegrand_quadratic_split (x u : ℝ) :
    Real.cos (x * stationaryPhase u) =
      Real.cos x * Real.cos ((x / 2) * stationaryCoordinate u ^ 2) +
        Real.sin x * Real.sin ((x / 2) * stationaryCoordinate u ^ 2) := by
  rw [oscillatoryIntegrand_quadratic, Real.cos_sub]

end RiemannCvs.BesselJ0StationaryPhase
