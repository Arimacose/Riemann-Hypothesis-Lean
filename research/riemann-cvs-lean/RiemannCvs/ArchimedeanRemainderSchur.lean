import RiemannCvs.V23BoundaryWeylMainline

noncomputable section

/-!
# Archimedean remainder Schur closure

This module closes the off-diagonal Archimedean remainder on every consecutive
dyadic shell above mode 960. Its central estimate is deliberately entrywise:
the centered logarithmic symbol satisfies the inverse-mode envelope, the
same-sign and reflected parity entries are then bounded explicitly, and the
finite quadratic form is controlled by the shell cardinality. No numerical
interval certificate or operator-norm hypothesis is used.
-/
open scoped BigOperators

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.C13ArchimedeanEndpoint
open RiemannCvs.DigammaEulerMaclaurin
open RiemannCvs.BoundaryWeylSchurTail

lemma arctan_le_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  let f : ℝ → ℝ := fun u => u - Real.arctan u
  have hf : Differentiable ℝ f := by
    change Differentiable ℝ (id - Real.arctan)
    exact differentiable_id.sub Real.differentiable_arctan
  have hderiv : ∀ u : ℝ, 0 ≤ deriv f u := by
    intro u
    have hdu : deriv f u = 1 - 1 / (1 + u ^ 2) := by
      change deriv (id - Real.arctan) u = 1 - 1 / (1 + u ^ 2)
      exact ((hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)).deriv
    rw [hdu]
    have hden : (0 : ℝ) < 1 + u ^ 2 := by positivity
    rw [sub_nonneg, div_le_one hden]
    nlinarith [sq_nonneg u]
  have hmono : Monotone f := monotone_of_deriv_nonneg hf hderiv
  have h := hmono ht
  simpa [f] using h

lemma archimedeanArgument_arg_complement_le
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    Real.pi / 2 - (archimedeanArgument c x).arg ≤
      1 / (4 * archimedeanAsymptoticHeight c x) := by
  let z : ℂ := archimedeanArgument c x
  let y : ℝ := archimedeanAsymptoticHeight c x
  have hy : 0 < y := by
    simpa [y] using archimedeanAsymptoticHeight_pos c x hc hx
  have hzre : z.re = 1 / 4 := by simp [z]
  have hzim : z.im = y := by simp [z, y]
  have harg0 : -(Real.pi / 2) < z.arg := by
    have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.2 (by
      rw [hzim]
      exact hy.le)
    linarith [Real.pi_pos]
  have harg2 : z.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.2 (Or.inl (by
      rw [hzre]
      norm_num))
  have htan : Real.tan z.arg = 4 * y := by
    rw [Complex.tan_arg, hzre, hzim]
    ring
  have harg : Real.arctan (4 * y) = z.arg := by
    rw [← htan]
    exact Real.arctan_tan harg0 harg2
  have hinv := Real.arctan_inv_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hy)
  have hcomp :
      Real.pi / 2 - z.arg = Real.arctan (1 / (4 * y)) := by
    rw [← harg, ← hinv]
    congr 1
    rw [inv_eq_one_div]
  rw [hcomp]
  exact arctan_le_self_of_nonneg (by positivity)

lemma archimedeanArgument_halfInv_im
    (c x : ℝ) :
    (1 / (2 * archimedeanArgument c x) : ℂ).im =
      -archimedeanAsymptoticHeight c x /
        (2 * ((1 / 4 : ℝ) ^ 2 +
          archimedeanAsymptoticHeight c x ^ 2)) := by
  rw [show (1 / (2 * archimedeanArgument c x) : ℂ) =
      (1 / 2 : ℂ) * (archimedeanArgument c x)⁻¹ by ring,
    Complex.mul_im, Complex.inv_im]
  simp [Complex.normSq_apply]
  have hden : (1 / 16 : ℝ) + archimedeanAsymptoticHeight c x ^ 2 ≠ 0 := by
    positivity
  field_simp [hden]

lemma archimedeanDigammaImaginary_model
    (c x : ℝ) :
    (Complex.digamma (archimedeanArgument c x)).im =
      (archimedeanArgument c x).arg +
        archimedeanAsymptoticHeight c x /
          (2 * ((1 / 4 : ℝ) ^ 2 +
            archimedeanAsymptoticHeight c x ^ 2)) +
        (Complex.digamma (archimedeanArgument c x) -
          (Complex.log (archimedeanArgument c x) -
            1 / (2 * archimedeanArgument c x))).im := by
  rw [Complex.sub_im, Complex.sub_im, Complex.log_im,
    archimedeanArgument_halfInv_im]
  ring

lemma archimedean_reciprocal_imaginary_le
    {y : ℝ} (hy : 0 < y) :
    y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) ≤ 1 / (4 * y) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg y]

theorem centeredLogarithmicArchimedeanSymbol_bounds
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    let y := archimedeanAsymptoticHeight c x
    logarithmicArchimedeanSymbol c x - Real.pi / 4 ≤
        1 / (4 * y) + Real.sqrt 2 / (12 * y ^ 2) ∧
      -(logarithmicArchimedeanSymbol c x - Real.pi / 4) ≤
        1 / (8 * y) + Real.sqrt 2 / (12 * y ^ 2) +
          archimedeanGeometricMass c / (2 * y) := by
  let y : ℝ := archimedeanAsymptoticHeight c x
  let z : ℂ := archimedeanArgument c x
  let R : ℂ := Complex.digamma z -
    (Complex.log z - 1 / (2 * z))
  let G : ℝ := archimedeanFrequency c x *
    archimedeanGeometricSeries c x
  have hy : 0 < y := by
    simpa [y] using archimedeanAsymptoticHeight_pos c x hc hx
  have hRnorm : ‖R‖ ≤ (Real.sqrt 2 / 6) / y ^ 2 := by
    simpa [R, z, y] using
      archimedean_digamma_remainder_le_of_quadratic_remainder_bound
        c x (Real.sqrt 2 / 6) hc hx (by positivity)
          RiemannCvs.DigammaEulerMaclaurin.digamma_quadratic_remainder_bound
  have hRim : |R.im| ≤ (Real.sqrt 2 / 6) / y ^ 2 :=
    (Complex.abs_im_le_norm R).trans hRnorm
  have hRhalf : |R.im| / 2 ≤ Real.sqrt 2 / (12 * y ^ 2) := by
    calc
      |R.im| / 2 ≤ ((Real.sqrt 2 / 6) / y ^ 2) / 2 := by gcongr
      _ = Real.sqrt 2 / (12 * y ^ 2) := by ring
  have hDelta0 : 0 ≤ Real.pi / 2 - z.arg := by
    have harg : z.arg ≤ Real.pi / 2 :=
      Complex.arg_le_pi_div_two_iff.2 (Or.inl (by simp [z]))
    linarith
  have hDelta : Real.pi / 2 - z.arg ≤ 1 / (4 * y) := by
    simpa [z, y] using archimedeanArgument_arg_complement_le c x hc hx
  have hRecip :
      y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) ≤ 1 / (4 * y) :=
    archimedean_reciprocal_imaginary_le hy
  have hFrequency : archimedeanFrequency c x = 2 * y := by
    simpa [y] using archimedeanFrequency_eq_two_mul_height c x
  have hG0 : 0 ≤ G := by
    dsimp [G]
    rw [hFrequency]
    exact mul_nonneg (by positivity) (archimedeanGeometricSeries_nonneg c x)
  have hG : G ≤ archimedeanGeometricMass c / (2 * y) := by
    have h := abs_archimedeanFrequency_mul_geometricSeries_le_mass
      c x hc (archimedeanFrequency_ne_zero_of_pos c x hc hx)
    rw [abs_of_nonneg hG0, hFrequency, abs_of_pos (by positivity)] at h
    simpa [G] using h
  have hModel :
      logarithmicArchimedeanSymbol c x - Real.pi / 4 =
        -(Real.pi / 2 - z.arg) / 2 +
          y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) +
          R.im / 2 - G := by
    rw [logarithmicArchimedeanSymbol,
      archimedeanDigammaImaginary_eq_argument,
      archimedeanDigammaImaginary_model]
    simp only [z, y, R, G]
    have hden : (1 / 16 : ℝ) +
        archimedeanAsymptoticHeight c x ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring
  constructor
  · rw [hModel]
    calc
      -(Real.pi / 2 - z.arg) / 2 +
            y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) +
            R.im / 2 - G ≤
          y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) + |R.im| / 2 := by
        nlinarith [le_abs_self R.im]
      _ ≤ 1 / (4 * y) + Real.sqrt 2 / (12 * y ^ 2) :=
        add_le_add hRecip hRhalf
  · rw [hModel]
    calc
      -(-(Real.pi / 2 - z.arg) / 2 +
            y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) +
            R.im / 2 - G) ≤
          (Real.pi / 2 - z.arg) / 2 + |R.im| / 2 + G := by
        have hrecip0 : 0 ≤
            y / (4 * ((1 / 4 : ℝ) ^ 2 + y ^ 2)) := by positivity
        nlinarith [neg_le_abs R.im]
      _ ≤ 1 / (8 * y) + Real.sqrt 2 / (12 * y ^ 2) +
          archimedeanGeometricMass c / (2 * y) := by
        have hDeltaHalf : (Real.pi / 2 - z.arg) / 2 ≤ 1 / (8 * y) := by
          calc
            (Real.pi / 2 - z.arg) / 2 ≤ (1 / (4 * y)) / 2 := by gcongr
            _ = 1 / (8 * y) := by ring
        exact add_le_add (add_le_add hDeltaHalf hRhalf) hG

lemma c13_geometricMass_le_sevenTwentyFive :
    archimedeanGeometricMass 13 ≤ (7 / 25 : ℝ) := by
  rw [c13_archimedeanGeometricMass_eq]
  nlinarith [sqrt_thirteen_upper]

lemma c13_height_lower_of_ge_960
    {x : ℝ} (hx : (960 : ℝ) ≤ x) :
    (1000 : ℝ) ≤ archimedeanAsymptoticHeight 13 x := by
  have hL : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have hmono : archimedeanAsymptoticHeight 13 960 ≤
      archimedeanAsymptoticHeight 13 x := by
    unfold archimedeanAsymptoticHeight
    apply (div_le_div_iff_of_pos_right hL).2
    exact mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  exact c13_height_960_lower.trans hmono

lemma c13_mode_height_ratio_le
    {x : ℝ} (hx : 0 < x) :
    x / archimedeanAsymptoticHeight 13 x ≤ (171 / 200 : ℝ) := by
  have hL : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have hRatio :
      x / archimedeanAsymptoticHeight 13 x =
        Real.log 13 / Real.pi := by
    unfold archimedeanAsymptoticHeight
    field_simp [ne_of_gt hx, ne_of_gt hL, Real.pi_ne_zero]
  rw [hRatio]
  apply (div_le_iff₀ Real.pi_pos).2
  nlinarith [log_thirteen_lt, Real.pi_gt_three]

lemma c13_mode_heightSq_ratio_le
    {x : ℝ} (hx : (960 : ℝ) ≤ x) :
    x / archimedeanAsymptoticHeight 13 x ^ 2 ≤
      (171 / 200000 : ℝ) := by
  let y : ℝ := archimedeanAsymptoticHeight 13 x
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 960).trans_le hx
  have hy : (1000 : ℝ) ≤ y := by
    simpa [y] using c13_height_lower_of_ge_960 hx
  have hyPos : 0 < y := by linarith
  have hRatio : x / y ≤ (171 / 200 : ℝ) := by
    simpa [y] using c13_mode_height_ratio_le hxPos
  have hInv : 1 / y ≤ (1 / 1000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hy
  have hEq : x / y ^ 2 = (x / y) * (1 / y) := by
    field_simp [ne_of_gt hyPos]
  rw [hEq]
  calc
    (x / y) * (1 / y) ≤ (171 / 200 : ℝ) * (1 / y) :=
      mul_le_mul_of_nonneg_right hRatio (by positivity)
    _ ≤ (171 / 200 : ℝ) * (1 / 1000 : ℝ) :=
      mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ = 171 / 200000 := by norm_num

theorem c13_centeredLogarithmicArchimedeanSymbol_abs_le
    (x : ℝ) (hx : (960 : ℝ) ≤ x) :
    |logarithmicArchimedeanSymbol 13 x - Real.pi / 4| ≤
      (1 / 4 : ℝ) / x := by
  let y : ℝ := archimedeanAsymptoticHeight 13 x
  let e : ℝ := logarithmicArchimedeanSymbol 13 x - Real.pi / 4
  let U : ℝ := 1 / (4 * y) + Real.sqrt 2 / (12 * y ^ 2)
  let L : ℝ := 1 / (8 * y) + Real.sqrt 2 / (12 * y ^ 2) +
    archimedeanGeometricMass 13 / (2 * y)
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 960).trans_le hx
  have hy : (1000 : ℝ) ≤ y := by
    simpa [y] using c13_height_lower_of_ge_960 hx
  have hyPos : 0 < y := by linarith
  have hRatio : x / y ≤ (171 / 200 : ℝ) := by
    simpa [y] using c13_mode_height_ratio_le hxPos
  have hRatioSq : x / y ^ 2 ≤ (171 / 200000 : ℝ) := by
    simpa [y] using c13_mode_heightSq_ratio_le hx
  have hSqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hSqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := sqrt_two_upper
  have hMass0 : 0 ≤ archimedeanGeometricMass 13 :=
    archimedeanGeometricMass_nonneg 13 (by norm_num)
  have hMass : archimedeanGeometricMass 13 ≤ (7 / 25 : ℝ) :=
    c13_geometricMass_le_sevenTwentyFive
  have hTermQuarter : x * (1 / (4 * y)) ≤ (171 / 800 : ℝ) := by
    calc
      x * (1 / (4 * y)) = (x / y) / 4 := by ring
      _ ≤ (171 / 200 : ℝ) / 4 := by gcongr
      _ = 171 / 800 := by norm_num
  have hTermEighth : x * (1 / (8 * y)) ≤ (171 / 1600 : ℝ) := by
    calc
      x * (1 / (8 * y)) = (x / y) / 8 := by ring
      _ ≤ (171 / 200 : ℝ) / 8 := by gcongr
      _ = 171 / 1600 := by norm_num
  have hTermRemainder :
      x * (Real.sqrt 2 / (12 * y ^ 2)) ≤
        (171 / 1600000 : ℝ) := by
    calc
      x * (Real.sqrt 2 / (12 * y ^ 2)) =
          (Real.sqrt 2 / 12) * (x / y ^ 2) := by ring
      _ ≤ ((3 / 2 : ℝ) / 12) * (x / y ^ 2) :=
        mul_le_mul_of_nonneg_right (by gcongr) (by positivity)
      _ ≤ ((3 / 2 : ℝ) / 12) * (171 / 200000 : ℝ) :=
        mul_le_mul_of_nonneg_left hRatioSq (by norm_num)
      _ = 171 / 1600000 := by norm_num
  have hTermMass :
      x * (archimedeanGeometricMass 13 / (2 * y)) ≤
        (1197 / 10000 : ℝ) := by
    calc
      x * (archimedeanGeometricMass 13 / (2 * y)) =
          (archimedeanGeometricMass 13 / 2) * (x / y) := by ring
      _ ≤ ((7 / 25 : ℝ) / 2) * (x / y) :=
        mul_le_mul_of_nonneg_right (by gcongr) (by positivity)
      _ ≤ ((7 / 25 : ℝ) / 2) * (171 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_left hRatio (by norm_num)
      _ = 1197 / 10000 := by norm_num
  have hBounds :=
    centeredLogarithmicArchimedeanSymbol_bounds 13 x (by norm_num) hxPos
  have heUpper : e ≤ U := by simpa [e, U, y] using hBounds.1
  have heLower : -e ≤ L := by simpa [e, L, y] using hBounds.2
  have hUscaled : x * U ≤ (1 / 4 : ℝ) := by
    dsimp [U]
    nlinarith [hTermQuarter, hTermRemainder]
  have hLscaled : x * L ≤ (1 / 4 : ℝ) := by
    dsimp [L]
    nlinarith [hTermEighth, hTermRemainder, hTermMass]
  have hU : U ≤ (1 / 4 : ℝ) / x := by
    apply (le_div_iff₀ hxPos).2
    simpa [mul_comm] using hUscaled
  have hL : L ≤ (1 / 4 : ℝ) / x := by
    apply (le_div_iff₀ hxPos).2
    simpa [mul_comm] using hLscaled
  rw [abs_le]
  constructor
  · dsimp [e] at heLower ⊢
    nlinarith
  · dsimp [e] at heUpper ⊢
    exact heUpper.trans hU


noncomputable def centeredArchimedeanSymbol (c : ℝ) (n : ℤ) : ℝ :=
  logarithmicArchimedeanSymbol c (n : ℝ) - Real.pi / 4

theorem logarithmicCvSArchimedeanEntry_reflected_eq (c : ℝ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) :
    logarithmicCvSArchimedeanEntry c n (-m) =
      -(1 / (2 * ((n : ℝ) + (m : ℝ)))) -
        (centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
          (Real.pi * ((n : ℝ) + (m : ℝ))) := by
  have hne : n ≠ -m := by omega
  have hcast : (n : ℝ) + (m : ℝ) ≠ 0 := by positivity
  simp only [logarithmicCvSArchimedeanEntry, hne, if_false,
    Int.cast_neg, sub_neg_eq_add]
  rw [signedLogarithmicArchimedeanSymbol_eq,
    signedLogarithmicArchimedeanSymbol_eq,
    logarithmicArchimedeanSymbol_odd]
  unfold centeredArchimedeanSymbol
  field_simp [hcast, Real.pi_ne_zero]
  ring

theorem logarithmicCvSArchimedeanEntry_sameSign_eq (c : ℝ) (n m : ℤ) (hne : n ≠ m) :
    logarithmicCvSArchimedeanEntry c n m =
      (centeredArchimedeanSymbol c m - centeredArchimedeanSymbol c n) /
        (Real.pi * ((n : ℝ) - (m : ℝ))) := by
  simp only [logarithmicCvSArchimedeanEntry, hne, if_false]
  rw [signedLogarithmicArchimedeanSymbol_eq,
    signedLogarithmicArchimedeanSymbol_eq]
  unfold centeredArchimedeanSymbol
  ring

theorem energy_abs_le_card_mul_of_entry_abs_le
    {κ : Type*} [Fintype κ]
    (A : Matrix κ κ ℝ) (x : κ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) :
    |finiteMatrixQuadraticEnergy A x| ≤
      (Fintype.card κ : ℝ) * B * finiteVectorEuclideanNormSq x := by
  unfold finiteMatrixQuadraticEnergy finiteVectorEuclideanNormSq
  calc
    |∑ i, ∑ j, x i * A i j * x j| ≤
        ∑ i, ∑ j, |x i * A i j * x j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, B * (x i ^ 2 + x j ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      have hxy : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|x i| - |x j|),
          sq_abs (x i), sq_abs (x j)]
      calc
        |x i| * |A i j| * |x j| = |A i j| * (|x i| * |x j|) := by ring
        _ ≤ B * (|x i| * |x j|) :=
          mul_le_mul_of_nonneg_right (hA i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ B * ((x i ^ 2 + x j ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hxy hB
        _ = B * (x i ^ 2 + x j ^ 2) / 2 := by ring
    _ = ∑ i, ∑ j, ((B / 2) * x i ^ 2 + (B / 2) * x j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (Fintype.card κ : ℝ) * B * ∑ i, x i ^ 2 := by
      have hscaled :
          (∑ i, (B / 2) * x i ^ 2) =
            (B / 2) * ∑ i, x i ^ 2 := (Finset.mul_sum _ _ _).symm
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, hscaled]
      ring

theorem reflected_entry_abs_le
    (c N D : ℝ) (n m : ℤ)
    (hN : 0 < N) (hD : 0 ≤ D)
    (hn : N ≤ (n : ℝ)) (hm : N ≤ (m : ℝ))
    (hnPos : 0 < n) (hmPos : 0 < m)
    (hcn : |centeredArchimedeanSymbol c n| ≤ D / N)
    (hcm : |centeredArchimedeanSymbol c m| ≤ D / N) :
    |logarithmicCvSArchimedeanEntry c n (-m)| ≤
      1 / (4 * N) + D / (3 * N ^ 2) := by
  have hsumPos : 0 < (n : ℝ) + (m : ℝ) := by positivity
  have hsumLower : 2 * N ≤ (n : ℝ) + (m : ℝ) := by linarith
  have hdenLower : 6 * N ≤
      Real.pi * ((n : ℝ) + (m : ℝ)) := by
    calc
      6 * N = 3 * (2 * N) := by ring
      _ ≤ Real.pi * ((n : ℝ) + (m : ℝ)) := by
        exact mul_le_mul Real.pi_gt_three.le hsumLower
          (by positivity) Real.pi_pos.le
  have hdenPos : 0 < Real.pi * ((n : ℝ) + (m : ℝ)) :=
    mul_pos Real.pi_pos hsumPos
  have hcenterSum :
      |centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m| ≤
        2 * D / N := by
    calc
      |centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m| ≤
          |centeredArchimedeanSymbol c n| +
            |centeredArchimedeanSymbol c m| := abs_add_le _ _
      _ ≤ D / N + D / N := add_le_add hcn hcm
      _ = 2 * D / N := by ring
  have hcenterNonneg : 0 ≤ 2 * D / N := by positivity
  have hcenterFrac :
      |(centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
          (Real.pi * ((n : ℝ) + (m : ℝ)))| ≤
        D / (3 * N ^ 2) := by
    rw [abs_div, abs_of_pos hdenPos]
    calc
      |centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m| /
          (Real.pi * ((n : ℝ) + (m : ℝ))) ≤
          (2 * D / N) /
            (Real.pi * ((n : ℝ) + (m : ℝ))) :=
        div_le_div_of_nonneg_right hcenterSum hdenPos.le
      _ ≤ (2 * D / N) / (6 * N) := by
        gcongr
      _ = D / (3 * N ^ 2) := by
        field_simp [ne_of_gt hN]
        ring
  have hlead :
      1 / (2 * ((n : ℝ) + (m : ℝ))) ≤ 1 / (4 * N) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [show logarithmicCvSArchimedeanEntry c n (-m) =
      -(1 / (2 * ((n : ℝ) + (m : ℝ)))) -
        (centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
          (Real.pi * ((n : ℝ) + (m : ℝ))) by
    exact (by
      have hne : n ≠ -m := by omega
      have hcast : (n : ℝ) + (m : ℝ) ≠ 0 := by positivity
      simp only [logarithmicCvSArchimedeanEntry, hne, if_false,
        Int.cast_neg, sub_neg_eq_add]
      rw [signedLogarithmicArchimedeanSymbol_eq,
        signedLogarithmicArchimedeanSymbol_eq,
        logarithmicArchimedeanSymbol_odd]
      unfold centeredArchimedeanSymbol
      field_simp [hcast, Real.pi_ne_zero]
      ring)]
  calc
    |-(1 / (2 * ((n : ℝ) + (m : ℝ)))) -
        (centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
          (Real.pi * ((n : ℝ) + (m : ℝ)))| ≤
        |-(1 / (2 * ((n : ℝ) + (m : ℝ))))| +
          |(centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
            (Real.pi * ((n : ℝ) + (m : ℝ)))| := abs_sub _ _
    _ = 1 / (2 * ((n : ℝ) + (m : ℝ))) +
          |(centeredArchimedeanSymbol c n + centeredArchimedeanSymbol c m) /
            (Real.pi * ((n : ℝ) + (m : ℝ)))| := by
      rw [abs_neg, abs_of_pos]
      positivity
    _ ≤ 1 / (4 * N) + D / (3 * N ^ 2) :=
      add_le_add hlead hcenterFrac

theorem sameSign_entry_abs_le
    (c N D : ℝ) (n m : ℤ)
    (hN : 0 < N) (hD : 0 ≤ D)
    (hne : n ≠ m)
    (hcn : |centeredArchimedeanSymbol c n| ≤ D / N)
    (hcm : |centeredArchimedeanSymbol c m| ≤ D / N) :
    |logarithmicCvSArchimedeanEntry c n m| ≤ 2 * D / (3 * N) := by
  have hdiffInt : (1 : ℤ) ≤ |n - m| :=
    Int.one_le_abs (sub_ne_zero.mpr hne)
  have hdiff : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
    exact_mod_cast hdiffInt
  have hdenLower : (3 : ℝ) ≤
      |Real.pi * ((n : ℝ) - (m : ℝ))| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hdenPos : 0 < |Real.pi * ((n : ℝ) - (m : ℝ))| :=
    lt_of_lt_of_le (by norm_num) hdenLower
  have hcenterDiff :
      |centeredArchimedeanSymbol c m - centeredArchimedeanSymbol c n| ≤
        2 * D / N := by
    calc
      |centeredArchimedeanSymbol c m - centeredArchimedeanSymbol c n| ≤
          |centeredArchimedeanSymbol c m| +
            |centeredArchimedeanSymbol c n| := abs_sub _ _
      _ ≤ D / N + D / N := add_le_add hcm hcn
      _ = 2 * D / N := by ring
  have hcenterNonneg : 0 ≤ 2 * D / N := by positivity
  rw [show logarithmicCvSArchimedeanEntry c n m =
      (centeredArchimedeanSymbol c m - centeredArchimedeanSymbol c n) /
        (Real.pi * ((n : ℝ) - (m : ℝ))) by
    simp only [logarithmicCvSArchimedeanEntry, hne, if_false]
    rw [signedLogarithmicArchimedeanSymbol_eq,
      signedLogarithmicArchimedeanSymbol_eq]
    unfold centeredArchimedeanSymbol
    ring]
  rw [abs_div]
  calc
    |centeredArchimedeanSymbol c m - centeredArchimedeanSymbol c n| /
        |Real.pi * ((n : ℝ) - (m : ℝ))| ≤
        (2 * D / N) / |Real.pi * ((n : ℝ) - (m : ℝ))| :=
      div_le_div_of_nonneg_right hcenterDiff hdenPos.le
    _ ≤ (2 * D / N) / 3 := by
      gcongr
    _ = 2 * D / (3 * N) := by ring

theorem evenRemainder_entry_abs_le
    (c D : ℝ) (old shell : ℕ) (hOld : old ≠ 0) (hD : 0 ≤ D)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤ D / (old : ℝ))
    (i j : Fin shell) :
    |logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤
      1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2) +
        2 * D / (3 * (old : ℝ)) := by
  have hN : 0 < (old : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hOld
  have hLower : ∀ k : Fin shell,
      (old : ℝ) ≤ (finGlobalShellPositiveMode old shell k : ℝ) := by
    intro k
    unfold finGlobalShellPositiveMode
    norm_cast
    omega
  have href := reflected_entry_abs_le c (old : ℝ) D
    (finGlobalShellPositiveMode old shell i)
    (finGlobalShellPositiveMode old shell j)
    hN hD (hLower i) (hLower j)
    (finGlobalShellPositiveMode_pos old shell i)
    (finGlobalShellPositiveMode_pos old shell j)
    (hCentered i) (hCentered j)
  by_cases hij : i = j
  · subst j
    simp only [logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
      if_pos, neg_zero, zero_sub]
    rw [abs_neg]
    exact href.trans (le_add_of_nonneg_right (by positivity))
  · have hmodeNe : finGlobalShellPositiveMode old shell i ≠
        finGlobalShellPositiveMode old shell j :=
      (finGlobalShellPositiveMode_injective old shell).ne hij
    have hsame := sameSign_entry_abs_le c (old : ℝ) D
      (finGlobalShellPositiveMode old shell i)
      (finGlobalShellPositiveMode old shell j)
      hN hD hmodeNe (hCentered i) (hCentered j)
    simp only [logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
      hij, if_false]
    calc
      |-logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j) -
          logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j)| ≤
          |logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j)| +
          |logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j)| := by
        simpa only [abs_neg] using abs_sub
          (-logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j))
          (logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j))
      _ ≤ 2 * D / (3 * (old : ℝ)) +
          (1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2)) :=
        add_le_add hsame href
      _ = 1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2) +
          2 * D / (3 * (old : ℝ)) := by ring

theorem oddRemainder_entry_abs_le
    (c D : ℝ) (old shell : ℕ) (hOld : old ≠ 0) (hD : 0 ≤ D)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤ D / (old : ℝ))
    (i j : Fin shell) :
    |logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤
      1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2) +
        2 * D / (3 * (old : ℝ)) := by
  have hN : 0 < (old : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hOld
  have hLower : ∀ k : Fin shell,
      (old : ℝ) ≤ (finGlobalShellPositiveMode old shell k : ℝ) := by
    intro k
    unfold finGlobalShellPositiveMode
    norm_cast
    omega
  have href := reflected_entry_abs_le c (old : ℝ) D
    (finGlobalShellPositiveMode old shell i)
    (finGlobalShellPositiveMode old shell j)
    hN hD (hLower i) (hLower j)
    (finGlobalShellPositiveMode_pos old shell i)
    (finGlobalShellPositiveMode_pos old shell j)
    (hCentered i) (hCentered j)
  by_cases hij : i = j
  · subst j
    simp only [logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
      if_pos, neg_zero, zero_add]
    exact href.trans (le_add_of_nonneg_right (by positivity))
  · have hmodeNe : finGlobalShellPositiveMode old shell i ≠
        finGlobalShellPositiveMode old shell j :=
      (finGlobalShellPositiveMode_injective old shell).ne hij
    have hsame := sameSign_entry_abs_le c (old : ℝ) D
      (finGlobalShellPositiveMode old shell i)
      (finGlobalShellPositiveMode old shell j)
      hN hD hmodeNe (hCentered i) (hCentered j)
    simp only [logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
      hij, if_false]
    calc
      |-logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j) +
          logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j)| ≤
          |logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j)| +
          |logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j)| := by
        simpa only [abs_neg] using abs_add_le
          (-logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (finGlobalShellPositiveMode old shell j))
          (logarithmicCvSArchimedeanEntry c
            (finGlobalShellPositiveMode old shell i)
            (-finGlobalShellPositiveMode old shell j))
      _ ≤ 2 * D / (3 * (old : ℝ)) +
          (1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2)) :=
        add_le_add hsame href
      _ = 1 / (4 * (old : ℝ)) + D / (3 * (old : ℝ) ^ 2) +
          2 * D / (3 * (old : ℝ)) := by ring

lemma dyadic_archCoefficient_le_half
    (old shell : ℕ) (hOld : old ≠ 0) (hShell : shell ≤ old) :
    (shell : ℝ) *
        (1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
          2 * (1 / 4 : ℝ) / (3 * (old : ℝ))) ≤
      1 / 2 := by
  have hN : (0 : ℝ) < old := by exact_mod_cast Nat.pos_of_ne_zero hOld
  have hNOne : (1 : ℝ) ≤ old := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hOld
  have hMN : (shell : ℝ) ≤ old := by exact_mod_cast hShell
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hScale : (shell : ℝ) * E ≤ (old : ℝ) * E :=
    mul_le_mul_of_nonneg_right hMN hE
  have hInv : 1 / (old : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hNOne
  have hTwelfth : 1 / (12 * (old : ℝ)) ≤ 1 / 12 := by
    calc
      1 / (12 * (old : ℝ)) = (1 / 12 : ℝ) * (1 / (old : ℝ)) := by ring
      _ ≤ (1 / 12 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = 1 / 12 := by ring
  calc
    (shell : ℝ) *
        (1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
          2 * (1 / 4 : ℝ) / (3 * (old : ℝ))) =
        (shell : ℝ) * E := rfl
    _ ≤ (old : ℝ) * E := hScale
    _ = 1 / 4 + 1 / (12 * (old : ℝ)) + 1 / 6 := by
      dsimp [E]
      field_simp [ne_of_gt hN]
      ring
    _ ≤ 1 / 2 := by nlinarith [hTwelfth]

theorem evenRemainder_energy_abs_le_half_of_centered
    (c : ℝ) (old shell : ℕ) (hOld : old ≠ 0) (hShell : shell ≤ old)
    (x : Fin shell → ℝ)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤
          (1 / 4 : ℝ) / (old : ℝ)) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
          (finGlobalShellPositiveMode old shell)) x| ≤
      (1 / 2 : ℝ) * finiteVectorEuclideanNormSq x := by
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEntry : ∀ i j : Fin shell,
      |logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤ E := by
    intro i j
    exact evenRemainder_entry_abs_le c (1 / 4) old shell hOld
      (by norm_num) hCentered i j
  have hEnergy := energy_abs_le_card_mul_of_entry_abs_le
    (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c
      (finGlobalShellPositiveMode old shell)) x E hE hEntry
  have hCoeff : (Fintype.card (Fin shell) : ℝ) * E ≤ 1 / 2 := by
    simpa [E] using dyadic_archCoefficient_le_half old shell hOld hShell
  exact hEnergy.trans (mul_le_mul_of_nonneg_right hCoeff
    (by exact Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem oddRemainder_energy_abs_le_half_of_centered
    (c : ℝ) (old shell : ℕ) (hOld : old ≠ 0) (hShell : shell ≤ old)
    (x : Fin shell → ℝ)
    (hCentered : ∀ i : Fin shell,
      |centeredArchimedeanSymbol c
        (finGlobalShellPositiveMode old shell i)| ≤
          (1 / 4 : ℝ) / (old : ℝ)) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
          (finGlobalShellPositiveMode old shell)) x| ≤
      (1 / 2 : ℝ) * finiteVectorEuclideanNormSq x := by
  let E : ℝ :=
    1 / (4 * (old : ℝ)) + (1 / 4 : ℝ) / (3 * (old : ℝ) ^ 2) +
      2 * (1 / 4 : ℝ) / (3 * (old : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEntry : ∀ i j : Fin shell,
      |logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
        (finGlobalShellPositiveMode old shell) i j| ≤ E := by
    intro i j
    exact oddRemainder_entry_abs_le c (1 / 4) old shell hOld
      (by norm_num) hCentered i j
  have hEnergy := energy_abs_le_card_mul_of_entry_abs_le
    (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c
      (finGlobalShellPositiveMode old shell)) x E hE hEntry
  have hCoeff : (Fintype.card (Fin shell) : ℝ) * E ≤ 1 / 2 := by
    simpa [E] using dyadic_archCoefficient_le_half old shell hOld hShell
  exact hEnergy.trans (mul_le_mul_of_nonneg_right hCoeff
    (by exact Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-!
## Premise-free cutoff-13 shell closure

The real inverse-mode envelope above specializes to each integral shell mode.
Since every mode in the shell is at least the old cutoff, it supplies exactly
the centered-symbol premise consumed by the entrywise Schur estimate.
-/

theorem c13_centeredArchimedeanSymbol_shell_abs_le
    (old shell : ℕ) (hOld : 960 ≤ old) (i : Fin shell) :
    |centeredArchimedeanSymbol 13
        (finGlobalShellPositiveMode old shell i)| ≤
      (1 / 4 : ℝ) / (old : ℝ) := by
  let n : ℤ := finGlobalShellPositiveMode old shell i
  have hModeNat : 960 ≤ old + 1 + (i : ℕ) := by omega
  have hMode : (960 : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast hModeNat
  have hOldPos : 0 < (old : ℝ) := by
    exact_mod_cast (show 0 < old by omega)
  have hOldMode : (old : ℝ) ≤ (n : ℝ) := by
    dsimp [n, finGlobalShellPositiveMode]
    exact_mod_cast (show old ≤ old + 1 + (i : ℕ) by omega)
  have hPoint :
      |centeredArchimedeanSymbol 13 n| ≤ (1 / 4 : ℝ) / (n : ℝ) := by
    simpa [centeredArchimedeanSymbol, n] using
      c13_centeredLogarithmicArchimedeanSymbol_abs_le (n : ℝ) hMode
  exact hPoint.trans
    (div_le_div_of_nonneg_left (by norm_num) hOldPos hOldMode)

/-- On every dyadic shell above `960`, the even Archimedean off-diagonal
quadratic form has operator bound `1/2`, with no analytic premise. -/
theorem c13_evenRemainder_energy_abs_le_half
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix 13
          (finGlobalShellPositiveMode old shell)) x| ≤
      (1 / 2 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact evenRemainder_energy_abs_le_half_of_centered
    13 old shell (by omega) hShell x
      (c13_centeredArchimedeanSymbol_shell_abs_le old shell hOld)

/-- The same premise-free `1/2` bound holds on the odd parity block. -/
theorem c13_oddRemainder_energy_abs_le_half
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix 13
          (finGlobalShellPositiveMode old shell)) x| ≤
      (1 / 2 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact oddRemainder_energy_abs_le_half_of_centered
    13 old shell (by omega) hShell x
      (c13_centeredArchimedeanSymbol_shell_abs_le old shell hOld)

/-!
## Closing the scalar reserve

A deliberately coarse bound is enough here: `sinh(log 13 / 4)^2 ≤ 169`.
Together with `log 13 < 513/200`, `π > 3`, and `old ≥ 960`, it puts the pole
tail below `13/60`.  Meanwhile `old ≥ 960 > 13^2` gives `log old > 5`.
Those two rational margins exactly dominate the diagonal loss `19/20`, the
Archimedean remainder `1/2`, and the prime loss `10/3`.
-/

lemma c13_sinh_quarterLog_sq_le_169 :
    Real.sinh (Real.log 13 / 4) ^ 2 ≤ (169 : ℝ) := by
  have hLog : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 < Real.log (13 : ℝ) / 4 := by positivity
  have hSinh0 : 0 ≤ Real.sinh (Real.log 13 / 4) :=
    (Real.sinh_pos_iff.mpr ht).le
  have hSinhExp :
      Real.sinh (Real.log 13 / 4) ≤ Real.exp (Real.log 13 / 4) := by
    rw [Real.sinh_eq]
    nlinarith [Real.exp_pos (Real.log (13 : ℝ) / 4),
      Real.exp_pos (-(Real.log (13 : ℝ) / 4))]
  have htLog : Real.log (13 : ℝ) / 4 ≤ Real.log 13 := by
    nlinarith
  have hExp : Real.exp (Real.log 13 / 4) ≤ (13 : ℝ) := by
    calc
      Real.exp (Real.log 13 / 4) ≤ Real.exp (Real.log 13) :=
        Real.exp_le_exp.mpr htLog
      _ = 13 := Real.exp_log (by norm_num)
  nlinarith

lemma c13_logarithmicCvSPoleScale_le_13872 :
    logarithmicCvSPoleScale 13 ≤ (13872 : ℝ) := by
  have hLog0 : 0 ≤ Real.log (13 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hSinhSq0 : 0 ≤ Real.sinh (Real.log 13 / 4) ^ 2 := sq_nonneg _
  unfold logarithmicCvSPoleScale
  calc
    32 * Real.log 13 * Real.sinh (Real.log 13 / 4) ^ 2 ≤
        32 * (513 / 200 : ℝ) *
          Real.sinh (Real.log 13 / 4) ^ 2 := by
      gcongr
      exact log_thirteen_lt.le
    _ ≤ 32 * (513 / 200 : ℝ) * 169 := by
      gcongr
      exact c13_sinh_quarterLog_sq_le_169
    _ ≤ 13872 := by norm_num

theorem c13_logarithmicCvSPoleTail_le_thirteenSixtieth
    (old : ℕ) (hOld : 960 ≤ old) :
    logarithmicCvSPoleScale 13 /
        (8 * Real.pi ^ 2 * (old : ℝ)) ≤ (13 / 60 : ℝ) := by
  have hOldReal : (960 : ℝ) ≤ (old : ℝ) := by exact_mod_cast hOld
  have hOldPos : 0 < (old : ℝ) := by positivity
  have hPiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hDenLower : (69120 : ℝ) ≤ 8 * Real.pi ^ 2 * (old : ℝ) := by
    calc
      (69120 : ℝ) = 8 * 9 * 960 := by norm_num
      _ ≤ 8 * Real.pi ^ 2 * 960 := by
        nlinarith
      _ ≤ 8 * Real.pi ^ 2 * (old : ℝ) := by
        exact mul_le_mul_of_nonneg_left hOldReal (by positivity)
  have hDenPos : 0 < 8 * Real.pi ^ 2 * (old : ℝ) := by positivity
  rw [div_le_iff₀ hDenPos]
  nlinarith [c13_logarithmicCvSPoleScale_le_13872]

lemma five_lt_log_nat_of_c13_shell
    (old : ℕ) (hOld : 960 ≤ old) :
    (5 : ℝ) < Real.log (old : ℝ) := by
  have h169 : (169 : ℝ) ≤ (old : ℝ) := by
    exact_mod_cast (show 169 ≤ old by omega)
  have hLogMono : Real.log (169 : ℝ) ≤ Real.log (old : ℝ) :=
    Real.log_le_log (by norm_num) h169
  have hLog169 : Real.log (169 : ℝ) = 2 * Real.log 13 := by
    rw [show (169 : ℝ) = 13 * 13 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLog169] at hLogMono
  nlinarith [five_halves_lt_log_thirteen]

/-- A slightly longer rational arctanh sum sharpens the elementary cutoff
estimate enough to retain a uniform coercive reserve. -/
lemma sixtyFourTwentyFive_lt_log_thirteen :
    (64 / 25 : ℝ) < Real.log 13 := by
  have h := Real.sum_range_le_log_div
    (x := (6 / 7 : ℝ)) (by norm_num) (by norm_num) 20
  norm_num at h
  linarith

lemma oneHundredTwentyEightTwentyFive_lt_log_nat_of_c13_shell
    (old : ℕ) (hOld : 960 ≤ old) :
    (128 / 25 : ℝ) < Real.log (old : ℝ) := by
  have h169 : (169 : ℝ) ≤ (old : ℝ) := by
    exact_mod_cast (show 169 ≤ old by omega)
  have hLogMono : Real.log (169 : ℝ) ≤ Real.log (old : ℝ) :=
    Real.log_le_log (by norm_num) h169
  have hLog169 : Real.log (169 : ℝ) = 2 * Real.log 13 := by
    rw [show (169 : ℝ) = 13 * 13 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLog169] at hLogMono
  nlinarith [sixtyFourTwentyFive_lt_log_thirteen]

/-- The complete cutoff-13 loss budget is nonnegative on every old cutoff at
least `960`: diagonal floor minus pole, Archimedean, and prime losses. -/
theorem c13_shell_complete_scalar_reserve_nonneg
    (old : ℕ) (hOld : 960 ≤ old) :
    0 ≤ Real.log (old : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) +
        1 / 2 + 10 / 3) := by
  have hLog := five_lt_log_nat_of_c13_shell old hOld
  have hPole := c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld
  nlinarith

/-- Quantitative version of the complete scalar budget: a uniform `3/25`
coercive gap remains after all four concrete cutoff-13 components. -/
theorem c13_shell_complete_scalar_reserve_ge_threeTwentyFive
    (old : ℕ) (hOld : 960 ≤ old) :
    (3 / 25 : ℝ) ≤ Real.log (old : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) +
        1 / 2 + 10 / 3) := by
  have hLog :=
    oneHundredTwentyEightTwentyFive_lt_log_nat_of_c13_shell old hOld
  have hPole := c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld
  nlinarith

/-!
### Sharp elementary reserve at the actual cutoff

The earlier `3/25` floor used only `960 ≥ 13²`, discarding most of the
available logarithmic diagonal.  Factoring `960 = 2⁶ * 3 * 5` and applying
short rational arctanh sums at `1/3`, `1/2`, and `2/3` recovers a much larger
fully exact reserve without changing any operator estimate.
-/

lemma log_two_gt_sixtyNineHundredths :
    (69 / 100 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num at h
  linarith

lemma log_three_gt_oneHundredNineHundredths :
    (109 / 100 : ℝ) < Real.log 3 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num at h
  linarith

lemma log_five_gt_eightFifths :
    (8 / 5 : ℝ) < Real.log 5 := by
  have h := Real.sum_range_le_log_div
    (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num at h
  linarith

lemma sixHundredEightyThreeHundredths_lt_log_nat_of_c13_shell
    (old : ℕ) (hOld : 960 ≤ old) :
    (683 / 100 : ℝ) < Real.log (old : ℝ) := by
  have h960 : (960 : ℝ) ≤ (old : ℝ) := by exact_mod_cast hOld
  have hLogMono : Real.log (960 : ℝ) ≤ Real.log (old : ℝ) :=
    Real.log_le_log (by norm_num) h960
  have hLog960 :
      Real.log (960 : ℝ) = 6 * Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (960 : ℝ) = 2 * 2 * 2 * 2 * 2 * 2 * 3 * 5 by norm_num]
    repeat' rw [Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hLog960] at hLogMono
  nlinarith [log_two_gt_sixtyNineHundredths,
    log_three_gt_oneHundredNineHundredths,
    log_five_gt_eightFifths]

/-- The actual cutoff leaves a `9/5` coercive reserve.  This is fifteen times
the earlier `3/25` interface and is the preferred gap for future relative
coupling estimates. -/
theorem c13_shell_complete_scalar_reserve_ge_nineFifths
    (old : ℕ) (hOld : 960 ≤ old) :
    (9 / 5 : ℝ) ≤ Real.log (old : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (old : ℝ)) +
        1 / 2 + 10 / 3) := by
  have hLog :=
    sixHundredEightyThreeHundredths_lt_log_nat_of_c13_shell old hOld
  have hPole := c13_logarithmicCvSPoleTail_le_thirteenSixtieth old hOld
  nlinarith

/-!
## Fully closed asymptotic shell coercivity

The diagonal, pole, prime-translation, and Archimedean-remainder components
are now all internal theorems.  Hence both parity blocks of the actual
cutoff-13 CvS builder are positive semidefinite on every consecutive dyadic
shell with `old ≥ 960` and `shell ≤ old`.
-/

theorem c13_logarithmicCvSBuilderEvenShell_energy_nonneg
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    0 ≤ finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderEvenPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 0 (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_evenRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using c13_shell_complete_scalar_reserve_nonneg old hOld)
  simpa using h

theorem c13_logarithmicCvSBuilderOddShell_energy_nonneg
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    0 ≤ finiteMatrixQuadraticEnergy
      (logarithmicCvSBuilderOddPositiveModeMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 0 (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_oddRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using c13_shell_complete_scalar_reserve_nonneg old hOld)
  simpa using h

/-- Uniform even-shell coercivity retained by the complete cutoff-13 budget. -/
theorem c13_logarithmicCvSBuilderEvenShell_energy_ge_threeTwentyFive_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    (3 / 25 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (3 / 25) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_evenRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using
      c13_shell_complete_scalar_reserve_ge_threeTwentyFive old hOld)
  simpa using h

/-- Uniform odd-shell coercivity with the same `3/25` gap. -/
theorem c13_logarithmicCvSBuilderOddShell_energy_ge_threeTwentyFive_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    (3 / 25 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (3 / 25) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_oddRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using
      c13_shell_complete_scalar_reserve_ge_threeTwentyFive old hOld)
  simpa using h

/-- Preferred quantitative even-shell coercivity at the literal cutoff. -/
theorem c13_logarithmicCvSBuilderEvenShell_energy_ge_nineFifths_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    (9 / 5 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (9 / 5) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_evenRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using c13_shell_complete_scalar_reserve_ge_nineFifths old hOld)
  simpa using h

/-- Preferred quantitative odd-shell coercivity at the literal cutoff. -/
theorem c13_logarithmicCvSBuilderOddShell_energy_ge_nineFifths_normSq
    (old shell : ℕ) (hOld : 960 ≤ old) (hShell : shell ≤ old)
    (x : Fin shell → ℝ) :
    (9 / 5 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode old shell)) x := by
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    old shell (by omega) x
    (Real.log (old : ℝ) - 19 / 20) 0 (9 / 5) (1 / 2)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      old shell hOld)
    (c13_oddRemainder_energy_abs_le_half old shell hOld hShell x)
    (by simpa using c13_shell_complete_scalar_reserve_ge_nineFifths old hOld)
  simpa using h

/-- The actual even matrix-tower tail is nonnegative whenever its newest
shell is no larger than its previous core and that core has reached `960`. -/
theorem c13_logarithmicCvSBuilderEvenTowerTailEnergy_nonneg
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    0 ≤ finiteMatrixTowerTailEnergy
      (logarithmicCvSBuilderEvenTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderEvenTowerShellVector z size shell)
      (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact c13_logarithmicCvSBuilderEvenShell_energy_nonneg
    (size n) (shell n) hOld hShell
      (finGlobalShellVector z (size n) (shell n))

/-- Odd-parity analogue of the premise-free matrix-tower tail theorem. -/
theorem c13_logarithmicCvSBuilderOddTowerTailEnergy_nonneg
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    0 ≤ finiteMatrixTowerTailEnergy
      (logarithmicCvSBuilderOddTowerMatrix
        13 c13PrimePowerLocation c13PrimePowerBase size)
      (logarithmicCvSBuilderOddTowerShellVector z size shell)
      (logarithmicCvSBuilderOddTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact c13_logarithmicCvSBuilderOddShell_energy_nonneg
    (size n) (shell n) hOld hShell
      (finGlobalShellVector z (size n) (shell n))

/-- Quantitative even matrix-tower tail coercivity. -/
theorem c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_threeTwentyFive_normSq
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    (3 / 25 : ℝ) * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderEvenTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderEvenTowerShellVector z size shell)
        (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact
    c13_logarithmicCvSBuilderEvenShell_energy_ge_threeTwentyFive_normSq
      (size n) (shell n) hOld hShell
        (finGlobalShellVector z (size n) (shell n))

/-- Quantitative odd matrix-tower tail coercivity. -/
theorem c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_threeTwentyFive_normSq
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    (3 / 25 : ℝ) * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderOddTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderOddTowerShellVector z size shell)
        (logarithmicCvSBuilderOddTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact
    c13_logarithmicCvSBuilderOddShell_energy_ge_threeTwentyFive_normSq
      (size n) (shell n) hOld hShell
        (finGlobalShellVector z (size n) (shell n))

/-- Quantitative even tower-tail coercivity with the sharpened `9/5` gap. -/
theorem c13_logarithmicCvSBuilderEvenTowerTailEnergy_ge_nineFifths_normSq
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    (9 / 5 : ℝ) * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderEvenTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderEvenTowerShellVector z size shell)
        (logarithmicCvSBuilderEvenTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderEvenTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact
    c13_logarithmicCvSBuilderEvenShell_energy_ge_nineFifths_normSq
      (size n) (shell n) hOld hShell
        (finGlobalShellVector z (size n) (shell n))

/-- Quantitative odd tower-tail coercivity with the sharpened `9/5` gap. -/
theorem c13_logarithmicCvSBuilderOddTowerTailEnergy_ge_nineFifths_normSq
    (z : ℕ → ℝ) (size shell : ℕ → ℕ)
    (hSize : ∀ n, size (n + 1) = size n + shell n)
    (n : ℕ) (hOld : 960 ≤ size n) (hShell : shell n ≤ size n) :
    (9 / 5 : ℝ) * finiteVectorEuclideanNormSq
        (finGlobalShellVector z (size n) (shell n)) ≤
      finiteMatrixTowerTailEnergy
        (logarithmicCvSBuilderOddTowerMatrix
          13 c13PrimePowerLocation c13PrimePowerBase size)
        (logarithmicCvSBuilderOddTowerShellVector z size shell)
        (logarithmicCvSBuilderOddTowerSplit size shell hSize) n := by
  rw [logarithmicCvSBuilderOddTowerTailEnergy_eq_positiveModeEnergy
    13 c13PrimePowerLocation c13PrimePowerBase z size shell hSize n]
  exact
    c13_logarithmicCvSBuilderOddShell_energy_ge_nineFifths_normSq
      (size n) (shell n) hOld hShell
        (finGlobalShellVector z (size n) (shell n))

end RiemannCvs.V23BoundaryWeylMainline
