import RiemannCvs.CombinedSymbolDyadicL2
import RiemannCvs.BoundaryWeylSchurTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators Real Interval

namespace RiemannCvs.PrimeTranslationFourierBridge

open RiemannCvs.CombinedSymbolDyadicL2

lemma integral_cos_affine (a b u v : ℝ) (ha : a ≠ 0) :
    (∫ x in u..v, Real.cos (a * x + b)) =
      (Real.sin (a * v + b) - Real.sin (a * u + b)) / a := by
  apply (eq_div_iff ha).2
  simpa only [integral_cos, mul_comm] using
    (intervalIntegral.mul_integral_comp_mul_add
      (f := Real.cos) (a := u) (b := v) a b)

/-- Twice the real Fourier coefficient of translation by `y`, truncated to
the overlap interval `[0, L-y]`, in the normalized integer Fourier basis on
`[0,L]`. -/
noncomputable def truncatedTranslationFourierEntry
    (L y : ℝ) (n m : ℤ) : ℝ :=
  (2 / L) * ∫ x in 0..(L - y),
    Real.cos
      (2 * Real.pi *
        (((m : ℝ) - (n : ℝ)) * x + (m : ℝ) * y) / L)

@[simp]
theorem truncatedTranslationFourierEntry_fullShift
    (L : ℝ) (n m : ℤ) :
    truncatedTranslationFourierEntry L L n m = 0 := by
  simp [truncatedTranslationFourierEntry]

theorem truncatedTranslationFourierEntry_neg_neg
    (L y : ℝ) (n m : ℤ) :
    truncatedTranslationFourierEntry L y (-n) (-m) =
      truncatedTranslationFourierEntry L y n m := by
  unfold truncatedTranslationFourierEntry
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  change Real.cos
      (2 * Real.pi *
        ((((-m : ℤ) : ℝ) - ((-n : ℤ) : ℝ)) * x + ((-m : ℤ) : ℝ) * y) / L) =
    Real.cos
      (2 * Real.pi *
        (((m : ℝ) - (n : ℝ)) * x + (m : ℝ) * y) / L)
  rw [show
      2 * Real.pi *
          ((((-m : ℤ) : ℝ) - ((-n : ℤ) : ℝ)) * x + ((-m : ℤ) : ℝ) * y) / L =
        -(2 * Real.pi *
          (((m : ℝ) - (n : ℝ)) * x + (m : ℝ) * y) / L) by
    push_cast
    ring]
  exact Real.cos_neg _

theorem truncatedTranslationFourierEntry_diagonal
    (L y : ℝ) (n : ℤ) (hL : L ≠ 0) :
    truncatedTranslationFourierEntry L y n n =
      2 * (1 - y / L) *
        Real.cos (2 * Real.pi * (n : ℝ) * y / L) := by
  simp only [truncatedTranslationFourierEntry, sub_self, zero_mul, zero_add,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem truncatedTranslationFourierEntry_offDiagonal
    (L y : ℝ) (n m : ℤ) (hL : L ≠ 0) (hnm : n ≠ m) :
    truncatedTranslationFourierEntry L y n m =
      (Real.sin (2 * Real.pi * (m : ℝ) * y / L) -
        Real.sin (2 * Real.pi * (n : ℝ) * y / L)) /
        (Real.pi * ((n : ℝ) - (m : ℝ))) := by
  have hnmR : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
  have hFreq : 2 * Real.pi * ((m : ℝ) - (n : ℝ)) / L ≠ 0 := by
    positivity
  rw [truncatedTranslationFourierEntry]
  have hInt := integral_cos_affine
    (2 * Real.pi * ((m : ℝ) - (n : ℝ)) / L)
    (2 * Real.pi * (m : ℝ) * y / L)
    0 (L - y) hFreq
  have hPhase :
      2 * Real.pi * ((m : ℝ) - (n : ℝ)) / L * (L - y) +
          2 * Real.pi * (m : ℝ) * y / L =
        ((m - n : ℤ) : ℝ) * (2 * Real.pi) +
          2 * Real.pi * (n : ℝ) * y / L := by
    push_cast
    field_simp
    ring
  rw [show (fun x : ℝ =>
      Real.cos
        (2 * Real.pi *
          (((m : ℝ) - (n : ℝ)) * x + (m : ℝ) * y) / L)) =
      (fun x : ℝ => Real.cos
        ((2 * Real.pi * ((m : ℝ) - (n : ℝ)) / L) * x +
          2 * Real.pi * (m : ℝ) * y / L)) by
        funext x
        congr 1
        field_simp]
  rw [hInt, hPhase]
  rw [add_comm (((m - n : ℤ) : ℝ) * (2 * Real.pi))]
  rw [Real.sin_add_int_mul_two_pi]
  simp only [mul_zero, zero_add]
  field_simp
  ring

/-- A single CvS logarithmic prime event is exactly its von-Mangoldt weight
times the self-adjoint truncated-translation Fourier coefficient. -/
theorem logarithmicPrimeEventEntry_eq_weight_mul_truncatedTranslation
    (c location base : ℝ) (n m : ℤ) (hc : 1 < c) :
    logarithmicPrimeEventEntry c location base (n : ℝ) (m : ℝ) =
      logarithmicPrimeWeight location base *
        truncatedTranslationFourierEntry
          (Real.log c) (Real.log location) n m := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hcNe : c ≠ 1 := ne_of_gt hc
  have hLog : Real.log c ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hcPos hcNe
  by_cases hnm : n = m
  · subst m
    rw [truncatedTranslationFourierEntry_diagonal _ _ _ hLog]
    rw [logarithmicPrimeEventEntry, if_pos rfl]
    unfold logarithmicPrimePhase
    ring_nf
  · have hnmR : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
    rw [truncatedTranslationFourierEntry_offDiagonal _ _ _ _ hLog hnm]
    rw [logarithmicPrimeEventEntry, if_neg hnmR]
    unfold logarithmicPrimePhase
    ring_nf

/-- The integral coefficient is symmetric on the integer Fourier lattice, as
required for the self-adjoint part of truncated translation. -/
theorem truncatedTranslationFourierEntry_symm
    (L y : ℝ) (n m : ℤ) (hL : L ≠ 0) :
    truncatedTranslationFourierEntry L y n m =
      truncatedTranslationFourierEntry L y m n := by
  by_cases hnm : n = m
  · subst m
    rfl
  · have hmn : m ≠ n := Ne.symm hnm
    have hnmR : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
    have hmnR : (m : ℝ) ≠ (n : ℝ) := Ne.symm hnmR
    rw [truncatedTranslationFourierEntry_offDiagonal L y n m hL hnm,
      truncatedTranslationFourierEntry_offDiagonal L y m n hL hmn]
    field_simp [Real.pi_ne_zero, hnmR, hmnR]
    ring

/-- The weighted sum of integral coefficients for all prime-power events. -/
noncomputable def finitePrimeTranslationFourierEntry
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) : ℝ :=
  ∑ i, logarithmicPrimeWeight (location i) (base i) *
    truncatedTranslationFourierEntry
      (Real.log c) (Real.log (location i)) n m

theorem finitePrimeTranslationFourierEntry_neg_neg
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    finitePrimeTranslationFourierEntry c location base (-n) (-m) =
      finitePrimeTranslationFourierEntry c location base n m := by
  unfold finitePrimeTranslationFourierEntry
  apply Finset.sum_congr rfl
  intro i hi
  rw [truncatedTranslationFourierEntry_neg_neg]

theorem finitePrimeTranslationFourierEntry_neg_left
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    finitePrimeTranslationFourierEntry c location base (-n) m =
      finitePrimeTranslationFourierEntry c location base n (-m) := by
  simpa using (finitePrimeTranslationFourierEntry_neg_neg
    c location base (-n) m).symm

/-- The literal finite CvS prime matrix is the integer-Fourier compression of
the weighted sum of self-adjoint truncated translations. -/
theorem finiteLogarithmicPrimeEntry_eq_translationCompression
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) (hc : 1 < c) :
    finiteLogarithmicPrimeEntry c location base (n : ℝ) (m : ℝ) =
      finitePrimeTranslationFourierEntry c location base n m := by
  rw [finiteLogarithmicPrimeEntry_eq_sum_eventEntries]
  unfold finitePrimeTranslationFourierEntry
  apply Finset.sum_congr rfl
  intro i hi
  exact logarithmicPrimeEventEntry_eq_weight_mul_truncatedTranslation
    c (location i) (base i) n m hc

/-- Pull the translation compression back to any finite family of integer
Fourier modes. -/
noncomputable def finitePrimeTranslationModeMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j => finitePrimeTranslationFourierEntry c location base
    (mode i) (mode j)

/-- Positive-mode even compression of the translation matrix. -/
noncomputable def finitePrimeTranslationEvenModeMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    finitePrimeTranslationFourierEntry c location base (mode i) (mode j) +
      finitePrimeTranslationFourierEntry c location base (mode i) (-mode j)

/-- Positive-mode odd compression of the translation matrix. -/
noncomputable def finitePrimeTranslationOddModeMatrix
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) :
    Matrix κ κ ℝ :=
  fun i j =>
    finitePrimeTranslationFourierEntry c location base (mode i) (mode j) -
      finitePrimeTranslationFourierEntry c location base (mode i) (-mode j)

theorem finitePrimeTranslationEvenModeMatrix_eq_source
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ)
    (hc : 1 < c) (i j : κ) :
    finitePrimeTranslationEvenModeMatrix c location base mode i j =
      finiteLogarithmicPrimeEntry c location base
          (mode i : ℝ) (mode j : ℝ) +
        finiteLogarithmicPrimeEntry c location base
          (mode i : ℝ) (-mode j : ℝ) := by
  rw [show (-mode j : ℝ) = ((-mode j : ℤ) : ℝ) by norm_num]
  rw [finitePrimeTranslationEvenModeMatrix,
    finiteLogarithmicPrimeEntry_eq_translationCompression
      c location base (mode i) (mode j) hc,
    finiteLogarithmicPrimeEntry_eq_translationCompression
      c location base (mode i) (-mode j) hc]

theorem finitePrimeTranslationOddModeMatrix_eq_source
    {ι κ : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ)
    (hc : 1 < c) (i j : κ) :
    finitePrimeTranslationOddModeMatrix c location base mode i j =
      finiteLogarithmicPrimeEntry c location base
          (mode i : ℝ) (mode j : ℝ) -
        finiteLogarithmicPrimeEntry c location base
          (mode i : ℝ) (-mode j : ℝ) := by
  rw [show (-mode j : ℝ) = ((-mode j : ℤ) : ℝ) by norm_num]
  rw [finitePrimeTranslationOddModeMatrix,
    finiteLogarithmicPrimeEntry_eq_translationCompression
      c location base (mode i) (mode j) hc,
    finiteLogarithmicPrimeEntry_eq_translationCompression
      c location base (mode i) (-mode j) hc]

/-- Signed-mode family used to realize the parity blocks as literal
compressions of one full translation matrix. -/
def signedMode {κ : Type*} (mode : κ → ℤ) : κ ⊕ κ → ℤ :=
  Sum.elim mode (fun i => -mode i)

def evenSignedVector {κ : Type*} (x : κ → ℝ) : κ ⊕ κ → ℝ :=
  Sum.elim x x

def oddSignedVector {κ : Type*} (x : κ → ℝ) : κ ⊕ κ → ℝ :=
  Sum.elim x (fun i => -x i)

private lemma sum_neg_univ {κ : Type*} [Fintype κ] (f : κ → ℝ) :
    (∑ i, -f i) = -(∑ i, f i) := by
  exact Finset.sum_neg_distrib (s := Finset.univ) f

/-- The full signed-mode energy of an even vector is twice the energy of the
positive-mode even compression. -/
theorem signedMode_evenEnergy_eq_two_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix c location base (signedMode mode))
        (evenSignedVector x) =
      2 * BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationEvenModeMatrix c location base mode) x := by
  simp only [BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy,
    Fintype.sum_sum_type, finitePrimeTranslationModeMatrix,
    finitePrimeTranslationEvenModeMatrix, signedMode, evenSignedVector,
    Sum.elim_inl, Sum.elim_inr]
  simp_rw [finitePrimeTranslationFourierEntry_neg_left]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

/-- The corresponding signed-mode identity for the odd parity sector. -/
theorem signedMode_oddEnergy_eq_two_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ) :
    BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationModeMatrix c location base (signedMode mode))
        (oddSignedVector x) =
      2 * BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationOddModeMatrix c location base mode) x := by
  simp only [BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy,
    Fintype.sum_sum_type, finitePrimeTranslationModeMatrix,
    finitePrimeTranslationOddModeMatrix, signedMode, oddSignedVector,
    Sum.elim_inl, Sum.elim_inr]
  simp_rw [finitePrimeTranslationFourierEntry_neg_left]
  let Arow : κ → ℝ := fun i => ∑ j, x i *
    finitePrimeTranslationFourierEntry c location base
      (mode i) (mode j) * x j
  let Brow : κ → ℝ := fun i => ∑ j, x i *
    finitePrimeTranslationFourierEntry c location base
      (mode i) (-mode j) * x j
  have hNegB (i : κ) :
      (∑ j, -(x i * finitePrimeTranslationFourierEntry c location base
        (mode i) (-mode j) * x j)) = -Brow i := by
    exact (sum_neg_univ (fun j => x i *
      finitePrimeTranslationFourierEntry c location base
        (mode i) (-mode j) * x j)).trans (congrArg Neg.neg rfl)
  have hPN (i : κ) :
      (∑ j, x i * finitePrimeTranslationFourierEntry c location base
        (mode i) (-mode j) * -x j) = -Brow i := by
    calc
      _ = ∑ j, -(x i * finitePrimeTranslationFourierEntry c location base
          (mode i) (-mode j) * x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -Brow i := hNegB i
  have hNP (i : κ) :
      (∑ j, -x i * finitePrimeTranslationFourierEntry c location base
        (mode i) (-mode j) * x j) = -Brow i := by
    calc
      _ = ∑ j, -(x i * finitePrimeTranslationFourierEntry c location base
          (mode i) (-mode j) * x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -Brow i := hNegB i
  have hNN (i : κ) :
      (∑ j, -x i * finitePrimeTranslationFourierEntry c location base
        (mode i) (- -mode j) * -x j) = Arow i := by
    dsimp only [Arow]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [neg_neg]
    ring
  have hOddRow (i : κ) :
      (∑ j, x i *
        (finitePrimeTranslationFourierEntry c location base
            (mode i) (mode j) -
          finitePrimeTranslationFourierEntry c location base
            (mode i) (-mode j)) * x j) = Arow i - Brow i := by
    dsimp only [Arow, Brow]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ = (∑ i : κ, (Arow i - Brow i)) +
        (∑ i : κ, (Arow i - Brow i)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        change Arow i + (∑ j, x i *
          finitePrimeTranslationFourierEntry c location base
            (mode i) (-mode j) * -x j) = Arow i - Brow i
        rw [hPN]
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hNP, hNN]
        ring
    _ = 2 * (∑ i : κ, (Arow i - Brow i)) := by
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (hOddRow i).symm

/-- Squared coordinate norm used by the finite translation compression. -/
noncomputable def finiteTranslationVectorNormSq
    {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ :=
  ∑ i, x i ^ 2

theorem evenSignedVector_normSq
    {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    finiteTranslationVectorNormSq (evenSignedVector x) =
      2 * finiteTranslationVectorNormSq x := by
  simp [finiteTranslationVectorNormSq, Fintype.sum_sum_type,
    evenSignedVector]
  ring

theorem oddSignedVector_normSq
    {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    finiteTranslationVectorNormSq (oddSignedVector x) =
      2 * finiteTranslationVectorNormSq x := by
  simp [finiteTranslationVectorNormSq, Fintype.sum_sum_type,
    oddSignedVector]
  ring

/-- A single full signed-space form bound passes to every even parity
compression with the same constant. -/
theorem evenModeEnergy_abs_le_of_signedModeEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c B : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ)
    (hSigned :
      |BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
          (finitePrimeTranslationModeMatrix c location base (signedMode mode))
          (evenSignedVector x)| ≤
        B * finiteTranslationVectorNormSq (evenSignedVector x)) :
    |BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationEvenModeMatrix c location base mode) x| ≤
      B * finiteTranslationVectorNormSq x := by
  rw [signedMode_evenEnergy_eq_two_mul, evenSignedVector_normSq,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hSigned
  nlinarith

/-- The identical full-space bound passes to every odd parity compression. -/
theorem oddModeEnergy_abs_le_of_signedModeEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c B : ℝ) (location base : ι → ℝ) (mode : κ → ℤ) (x : κ → ℝ)
    (hSigned :
      |BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
          (finitePrimeTranslationModeMatrix c location base (signedMode mode))
          (oddSignedVector x)| ≤
        B * finiteTranslationVectorNormSq (oddSignedVector x)) :
    |BoundaryWeylSchurTail.finiteMatrixQuadraticEnergy
        (finitePrimeTranslationOddModeMatrix c location base mode) x| ≤
      B * finiteTranslationVectorNormSq x := by
  rw [signedMode_oddEnergy_eq_two_mul, oddSignedVector_normSq,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hSigned
  nlinarith

/-- Centered finite-matrix form of the same exact compression identity. -/
noncomputable def logarithmicPrimeTranslationMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => finitePrimeTranslationFourierEntry c location base
    (centeredIntegerMode N i) (centeredIntegerMode N j)

theorem logarithmicPrimeTranslationMatrix_eq_source
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) (hc : 1 < c)
    (i j : Fin (2 * N + 1)) :
    logarithmicPrimeTranslationMatrix c location base N i j =
      finiteLogarithmicPrimeEntry c location base
        (centeredIntegerMode N i : ℝ) (centeredIntegerMode N j : ℝ) := by
  exact (finiteLogarithmicPrimeEntry_eq_translationCompression
    c location base (centeredIntegerMode N i) (centeredIntegerMode N j) hc).symm

end RiemannCvs.PrimeTranslationFourierBridge
