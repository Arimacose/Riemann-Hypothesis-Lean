import Mathlib

/-!
# Concrete parity displacement for the finite CvS kernel

The corrected cutoff-free CvS matrix is assembled from two entry types:

* an odd-symbol Loewner difference quotient (covering the archimedean and
  prime-translation entries), and
* the explicit rational pole kernel.

Both satisfy the same cross-multiplied Fourier identity

`(p-q) A(p,q) + (p+q) A(p,-q) = 2p A(p,0)`.

After passing to the orthonormal cosine/sine parity bases, this identity is
exactly the rectangular rank-one displacement

`D E - O D = beta etaᵀ`,

where `D` is the positive-frequency derivative matrix, its kernel is the
central cosine coordinate, and `eta = (1, sqrt 2, ..., sqrt 2)` is evaluation
at the origin.  The V22 zero-mode correction changes only the central-central
entry and is therefore annihilated by `D`.
-/

namespace RiemannCvs.CvSParityDisplacement

open scoped InnerProductSpace

/-- Difference-quotient kernel with an arbitrary diagonal value.  The
diagonal is irrelevant to the displacement identity because its coefficient
is `p-p = 0`. -/
noncomputable def oddDifferenceKernel
    (symbol diagonal : ℝ → ℝ) (p q : ℝ) : ℝ :=
  if p = q then diagonal p else (symbol q - symbol p) / (p - q)

/-- Every odd-symbol difference quotient satisfies the CvS Fourier
cross-multiplied displacement identity at positive frequencies. -/
theorem oddDifferenceKernel_displacement
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hOdd : Function.Odd symbol) :
    (p - q) * oddDifferenceKernel symbol diagonal p q +
        (p + q) * oddDifferenceKernel symbol diagonal p (-q) =
      2 * p * oddDifferenceKernel symbol diagonal p 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpNegQ : p ≠ -q := by linarith
  have hSymbolZero : symbol 0 = 0 := by
    have h := hOdd 0
    simp only [neg_zero] at h
    linarith
  by_cases hpq : p = q
  · subst q
    simp only [oddDifferenceKernel, if_pos, hpNegQ, if_false, hp0,
      hSymbolZero]
    field_simp [hp0]
    rw [hOdd p]
    ring
  · simp only [oddDifferenceKernel, hpq, if_false, hpNegQ, hp0,
      hSymbolZero]
    field_simp [hpq, hpNegQ, hp0]
    rw [hOdd q]
    ring

/-- Rational pole entry used by the cutoff-free CvS kernel. -/
noncomputable def poleKernel
    (scale a b : ℝ) (p q : ℝ) : ℝ :=
  scale * (a - b * p * q) /
    ((a + b * p ^ 2) * (a + b * q ^ 2))

/-- The rational pole entry satisfies the same displacement identity whenever
`a > 0` and `b ≥ 0`, which are the source-side values `L²` and `16π²`. -/
theorem poleKernel_displacement
    (scale a b p q : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) :
    (p - q) * poleKernel scale a b p q +
        (p + q) * poleKernel scale a b p (-q) =
      2 * p * poleKernel scale a b p 0 := by
  have hpDen : a + b * p ^ 2 ≠ 0 := by
    have : 0 < a + b * p ^ 2 := by positivity
    exact ne_of_gt this
  have hqDen : a + b * q ^ 2 ≠ 0 := by
    have : 0 < a + b * q ^ 2 := by positivity
    exact ne_of_gt this
  have ha0 : a ≠ 0 := ne_of_gt ha
  unfold poleKernel
  field_simp [hpDen, hqDen, ha0]
  ring

/-- The cross-multiplied identity as a reusable property of a full Fourier
kernel. -/
def DisplacementLaw (A : ℝ → ℝ → ℝ) : Prop :=
  ∀ p q, 0 < p → 0 < q →
    (p - q) * A p q + (p + q) * A p (-q) = 2 * p * A p 0

theorem oddDifferenceKernel_law
    (symbol diagonal : ℝ → ℝ)
    (hOdd : Function.Odd symbol) :
    DisplacementLaw (oddDifferenceKernel symbol diagonal) := by
  intro p q hp hq
  exact oddDifferenceKernel_displacement symbol diagonal p q hp hq hOdd

theorem poleKernel_law
    (scale a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) :
    DisplacementLaw (poleKernel scale a b) := by
  intro p q _hp _hq
  exact poleKernel_displacement scale a b p q ha hb

theorem DisplacementLaw.add
    {A B : ℝ → ℝ → ℝ}
    (hA : DisplacementLaw A)
    (hB : DisplacementLaw B) :
    DisplacementLaw (fun p q => A p q + B p q) := by
  intro p q hp hq
  have hA' := hA p q hp hq
  have hB' := hB p q hp hq
  linarith

theorem DisplacementLaw.smul
    {A : ℝ → ℝ → ℝ}
    (hA : DisplacementLaw A) (c : ℝ) :
    DisplacementLaw (fun p q => c * A p q) := by
  intro p q hp hq
  have h := hA p q hp hq
  calc
    (p - q) * (c * A p q) + (p + q) * (c * A p (-q)) =
        c * ((p - q) * A p q + (p + q) * A p (-q)) := by ring
    _ = c * (2 * p * A p 0) := by rw [h]
    _ = 2 * p * (c * A p 0) := by ring

theorem DisplacementLaw.neg
    {A : ℝ → ℝ → ℝ}
    (hA : DisplacementLaw A) :
    DisplacementLaw (fun p q => -A p q) := by
  intro p q hp hq
  have h := hA p q hp hq
  calc
    (p - q) * -A p q + (p + q) * -A p (-q) =
        -((p - q) * A p q + (p + q) * A p (-q)) := by ring
    _ = -(2 * p * A p 0) := by rw [h]
    _ = 2 * p * -A p 0 := by ring

section ParityMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rectangular positive-frequency derivative.  The `none` coordinate is the
central cosine mode and every `some i` coordinate is paired with the
corresponding sine mode. -/
noncomputable def derivativeMatrix
    (frequency : ι → ℝ) : Matrix ι (Option ι) ℝ :=
  fun i => fun
    | none => 0
    | some j => if i = j then frequency i else 0

/-- Even (cosine) parity compression of a reflection-symmetric full Fourier
kernel.  Only the positive-frequency rows enter the displacement proof; the
`none` row is included to give the complete `(N+1) × (N+1)` block. -/
noncomputable def evenParityMatrix
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) :
    Matrix (Option ι) (Option ι) ℝ :=
  fun i j =>
    match i, j with
    | none, none => A 0 0
    | none, some k => Real.sqrt 2 * A 0 (frequency k)
    | some k, none => Real.sqrt 2 * A (frequency k) 0
    | some k, some l =>
        A (frequency k) (frequency l) +
          A (frequency k) (-frequency l)

/-- Odd (sine) parity compression of the same full Fourier kernel. -/
noncomputable def oddParityMatrix
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    A (frequency i) (frequency j) -
      A (frequency i) (-frequency j)

/-- Origin evaluation in the orthonormal cosine basis. -/
noncomputable def boundaryVector : Option ι → ℝ
  | none => 1
  | some _ => Real.sqrt 2

/-- The rank-one output vector forced by the zero column of the full kernel. -/
noncomputable def displacementBeta
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) : ι → ℝ :=
  fun i => Real.sqrt 2 * frequency i * A (frequency i) 0

/-- The single central coordinate spanning the kernel of the rectangular
derivative when all positive frequencies are nonzero. -/
def centralVector : Option ι → ℝ
  | none => 1
  | some _ => 0

/-- Rank-one projector onto the central cosine coordinate.  The corrected V22
zero-mode term is a scalar multiple of this matrix. -/
def centralRankOne : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.vecMulVec centralVector centralVector

/-- The positive-frequency derivative annihilates every central-central
rank-one correction. -/
@[simp]
theorem derivativeMatrix_mul_centralRankOne
    (frequency : ι → ℝ) :
    derivativeMatrix frequency * (centralRankOne :
      Matrix (Option ι) (Option ι) ℝ) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  simp [derivativeMatrix, centralRankOne, Matrix.vecMulVec,
    centralVector]

@[simp]
theorem derivativeMatrix_mul_even_apply
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ)
    (i : ι) (j : Option ι) :
    (derivativeMatrix frequency * evenParityMatrix A frequency) i j =
      frequency i * evenParityMatrix A frequency (some i) j := by
  rw [Matrix.mul_apply]
  simp [derivativeMatrix]

@[simp]
theorem odd_mul_derivativeMatrix_none
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) (i : ι) :
    (oddParityMatrix A frequency * derivativeMatrix frequency) i none = 0 := by
  rw [Matrix.mul_apply]
  simp [derivativeMatrix]

@[simp]
theorem odd_mul_derivativeMatrix_some
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) (i j : ι) :
    (oddParityMatrix A frequency * derivativeMatrix frequency) i (some j) =
      oddParityMatrix A frequency i j * frequency j := by
  rw [Matrix.mul_apply]
  simp [derivativeMatrix]

/-- Source-kernel displacement becomes a concrete rectangular rank-one matrix
identity after cosine/sine parity compression. -/
theorem parityMatrix_displacement
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ)
    (hFrequency : ∀ i, 0 < frequency i)
    (hLaw : DisplacementLaw A) :
    derivativeMatrix frequency * evenParityMatrix A frequency -
        oddParityMatrix A frequency * derivativeMatrix frequency =
      Matrix.vecMulVec
        (displacementBeta A frequency)
        (boundaryVector : Option ι → ℝ) := by
  ext i j
  cases j with
  | none =>
      rw [Matrix.sub_apply, derivativeMatrix_mul_even_apply,
        odd_mul_derivativeMatrix_none, Matrix.vecMulVec_apply]
      simp [evenParityMatrix, displacementBeta, boundaryVector]
      ring
  | some j =>
      rw [Matrix.sub_apply, derivativeMatrix_mul_even_apply,
        odd_mul_derivativeMatrix_some, Matrix.vecMulVec_apply]
      simp only [evenParityMatrix, oddParityMatrix, displacementBeta,
        boundaryVector]
      have h := hLaw (frequency i) (frequency j)
        (hFrequency i) (hFrequency j)
      calc
        frequency i *
              (A (frequency i) (frequency j) +
                A (frequency i) (-frequency j)) -
            (A (frequency i) (frequency j) -
                A (frequency i) (-frequency j)) * frequency j =
            (frequency i - frequency j) *
                A (frequency i) (frequency j) +
              (frequency i + frequency j) *
                A (frequency i) (-frequency j) := by ring
        _ = 2 * frequency i * A (frequency i) 0 := h
        _ =
            (Real.sqrt 2 * frequency i * A (frequency i) 0) *
              Real.sqrt 2 := by
                have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
                  norm_num
                calc
                  2 * frequency i * A (frequency i) 0 =
                      (Real.sqrt 2) ^ 2 * frequency i *
                        A (frequency i) 0 := by rw [hsqrt]
                  _ =
                      (Real.sqrt 2 * frequency i * A (frequency i) 0) *
                        Real.sqrt 2 := by ring

/-- Adding any scalar central-central term leaves the rectangular displacement
unchanged.  In particular the V22 zero-mode repair preserves the same
`beta etaᵀ` identity exactly, rather than only perturbatively. -/
theorem parityMatrix_displacement_centralCorrected
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ)
    (hFrequency : ∀ i, 0 < frequency i)
    (hLaw : DisplacementLaw A) (delta : ℝ) :
    derivativeMatrix frequency *
          (evenParityMatrix A frequency +
            delta • (centralRankOne :
              Matrix (Option ι) (Option ι) ℝ)) -
        oddParityMatrix A frequency * derivativeMatrix frequency =
      Matrix.vecMulVec
        (displacementBeta A frequency)
        (boundaryVector : Option ι → ℝ) := by
  rw [Matrix.mul_add, Matrix.mul_smul,
    derivativeMatrix_mul_centralRankOne]
  simp only [smul_zero, add_zero]
  exact parityMatrix_displacement A frequency hFrequency hLaw

/-- Applying the concrete rectangular displacement to an even-coordinate
vector gives the pointwise Sylvester relation used by the no-crossing layer.
The scalar on the right is exactly origin evaluation in the orthonormal
cosine basis. -/
theorem parityMulVec_displacement
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ)
    (hFrequency : ∀ i, 0 < frequency i)
    (hLaw : DisplacementLaw A)
    (x : Option ι → ℝ) :
    (derivativeMatrix frequency).mulVec
          ((evenParityMatrix A frequency).mulVec x) -
        (oddParityMatrix A frequency).mulVec
          ((derivativeMatrix frequency).mulVec x) =
      (∑ j : Option ι,
          (boundaryVector (ι := ι) j : ℝ) * x j) •
        displacementBeta A frequency := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.sub_mulVec]
  rw [parityMatrix_displacement A frequency hFrequency hLaw]
  rw [Matrix.vecMulVec_mulVec]
  ext i
  change displacementBeta A frequency i *
      (∑ j : Option ι, boundaryVector j * x j) =
    (∑ j : Option ι, boundaryVector j * x j) *
      displacementBeta A frequency i
  exact mul_comm _ _

/-- Positive-frequency derivative as the concrete rectangular map consumed by
the abstract Sylvester no-crossing theorem. -/
noncomputable def derivativeLinearMap
    (frequency : ι → ℝ) :
    (Option ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.mulVecLin (derivativeMatrix frequency)

/-- Even CvS parity block as a linear endomorphism. -/
noncomputable def evenParityLinearMap
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) :
    (Option ι → ℝ) →ₗ[ℝ] (Option ι → ℝ) :=
  Matrix.mulVecLin (evenParityMatrix A frequency)

/-- Odd CvS parity block as a linear endomorphism. -/
noncomputable def oddParityLinearMap
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.mulVecLin (oddParityMatrix A frequency)

omit [DecidableEq ι] in
/-- Origin evaluation as an actual linear functional, with coefficients
`(1, sqrt 2, ..., sqrt 2)` in the orthonormal cosine basis. -/
noncomputable def boundaryFunctional :
    (Option ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j : Option ι, boundaryVector j * x j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

omit [Fintype ι] [DecidableEq ι] in
/-- The same origin-evaluation coefficients as a vector in the Euclidean
cosine-coordinate space used by the quantitative Schur-resolvent layer. -/
noncomputable def boundaryEuclideanVector :
    EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 (boundaryVector : Option ι → ℝ)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem boundaryEuclideanVector_apply (j : Option ι) :
    (boundaryEuclideanVector (ι := ι)).ofLp j = boundaryVector j := rfl

omit [DecidableEq ι] in
/-- Exact Euclidean size of the CvS boundary vector.  For the `N = 20`
positive-frequency block this specializes to `‖eta‖² = 41`. -/
@[simp]
theorem boundaryEuclideanVector_norm_sq :
    ‖boundaryEuclideanVector (ι := ι)‖ ^ 2 =
      2 * Fintype.card ι + 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_option]
  simp [boundaryEuclideanVector, boundaryVector]
  ring

/-- Finite Fourier-cutoff specialization of the boundary-vector norm. -/
@[simp]
theorem boundaryEuclideanVector_norm_sq_fin (N : ℕ) :
    ‖boundaryEuclideanVector (ι := Fin N)‖ ^ 2 =
      2 * (N : ℝ) + 1 := by
  simp

/-- Concrete norm entering the current `(c,N) = (13,20)` Schur budget. -/
@[simp]
theorem boundaryEuclideanVector_norm_sq_fin_twenty :
    ‖boundaryEuclideanVector (ι := Fin 20)‖ ^ 2 = 41 := by
  norm_num

omit [DecidableEq ι] in
/-- Riesz identification of the Euclidean boundary vector with the existing
origin-evaluation functional.  This is the concrete `eta` adapter needed by
`BoundaryWeylSchurTail`. -/
@[simp]
theorem boundaryEuclideanVector_inner_eq_boundaryFunctional
    (x : EuclideanSpace ℝ (Option ι)) :
    ⟪boundaryEuclideanVector (ι := ι), x⟫_ℝ =
      boundaryFunctional x.ofLp := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  change x.ofLp j * boundaryVector j = boundaryVector j * x.ofLp j
  ring

/-- Fully typed concrete instance of the rank-one Sylvester relation.  This
statement can be passed directly to `SylvesterNoCrossing` without another
matrix-to-linear-map adapter. -/
theorem concreteSylvesterRelation
    (A : ℝ → ℝ → ℝ) (frequency : ι → ℝ)
    (hFrequency : ∀ i, 0 < frequency i)
    (hLaw : DisplacementLaw A) :
    ∀ x,
      derivativeLinearMap frequency
          (evenParityLinearMap A frequency x) -
        oddParityLinearMap A frequency
          (derivativeLinearMap frequency x) =
        boundaryFunctional x • displacementBeta A frequency := by
  intro x
  exact parityMulVec_displacement A frequency hFrequency hLaw x

@[simp]
theorem derivativeMatrix_mulVec_apply
    (frequency : ι → ℝ) (x : Option ι → ℝ) (i : ι) :
    (derivativeMatrix frequency).mulVec x i =
      frequency i * x (some i) := by
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_option]
  simp [derivativeMatrix]

/-- Every vector killed by `D` is a scalar multiple of the central mode. -/
theorem eq_central_smul_of_derivative_mulVec_eq_zero
    (frequency : ι → ℝ) (x : Option ι → ℝ)
    (hFrequency : ∀ i, frequency i ≠ 0)
    (hKernel : (derivativeMatrix frequency).mulVec x = 0) :
    x = x none • centralVector := by
  funext j
  cases j with
  | none => simp [centralVector]
  | some j =>
      have hAt := congrFun hKernel j
      rw [derivativeMatrix_mulVec_apply] at hAt
      have hx : x (some j) = 0 := (mul_eq_zero.mp hAt).resolve_left
        (hFrequency j)
      simp [centralVector, hx]

@[simp]
theorem derivativeMatrix_mulVec_central
    (frequency : ι → ℝ) :
    (derivativeMatrix frequency).mulVec centralVector = 0 := by
  funext i
  simp [derivativeMatrix_mulVec_apply, centralVector]

omit [DecidableEq ι] in
/-- Boundary evaluation of the central kernel vector is normalized to one. -/
theorem boundaryVector_dot_central :
    (∑ j : Option ι,
      (boundaryVector (ι := ι) j : ℝ) * centralVector j) = 1 := by
  rw [Fintype.sum_option]
  simp [boundaryVector, centralVector]

end ParityMatrices

end RiemannCvs.CvSParityDisplacement
