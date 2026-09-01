import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import RiemannCvs.BoundaryWeylCumulative
import RiemannCvs.CvSParityDisplacement
import RiemannCvs.DigammaQuarter

/-!
# Combined-symbol dyadic L2 adapters

The V23 previous-core route keeps the Archimedean and prime pieces inside one
odd Loewner symbol.  This module supplies the kernel-checked algebra that turns
source estimates for that symbol into dyadic square-sum and rectangular-form
bounds.

There are eight layers.

1. A source-algebra layer builds the finite prime sine polynomial, defines the
   concrete digamma/geometric Archimedean symbol and diagonal, proves all
   series convergent and their reflection laws, identifies the centered
   signed-integer finite builder and its orthonormal parity compression with
   the exact kernel, preserves the exact `1 / π` normalization, and removes
   the endpoint phase `2 * π * n` on natural Fourier modes.
2. Exact finite geometric-sum theorems control every nonresonant shifted
   exponential, sine, and cosine phase sum used by the scalar certificate.
3. The exact parity formulas from `CvSParityDisplacement` give entry bounds
   for positive separated modes.
4. Finite Cauchy--Schwarz converts entry-square budgets into rectangular
   bilinear bounds.
5. The Mathlib reciprocal-square tail estimate gives the exact dyadic factor
   `1 / (2 * N)`.
6. Finite Abel summation turns an affine prefix bound into a weighted dyadic
   bound and exposes the strict endpoint expression consumed by the Arb
   certificate.
7. Rowwise square estimates and rectangular Cauchy--Schwarz send that scalar
   bound into a matrix Frobenius budget and then into coercive relative energy.
8. The newest-band specialization closes the constant `24*C`, while the exact
   doubled-shell identity supplies the one-half transport used by the recursive
   channel envelope.

The concrete source builder, its orthonormal parity compression, and the
newest separated row/column bands are identified exactly below.  Its symmetry
and simultaneous-reflection invariance are also proved, so the finite recursive
  cross coordinate is the literal historical/newest rectangular form.  The
  remaining operator input is the concrete Archimedean diagonal/remainder and
  prime-form bound.  The exponential-series mass and first moment are evaluated
  exactly below, closing every geometric correction in the Archimedean symbol
  and diagonal.  Its lower bound is now reduced further to one global
  DLMF-form quadratic digamma remainder and one cutoff-13 endpoint scalar
  comparison.  Lean derives the canonical trigamma `HasSum` identity by a
  differentiated shift equation and finite telescoping.  A Cauchy estimate on
  fixed complex circles turns the same quadratic remainder into decay of the
  shifted digamma derivative, so the pointwise digamma and trigamma inputs are
  both discharged by that single analytic bound before the all-mode shell
  floor is formed.
  The scalar pole-weight tail estimate is now closed by
  pointwise reciprocal-square bounds and a consecutive-shell reindexing.  The
  all-scale shell-tower compatibility, the exact positive-mode component
  decomposition, its direct application to the concrete tower-tail energy,
  the rank-one reduction and `poleTail` bounds of both pole parity blocks, and
  the pole-closed cutoff-13 coercivity consumers are instantiated in
  `V23BoundaryWeylMainline`.  No numerical certificate is promoted to a Lean
  theorem here.
-/

namespace RiemannCvs.CombinedSymbolDyadicL2

open Finset
open Filter
open Metric
open scoped BigOperators Topology

/-!
## Combined-symbol source algebra

The prime-power contribution is a finite sine polynomial.  The following
definitions and identities close the purely algebraic part of combining it
with an odd Archimedean symbol and applying the concrete `1 / π` Fourier
normalization.  The finite prime entrywise formula is connected to these
functions below; the remaining source task is the analytic Archimedean symbol
and diagonal.
-/

/-- A finite real sine polynomial, the exact shape of the prime-power part of
the combined CvS Loewner symbol. -/
noncomputable def finiteSineSymbol
    {ι : Type*} [Fintype ι]
    (weight phase : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, weight i * Real.sin (phase i * x)

/-- Every finite sine polynomial is odd. -/
theorem finiteSineSymbol_odd
    {ι : Type*} [Fintype ι]
    (weight phase : ι → ℝ) :
    Function.Odd (finiteSineSymbol weight phase) := by
  intro x
  simp [finiteSineSymbol]

/-- The source-level combined symbol keeps the Archimedean and prime pieces
inside one Loewner symbol. -/
noncomputable def combinedSineSymbol
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (weight phase : ι → ℝ) (x : ℝ) : ℝ :=
  arch x + finiteSineSymbol weight phase x

/-- An odd Archimedean symbol plus the prime sine polynomial is odd. -/
theorem combinedSineSymbol_odd
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (weight phase : ι → ℝ)
    (hArch : Function.Odd arch) :
    Function.Odd (combinedSineSymbol arch weight phase) := by
  intro x
  rw [combinedSineSymbol, combinedSineSymbol, hArch x,
    finiteSineSymbol_odd weight phase x]
  ring

/-- Fourier normalization used by the concrete CvS off-diagonal kernel. -/
noncomputable def fourierNormalizedSymbol
    (symbol : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.pi) * symbol x

/-- Fourier normalization preserves oddness. -/
theorem fourierNormalizedSymbol_odd
    (symbol : ℝ → ℝ) (hSymbol : Function.Odd symbol) :
    Function.Odd (fourierNormalizedSymbol symbol) := by
  intro x
  rw [fourierNormalizedSymbol, fourierNormalizedSymbol, hSymbol x]
  ring

/-- Adding source symbols and diagonal data adds their complete Loewner
kernels. -/
theorem oddDifferenceKernel_add
    (leftSymbol leftDiagonal rightSymbol rightDiagonal : ℝ → ℝ)
    (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fun x => leftSymbol x + rightSymbol x)
        (fun x => leftDiagonal x + rightDiagonal x) p q =
      CvSParityDisplacement.oddDifferenceKernel leftSymbol leftDiagonal p q +
        CvSParityDisplacement.oddDifferenceKernel rightSymbol rightDiagonal p q := by
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel]
  · simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    ring

/-- Scaling both the off-diagonal symbol and diagonal source data scales the
complete Loewner kernel exactly. -/
theorem oddDifferenceKernel_smul
    (symbol diagonal : ℝ → ℝ) (scale p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fun x => scale * symbol x)
        (fun x => scale * diagonal x) p q =
      scale * CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q := by
  by_cases hpq : p = q
  · subst q
    simp [CvSParityDisplacement.oddDifferenceKernel]
  · simp only [CvSParityDisplacement.oddDifferenceKernel, hpq, if_false]
    ring

/-- The exact `1 / π` CvS normalization commutes with the complete Loewner
kernel when its diagonal data use the same normalization. -/
theorem oddDifferenceKernel_fourierNormalized
    (symbol diagonal : ℝ → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol symbol)
        (fourierNormalizedSymbol diagonal) p q =
      (1 / Real.pi) *
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q := by
  change CvSParityDisplacement.oddDifferenceKernel
      (fun x => (1 / Real.pi) * symbol x)
      (fun x => (1 / Real.pi) * diagonal x) p q = _
  exact oddDifferenceKernel_smul symbol diagonal (1 / Real.pi) p q

/-- End-to-end algebraic source identity: the normalized combined kernel is
the normalized sum of the Archimedean and prime sine Loewner kernels. -/
theorem oddDifferenceKernel_fourierNormalized_combined
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (weight phase : ι → ℝ)
    (primeDiagonal : ℝ → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol (combinedSineSymbol arch weight phase))
        (fourierNormalizedSymbol
          (fun x => archDiagonal x + primeDiagonal x)) p q =
      (1 / Real.pi) *
        (CvSParityDisplacement.oddDifferenceKernel arch archDiagonal p q +
          CvSParityDisplacement.oddDifferenceKernel
            (finiteSineSymbol weight phase) primeDiagonal p q) := by
  rw [oddDifferenceKernel_fourierNormalized]
  change (1 / Real.pi) *
      CvSParityDisplacement.oddDifferenceKernel
        (fun x => arch x + finiteSineSymbol weight phase x)
        (fun x => archDiagonal x + primeDiagonal x) p q = _
  exact congrArg (fun z => (1 / Real.pi) * z)
    (oddDifferenceKernel_add arch archDiagonal
      (finiteSineSymbol weight phase) primeDiagonal p q)

/-- The endpoint phase `2 * π * n` vanishes exactly on every natural Fourier
mode, justifying deletion of the `q = c` sine event from off-diagonal symbols. -/
theorem sin_two_pi_nat (n : ℕ) :
    Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
  rw [show 2 * Real.pi * (n : ℝ) = ((2 * n : ℕ) : ℝ) * Real.pi by
    push_cast
    ring]
  exact Real.sin_nat_mul_pi (2 * n)

/-!
## Exact finite geometric-sum bounds

The Arb square-sum certificate uses the standard bound
`|∑ exp (i*n*phase)| ≤ 1 / |sin (phase/2)|` for every nonresonant phase.
The next six results prove the complex geometric identity, preserve an
arbitrary starting index, and expose the real sine/cosine consequences used
for the single, doubled, difference, and sum phases in that certificate.
-/

/-- A nonresonant finite geometric progression on the unit circle is bounded
by the reciprocal half-angle sine. -/
theorem norm_geometric_sum_le_inv_abs_sin_half
    (phase : ℝ) (count : ℕ) (hPhase : Real.sin (phase / 2) ≠ 0) :
    ‖∑ n ∈ Finset.range count,
        (Complex.exp (Complex.I * (phase : ℂ))) ^ n‖ ≤
      1 / |Real.sin (phase / 2)| := by
  let z : ℂ := Complex.exp (Complex.I * (phase : ℂ))
  have hz : ‖z‖ = 1 := by
    simp [z]
  have hChord : ‖z - 1‖ = 2 * |Real.sin (phase / 2)| := by
    dsimp [z]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs]
  have hGeom := geom_sum_mul z count
  have hNormEq := congrArg norm hGeom
  rw [norm_mul, hChord] at hNormEq
  have hNumerator : ‖z ^ count - 1‖ ≤ 2 := by
    calc
      ‖z ^ count - 1‖ ≤ ‖z ^ count‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  apply (le_div_iff₀ (abs_pos.mpr hPhase)).2
  nlinarith [norm_nonneg
    (∑ n ∈ Finset.range count,
      (Complex.exp (Complex.I * (phase : ℂ))) ^ n)]

/-- Shifting the starting exponent does not enlarge the unit-circle
geometric-sum bound. -/
theorem norm_shifted_geometric_sum_le_inv_abs_sin_half
    (phase : ℝ) (start count : ℕ)
    (hPhase : Real.sin (phase / 2) ≠ 0) :
    ‖∑ j ∈ Finset.range count,
        (Complex.exp (Complex.I * (phase : ℂ))) ^ (start + j)‖ ≤
      1 / |Real.sin (phase / 2)| := by
  let z : ℂ := Complex.exp (Complex.I * (phase : ℂ))
  have hz : ‖z‖ = 1 := by
    simp [z]
  calc
    ‖∑ j ∈ Finset.range count,
        (Complex.exp (Complex.I * (phase : ℂ))) ^ (start + j)‖ =
        ‖z ^ start * ∑ j ∈ Finset.range count, z ^ j‖ := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [z, pow_add]
    _ = ‖∑ j ∈ Finset.range count, z ^ j‖ := by
      rw [norm_mul, norm_pow, hz]
      norm_num
    _ ≤ 1 / |Real.sin (phase / 2)| := by
      simpa [z] using
        norm_geometric_sum_le_inv_abs_sin_half phase count hPhase

/-- Integer multiples of a real phase exponentiate to powers of the one-step
unit-circle phase. -/
lemma exp_nat_mul_real_phase
    (phase : ℝ) (n : ℕ) :
    Complex.exp ((((n : ℕ) : ℝ) * phase : ℝ) * Complex.I) =
      (Complex.exp (Complex.I * (phase : ℂ))) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Complex-exponential form of the shifted finite geometric-sum bound. -/
theorem norm_shifted_exp_sum_le_inv_abs_sin_half
    (phase : ℝ) (start count : ℕ)
    (hPhase : Real.sin (phase / 2) ≠ 0) :
    ‖∑ j ∈ Finset.range count,
        Complex.exp (((((start + j : ℕ) : ℝ) * phase : ℝ)) * Complex.I)‖ ≤
      1 / |Real.sin (phase / 2)| := by
  rw [show (∑ j ∈ Finset.range count,
      Complex.exp (((((start + j : ℕ) : ℝ) * phase : ℝ)) * Complex.I)) =
      ∑ j ∈ Finset.range count,
        (Complex.exp (Complex.I * (phase : ℂ))) ^ (start + j) by
    apply Finset.sum_congr rfl
    intro j hj
    exact exp_nat_mul_real_phase phase (start + j)]
  exact norm_shifted_geometric_sum_le_inv_abs_sin_half
    phase start count hPhase

/-- Every shifted finite sine sum inherits the nonresonant geometric bound. -/
theorem abs_shifted_sine_sum_le_inv_abs_sin_half
    (phase : ℝ) (start count : ℕ)
    (hPhase : Real.sin (phase / 2) ≠ 0) :
    |∑ j ∈ Finset.range count,
        Real.sin (((start + j : ℕ) : ℝ) * phase)| ≤
      1 / |Real.sin (phase / 2)| := by
  let z : ℂ := ∑ j ∈ Finset.range count,
    Complex.exp (((((start + j : ℕ) : ℝ) * phase : ℝ)) * Complex.I)
  have hIm : z.im = ∑ j ∈ Finset.range count,
      Real.sin (((start + j : ℕ) : ℝ) * phase) := by
    dsimp [z]
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact Complex.exp_ofReal_mul_I_im
      (((start + j : ℕ) : ℝ) * phase)
  rw [← hIm]
  exact (Complex.abs_im_le_norm z).trans
    (norm_shifted_exp_sum_le_inv_abs_sin_half
      phase start count hPhase)

/-- Every shifted finite cosine sum inherits the nonresonant geometric bound. -/
theorem abs_shifted_cosine_sum_le_inv_abs_sin_half
    (phase : ℝ) (start count : ℕ)
    (hPhase : Real.sin (phase / 2) ≠ 0) :
    |∑ j ∈ Finset.range count,
        Real.cos (((start + j : ℕ) : ℝ) * phase)| ≤
      1 / |Real.sin (phase / 2)| := by
  let z : ℂ := ∑ j ∈ Finset.range count,
    Complex.exp (((((start + j : ℕ) : ℝ) * phase : ℝ)) * Complex.I)
  have hRe : z.re = ∑ j ∈ Finset.range count,
      Real.cos (((start + j : ℕ) : ℝ) * phase) := by
    dsimp [z]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact Complex.exp_ofReal_mul_I_re
      (((start + j : ℕ) : ℝ) * phase)
  rw [← hRe]
  exact (Complex.abs_re_le_norm z).trans
    (norm_shifted_exp_sum_le_inv_abs_sin_half
      phase start count hPhase)

/-!
## Concrete logarithmic prime-power source formula

The abstract finite sine polynomial can now be instantiated with the exact
weights and phases used by the CvS prime source.  These definitions and
identities expose the concrete formula to the kernel and certificate layers;
the entrywise adapter below proves equality with the original finite prime
matrix formula.
-/

/-- The exact von-Mangoldt weight attached to a prime-power location `q=p^k`. -/
noncomputable def logarithmicPrimeWeight (q p : ℝ) : ℝ :=
  Real.log p / Real.sqrt q

/-- The Fourier phase of the prime-power event at location `q` for cutoff `c`. -/
noncomputable def logarithmicPrimePhase (c q : ℝ) : ℝ :=
  2 * Real.pi * Real.log q / Real.log c

/-- The concrete finite prime-power sine symbol used by the CvS certificate. -/
noncomputable def finiteLogarithmicPrimeSymbol
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (x : ℝ) : ℝ :=
  finiteSineSymbol
    (fun i => logarithmicPrimeWeight (location i) (base i))
    (fun i => logarithmicPrimePhase c (location i)) x

/-- The concrete logarithmic prime-power symbol is odd. -/
theorem finiteLogarithmicPrimeSymbol_odd
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) :
    Function.Odd (finiteLogarithmicPrimeSymbol c location base) := by
  exact finiteSineSymbol_odd
    (fun i => logarithmicPrimeWeight (location i) (base i))
    (fun i => logarithmicPrimePhase c (location i))

/-- The source-level combined symbol with the concrete logarithmic prime
weights and phases exposed. -/
noncomputable def logarithmicCombinedSymbol
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (c : ℝ) (location base : ι → ℝ) (x : ℝ) : ℝ :=
  combinedSineSymbol arch
    (fun i => logarithmicPrimeWeight (location i) (base i))
    (fun i => logarithmicPrimePhase c (location i)) x

/-- An odd Archimedean symbol plus the concrete logarithmic prime symbol is
odd. -/
theorem logarithmicCombinedSymbol_odd
    {ι : Type*} [Fintype ι]
    (arch : ℝ → ℝ) (c : ℝ) (location base : ι → ℝ)
    (hArch : Function.Odd arch) :
    Function.Odd (logarithmicCombinedSymbol arch c location base) := by
  exact combinedSineSymbol_odd arch
    (fun i => logarithmicPrimeWeight (location i) (base i))
    (fun i => logarithmicPrimePhase c (location i)) hArch

/-- Exact complete-kernel identity for the concrete logarithmic combined
symbol, including supplied diagonal values and the Fourier `1/pi` scale. -/
theorem oddDifferenceKernel_fourierNormalized_logarithmicCombined
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (primeDiagonal : ℝ → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol
          (logarithmicCombinedSymbol arch c location base))
        (fourierNormalizedSymbol
          (fun x => archDiagonal x + primeDiagonal x)) p q =
      (1 / Real.pi) *
        (CvSParityDisplacement.oddDifferenceKernel arch archDiagonal p q +
          CvSParityDisplacement.oddDifferenceKernel
            (finiteLogarithmicPrimeSymbol c location base)
            primeDiagonal p q) := by
  change CvSParityDisplacement.oddDifferenceKernel
      (fourierNormalizedSymbol
        (combinedSineSymbol arch
          (fun i => logarithmicPrimeWeight (location i) (base i))
          (fun i => logarithmicPrimePhase c (location i))))
      (fourierNormalizedSymbol
        (fun x => archDiagonal x + primeDiagonal x)) p q =
    (1 / Real.pi) *
      (CvSParityDisplacement.oddDifferenceKernel arch archDiagonal p q +
        CvSParityDisplacement.oddDifferenceKernel
          (finiteSineSymbol
            (fun i => logarithmicPrimeWeight (location i) (base i))
            (fun i => logarithmicPrimePhase c (location i)))
          primeDiagonal p q)
  exact oddDifferenceKernel_fourierNormalized_combined arch archDiagonal
    (fun i => logarithmicPrimeWeight (location i) (base i))
    (fun i => logarithmicPrimePhase c (location i))
    primeDiagonal p q

/-- The event at the cutoff itself has phase exactly `2*pi`. -/
theorem logarithmicPrimePhase_self
    (c : ℝ) (hc : 1 < c) :
    logarithmicPrimePhase c c = 2 * Real.pi := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hcNe : c ≠ 1 := ne_of_gt hc
  have hLog : Real.log c ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hcPos hcNe
  unfold logarithmicPrimePhase
  field_simp

/-- Consequently the cutoff event vanishes on every natural Fourier mode. -/
theorem logarithmicPrimeEndpoint_sine_zero
    (c : ℝ) (n : ℕ) (hc : 1 < c) :
    Real.sin (logarithmicPrimePhase c c * (n : ℝ)) = 0 := by
  rw [logarithmicPrimePhase_self c hc]
  exact sin_two_pi_nat n

/-- The complete weighted endpoint event is therefore exactly zero. -/
theorem logarithmicPrimeEndpoint_term_zero
    (c p : ℝ) (n : ℕ) (hc : 1 < c) :
    logarithmicPrimeWeight c p *
        Real.sin (logarithmicPrimePhase c c * (n : ℝ)) = 0 := by
  rw [logarithmicPrimeEndpoint_sine_zero c n hc]
  ring

/-!
### Exact entrywise prime-source adapter

The numerical CvS builder uses a piecewise formula: an explicit diagonal
cosine sum and, off the diagonal, a normalized sine divided difference.  The
following definitions expose that formula literally and prove that it is the
complete diagonal-aware Loewner kernel of the logarithmic prime symbol.  Thus
the prime matrix-entry identification is algebraic; the remaining source
identification is the Archimedean symbol and its diagonal.
-/

/-- The actual diagonal value of the finite prime-power block. -/
noncomputable def finiteLogarithmicPrimeDiagonal
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, 2 * logarithmicPrimeWeight (location i) (base i) *
    (1 - Real.log (location i) / Real.log c) *
    Real.cos (logarithmicPrimePhase c (location i) * x)

/-- The actual finite prime diagonal is even in the Fourier mode. -/
theorem finiteLogarithmicPrimeDiagonal_even
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) :
    Function.Even (finiteLogarithmicPrimeDiagonal c location base) := by
  intro x
  simp [finiteLogarithmicPrimeDiagonal, mul_neg]

/-- Piecewise source formula used to assemble the finite prime-power matrix. -/
noncomputable def finiteLogarithmicPrimeEntry
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (p q : ℝ) : ℝ :=
  if p = q then finiteLogarithmicPrimeDiagonal c location base p
  else
    ∑ i, logarithmicPrimeWeight (location i) (base i) *
      (Real.sin (logarithmicPrimePhase c (location i) * q) -
        Real.sin (logarithmicPrimePhase c (location i) * p)) /
      (Real.pi * (p - q))

/-- One prime-power event in the entrywise assembly loop. -/
noncomputable def logarithmicPrimeEventEntry
    (c location base p q : ℝ) : ℝ :=
  if p = q then
    2 * logarithmicPrimeWeight location base *
      (1 - Real.log location / Real.log c) *
      Real.cos (logarithmicPrimePhase c location * p)
  else
    logarithmicPrimeWeight location base *
      (Real.sin (logarithmicPrimePhase c location * q) -
        Real.sin (logarithmicPrimePhase c location * p)) /
      (Real.pi * (p - q))

/-- The finite source entry is exactly the sum of the eventwise matrix loop. -/
theorem finiteLogarithmicPrimeEntry_eq_sum_eventEntries
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (p q : ℝ) :
    finiteLogarithmicPrimeEntry c location base p q =
      ∑ i, logarithmicPrimeEventEntry c (location i) (base i) p q := by
  by_cases hpq : p = q
  · subst q
    simp [finiteLogarithmicPrimeEntry, finiteLogarithmicPrimeDiagonal,
      logarithmicPrimeEventEntry]
  · simp [finiteLogarithmicPrimeEntry, logarithmicPrimeEventEntry, hpq]

/-- The event exactly at the cutoff contributes zero on integer Fourier modes,
both on and off the diagonal. -/
theorem logarithmicPrimeEndpointEventEntry_nat_zero
    (c base : ℝ) (m n : ℕ) (hc : 1 < c) :
    logarithmicPrimeEventEntry c c base (m : ℝ) (n : ℝ) = 0 := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hcNe : c ≠ 1 := ne_of_gt hc
  have hLog : Real.log c ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hcPos hcNe
  by_cases hmn : (m : ℝ) = (n : ℝ)
  · simp [logarithmicPrimeEventEntry, hmn, hLog]
  · rw [logarithmicPrimeEventEntry, if_neg hmn,
      logarithmicPrimeEndpoint_sine_zero c n hc,
      logarithmicPrimeEndpoint_sine_zero c m hc]
    ring

/-- The literal piecewise prime-source entry is exactly the normalized odd
Loewner kernel with its actual matrix diagonal. -/
theorem finiteLogarithmicPrimeEntry_eq_oddDifferenceKernel
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (p q : ℝ) :
    finiteLogarithmicPrimeEntry c location base p q =
      CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol
          (finiteLogarithmicPrimeSymbol c location base))
        (finiteLogarithmicPrimeDiagonal c location base) p q := by
  by_cases hpq : p = q
  · subst q
    simp [finiteLogarithmicPrimeEntry,
      CvSParityDisplacement.oddDifferenceKernel]
  · simp only [finiteLogarithmicPrimeEntry, hpq, if_false,
      CvSParityDisplacement.oddDifferenceKernel,
      fourierNormalizedSymbol, finiteLogarithmicPrimeSymbol,
      finiteSineSymbol]
    rw [← Finset.sum_div]
    simp only [mul_sub, Finset.sum_sub_distrib]
    field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hpq]
    simp [mul_comm]

/-- Complete Archimedean-plus-prime source adapter with the actual, already
normalized matrix diagonal.  After this equality only the Archimedean source
entry needs an analytic identification. -/
theorem oddDifferenceKernel_logarithmicCombined_actualDiagonal
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) :
    CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol
          (logarithmicCombinedSymbol arch c location base))
        (fun x => archDiagonal x +
          finiteLogarithmicPrimeDiagonal c location base x) p q =
      CvSParityDisplacement.oddDifferenceKernel
          (fourierNormalizedSymbol arch) archDiagonal p q +
        finiteLogarithmicPrimeEntry c location base p q := by
  rw [finiteLogarithmicPrimeEntry_eq_oddDifferenceKernel]
  have hSymbol :
      fourierNormalizedSymbol
          (logarithmicCombinedSymbol arch c location base) =
        fun x => fourierNormalizedSymbol arch x +
          fourierNormalizedSymbol
            (finiteLogarithmicPrimeSymbol c location base) x := by
    funext x
    simp only [fourierNormalizedSymbol, logarithmicCombinedSymbol,
      combinedSineSymbol, finiteLogarithmicPrimeSymbol]
    ring
  rw [hSymbol]
  exact oddDifferenceKernel_add
    (fourierNormalizedSymbol arch) archDiagonal
    (fourierNormalizedSymbol
      (finiteLogarithmicPrimeSymbol c location base))
    (finiteLogarithmicPrimeDiagonal c location base) p q

/-!
### Full cutoff-free source assembly

The Archimedean builder has the same literal diagonal/off-diagonal shape as
the prime block.  The normalized source entry below makes that formula
explicit.  Adding the already identified prime entry and subtracting both
from the exact rational `W_{0,2}` pole kernel gives the complete regular
cutoff-free source convention used by the numerical matrix builder.
-/

/-- Literal diagonal/off-diagonal source formula for a normalized Loewner
entry with an already normalized matrix diagonal. -/
noncomputable def normalizedLoewnerSourceEntry
    (symbol diagonal : ℝ → ℝ) (p q : ℝ) : ℝ :=
  if p = q then diagonal p
  else (symbol q - symbol p) / (Real.pi * (p - q))

theorem normalizedLoewnerSourceEntry_eq_oddDifferenceKernel
    (symbol diagonal : ℝ → ℝ) (p q : ℝ) :
    normalizedLoewnerSourceEntry symbol diagonal p q =
      CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol symbol) diagonal p q := by
  by_cases hpq : p = q
  · subst q
    simp [normalizedLoewnerSourceEntry,
      CvSParityDisplacement.oddDifferenceKernel]
  · simp only [normalizedLoewnerSourceEntry, hpq, if_false,
      CvSParityDisplacement.oddDifferenceKernel, fourierNormalizedSymbol]
    field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hpq]

/-- Literal regular source block `W_R + W_p`. -/
noncomputable def logarithmicArchPrimeEntry
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) : ℝ :=
  normalizedLoewnerSourceEntry arch archDiagonal p q +
    finiteLogarithmicPrimeEntry c location base p q

theorem logarithmicArchPrimeEntry_eq_oddDifferenceKernel
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) :
    logarithmicArchPrimeEntry arch archDiagonal c location base p q =
      CvSParityDisplacement.oddDifferenceKernel
        (fourierNormalizedSymbol
          (logarithmicCombinedSymbol arch c location base))
        (fun x => archDiagonal x +
          finiteLogarithmicPrimeDiagonal c location base x) p q := by
  unfold logarithmicArchPrimeEntry
  rw [normalizedLoewnerSourceEntry_eq_oddDifferenceKernel]
  exact (oddDifferenceKernel_logarithmicCombined_actualDiagonal
    arch archDiagonal c location base p q).symm

/-- Exact cutoff-dependent rational `W_{0,2}` kernel. -/
noncomputable def logarithmicPoleKernel (c p q : ℝ) : ℝ :=
  CvSParityDisplacement.poleKernel
    (32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2)
    ((Real.log c) ^ 2) (16 * Real.pi ^ 2) p q

theorem logarithmicPoleKernel_symm (c p q : ℝ) :
    logarithmicPoleKernel c p q = logarithmicPoleKernel c q p := by
  unfold logarithmicPoleKernel
  exact CvSParityDisplacement.poleKernel_symm _ _ _ _ _

theorem logarithmicPoleKernel_neg_neg (c p q : ℝ) :
    logarithmicPoleKernel c (-p) (-q) = logarithmicPoleKernel c p q := by
  unfold logarithmicPoleKernel
  exact CvSParityDisplacement.poleKernel_neg_neg _ _ _ _ _

theorem logarithmicPoleKernel_law
    (c : ℝ) (hc : 1 < c) :
    CvSParityDisplacement.DisplacementLaw (logarithmicPoleKernel c) := by
  have hLog : 0 < Real.log c := Real.log_pos hc
  unfold logarithmicPoleKernel
  exact CvSParityDisplacement.poleKernel_law
    (32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2)
    ((Real.log c) ^ 2) (16 * Real.pi ^ 2)
    (by positivity) (by positivity)

/-- Literal corrected regular cutoff-free assembly `W_02 - W_R - W_p`. -/
noncomputable def logarithmicCutoffFreeKernel
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) : ℝ :=
  logarithmicPoleKernel c p q -
    logarithmicArchPrimeEntry arch archDiagonal c location base p q

theorem logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) :
    logarithmicCutoffFreeKernel arch archDiagonal c location base p q =
      logarithmicPoleKernel c p q -
        CvSParityDisplacement.oddDifferenceKernel
          (fourierNormalizedSymbol
            (logarithmicCombinedSymbol arch c location base))
          (fun x => archDiagonal x +
            finiteLogarithmicPrimeDiagonal c location base x) p q := by
  unfold logarithmicCutoffFreeKernel
  rw [logarithmicArchPrimeEntry_eq_oddDifferenceKernel]

/-- The complete cutoff-free source kernel is symmetric before any parity
compression. -/
theorem logarithmicCutoffFreeKernel_symm
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (p q : ℝ) :
    logarithmicCutoffFreeKernel arch archDiagonal c location base p q =
      logarithmicCutoffFreeKernel arch archDiagonal c location base q p := by
  rw [logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicPoleKernel_symm,
    CvSParityDisplacement.oddDifferenceKernel_symm]

theorem logarithmicCutoffFreeKernel_law
    {ι : Type*} [Fintype ι]
    (arch archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ)
    (hArch : Function.Odd arch) (hc : 1 < c) :
    CvSParityDisplacement.DisplacementLaw
      (logarithmicCutoffFreeKernel arch archDiagonal c location base) := by
  have hKernel :
      logarithmicCutoffFreeKernel arch archDiagonal c location base =
        fun p q => logarithmicPoleKernel c p q -
          CvSParityDisplacement.oddDifferenceKernel
            (fourierNormalizedSymbol
              (logarithmicCombinedSymbol arch c location base))
            (fun x => archDiagonal x +
              finiteLogarithmicPrimeDiagonal c location base x) p q := by
    funext p q
    exact logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel
      arch archDiagonal c location base p q
  rw [hKernel]
  have hRegular := CvSParityDisplacement.oddDifferenceKernel_law
    (fourierNormalizedSymbol
      (logarithmicCombinedSymbol arch c location base))
    (fun x => archDiagonal x +
      finiteLogarithmicPrimeDiagonal c location base x)
    (fourierNormalizedSymbol_odd
      (logarithmicCombinedSymbol arch c location base)
      (logarithmicCombinedSymbol_odd arch c location base hArch))
  simpa [sub_eq_add_neg] using
    (logarithmicPoleKernel_law c hc).add hRegular.neg

/-!
### Concrete Archimedean symbol

The numerical source builder evaluates a digamma imaginary part and subtracts
an exponentially convergent geometric correction.  The definitions below
record that formula literally, prove convergence for every `c > 1`, establish
its oddness from complex conjugation, and instantiate the complete cutoff-free
displacement law without an abstract Archimedean-symbol premise.
-/

theorem deriv_gamma_conj (s : ℂ) :
    deriv Complex.Gamma ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv Complex.Gamma s) := by
  have hGamma :
      (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) =
        Complex.Gamma := by
    funext z
    simp [Function.comp_apply, Complex.Gamma_conj]
  have hDeriv := congrArg deriv hGamma
  rw [deriv_conj_conj] at hDeriv
  have hs := congrFun hDeriv ((starRingEnd ℂ) s)
  simpa [Function.comp_apply] using hs.symm

theorem digamma_conj (s : ℂ) :
    Complex.digamma ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (Complex.digamma s) := by
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply,
    deriv_gamma_conj, Complex.Gamma_conj]
  exact (map_div₀ (starRingEnd ℂ)
    (deriv Complex.Gamma s) (Complex.Gamma s)).symm

/-- Fourier frequency used by the Archimedean source at cutoff `c`. -/
noncomputable def archimedeanFrequency (c x : ℝ) : ℝ :=
  2 * Real.pi * x / Real.log c

/-- Positive half-integer in the geometric correction series. -/
noncomputable def archimedeanHalfInteger (k : ℕ) : ℝ :=
  2 * (k : ℝ) + 1 / 2

/-- The even geometric correction series in the Archimedean sine symbol. -/
noncomputable def archimedeanGeometricSeries (c x : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-archimedeanHalfInteger k * Real.log c) /
    (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2)

theorem summable_archimedeanGeometricSeries_terms
    (c x : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) /
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2)) := by
  have hLog : 0 < Real.log c := Real.log_pos hc
  have hExp : Summable (fun k : ℕ =>
      Real.exp ((k : ℝ) * (-2 * Real.log c))) :=
    Real.summable_exp_nat_mul_iff.mpr (by linarith)
  have hNumerator : Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c)) := by
    have hEq :
        (fun k : ℕ =>
            Real.exp (-archimedeanHalfInteger k * Real.log c)) =
          fun k : ℕ => Real.exp (-Real.log c / 2) *
            Real.exp ((k : ℝ) * (-2 * Real.log c)) := by
      funext k
      rw [← Real.exp_add]
      unfold archimedeanHalfInteger
      congr 1
      ring
    rw [hEq]
    exact hExp.mul_left _
  refine (hNumerator.mul_left 4).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · positivity
  · have hHalf : 1 / 2 ≤ archimedeanHalfInteger k := by
      unfold archimedeanHalfInteger
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hDen : 0 <
        archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
      nlinarith [sq_nonneg (archimedeanFrequency c x)]
    apply (div_le_iff₀ hDen).2
    have hExpNonneg :
        0 ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) := by
      positivity
    have hOne : 1 ≤ 4 *
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) := by
      nlinarith [sq_nonneg (archimedeanFrequency c x)]
    calc
      Real.exp (-archimedeanHalfInteger k * Real.log c) =
          Real.exp (-archimedeanHalfInteger k * Real.log c) * 1 := by ring
      _ ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) *
          (4 * (archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2)) :=
        mul_le_mul_of_nonneg_left hOne hExpNonneg
      _ = 4 * Real.exp (-archimedeanHalfInteger k * Real.log c) *
          (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) := by
        ring

theorem archimedeanFrequency_neg (c x : ℝ) :
    archimedeanFrequency c (-x) = -archimedeanFrequency c x := by
  unfold archimedeanFrequency
  ring

theorem archimedeanGeometricSeries_neg (c x : ℝ) :
    archimedeanGeometricSeries c (-x) =
      archimedeanGeometricSeries c x := by
  unfold archimedeanGeometricSeries
  apply tsum_congr
  intro k
  rw [archimedeanFrequency_neg]
  ring

/-- Digamma contribution to the odd Archimedean symbol. -/
noncomputable def archimedeanDigammaImaginary (c x : ℝ) : ℝ :=
  (1 / 2) *
    (Complex.digamma
      ((1 / 4 : ℂ) +
        ((Real.pi * x / Real.log c : ℝ) : ℂ) * Complex.I)).im

theorem archimedeanDigammaImaginary_neg (c x : ℝ) :
    archimedeanDigammaImaginary c (-x) =
      -archimedeanDigammaImaginary c x := by
  have hArg :
      (1 / 4 : ℂ) +
          ((Real.pi * (-x) / Real.log c : ℝ) : ℂ) * Complex.I =
        (starRingEnd ℂ) ((1 / 4 : ℂ) +
          ((Real.pi * x / Real.log c : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp
    · simp
      ring
  unfold archimedeanDigammaImaginary
  rw [hArg, digamma_conj]
  simp

/-- Concrete real odd symbol used by the cutoff-free Archimedean
off-diagonal matrix entries. -/
noncomputable def logarithmicArchimedeanSymbol (c x : ℝ) : ℝ :=
  archimedeanDigammaImaginary c x -
    archimedeanFrequency c x * archimedeanGeometricSeries c x

theorem logarithmicArchimedeanSymbol_odd (c : ℝ) :
    Function.Odd (logarithmicArchimedeanSymbol c) := by
  intro x
  rw [logarithmicArchimedeanSymbol, logarithmicArchimedeanSymbol,
    archimedeanDigammaImaginary_neg, archimedeanFrequency_neg,
    archimedeanGeometricSeries_neg]
  ring

theorem logarithmicCutoffFreeKernel_archimedean_law
    {ι : Type*} [Fintype ι]
    (archDiagonal : ℝ → ℝ) (c : ℝ)
    (location base : ι → ℝ) (hc : 1 < c) :
    CvSParityDisplacement.DisplacementLaw
      (logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c) archDiagonal c location base) := by
  exact logarithmicCutoffFreeKernel_law
    (logarithmicArchimedeanSymbol c) archDiagonal c location base
    (logarithmicArchimedeanSymbol_odd c) hc

/-!
### Concrete Archimedean diagonal

The diagonal branch used by the finite CvS builder contains the real digamma
correction, the real derivative of digamma, three exponentially convergent
geometric corrections, and two cutoff constants.  The following definitions
record that formula, prove every series summable for `c > 1`, prove reflection
evenness, and instantiate the full cutoff-free kernel with no free
Archimedean source argument.
-/
noncomputable def archimedeanArgument (c x : ℝ) : ℂ :=
  (1 / 4 : ℂ) + ((Real.pi * x / Real.log c : ℝ) : ℂ) * Complex.I

theorem archimedeanArgument_neg (c x : ℝ) :
    archimedeanArgument c (-x) =
      (starRingEnd ℂ) (archimedeanArgument c x) := by
  unfold archimedeanArgument
  apply Complex.ext
  · simp
  · simp
    ring

theorem archimedeanDigammaImaginary_eq_argument (c x : ℝ) :
    archimedeanDigammaImaginary c x =
      (1 / 2) * (Complex.digamma (archimedeanArgument c x)).im := by
  rfl

theorem deriv_digamma_conj (s : ℂ) :
    deriv Complex.digamma ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv Complex.digamma s) := by
  have hDigamma :
      (starRingEnd ℂ) ∘ Complex.digamma ∘ (starRingEnd ℂ) =
        Complex.digamma := by
    funext z
    simp [Function.comp_apply, digamma_conj]
  have hDeriv := congrArg deriv hDigamma
  rw [deriv_conj_conj] at hDeriv
  have hs := congrFun hDeriv ((starRingEnd ℂ) s)
  simpa [Function.comp_apply] using hs.symm

noncomputable def archimedeanCosineGeometricSeries (c x : ℝ) : ℝ :=
  ∑' k : ℕ,
    Real.exp (-archimedeanHalfInteger k * Real.log c) *
      archimedeanFrequency c x ^ 2 /
        (archimedeanHalfInteger k *
          (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2))

noncomputable def archimedeanXOneGeometricSeries (c x : ℝ) : ℝ :=
  ∑' k : ℕ,
    Real.exp (-archimedeanHalfInteger k * Real.log c) *
      archimedeanHalfInteger k /
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2)

noncomputable def archimedeanXTwoGeometricSeries (c x : ℝ) : ℝ :=
  ∑' k : ℕ,
    Real.exp (-archimedeanHalfInteger k * Real.log c) *
      (archimedeanHalfInteger k ^ 2 - archimedeanFrequency c x ^ 2) /
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) ^ 2

theorem summable_archimedeanExponential_terms (c : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c)) := by
  have hLog : 0 < Real.log c := Real.log_pos hc
  have hExp : Summable (fun k : ℕ =>
      Real.exp ((k : ℝ) * (-2 * Real.log c))) :=
    Real.summable_exp_nat_mul_iff.mpr (by linarith)
  have hEq :
      (fun k : ℕ =>
          Real.exp (-archimedeanHalfInteger k * Real.log c)) =
        fun k : ℕ => Real.exp (-Real.log c / 2) *
          Real.exp ((k : ℝ) * (-2 * Real.log c)) := by
    funext k
    rw [← Real.exp_add]
    unfold archimedeanHalfInteger
    congr 1
    ring
  rw [hEq]
  exact hExp.mul_left _

theorem summable_archimedeanCosineGeometricSeries_terms
    (c x : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) *
        archimedeanFrequency c x ^ 2 /
          (archimedeanHalfInteger k *
            (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2))) := by
  refine ((summable_archimedeanExponential_terms c hc).mul_left 2).of_nonneg_of_le
    (fun k => ?_) (fun k => ?_)
  · have hA : 0 ≤ archimedeanHalfInteger k := by
      unfold archimedeanHalfInteger
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _))
        (sq_nonneg (archimedeanFrequency c x)))
      (mul_nonneg hA
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  · have hHalf : 1 / 2 ≤ archimedeanHalfInteger k := by
      unfold archimedeanHalfInteger
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hA : 0 < archimedeanHalfInteger k := lt_of_lt_of_le (by norm_num) hHalf
    have hDen : 0 <
        archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
      nlinarith [sq_nonneg (archimedeanFrequency c x)]
    have hFull : 0 < archimedeanHalfInteger k *
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) :=
      mul_pos hA hDen
    apply (div_le_iff₀ hFull).2
    have hOne : 1 ≤ 2 * archimedeanHalfInteger k := by linarith
    have hFreqDen : archimedeanFrequency c x ^ 2 ≤
        archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
      nlinarith [sq_nonneg (archimedeanHalfInteger k)]
    have hRatio : archimedeanFrequency c x ^ 2 ≤
        (2 * archimedeanHalfInteger k) *
          (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) :=
      hFreqDen.trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hOne (le_of_lt hDen))
    have hExpNonneg :
        0 ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hRatio hExpNonneg
    nlinarith

theorem summable_archimedeanXOneGeometricSeries_terms
    (c x : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) *
        archimedeanHalfInteger k /
          (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2)) := by
  refine ((summable_archimedeanExponential_terms c hc).mul_left 2).of_nonneg_of_le
    (fun k => ?_) (fun k => ?_)
  · have hA : 0 ≤ archimedeanHalfInteger k := by
      unfold archimedeanHalfInteger
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _)) hA)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · have hHalf : 1 / 2 ≤ archimedeanHalfInteger k := by
      unfold archimedeanHalfInteger
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hDen : 0 <
        archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
      nlinarith [sq_nonneg (archimedeanFrequency c x)]
    apply (div_le_iff₀ hDen).2
    have hRatio : archimedeanHalfInteger k ≤ 2 *
        (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) := by
      nlinarith [sq_nonneg (archimedeanHalfInteger k - 1 / 2),
        sq_nonneg (archimedeanFrequency c x)]
    have hExpNonneg :
        0 ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hRatio hExpNonneg
    nlinarith

theorem summable_archimedeanXTwoGeometricSeries_terms
    (c x : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) *
        (archimedeanHalfInteger k ^ 2 - archimedeanFrequency c x ^ 2) /
          (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) ^ 2) := by
  refine ((summable_archimedeanExponential_terms c hc).mul_left 4).of_norm_bounded
    (fun k => ?_)
  have hHalf : 1 / 2 ≤ archimedeanHalfInteger k := by
    unfold archimedeanHalfInteger
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hDen : 0 <
      archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
    nlinarith [sq_nonneg (archimedeanFrequency c x)]
  have hAbsDiff :
      |archimedeanHalfInteger k ^ 2 - archimedeanFrequency c x ^ 2| ≤
        archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
    calc
      |archimedeanHalfInteger k ^ 2 - archimedeanFrequency c x ^ 2| ≤
          |archimedeanHalfInteger k ^ 2| + |archimedeanFrequency c x ^ 2| :=
        abs_sub _ _
      _ = archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  have hOne : 1 ≤ 4 *
      (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) := by
    nlinarith [sq_nonneg (archimedeanFrequency c x)]
  have hDenScaled :
      archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2 ≤
        4 * (archimedeanHalfInteger k ^ 2 + archimedeanFrequency c x ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hOne (le_of_lt hDen)
    nlinarith
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (sq_pos_of_pos hDen)]
  apply (div_le_iff₀ (sq_pos_of_pos hDen)).2
  have hExpNonneg :
      0 ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left
    (hAbsDiff.trans hDenScaled) hExpNonneg
  nlinarith

theorem archimedeanCosineGeometricSeries_neg (c x : ℝ) :
    archimedeanCosineGeometricSeries c (-x) =
      archimedeanCosineGeometricSeries c x := by
  unfold archimedeanCosineGeometricSeries
  apply tsum_congr
  intro k
  rw [archimedeanFrequency_neg]
  ring

theorem archimedeanXOneGeometricSeries_neg (c x : ℝ) :
    archimedeanXOneGeometricSeries c (-x) =
      archimedeanXOneGeometricSeries c x := by
  unfold archimedeanXOneGeometricSeries
  apply tsum_congr
  intro k
  rw [archimedeanFrequency_neg]
  ring

theorem archimedeanXTwoGeometricSeries_neg (c x : ℝ) :
    archimedeanXTwoGeometricSeries c (-x) =
      archimedeanXTwoGeometricSeries c x := by
  unfold archimedeanXTwoGeometricSeries
  apply tsum_congr
  intro k
  rw [archimedeanFrequency_neg]
  ring

noncomputable def archimedeanCosineCorrection (c x : ℝ) : ℝ :=
  -(1 / 2) *
      ((Complex.digamma (archimedeanArgument c x)).re -
        (Complex.digamma (1 / 4 : ℂ)).re) +
    archimedeanCosineGeometricSeries c x

theorem archimedeanCosineCorrection_neg (c x : ℝ) :
    archimedeanCosineCorrection c (-x) =
      archimedeanCosineCorrection c x := by
  unfold archimedeanCosineCorrection
  rw [archimedeanArgument_neg, digamma_conj,
    archimedeanCosineGeometricSeries_neg]
  simp

noncomputable def archimedeanCrossCorrection (c x : ℝ) : ℝ :=
  (1 / 4) * (deriv Complex.digamma (archimedeanArgument c x)).re -
    Real.log c * archimedeanXOneGeometricSeries c x -
    archimedeanXTwoGeometricSeries c x

theorem archimedeanCrossCorrection_neg (c x : ℝ) :
    archimedeanCrossCorrection c (-x) =
      archimedeanCrossCorrection c x := by
  unfold archimedeanCrossCorrection
  rw [archimedeanArgument_neg, deriv_digamma_conj,
    archimedeanXOneGeometricSeries_neg,
    archimedeanXTwoGeometricSeries_neg]
  simp

noncomputable def logarithmicArchimedeanKappa (c : ℝ) : ℝ :=
  Real.log
      (4 * Real.pi *
        (Real.exp (Real.log c) - 1) / (Real.exp (Real.log c) + 1)) +
    Real.eulerMascheroniConstant

noncomputable def logarithmicArchimedeanPoleJ (c : ℝ) : ℝ :=
  let u := Real.exp (Real.log c / 2)
  (-2 * Real.log (u + 1) + Real.log (u ^ 2 + 1) +
    2 * Real.arctan u + Real.log 2 - Real.pi / 2)

noncomputable def logarithmicArchimedeanDiagonal (c x : ℝ) : ℝ :=
  logarithmicArchimedeanKappa c +
    2 * archimedeanCosineCorrection c x +
    logarithmicArchimedeanPoleJ c -
    (2 / Real.log c) * archimedeanCrossCorrection c x

/-!
### Exact geometric correction bounds

The interval certificate abbreviates the exponentially convergent correction
terms by their geometric mass `C` and first moment `B`.  The next layer
evaluates both sums exactly, proves the four source bounds
`w * g_s <= C / |w|`, `g_cc <= 2C`, `g_x1 <= B / w^2`, and
`|g_x2| <= C / w^2`, and combines them with supplied real digamma and
trigamma lower bounds.  Thus no geometric-series estimate remains in the
Archimedean diagonal premise.
-/
noncomputable def archimedeanGeometricMass (c : ℝ) : ℝ :=
  Real.exp (-Real.log c / 2) /
    (1 - Real.exp (-2 * Real.log c))

noncomputable def archimedeanGeometricFirstMoment (c : ℝ) : ℝ :=
  Real.exp (-Real.log c / 2) *
    ((1 / 2) / (1 - Real.exp (-2 * Real.log c)) +
      2 * Real.exp (-2 * Real.log c) /
        (1 - Real.exp (-2 * Real.log c)) ^ 2)

private theorem archimedeanExponential_eq_geometric
    (c : ℝ) (k : ℕ) :
    Real.exp (-archimedeanHalfInteger k * Real.log c) =
      Real.exp (-Real.log c / 2) *
        Real.exp (-2 * Real.log c) ^ k := by
  rw [show -archimedeanHalfInteger k * Real.log c =
      -Real.log c / 2 + (k : ℝ) * (-2 * Real.log c) by
    unfold archimedeanHalfInteger
    ring]
  rw [Real.exp_add, Real.exp_nat_mul]

theorem tsum_archimedeanExponential_eq_geometricMass
    (c : ℝ) (hc : 1 < c) :
    ∑' k : ℕ, Real.exp (-archimedeanHalfInteger k * Real.log c) =
      archimedeanGeometricMass c := by
  have hr0 : 0 ≤ Real.exp (-2 * Real.log c) := by positivity
  have hr1 : Real.exp (-2 * Real.log c) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.log_pos hc]
  simp_rw [archimedeanExponential_eq_geometric]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  simp [archimedeanGeometricMass, div_eq_mul_inv]

theorem tsum_archimedeanExponentialMoment_eq_geometricFirstMoment
    (c : ℝ) (hc : 1 < c) :
    ∑' k : ℕ,
        archimedeanHalfInteger k *
          Real.exp (-archimedeanHalfInteger k * Real.log c) =
      archimedeanGeometricFirstMoment c := by
  let r : ℝ := Real.exp (-2 * Real.log c)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.log_pos hc]
  have hrAbs : |r| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hGeom := hasSum_geometric_of_lt_one hr0 hr1
  have hMoment := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs] using hrAbs)
  have hCombined :=
    (hGeom.mul_left (1 / 2 : ℝ)).add (hMoment.mul_left (2 : ℝ))
  have hScaled := hCombined.mul_left (Real.exp (-Real.log c / 2))
  calc
    (∑' k : ℕ,
        archimedeanHalfInteger k *
          Real.exp (-archimedeanHalfInteger k * Real.log c)) =
        ∑' k : ℕ, Real.exp (-Real.log c / 2) *
          ((1 / 2 : ℝ) * r ^ k + 2 * ((k : ℝ) * r ^ k)) := by
      apply tsum_congr
      intro k
      rw [archimedeanExponential_eq_geometric]
      dsimp [r]
      unfold archimedeanHalfInteger
      ring
    _ = Real.exp (-Real.log c / 2) *
        ((1 / 2 : ℝ) * (1 - r)⁻¹ +
          2 * (r / (1 - r) ^ 2)) := hScaled.tsum_eq
    _ = archimedeanGeometricFirstMoment c := by
      simp [archimedeanGeometricFirstMoment, r, div_eq_mul_inv]
      ring

theorem summable_archimedeanExponentialMoment_terms
    (c : ℝ) (hc : 1 < c) :
    Summable (fun k : ℕ =>
      archimedeanHalfInteger k *
        Real.exp (-archimedeanHalfInteger k * Real.log c)) := by
  let r : ℝ := Real.exp (-2 * Real.log c)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.log_pos hc]
  have hrAbs : |r| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hGeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr0 hr1
  have hMoment : Summable (fun k : ℕ => (k : ℝ) * r ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs] using hrAbs)).summable
  have hScaled : Summable (fun k : ℕ =>
      Real.exp (-Real.log c / 2) *
        ((1 / 2 : ℝ) * r ^ k + 2 * ((k : ℝ) * r ^ k))) :=
    ((hGeom.mul_left (1 / 2 : ℝ)).add
      (hMoment.mul_left (2 : ℝ))).mul_left _
  exact hScaled.congr (fun k => by
    rw [archimedeanExponential_eq_geometric]
    dsimp [r]
    unfold archimedeanHalfInteger
    ring)

theorem archimedeanGeometricMass_nonneg (c : ℝ) (hc : 1 < c) :
    0 ≤ archimedeanGeometricMass c := by
  rw [← tsum_archimedeanExponential_eq_geometricMass c hc]
  exact tsum_nonneg (fun _ => le_of_lt (Real.exp_pos _))

theorem archimedeanGeometricSeries_nonneg (c x : ℝ) :
    0 ≤ archimedeanGeometricSeries c x := by
  unfold archimedeanGeometricSeries
  apply tsum_nonneg
  intro k
  have hHalf : 0 < archimedeanHalfInteger k := by
    unfold archimedeanHalfInteger
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (by nlinarith [sq_pos_of_pos hHalf,
      sq_nonneg (archimedeanFrequency c x)])

theorem archimedeanGeometricSeries_le_mass
    (c x : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0) :
    archimedeanGeometricSeries c x ≤
      archimedeanGeometricMass c /
        archimedeanFrequency c x ^ 2 := by
  have hFrequencySq : 0 < archimedeanFrequency c x ^ 2 :=
    sq_pos_of_ne_zero hFrequency
  have hUpper : Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) /
        archimedeanFrequency c x ^ 2) := by
    simpa [div_eq_mul_inv] using
      (summable_archimedeanExponential_terms c hc).mul_right
        (archimedeanFrequency c x ^ 2)⁻¹
  unfold archimedeanGeometricSeries
  calc
    (∑' k : ℕ,
        Real.exp (-archimedeanHalfInteger k * Real.log c) /
          (archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2)) ≤
        ∑' k : ℕ,
          Real.exp (-archimedeanHalfInteger k * Real.log c) /
            archimedeanFrequency c x ^ 2 := by
      apply (summable_archimedeanGeometricSeries_terms c x hc).tsum_le_tsum
      · intro k
        have hDen : 0 < archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2 := by
          have hHalf : 0 < archimedeanHalfInteger k := by
            unfold archimedeanHalfInteger
            have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
          nlinarith [sq_pos_of_pos hHalf,
            sq_nonneg (archimedeanFrequency c x)]
        apply (div_le_div_iff₀ hDen hFrequencySq).2
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (archimedeanHalfInteger k)])
          (le_of_lt (Real.exp_pos _))
      · exact hUpper
    _ = archimedeanGeometricMass c /
        archimedeanFrequency c x ^ 2 := by
      rw [tsum_div_const,
        tsum_archimedeanExponential_eq_geometricMass c hc]

theorem abs_archimedeanFrequency_mul_geometricSeries_le_mass
    (c x : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0) :
    |archimedeanFrequency c x * archimedeanGeometricSeries c x| ≤
      archimedeanGeometricMass c / |archimedeanFrequency c x| := by
  have hSeriesNonneg := archimedeanGeometricSeries_nonneg c x
  have hSeriesUpper := archimedeanGeometricSeries_le_mass
    c x hc hFrequency
  calc
    |archimedeanFrequency c x * archimedeanGeometricSeries c x| =
        |archimedeanFrequency c x| *
          archimedeanGeometricSeries c x := by
      rw [abs_mul, abs_of_nonneg hSeriesNonneg]
    _ ≤ |archimedeanFrequency c x| *
        (archimedeanGeometricMass c /
          archimedeanFrequency c x ^ 2) :=
      mul_le_mul_of_nonneg_left hSeriesUpper (abs_nonneg _)
    _ = archimedeanGeometricMass c /
        |archimedeanFrequency c x| := by
      have hAbs : |archimedeanFrequency c x| ≠ 0 :=
        abs_ne_zero.mpr hFrequency
      rw [← sq_abs]
      field_simp

theorem archimedeanCosineGeometricSeries_nonneg (c x : ℝ) :
    0 ≤ archimedeanCosineGeometricSeries c x := by
  unfold archimedeanCosineGeometricSeries
  apply tsum_nonneg
  intro k
  have hA : 0 ≤ archimedeanHalfInteger k := by
    unfold archimedeanHalfInteger
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact div_nonneg
    (mul_nonneg (le_of_lt (Real.exp_pos _))
      (sq_nonneg (archimedeanFrequency c x)))
    (mul_nonneg hA
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem archimedeanCosineGeometricSeries_le_mass
    (c x : ℝ) (hc : 1 < c) :
    archimedeanCosineGeometricSeries c x ≤
      2 * archimedeanGeometricMass c := by
  have hUpper : Summable (fun k : ℕ =>
      2 * Real.exp (-archimedeanHalfInteger k * Real.log c)) :=
    (summable_archimedeanExponential_terms c hc).mul_left 2
  unfold archimedeanCosineGeometricSeries
  calc
    (∑' k : ℕ,
        Real.exp (-archimedeanHalfInteger k * Real.log c) *
          archimedeanFrequency c x ^ 2 /
            (archimedeanHalfInteger k *
              (archimedeanHalfInteger k ^ 2 +
                archimedeanFrequency c x ^ 2))) ≤
        ∑' k : ℕ,
          2 * Real.exp (-archimedeanHalfInteger k * Real.log c) := by
      apply (summable_archimedeanCosineGeometricSeries_terms c x hc).tsum_le_tsum
      · intro k
        have hHalf : 1 / 2 ≤ archimedeanHalfInteger k := by
          unfold archimedeanHalfInteger
          have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hA : 0 < archimedeanHalfInteger k :=
          lt_of_lt_of_le (by norm_num) hHalf
        have hDen : 0 <
            archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2 := by
          nlinarith [sq_nonneg (archimedeanFrequency c x)]
        have hFull : 0 < archimedeanHalfInteger k *
            (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2) := mul_pos hA hDen
        apply (div_le_iff₀ hFull).2
        have hOne : 1 ≤ 2 * archimedeanHalfInteger k := by linarith
        have hFreqDen : archimedeanFrequency c x ^ 2 ≤
            archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2 := by
          nlinarith [sq_nonneg (archimedeanHalfInteger k)]
        have hRatio : archimedeanFrequency c x ^ 2 ≤
            (2 * archimedeanHalfInteger k) *
              (archimedeanHalfInteger k ^ 2 +
                archimedeanFrequency c x ^ 2) :=
          hFreqDen.trans (by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hOne (le_of_lt hDen))
        have hExpNonneg :
            0 ≤ Real.exp (-archimedeanHalfInteger k * Real.log c) := by
          positivity
        have hScaled := mul_le_mul_of_nonneg_left hRatio hExpNonneg
        nlinarith
      · exact hUpper
    _ = 2 * archimedeanGeometricMass c := by
      rw [tsum_mul_left,
        tsum_archimedeanExponential_eq_geometricMass c hc]

theorem archimedeanXOneGeometricSeries_nonneg (c x : ℝ) :
    0 ≤ archimedeanXOneGeometricSeries c x := by
  unfold archimedeanXOneGeometricSeries
  apply tsum_nonneg
  intro k
  have hA : 0 ≤ archimedeanHalfInteger k := by
    unfold archimedeanHalfInteger
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact div_nonneg
    (mul_nonneg (le_of_lt (Real.exp_pos _)) hA)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem archimedeanXOneGeometricSeries_le_firstMoment
    (c x : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0) :
    archimedeanXOneGeometricSeries c x ≤
      archimedeanGeometricFirstMoment c /
        archimedeanFrequency c x ^ 2 := by
  have hFrequencySq : 0 < archimedeanFrequency c x ^ 2 :=
    sq_pos_of_ne_zero hFrequency
  have hMoment : Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) *
        archimedeanHalfInteger k) :=
    (summable_archimedeanExponentialMoment_terms c hc).congr
      (fun k => by ring)
  have hUpper : Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) *
        archimedeanHalfInteger k /
          archimedeanFrequency c x ^ 2) := by
    simpa [div_eq_mul_inv] using
      hMoment.mul_right (archimedeanFrequency c x ^ 2)⁻¹
  unfold archimedeanXOneGeometricSeries
  calc
    (∑' k : ℕ,
        Real.exp (-archimedeanHalfInteger k * Real.log c) *
          archimedeanHalfInteger k /
            (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2)) ≤
        ∑' k : ℕ,
          Real.exp (-archimedeanHalfInteger k * Real.log c) *
            archimedeanHalfInteger k /
              archimedeanFrequency c x ^ 2 := by
      apply (summable_archimedeanXOneGeometricSeries_terms c x hc).tsum_le_tsum
      · intro k
        have hA : 0 ≤ archimedeanHalfInteger k := by
          unfold archimedeanHalfInteger
          have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hNumerator : 0 ≤
            Real.exp (-archimedeanHalfInteger k * Real.log c) *
              archimedeanHalfInteger k :=
          mul_nonneg (le_of_lt (Real.exp_pos _)) hA
        have hDen : 0 < archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2 := by
          nlinarith [sq_nonneg (archimedeanHalfInteger k)]
        apply (div_le_div_iff₀ hDen hFrequencySq).2
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (archimedeanHalfInteger k)]) hNumerator
      · exact hUpper
    _ = archimedeanGeometricFirstMoment c /
        archimedeanFrequency c x ^ 2 := by
      rw [tsum_div_const]
      congr 1
      simpa only [mul_comm] using
        tsum_archimedeanExponentialMoment_eq_geometricFirstMoment c hc

theorem abs_archimedeanXTwoGeometricSeries_le_mass
    (c x : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0) :
    |archimedeanXTwoGeometricSeries c x| ≤
      archimedeanGeometricMass c /
        archimedeanFrequency c x ^ 2 := by
  let f : ℕ → ℝ := fun k =>
    Real.exp (-archimedeanHalfInteger k * Real.log c) *
      (archimedeanHalfInteger k ^ 2 -
        archimedeanFrequency c x ^ 2) /
          (archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2) ^ 2
  have hf : Summable f := by
    simpa [f] using summable_archimedeanXTwoGeometricSeries_terms c x hc
  have hFrequencySq : 0 < archimedeanFrequency c x ^ 2 :=
    sq_pos_of_ne_zero hFrequency
  have hUpper : Summable (fun k : ℕ =>
      Real.exp (-archimedeanHalfInteger k * Real.log c) /
        archimedeanFrequency c x ^ 2) := by
    simpa [div_eq_mul_inv] using
      (summable_archimedeanExponential_terms c hc).mul_right
        (archimedeanFrequency c x ^ 2)⁻¹
  have hPointwise : ∀ k : ℕ,
      |f k| ≤
        Real.exp (-archimedeanHalfInteger k * Real.log c) /
          archimedeanFrequency c x ^ 2 := by
    intro k
    have hDen : 0 < archimedeanHalfInteger k ^ 2 +
        archimedeanFrequency c x ^ 2 := by
      have hHalf : 0 < archimedeanHalfInteger k := by
        unfold archimedeanHalfInteger
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      nlinarith [sq_pos_of_pos hHalf,
        sq_nonneg (archimedeanFrequency c x)]
    have hAbsDiff :
        |archimedeanHalfInteger k ^ 2 -
            archimedeanFrequency c x ^ 2| ≤
          archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2 := by
      calc
        |archimedeanHalfInteger k ^ 2 -
            archimedeanFrequency c x ^ 2| ≤
            |archimedeanHalfInteger k ^ 2| +
              |archimedeanFrequency c x ^ 2| := abs_sub _ _
        _ = archimedeanHalfInteger k ^ 2 +
            archimedeanFrequency c x ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _),
            abs_of_nonneg (sq_nonneg _)]
    have hFrequencyDen : archimedeanFrequency c x ^ 2 ≤
        archimedeanHalfInteger k ^ 2 +
          archimedeanFrequency c x ^ 2 := by
      nlinarith [sq_nonneg (archimedeanHalfInteger k)]
    have hProduct :
        |archimedeanHalfInteger k ^ 2 -
            archimedeanFrequency c x ^ 2| *
              archimedeanFrequency c x ^ 2 ≤
          (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2) ^ 2 := by
      calc
        |archimedeanHalfInteger k ^ 2 -
            archimedeanFrequency c x ^ 2| *
              archimedeanFrequency c x ^ 2 ≤
            (archimedeanHalfInteger k ^ 2 +
                archimedeanFrequency c x ^ 2) *
              archimedeanFrequency c x ^ 2 :=
          mul_le_mul_of_nonneg_right hAbsDiff
            (sq_nonneg (archimedeanFrequency c x))
        _ ≤ (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2) *
            (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2) :=
          mul_le_mul_of_nonneg_left hFrequencyDen (le_of_lt hDen)
        _ = (archimedeanHalfInteger k ^ 2 +
              archimedeanFrequency c x ^ 2) ^ 2 := by ring
    dsimp [f]
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (sq_pos_of_pos hDen)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hDen) hFrequencySq).2
    have hScaled := mul_le_mul_of_nonneg_left hProduct
      (le_of_lt (Real.exp_pos
        (-archimedeanHalfInteger k * Real.log c)))
    nlinarith
  unfold archimedeanXTwoGeometricSeries
  change |∑' k : ℕ, f k| ≤
    archimedeanGeometricMass c / archimedeanFrequency c x ^ 2
  calc
    |∑' k : ℕ, f k| = ‖∑' k : ℕ, f k‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖f k‖ := norm_tsum_le_tsum_norm hf.norm
    _ = ∑' k : ℕ, |f k| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑' k : ℕ,
        Real.exp (-archimedeanHalfInteger k * Real.log c) /
          archimedeanFrequency c x ^ 2 :=
      hf.norm.tsum_le_tsum (by simpa only [Real.norm_eq_abs] using hPointwise)
        hUpper
    _ = archimedeanGeometricMass c /
        archimedeanFrequency c x ^ 2 := by
      rw [tsum_div_const,
        tsum_archimedeanExponential_eq_geometricMass c hc]

theorem neg_two_mul_archimedeanCosineCorrection_ge
    (c x digammaRealFloor : ℝ) (hc : 1 < c)
    (hDigamma : digammaRealFloor ≤
      (Complex.digamma (archimedeanArgument c x)).re) :
    digammaRealFloor - (Complex.digamma (1 / 4 : ℂ)).re -
        4 * archimedeanGeometricMass c ≤
      -2 * archimedeanCosineCorrection c x := by
  have hSeries := archimedeanCosineGeometricSeries_le_mass c x hc
  unfold archimedeanCosineCorrection
  linarith

theorem archimedeanCrossCorrection_ge
    (c x trigammaRealFloor : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0)
    (hTrigamma : trigammaRealFloor ≤
      (deriv Complex.digamma (archimedeanArgument c x)).re) :
    (1 / 4) * trigammaRealFloor -
        Real.log c *
          (archimedeanGeometricFirstMoment c /
            archimedeanFrequency c x ^ 2) -
        archimedeanGeometricMass c /
          archimedeanFrequency c x ^ 2 ≤
      archimedeanCrossCorrection c x := by
  have hLog : 0 ≤ Real.log c := (Real.log_pos hc).le
  have hXOne := archimedeanXOneGeometricSeries_le_firstMoment
    c x hc hFrequency
  have hXOneScaled := mul_le_mul_of_nonneg_left hXOne hLog
  have hXTwo := abs_archimedeanXTwoGeometricSeries_le_mass
    c x hc hFrequency
  have hXTwoUpper : archimedeanXTwoGeometricSeries c x ≤
      archimedeanGeometricMass c /
        archimedeanFrequency c x ^ 2 :=
    (le_abs_self _).trans hXTwo
  unfold archimedeanCrossCorrection
  linarith

theorem neg_logarithmicArchimedeanDiagonal_ge_of_digamma
    (c x digammaRealFloor trigammaRealFloor : ℝ) (hc : 1 < c)
    (hFrequency : archimedeanFrequency c x ≠ 0)
    (hDigamma : digammaRealFloor ≤
      (Complex.digamma (archimedeanArgument c x)).re)
    (hTrigamma : trigammaRealFloor ≤
      (deriv Complex.digamma (archimedeanArgument c x)).re) :
    -logarithmicArchimedeanKappa c - logarithmicArchimedeanPoleJ c +
        (digammaRealFloor - (Complex.digamma (1 / 4 : ℂ)).re -
          4 * archimedeanGeometricMass c) +
        (2 / Real.log c) *
          ((1 / 4) * trigammaRealFloor -
            Real.log c *
              (archimedeanGeometricFirstMoment c /
                archimedeanFrequency c x ^ 2) -
            archimedeanGeometricMass c /
              archimedeanFrequency c x ^ 2) ≤
      -logarithmicArchimedeanDiagonal c x := by
  have hCosine := neg_two_mul_archimedeanCosineCorrection_ge
    c x digammaRealFloor hc hDigamma
  have hCross := archimedeanCrossCorrection_ge
    c x trigammaRealFloor hc hFrequency hTrigamma
  have hFactor : 0 ≤ 2 / Real.log c := by
    positivity [Real.log_pos hc]
  have hCrossScaled := mul_le_mul_of_nonneg_left hCross hFactor
  unfold logarithmicArchimedeanDiagonal
  linarith

/-!
### Explicit asymptotic bridge for the Archimedean diagonal

The numerical tail certificate uses the first digamma asymptotic term and the
real trigamma series estimate at `z = 1/4 + i*y`.  The next layer isolates
those two genuinely analytic statements.  A norm bound for
`digamma z - (log z - 1/(2*z))` is converted to the exact real floor used by
the certificate.  The complete diagonal bound is then expressed as
`log x + constant - error`, the error is proved antitone for positive modes,
and the cutoff-13 tail comparison is reduced to the single endpoint `x=960`.
-/
noncomputable def archimedeanAsymptoticHeight (c x : ℝ) : ℝ :=
  Real.pi * x / Real.log c

@[simp] theorem archimedeanArgument_re (c x : ℝ) :
    (archimedeanArgument c x).re = 1 / 4 := by
  simp [archimedeanArgument]

@[simp] theorem archimedeanArgument_im (c x : ℝ) :
    (archimedeanArgument c x).im = archimedeanAsymptoticHeight c x := by
  simp [archimedeanArgument, archimedeanAsymptoticHeight]

lemma archimedeanAsymptoticHeight_pos
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    0 < archimedeanAsymptoticHeight c x := by
  unfold archimedeanAsymptoticHeight
  positivity [Real.log_pos hc, Real.pi_pos]

lemma archimedeanFrequency_eq_two_mul_height (c x : ℝ) :
    archimedeanFrequency c x = 2 * archimedeanAsymptoticHeight c x := by
  unfold archimedeanFrequency archimedeanAsymptoticHeight
  ring

lemma archimedeanFrequency_ne_zero_of_pos
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    archimedeanFrequency c x ≠ 0 := by
  rw [archimedeanFrequency_eq_two_mul_height]
  exact mul_ne_zero (by norm_num)
    (ne_of_gt (archimedeanAsymptoticHeight_pos c x hc hx))

noncomputable def archimedeanDigammaAsymptoticFloor (c x : ℝ) : ℝ :=
  Real.log (archimedeanAsymptoticHeight c x) -
    (1 / 8 + Real.sqrt 2 / 6) / archimedeanAsymptoticHeight c x ^ 2

noncomputable def archimedeanTrigammaSeriesFloor (c x : ℝ) : ℝ :=
  -(1 / archimedeanAsymptoticHeight c x +
    1 / archimedeanAsymptoticHeight c x ^ 2)

/-- The canonical trigamma series term at the literal Archimedean argument.
The only analytic input required below is that these terms have sum
`deriv Complex.digamma (archimedeanArgument c x)`. -/
noncomputable def archimedeanTrigammaSeriesTerm
    (c x : ℝ) (n : ℕ) : ℂ :=
  1 / (archimedeanArgument c x + (n : ℂ)) ^ 2

/-!
The canonical series identity itself follows from one precise asymptotic
statement.  On the open right half-plane, `Gamma` is analytic and nonzero, so
`digamma = deriv Gamma / Gamma` is analytic.  Differentiating the digamma
shift equation and telescoping gives

`sum_{n < N} 1 / (z + n)^2 = digamma'(z) - digamma'(z + N)`.

The summands are absolutely summable there.  Hence the immediate input for the
canonical trigamma series is that `digamma'(z + N)` tends to zero.  The Cauchy
layer below derives this decay from either a vanishing uniform circle envelope
or a single global `C / ‖z‖²` remainder bound.
-/

private lemma gamma_analyticAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hGammaOn : DifferentiableOn ℂ Complex.Gamma U := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro m hwm
    have hneg : w.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hwm
    have hwPos : 0 < w.re := hw
    rw [hneg] at hwPos
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hwPos
  exact hGammaOn.analyticAt (hUOpen.mem_nhds hz)

/-- The digamma function is analytic at every point in the open right
half-plane. -/
theorem digamma_analyticAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hGamma := gamma_analyticAt_of_re_pos z hz
  rw [Complex.digamma_def]
  simpa only [logDeriv] using
    hGamma.deriv.div hGamma (Complex.Gamma_ne_zero_of_re_pos hz)

/-- The differentiability consequence of `digamma_analyticAt_of_re_pos`. -/
theorem digamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z :=
  (digamma_analyticAt_of_re_pos z hz).differentiableAt

/-- The derivative form of the digamma shift equation on the right
half-plane. -/
theorem deriv_digamma_add_one (z : ℂ) (hz : 0 < z.re) :
    deriv Complex.digamma (z + 1) =
      deriv Complex.digamma z - 1 / z ^ 2 := by
  have hEq :
      (fun w : ℂ => Complex.digamma (w + 1)) =ᶠ[𝓝 z]
        (fun w : ℂ => Complex.digamma w + w⁻¹) := by
    filter_upwards [Complex.continuous_re.isOpen_preimage
        (Set.Ioi (0 : ℝ)) isOpen_Ioi |>.mem_nhds hz] with w hw
    apply Complex.digamma_apply_add_one
    intro m hwm
    change 0 < w.re at hw
    have hneg : w.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hwm
    rw [hneg] at hw
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hw
  have hDeriv := hEq.deriv_eq
  rw [deriv_comp_add_const] at hDeriv
  rw [deriv_fun_add (digamma_differentiableAt_of_re_pos z hz)
      (differentiableAt_inv (Complex.ne_zero_of_re_pos hz)), deriv_inv] at hDeriv
  rw [hDeriv]
  ring

/-- Finite telescoping of the differentiated digamma shift equation. -/
theorem sum_range_one_div_add_sq_eq_deriv_digamma_sub
    (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (z + (n : ℂ)) ^ 2) =
      deriv Complex.digamma z - deriv Complex.digamma (z + (N : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hzN : 0 < (z + (N : ℂ)).re := by
        simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg N)
      have hShift := deriv_digamma_add_one (z + (N : ℂ)) hzN
      rw [show z + (N : ℂ) + 1 = z + ((N + 1 : ℕ) : ℂ) by
        push_cast
        ring] at hShift
      rw [hShift]
      ring

/-- The reciprocal-square series is absolutely summable whenever its complex
shift lies in the right half-plane. -/
theorem summable_one_div_complex_add_sq (z : ℂ) (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + (n : ℂ)) ^ 2) := by
  have hMajor : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + z.re| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow z.re 2).2 (by norm_num)
  refine hMajor.of_norm_bounded ?_
  intro n
  have hRePos : 0 < (n : ℝ) + z.re :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hz
  have hReNorm : (n : ℝ) + z.re ≤ ‖z + (n : ℂ)‖ := by
    simpa [add_comm] using Complex.re_le_norm (z + (n : ℂ))
  have hSq : ((n : ℝ) + z.re) ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (z + (n : ℂ))]
  rw [norm_div, norm_one, norm_pow, Real.rpow_two, abs_of_pos hRePos]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hRePos) hSq

/-- The canonical reciprocal-square identity, reduced exactly to decay of the
shifted digamma derivative. -/
theorem hasSum_one_div_complex_add_sq_of_tendsto_deriv_digamma
    (z : ℂ) (hz : 0 < z.re)
    (hTail : Tendsto (fun N : ℕ =>
      deriv Complex.digamma (z + (N : ℂ))) atTop (𝓝 0)) :
    HasSum (fun n : ℕ => 1 / (z + (n : ℂ)) ^ 2)
      (deriv Complex.digamma z) := by
  refine (Summable.hasSum_iff_tendsto_nat
    (summable_one_div_complex_add_sq z hz)).2 ?_
  have hLimit : Tendsto (fun N : ℕ =>
      deriv Complex.digamma z - deriv Complex.digamma (z + (N : ℂ)))
      atTop (𝓝 (deriv Complex.digamma z - 0)) :=
    tendsto_const_nhds.sub hTail
  have hPartial :
      (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (z + (n : ℂ)) ^ 2) =
        (fun N : ℕ => deriv Complex.digamma z -
          deriv Complex.digamma (z + (N : ℂ))) := by
    funext N
    exact sum_range_one_div_add_sq_eq_deriv_digamma_sub z hz N
  rw [hPartial]
  simpa only [sub_zero] using hLimit

/-- The literal Archimedean trigamma series follows from decay of the digamma
derivative along its positive-integer translates. -/
theorem archimedeanTrigammaSeries_hasSum_of_tendsto_deriv_digamma
    (c x : ℝ)
    (hTail : Tendsto (fun N : ℕ =>
      deriv Complex.digamma
        (archimedeanArgument c x + (N : ℂ))) atTop (𝓝 0)) :
    HasSum (archimedeanTrigammaSeriesTerm c x)
      (deriv Complex.digamma (archimedeanArgument c x)) := by
  change HasSum (fun n : ℕ =>
    1 / (archimedeanArgument c x + (n : ℂ)) ^ 2) _
  exact hasSum_one_div_complex_add_sq_of_tendsto_deriv_digamma
    (archimedeanArgument c x) (by simp) hTail

private lemma closedBall_natTranslate_subset_re_pos
    (z : ℂ) (r : ℝ) (hr : r < z.re) (N : ℕ) :
    closedBall (z + (N : ℂ)) r ⊆ {w : ℂ | 0 < w.re} := by
  intro w hw
  have hdist : dist w (z + (N : ℂ)) ≤ r := mem_closedBall.mp hw
  have hnorm : ‖w - (z + (N : ℂ))‖ ≤ r := by
    simpa [dist_eq_norm] using hdist
  have hreNorm : |w.re - (z + (N : ℂ)).re| ≤
      ‖w - (z + (N : ℂ))‖ := by
    simpa using Complex.abs_re_le_norm (w - (z + (N : ℂ)))
  have hre : |w.re - (z + (N : ℂ)).re| ≤ r := hreNorm.trans hnorm
  have hlow := (abs_le.mp hre).1
  change 0 < w.re
  simp only [Complex.add_re, Complex.natCast_re] at hlow
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

private lemma digamma_asymptotic_model_differentiableAt
    (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun u : ℂ => Complex.log u - 1 / (2 * u)) w := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hLog : DifferentiableAt ℂ Complex.log w :=
    Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hDen : DifferentiableAt ℂ (fun u : ℂ => 2 * u) w := by
    fun_prop
  have hRecip : DifferentiableAt ℂ (fun u : ℂ => 1 / (2 * u)) w := by
    exact (differentiableAt_const (c := (1 : ℂ))).div hDen
      (mul_ne_zero (by norm_num) hw0)
  exact hLog.sub hRecip

private lemma digamma_asymptotic_remainder_differentiableOn_re_pos :
    DifferentiableOn ℂ
      (fun w : ℂ => Complex.digamma w -
        (Complex.log w - 1 / (2 * w)))
      {w : ℂ | 0 < w.re} := by
  intro w hw
  exact ((digamma_differentiableAt_of_re_pos w hw).sub
    (digamma_asymptotic_model_differentiableAt w hw)).differentiableWithinAt

private lemma norm_deriv_digamma_asymptotic_remainder_natTranslate_le
    (z : ℂ) (r : ℝ) (hr0 : 0 < r) (hrz : r < z.re)
    (ε : ℕ → ℝ)
    (hSphere : ∀ N : ℕ, ∀ w ∈ sphere (z + (N : ℂ)) r,
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤ ε N)
    (N : ℕ) :
    ‖deriv (fun w : ℂ => Complex.digamma w -
      (Complex.log w - 1 / (2 * w))) (z + (N : ℂ))‖ ≤ ε N / r := by
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
    (digamma_asymptotic_remainder_differentiableOn_re_pos.diffContOnCl_ball
      (closedBall_natTranslate_subset_re_pos z r hrz N))
    (hSphere N)

private lemma tendsto_deriv_digamma_asymptotic_remainder_natTranslate
    (z : ℂ) (r : ℝ) (hr0 : 0 < r) (hrz : r < z.re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hSphere : ∀ N : ℕ, ∀ w ∈ sphere (z + (N : ℂ)) r,
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤ ε N) :
    Tendsto (fun N : ℕ =>
      deriv (fun w : ℂ => Complex.digamma w -
        (Complex.log w - 1 / (2 * w))) (z + (N : ℂ)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun N =>
    norm_deriv_digamma_asymptotic_remainder_natTranslate_le
      z r hr0 hrz ε hSphere N) ?_
  simpa using hε.div_const r

private lemma deriv_digamma_asymptotic_model (w : ℂ) (hw : 0 < w.re) :
    deriv (fun u : ℂ => Complex.log u - 1 / (2 * u)) w =
      w⁻¹ + 1 / (2 * w ^ 2) := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hLog : HasDerivAt Complex.log w⁻¹ w :=
    Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hRecipRaw : HasDerivAt
      (fun u : ℂ => (1 / 2 : ℂ) * u⁻¹)
      ((1 / 2 : ℂ) * (-(w ^ 2)⁻¹)) w :=
    (hasDerivAt_inv hw0).const_mul (1 / 2 : ℂ)
  have hRecip : HasDerivAt
      (fun u : ℂ => 1 / (2 * u))
      (-(1 / (2 * w ^ 2))) w := by
    convert hRecipRaw using 1 <;>
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  change deriv (Complex.log - fun u : ℂ => 1 / (2 * u)) w = _
  simpa only [sub_neg_eq_add] using (hLog.sub hRecip).deriv

private lemma tendsto_inv_natTranslate (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => (z + (N : ℂ))⁻¹) atTop (𝓝 0) := by
  refine squeeze_zero_norm
    (a := fun N : ℕ => 1 / ((N : ℝ) + z.re)) (fun N => ?_) ?_
  · have hRePos : 0 < (N : ℝ) + z.re :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) hz
    have hReNorm : (N : ℝ) + z.re ≤ ‖z + (N : ℂ)‖ := by
      simpa [add_comm] using Complex.re_le_norm (z + (N : ℂ))
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hRePos hReNorm
  · have hReal :=
      (tendsto_mul_add_inv_atTop_nhds_zero 1 z.re (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, one_mul, one_div] using hReal

private lemma tendsto_deriv_digamma_asymptotic_model_natTranslate
    (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ =>
      deriv (fun w : ℂ => Complex.log w - 1 / (2 * w))
        (z + (N : ℂ))) atTop (𝓝 0) := by
  have hInv := tendsto_inv_natTranslate z hz
  have hSq : Tendsto (fun N : ℕ =>
      (z + (N : ℂ))⁻¹ ^ 2) atTop (𝓝 (0 ^ 2)) := hInv.pow 2
  have hHalfSq : Tendsto (fun N : ℕ =>
      1 / (2 * (z + (N : ℂ)) ^ 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℂ))
        atTop (𝓝 (1 / 2 : ℂ))).mul hSq)
  have hModel : Tendsto (fun N : ℕ =>
      (z + (N : ℂ))⁻¹ + 1 / (2 * (z + (N : ℂ)) ^ 2))
      atTop (𝓝 0) := by
    simpa using hInv.add hHalfSq
  apply hModel.congr'
  filter_upwards with N
  rw [deriv_digamma_asymptotic_model]
  simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg N)

/-- A vanishing uniform digamma-remainder envelope on fixed circles implies
decay of the shifted digamma derivative by Cauchy's first-derivative estimate. -/
theorem tendsto_deriv_digamma_natTranslate_of_uniform_asymptotic
    (z : ℂ) (r : ℝ) (hr0 : 0 < r) (hrz : r < z.re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hSphere : ∀ N : ℕ, ∀ w ∈ sphere (z + (N : ℂ)) r,
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤ ε N) :
    Tendsto (fun N : ℕ =>
      deriv Complex.digamma (z + (N : ℂ))) atTop (𝓝 0) := by
  have hz : 0 < z.re := hr0.trans hrz
  have hRemainder :=
    tendsto_deriv_digamma_asymptotic_remainder_natTranslate
      z r hr0 hrz ε hε hSphere
  have hModel :=
    tendsto_deriv_digamma_asymptotic_model_natTranslate z hz
  have hSum := hRemainder.add hModel
  have hSum0 : Tendsto (fun N : ℕ =>
      deriv (fun w : ℂ => Complex.digamma w -
        (Complex.log w - 1 / (2 * w))) (z + (N : ℂ)) +
      deriv (fun w : ℂ => Complex.log w - 1 / (2 * w))
        (z + (N : ℂ))) atTop (𝓝 0) := by
    simpa using hSum
  apply hSum0.congr'
  filter_upwards with N
  have hw : 0 < (z + (N : ℂ)).re := by
    simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg N)
  have hDigamma := digamma_differentiableAt_of_re_pos
    (z + (N : ℂ)) hw
  have hAsymptotic := digamma_asymptotic_model_differentiableAt
    (z + (N : ℂ)) hw
  rw [deriv_fun_sub hDigamma hAsymptotic]
  ring

/-- A global quadratic DLMF-form remainder bound on the right half-plane
supplies the circle envelopes required by the Cauchy bridge. -/
theorem tendsto_deriv_digamma_natTranslate_of_quadratic_remainder_bound
    (z : ℂ) (hz : 0 < z.re) (C : ℝ) (hC : 0 ≤ C)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        C / ‖w‖ ^ 2) :
    Tendsto (fun N : ℕ =>
      deriv Complex.digamma (z + (N : ℂ))) atTop (𝓝 0) := by
  let r : ℝ := z.re / 2
  let ε : ℕ → ℝ := fun N =>
    C / (((N : ℝ) + z.re - r) ^ 2)
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrz : r < z.re := by dsimp [r]; linarith
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hInv : Tendsto (fun N : ℕ =>
        (((N : ℝ) + (z.re - r))⁻¹)) atTop (𝓝 0) := by
      have hReal :=
        (tendsto_mul_add_inv_atTop_nhds_zero 1 (z.re - r) (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [Function.comp_def, one_mul] using hReal
    have hSq := hInv.pow 2
    have hScaled :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hSq
    simpa [ε, div_eq_mul_inv, inv_pow, sub_eq_add_neg, add_assoc] using hScaled
  refine tendsto_deriv_digamma_natTranslate_of_uniform_asymptotic
    z r hr0 hrz ε hε ?_
  intro N w hwSphere
  have hwClosed : w ∈ closedBall (z + (N : ℂ)) r :=
    sphere_subset_closedBall hwSphere
  have hwPos : 0 < w.re :=
    closedBall_natTranslate_subset_re_pos z r hrz N hwClosed
  have hRaw := hRemainder w hwPos
  have hdist : dist w (z + (N : ℂ)) ≤ r := mem_closedBall.mp hwClosed
  have hnorm : ‖w - (z + (N : ℂ))‖ ≤ r := by
    simpa [dist_eq_norm] using hdist
  have hreNorm : |w.re - (z + (N : ℂ)).re| ≤
      ‖w - (z + (N : ℂ))‖ := by
    simpa using Complex.abs_re_le_norm (w - (z + (N : ℂ)))
  have hre : |w.re - (z + (N : ℂ)).re| ≤ r := hreNorm.trans hnorm
  have hlow := (abs_le.mp hre).1
  have hBasePos : 0 < (N : ℝ) + z.re - r := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hBaseRe : (N : ℝ) + z.re - r ≤ w.re := by
    simp only [Complex.add_re, Complex.natCast_re] at hlow
    linarith
  have hBaseNorm : (N : ℝ) + z.re - r ≤ ‖w‖ :=
    hBaseRe.trans (Complex.re_le_norm w)
  have hSq : ((N : ℝ) + z.re - r) ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg w]
  exact hRaw.trans (div_le_div_of_nonneg_left hC
    (sq_pos_of_pos hBasePos) hSq)

/-- The reciprocal-square `HasSum` identity under a vanishing fixed-circle
remainder envelope. -/
theorem hasSum_one_div_complex_add_sq_of_uniform_asymptotic
    (z : ℂ) (r : ℝ) (hr0 : 0 < r) (hrz : r < z.re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hSphere : ∀ N : ℕ, ∀ w ∈ sphere (z + (N : ℂ)) r,
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤ ε N) :
    HasSum (fun n : ℕ => 1 / (z + (n : ℂ)) ^ 2)
      (deriv Complex.digamma z) := by
  exact hasSum_one_div_complex_add_sq_of_tendsto_deriv_digamma
    z (hr0.trans hrz)
      (tendsto_deriv_digamma_natTranslate_of_uniform_asymptotic
        z r hr0 hrz ε hε hSphere)

/-- The reciprocal-square `HasSum` identity under one global quadratic
digamma-remainder bound. -/
theorem hasSum_one_div_complex_add_sq_of_quadratic_remainder_bound
    (z : ℂ) (hz : 0 < z.re) (C : ℝ) (hC : 0 ≤ C)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        C / ‖w‖ ^ 2) :
    HasSum (fun n : ℕ => 1 / (z + (n : ℂ)) ^ 2)
      (deriv Complex.digamma z) := by
  exact hasSum_one_div_complex_add_sq_of_tendsto_deriv_digamma z hz
    (tendsto_deriv_digamma_natTranslate_of_quadratic_remainder_bound
      z hz C hC hRemainder)

/-- The literal Archimedean trigamma series from radius-`1/8` circle
envelopes around all positive-integer translates. -/
theorem archimedeanTrigammaSeries_hasSum_of_uniform_asymptotic
    (c x : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hSphere : ∀ N : ℕ,
      ∀ w ∈ sphere (archimedeanArgument c x + (N : ℂ)) (1 / 8 : ℝ),
        ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤ ε N) :
    HasSum (archimedeanTrigammaSeriesTerm c x)
      (deriv Complex.digamma (archimedeanArgument c x)) := by
  change HasSum (fun n : ℕ =>
    1 / (archimedeanArgument c x + (n : ℂ)) ^ 2) _
  exact hasSum_one_div_complex_add_sq_of_uniform_asymptotic
    (archimedeanArgument c x) (1 / 8) (by norm_num) (by
      norm_num [archimedeanArgument]) ε hε hSphere

/-- The literal Archimedean trigamma series from one global quadratic
digamma-remainder estimate. -/
theorem archimedeanTrigammaSeries_hasSum_of_quadratic_remainder_bound
    (c x C : ℝ) (hC : 0 ≤ C)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        C / ‖w‖ ^ 2) :
    HasSum (archimedeanTrigammaSeriesTerm c x)
      (deriv Complex.digamma (archimedeanArgument c x)) := by
  change HasSum (fun n : ℕ =>
    1 / (archimedeanArgument c x + (n : ℂ)) ^ 2) _
  exact hasSum_one_div_complex_add_sq_of_quadratic_remainder_bound
    (archimedeanArgument c x) (by simp) C hC hRemainder

/-- A global norm-squared remainder bound specializes to the exact
Archimedean height denominator used by the diagonal certificate. -/
theorem archimedean_digamma_remainder_le_of_quadratic_remainder_bound
    (c x C : ℝ) (hc : 1 < c) (hx : 0 < x) (hC : 0 ≤ C)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        C / ‖w‖ ^ 2) :
    ‖Complex.digamma (archimedeanArgument c x) -
        (Complex.log (archimedeanArgument c x) -
          1 / (2 * archimedeanArgument c x))‖ ≤
      C / archimedeanAsymptoticHeight c x ^ 2 := by
  have hy : 0 < archimedeanAsymptoticHeight c x :=
    archimedeanAsymptoticHeight_pos c x hc hx
  have hRaw := hRemainder (archimedeanArgument c x) (by simp)
  have hImNorm : archimedeanAsymptoticHeight c x ≤
      ‖archimedeanArgument c x‖ := by
    have h := Complex.abs_im_le_norm (archimedeanArgument c x)
    simpa [abs_of_pos hy] using h
  have hSq : archimedeanAsymptoticHeight c x ^ 2 ≤
      ‖archimedeanArgument c x‖ ^ 2 := by
    nlinarith [norm_nonneg (archimedeanArgument c x)]
  exact hRaw.trans
    (div_le_div_of_nonneg_left hC (sq_pos_of_pos hy) hSq)

@[simp] theorem archimedeanTrigammaSeriesTerm_re
    (c x : ℝ) (n : ℕ) :
    (archimedeanTrigammaSeriesTerm c x n).re =
      (((n : ℝ) + 1 / 4) ^ 2 - archimedeanAsymptoticHeight c x ^ 2) /
        (((n : ℝ) + 1 / 4) ^ 2 + archimedeanAsymptoticHeight c x ^ 2) ^ 2 := by
  unfold archimedeanTrigammaSeriesTerm
  rw [Complex.div_re]
  simp [archimedeanArgument, archimedeanAsymptoticHeight,
    pow_two, Complex.normSq_apply]
  ring

private noncomputable def archimedeanTrigammaSeriesLower
    (c x : ℝ) (n : ℕ) : ℝ :=
  if n < ⌈archimedeanAsymptoticHeight c x⌉₊ then
    -(1 / archimedeanAsymptoticHeight c x ^ 2)
  else 0

private lemma archimedeanTrigammaSeriesLower_le_re
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) (n : ℕ) :
    archimedeanTrigammaSeriesLower c x n ≤
      (archimedeanTrigammaSeriesTerm c x n).re := by
  let y := archimedeanAsymptoticHeight c x
  have hy : 0 < y := archimedeanAsymptoticHeight_pos c x hc hx
  rw [archimedeanTrigammaSeriesTerm_re]
  change (if n < ⌈y⌉₊ then -(1 / y ^ 2) else 0) ≤
    (((n : ℝ) + 1 / 4) ^ 2 - y ^ 2) /
      (((n : ℝ) + 1 / 4) ^ 2 + y ^ 2) ^ 2
  by_cases hn : n < ⌈y⌉₊
  · rw [if_pos hn]
    have hySq : 0 < y ^ 2 := sq_pos_of_pos hy
    have hBase : 0 < ((n : ℝ) + 1 / 4) ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) + 1 / 4)]
    have hDen : 0 < (((n : ℝ) + 1 / 4) ^ 2 + y ^ 2) ^ 2 :=
      sq_pos_of_pos hBase
    rw [show -(1 / y ^ 2) = (-1 : ℝ) / y ^ 2 by ring]
    rw [div_le_div_iff₀ hySq hDen]
    nlinarith [sq_nonneg (((n : ℝ) + 1 / 4) ^ 2)]
  · rw [if_neg hn]
    have hCeilNat : ⌈y⌉₊ ≤ n := Nat.le_of_not_gt hn
    have hCeilReal : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    have hyn : y ≤ (n : ℝ) := hCeilReal.trans (by exact_mod_cast hCeilNat)
    have hya : y ≤ (n : ℝ) + 1 / 4 := by linarith
    have hSq : y ^ 2 ≤ ((n : ℝ) + 1 / 4) ^ 2 :=
      (sq_le_sq₀ hy.le (by positivity)).2 hya
    exact div_nonneg (sub_nonneg.mpr hSq) (sq_nonneg _)

private lemma summable_archimedeanTrigammaSeriesLower
    (c x : ℝ) : Summable (archimedeanTrigammaSeriesLower c x) := by
  apply summable_of_hasFiniteSupport
  refine (Finset.range ⌈archimedeanAsymptoticHeight c x⌉₊).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support] at *
  by_contra hmem
  simp only [Finset.mem_coe, Finset.mem_range] at hmem
  simp [archimedeanTrigammaSeriesLower,
    not_lt.mpr (Nat.le_of_not_gt hmem)] at hn

private lemma tsum_archimedeanTrigammaSeriesLower
    (c x : ℝ) :
    ∑' n : ℕ, archimedeanTrigammaSeriesLower c x n =
      -(⌈archimedeanAsymptoticHeight c x⌉₊ : ℝ) /
        archimedeanAsymptoticHeight c x ^ 2 := by
  rw [tsum_eq_sum (s := Finset.range ⌈archimedeanAsymptoticHeight c x⌉₊)]
  · calc
      ∑ n ∈ Finset.range ⌈archimedeanAsymptoticHeight c x⌉₊,
          archimedeanTrigammaSeriesLower c x n =
          ∑ _n ∈ Finset.range ⌈archimedeanAsymptoticHeight c x⌉₊,
            -(1 / archimedeanAsymptoticHeight c x ^ 2) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [archimedeanTrigammaSeriesLower, Finset.mem_range.mp hn]
      _ = -(⌈archimedeanAsymptoticHeight c x⌉₊ : ℝ) /
          archimedeanAsymptoticHeight c x ^ 2 := by
            simp
            ring
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [archimedeanTrigammaSeriesLower, hn]

/-- The elementary part of the trigamma tail estimate.  Terms before
`ceil y` are bounded below by `-1 / y^2`; every later term is nonnegative.
Consequently the canonical series identity implies the exact floor used by
the Archimedean diagonal certificate. -/
theorem archimedeanTrigammaSeriesFloor_le_of_hasSum
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x)
    (hSeries : HasSum (archimedeanTrigammaSeriesTerm c x)
      (deriv Complex.digamma (archimedeanArgument c x))) :
    archimedeanTrigammaSeriesFloor c x ≤
      (deriv Complex.digamma (archimedeanArgument c x)).re := by
  let y := archimedeanAsymptoticHeight c x
  have hy : 0 < y := archimedeanAsymptoticHeight_pos c x hc hx
  have hRe := Complex.hasSum_re hSeries
  have hCompare :
      (∑' n : ℕ, archimedeanTrigammaSeriesLower c x n) ≤
        ∑' n : ℕ, (archimedeanTrigammaSeriesTerm c x n).re :=
    (summable_archimedeanTrigammaSeriesLower c x).tsum_le_tsum
      (archimedeanTrigammaSeriesLower_le_re c x hc hx) hRe.summable
  have hCeil : (⌈y⌉₊ : ℝ) ≤ y + 1 :=
    (Nat.ceil_lt_add_one hy.le).le
  have hySq : 0 < y ^ 2 := sq_pos_of_pos hy
  have hScaled : (⌈y⌉₊ : ℝ) / y ^ 2 ≤ (y + 1) / y ^ 2 :=
    (div_le_div_iff_of_pos_right hySq).2 hCeil
  have hAlgebra : (y + 1) / y ^ 2 = 1 / y + 1 / y ^ 2 := by
    field_simp [ne_of_gt hy]
  rw [hRe.tsum_eq] at hCompare
  rw [tsum_archimedeanTrigammaSeriesLower] at hCompare
  change -(⌈y⌉₊ : ℝ) / y ^ 2 ≤
    (deriv Complex.digamma (archimedeanArgument c x)).re at hCompare
  unfold archimedeanTrigammaSeriesFloor
  change -(1 / y + 1 / y ^ 2) ≤
    (deriv Complex.digamma (archimedeanArgument c x)).re
  rw [← hAlgebra]
  calc
    -((y + 1) / y ^ 2) ≤ -((⌈y⌉₊ : ℝ) / y ^ 2) := neg_le_neg hScaled
    _ = -(⌈y⌉₊ : ℝ) / y ^ 2 := by ring
    _ ≤ (deriv Complex.digamma (archimedeanArgument c x)).re := hCompare

lemma archimedeanArgument_log_re_ge_log_height
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    Real.log (archimedeanAsymptoticHeight c x) ≤
      (Complex.log (archimedeanArgument c x)).re := by
  rw [Complex.log_re]
  apply Real.log_le_log (archimedeanAsymptoticHeight_pos c x hc hx)
  have hIm := Complex.abs_im_le_norm (archimedeanArgument c x)
  simpa [abs_of_pos (archimedeanAsymptoticHeight_pos c x hc hx)] using hIm

lemma archimedeanArgument_halfInv_re_le
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x) :
    (1 / (2 * archimedeanArgument c x) : ℂ).re ≤
      (1 / 8 : ℝ) / archimedeanAsymptoticHeight c x ^ 2 := by
  have hy : 0 < archimedeanAsymptoticHeight c x :=
    archimedeanAsymptoticHeight_pos c x hc hx
  rw [div_eq_mul_inv, one_mul, Complex.inv_re]
  simp [Complex.normSq_apply, archimedeanArgument]
  apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hy)).2
  unfold archimedeanAsymptoticHeight
  nlinarith [sq_nonneg (Real.pi * x / Real.log c)]

lemma digamma_real_ge_asymptoticFloor_of_norm_remainder
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x)
    (hRemainder :
      ‖Complex.digamma (archimedeanArgument c x) -
          (Complex.log (archimedeanArgument c x) -
            1 / (2 * archimedeanArgument c x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight c x ^ 2)) :
    archimedeanDigammaAsymptoticFloor c x ≤
      (Complex.digamma (archimedeanArgument c x)).re := by
  let z := archimedeanArgument c x
  let y := archimedeanAsymptoticHeight c x
  have hy : 0 < y := archimedeanAsymptoticHeight_pos c x hc hx
  have hLog : Real.log y ≤ (Complex.log z).re := by
    simpa [z, y] using archimedeanArgument_log_re_ge_log_height c x hc hx
  have hInv : (1 / (2 * z) : ℂ).re ≤ (1 / 8 : ℝ) / y ^ 2 := by
    simpa [z, y] using archimedeanArgument_halfInv_re_le c x hc hx
  let r : ℂ := Complex.digamma z - (Complex.log z - 1 / (2 * z))
  have hrNorm : ‖r‖ ≤ Real.sqrt 2 / (6 * y ^ 2) := by
    simpa [r, z, y] using hRemainder
  have hrRe : -(Real.sqrt 2 / (6 * y ^ 2)) ≤ r.re := by
    have hneg : -‖r‖ ≤ r.re := by
      have habs := Complex.abs_re_le_norm r
      linarith [neg_le_abs r.re]
    exact (neg_le_neg hrNorm).trans hneg
  have hIdentity :
      (Complex.digamma z).re =
        (Complex.log z).re - (1 / (2 * z) : ℂ).re + r.re := by
    change (Complex.digamma z).re =
      (Complex.log z).re - (1 / (2 * z) : ℂ).re +
        (Complex.digamma z - (Complex.log z - 1 / (2 * z))).re
    simp only [Complex.sub_re]
    ring
  have hError :
      (1 / 8 + Real.sqrt 2 / 6) / y ^ 2 =
        (1 / 8 : ℝ) / y ^ 2 + Real.sqrt 2 / (6 * y ^ 2) := by
    field_simp [ne_of_gt hy]
  have hFinal :
      Real.log y - (1 / 8 + Real.sqrt 2 / 6) / y ^ 2 ≤
        (Complex.digamma z).re := by
    rw [hIdentity, hError]
    linarith
  simpa [archimedeanDigammaAsymptoticFloor, z, y] using hFinal

theorem archimedeanGeometricFirstMoment_nonneg (c : ℝ) (hc : 1 < c) :
    0 ≤ archimedeanGeometricFirstMoment c := by
  rw [← tsum_archimedeanExponentialMoment_eq_geometricFirstMoment c hc]
  apply tsum_nonneg
  intro k
  have hHalf : 0 ≤ archimedeanHalfInteger k := by
    unfold archimedeanHalfInteger
    positivity
  exact mul_nonneg hHalf (le_of_lt (Real.exp_pos _))
noncomputable def archimedeanDiagonalAsymptoticConstant (c : ℝ) : ℝ :=
  Real.log (Real.pi / Real.log c) -
    (Complex.digamma (1 / 4 : ℂ)).re -
    logarithmicArchimedeanKappa c - logarithmicArchimedeanPoleJ c -
    4 * archimedeanGeometricMass c

/-- Eliminating `ψ(1/4)` from the asymptotic constant also cancels the
Euler--Mascheroni terms exactly.  The remaining cutoff endpoint is elementary:
it contains only logarithms, exponentials, arctangent, `π`, and square roots. -/
theorem archimedeanDiagonalAsymptoticConstant_eq_without_euler (c : ℝ) :
    archimedeanDiagonalAsymptoticConstant c =
      Real.log (Real.pi / Real.log c) + 3 * Real.log 2 + Real.pi / 2 -
        Real.log
          (4 * Real.pi *
            (Real.exp (Real.log c) - 1) / (Real.exp (Real.log c) + 1)) -
        logarithmicArchimedeanPoleJ c -
        4 * archimedeanGeometricMass c := by
  unfold archimedeanDiagonalAsymptoticConstant logarithmicArchimedeanKappa
  rw [RiemannCvs.digamma_one_fourth_re]
  ring

/-- Positive cutoffs replace `exp (log c)` by `c` in the elementary
asymptotic constant. -/
theorem archimedeanDiagonalAsymptoticConstant_eq_without_euler_of_pos
    (c : ℝ) (hc : 0 < c) :
    archimedeanDiagonalAsymptoticConstant c =
      Real.log (Real.pi / Real.log c) + 3 * Real.log 2 + Real.pi / 2 -
        Real.log (4 * Real.pi * (c - 1) / (c + 1)) -
        logarithmicArchimedeanPoleJ c -
        4 * archimedeanGeometricMass c := by
  rw [archimedeanDiagonalAsymptoticConstant_eq_without_euler,
    Real.exp_log hc]

noncomputable def archimedeanDiagonalAsymptoticError (c x : ℝ) : ℝ :=
  let y := archimedeanAsymptoticHeight c x
  let w := archimedeanFrequency c x
  (1 / 8 + Real.sqrt 2 / 6) / y ^ 2 +
    (1 / y + 1 / y ^ 2) / (2 * Real.log c) +
    2 * archimedeanGeometricFirstMoment c / w ^ 2 +
    (2 / Real.log c) * archimedeanGeometricMass c / w ^ 2

/-!
### Exact elementary normal form of the cutoff-13 endpoint

At the chosen cutoff, every exponential geometric correction is algebraic.
The following identities replace the mass and first moment by exact multiples
of `sqrt 13`, eliminate the remaining pole constant, and expose the unique
mode-960 comparison as an elementary real inequality.  No floating-point or
interval result is promoted in this reduction.
-/

lemma exp_log_thirteen_div_two :
    Real.exp (Real.log 13 / 2) = Real.sqrt 13 := by
  rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
  exact Real.exp_log (Real.sqrt_pos.2 (by norm_num))

lemma exp_neg_log_thirteen_div_two :
    Real.exp (-Real.log 13 / 2) = (Real.sqrt 13)⁻¹ := by
  rw [show -Real.log 13 / 2 = -(Real.log 13 / 2) by ring,
    ← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 13), Real.exp_neg,
    Real.exp_log (Real.sqrt_pos.2 (by norm_num))]

lemma exp_neg_two_mul_log_thirteen :
    Real.exp (-2 * Real.log 13) = (1 / 169 : ℝ) := by
  rw [show -2 * Real.log 13 = -(2 * Real.log 13) by ring,
    Real.exp_neg,
    show 2 * Real.log 13 = Real.log 13 + Real.log 13 by ring,
    Real.exp_add,
    Real.exp_log (by norm_num : (0 : ℝ) < 13)]
  norm_num

lemma c13_archimedeanGeometricMass_eq :
    archimedeanGeometricMass 13 = 13 * Real.sqrt 13 / 168 := by
  unfold archimedeanGeometricMass
  rw [exp_neg_log_thirteen_div_two, exp_neg_two_mul_log_thirteen]
  have hs : Real.sqrt (13 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]

lemma c13_archimedeanGeometricFirstMoment_eq :
    archimedeanGeometricFirstMoment 13 =
      559 * Real.sqrt 13 / 14112 := by
  unfold archimedeanGeometricFirstMoment
  rw [exp_neg_log_thirteen_div_two, exp_neg_two_mul_log_thirteen]
  have hs : Real.sqrt (13 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]

theorem c13_archimedeanDiagonalAsymptoticConstant_eq :
    archimedeanDiagonalAsymptoticConstant 13 =
      Real.pi - 2 * Real.arctan (Real.sqrt 13) +
        2 * Real.log (Real.sqrt 13 + 1) -
        Real.log (12 * Real.log 13) -
        13 * Real.sqrt 13 / 42 := by
  rw [archimedeanDiagonalAsymptoticConstant_eq_without_euler_of_pos
    13 (by norm_num), c13_archimedeanGeometricMass_eq]
  unfold logarithmicArchimedeanPoleJ
  dsimp only
  rw [exp_log_thirteen_div_two,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
  norm_num
  have hLog13 : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have hLogPiInv :
      Real.log (Real.pi * (Real.log 13)⁻¹) =
        Real.log Real.pi - Real.log (Real.log 13) := by
    rw [Real.log_mul Real.pi_ne_zero (inv_ne_zero (ne_of_gt hLog13)),
      Real.log_inv]
    ring
  have hLogPiRatio :
      Real.log (Real.pi * (24 / 7 : ℝ)) =
        Real.log Real.pi + Real.log (24 / 7 : ℝ) := by
    rw [Real.log_mul Real.pi_ne_zero (by norm_num)]
  have hLogTarget :
      Real.log (Real.log 13 * 12) =
        Real.log (Real.log 13) + Real.log 12 := by
    rw [Real.log_mul (ne_of_gt hLog13) (by norm_num)]
  have hLogTwo : Real.log 2 * 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  have hLogFortyEight :
      Real.log (24 / 7 : ℝ) + Real.log 14 = Real.log 48 := by
    rw [← Real.log_mul (by norm_num : (24 / 7 : ℝ) ≠ 0)
      (by norm_num : (14 : ℝ) ≠ 0)]
    norm_num
  have hLogQuotient : Real.log 4 - Real.log 48 = -Real.log 12 := by
    rw [← Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (48 : ℝ) ≠ 0)]
    rw [show (4 / 48 : ℝ) = (12 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hNumeric :
      Real.log 2 * 2 - Real.log (24 / 7 : ℝ) - Real.log 14 =
        -Real.log 12 := by
    linarith [hLogTwo, hLogFortyEight, hLogQuotient]
  ring_nf
  rw [hLogPiInv, hLogPiRatio, hLogTarget]
  linarith

/-- Replacing `atan (sqrt 13)` by the reciprocal arctangent and combining the
two logarithms removes `π` from the cutoff-13 asymptotic constant itself. -/
theorem c13_archimedeanDiagonalAsymptoticConstant_eq_reciprocal :
    archimedeanDiagonalAsymptoticConstant 13 =
      2 * Real.arctan (Real.sqrt 13)⁻¹ -
        Real.log (6 * Real.log 13 / (7 + Real.sqrt 13)) -
        13 * Real.sqrt 13 / 42 := by
  rw [c13_archimedeanDiagonalAsymptoticConstant_eq]
  have hs : 0 < Real.sqrt (13 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hL : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have hAtan := Real.arctan_inv_of_pos hs
  have hsq : Real.sqrt (13 : ℝ) ^ 2 = 13 :=
    Real.sq_sqrt (by norm_num)
  have hLogSquare :
      2 * Real.log (Real.sqrt 13 + 1) =
        Real.log (2 * (7 + Real.sqrt 13)) := by
    rw [show 2 * Real.log (Real.sqrt 13 + 1) =
        (2 : ℕ) * Real.log (Real.sqrt 13 + 1) by norm_num,
      ← Real.log_pow]
    congr 1
    nlinarith
  have hLogNumerator :
      Real.log (2 * (7 + Real.sqrt 13)) =
        Real.log 2 + Real.log (7 + Real.sqrt 13) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity))]
  have hLogDenominator :
      Real.log (12 * Real.log 13) =
        Real.log 2 + Real.log (6 * Real.log 13) := by
    rw [show (12 : ℝ) * Real.log 13 = 2 * (6 * Real.log 13) by ring,
      Real.log_mul (by norm_num) (ne_of_gt (mul_pos (by norm_num) hL))]
  have hLogRatio :
      Real.log (6 * Real.log 13 / (7 + Real.sqrt 13)) =
        Real.log (6 * Real.log 13) - Real.log (7 + Real.sqrt 13) := by
    rw [Real.log_div (ne_of_gt (mul_pos (by norm_num) hL))
      (ne_of_gt (by positivity))]
  rw [hLogSquare, hLogNumerator, hLogDenominator, hLogRatio]
  linarith

theorem c13_archimedeanDiagonalAsymptoticError_eq :
    archimedeanDiagonalAsymptoticError 13 960 =
      (1 / 8 + Real.sqrt 2 / 6) /
          (960 * Real.pi / Real.log 13) ^ 2 +
        (1 / (960 * Real.pi / Real.log 13) +
            1 / (960 * Real.pi / Real.log 13) ^ 2) /
          (2 * Real.log 13) +
        (2 * (559 * Real.sqrt 13 / 14112)) /
          (1920 * Real.pi / Real.log 13) ^ 2 +
        (2 / Real.log 13) * (13 * Real.sqrt 13 / 168) /
          (1920 * Real.pi / Real.log 13) ^ 2 := by
  unfold archimedeanDiagonalAsymptoticError
    archimedeanAsymptoticHeight archimedeanFrequency
  dsimp only
  rw [c13_archimedeanGeometricMass_eq,
    c13_archimedeanGeometricFirstMoment_eq]
  ring

/-- Elementary normal form of the unique cutoff-13 endpoint still required by
the Archimedean diagonal route. -/
noncomputable def c13ArchimedeanEndpointElementary : ℝ :=
  Real.pi - 2 * Real.arctan (Real.sqrt 13) +
      2 * Real.log (Real.sqrt 13 + 1) -
      Real.log (12 * Real.log 13) -
      13 * Real.sqrt 13 / 42 -
    ((1 / 8 + Real.sqrt 2 / 6) /
        (960 * Real.pi / Real.log 13) ^ 2 +
      (1 / (960 * Real.pi / Real.log 13) +
          1 / (960 * Real.pi / Real.log 13) ^ 2) /
        (2 * Real.log 13) +
      (2 * (559 * Real.sqrt 13 / 14112)) /
        (1920 * Real.pi / Real.log 13) ^ 2 +
      (2 / Real.log 13) * (13 * Real.sqrt 13 / 168) /
        (1920 * Real.pi / Real.log 13) ^ 2)

theorem c13_archimedeanEndpoint_eq_elementary :
    archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960 =
      c13ArchimedeanEndpointElementary := by
  rw [c13_archimedeanDiagonalAsymptoticConstant_eq,
    c13_archimedeanDiagonalAsymptoticError_eq]
  rfl

theorem c13_archimedeanEndpoint_bound_iff_elementary :
    (-(19 / 20 : ℝ) ≤
        archimedeanDiagonalAsymptoticConstant 13 -
          archimedeanDiagonalAsymptoticError 13 960) ↔
      (-(19 / 20 : ℝ) ≤ c13ArchimedeanEndpointElementary) := by
  rw [c13_archimedeanEndpoint_eq_elementary]

theorem archimedeanDiagonalAsymptoticError_antitone
    (c x₀ x : ℝ) (hc : 1 < c) (hx₀ : 0 < x₀) (hxx : x₀ ≤ x) :
    archimedeanDiagonalAsymptoticError c x ≤
      archimedeanDiagonalAsymptoticError c x₀ := by
  have hx : 0 < x := hx₀.trans_le hxx
  let y₀ := archimedeanAsymptoticHeight c x₀
  let y := archimedeanAsymptoticHeight c x
  let w₀ := archimedeanFrequency c x₀
  let w := archimedeanFrequency c x
  have hy₀ : 0 < y₀ := archimedeanAsymptoticHeight_pos c x₀ hc hx₀
  have hy : 0 < y := archimedeanAsymptoticHeight_pos c x hc hx
  have hy₀y : y₀ ≤ y := by
    calc
      y₀ = (Real.pi / Real.log c) * x₀ := by
        dsimp [y₀, archimedeanAsymptoticHeight]
        ring
      _ ≤ (Real.pi / Real.log c) * x :=
        mul_le_mul_of_nonneg_left hxx (div_nonneg Real.pi_pos.le (Real.log_pos hc).le)
      _ = y := by
        dsimp [y, archimedeanAsymptoticHeight]
        ring
  have hySq : y₀ ^ 2 ≤ y ^ 2 := by nlinarith
  have hInvY : 1 / y ≤ 1 / y₀ := one_div_le_one_div_of_le hy₀ hy₀y
  have hInvYSq : 1 / y ^ 2 ≤ 1 / y₀ ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hy₀) hySq
  have hw₀ : 0 < w₀ := by
    dsimp [w₀]
    rw [archimedeanFrequency_eq_two_mul_height]
    positivity
  have hw : 0 < w := by
    dsimp [w]
    rw [archimedeanFrequency_eq_two_mul_height]
    positivity
  have hw₀w : w₀ ≤ w := by
    dsimp [w₀, w]
    simp only [archimedeanFrequency_eq_two_mul_height]
    linarith
  have hwSq : w₀ ^ 2 ≤ w ^ 2 := by nlinarith
  have hA : 0 ≤ (1 / 8 + Real.sqrt 2 / 6 : ℝ) := by positivity
  have hB : 0 ≤ 2 * archimedeanGeometricFirstMoment c := by
    positivity [archimedeanGeometricFirstMoment_nonneg c hc]
  have hC : 0 ≤ (2 / Real.log c) * archimedeanGeometricMass c := by
    positivity [Real.log_pos hc, archimedeanGeometricMass_nonneg c hc]
  have hTermA :
      (1 / 8 + Real.sqrt 2 / 6) / y ^ 2 ≤
        (1 / 8 + Real.sqrt 2 / 6) / y₀ ^ 2 :=
    div_le_div_of_nonneg_left hA (sq_pos_of_pos hy₀) hySq
  have hTermTrigamma :
      (1 / y + 1 / y ^ 2) / (2 * Real.log c) ≤
        (1 / y₀ + 1 / y₀ ^ 2) / (2 * Real.log c) := by
    exact (div_le_div_iff_of_pos_right
      (mul_pos (by norm_num) (Real.log_pos hc))).2 (add_le_add hInvY hInvYSq)
  have hTermB :
      (2 * archimedeanGeometricFirstMoment c) / w ^ 2 ≤
        (2 * archimedeanGeometricFirstMoment c) / w₀ ^ 2 :=
    div_le_div_of_nonneg_left hB (sq_pos_of_pos hw₀) hwSq
  have hTermC :
      ((2 / Real.log c) * archimedeanGeometricMass c) / w ^ 2 ≤
        ((2 / Real.log c) * archimedeanGeometricMass c) / w₀ ^ 2 :=
    div_le_div_of_nonneg_left hC (sq_pos_of_pos hw₀) hwSq
  unfold archimedeanDiagonalAsymptoticError
  dsimp only
  change (1 / 8 + Real.sqrt 2 / 6) / y ^ 2 +
      (1 / y + 1 / y ^ 2) / (2 * Real.log c) +
      (2 * archimedeanGeometricFirstMoment c) / w ^ 2 +
      ((2 / Real.log c) * archimedeanGeometricMass c) / w ^ 2 ≤
    (1 / 8 + Real.sqrt 2 / 6) / y₀ ^ 2 +
      (1 / y₀ + 1 / y₀ ^ 2) / (2 * Real.log c) +
      (2 * archimedeanGeometricFirstMoment c) / w₀ ^ 2 +
      ((2 / Real.log c) * archimedeanGeometricMass c) / w₀ ^ 2
  linarith
noncomputable def archimedeanDiagonalAsymptoticLower (c x : ℝ) : ℝ :=
  Real.log x + archimedeanDiagonalAsymptoticConstant c -
    archimedeanDiagonalAsymptoticError c x

theorem neg_logarithmicArchimedeanDiagonal_ge_of_asymptotic_bounds
    (c x : ℝ) (hc : 1 < c) (hx : 0 < x)
    (hDigammaRemainder :
      ‖Complex.digamma (archimedeanArgument c x) -
          (Complex.log (archimedeanArgument c x) -
            1 / (2 * archimedeanArgument c x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight c x ^ 2))
    (hTrigamma : archimedeanTrigammaSeriesFloor c x ≤
      (deriv Complex.digamma (archimedeanArgument c x)).re) :
    archimedeanDiagonalAsymptoticLower c x ≤
      -logarithmicArchimedeanDiagonal c x := by
  have hy := archimedeanAsymptoticHeight_pos c x hc hx
  have hw := archimedeanFrequency_ne_zero_of_pos c x hc hx
  have hL := Real.log_pos hc
  have hDigamma := digamma_real_ge_asymptoticFloor_of_norm_remainder
    c x hc hx hDigammaRemainder
  have hRaw := neg_logarithmicArchimedeanDiagonal_ge_of_digamma
    c x (archimedeanDigammaAsymptoticFloor c x)
      (archimedeanTrigammaSeriesFloor c x) hc hw hDigamma hTrigamma
  have hRatio : 0 < Real.pi / Real.log c := div_pos Real.pi_pos hL
  have hHeight : archimedeanAsymptoticHeight c x =
      (Real.pi / Real.log c) * x := by
    unfold archimedeanAsymptoticHeight
    ring
  have hLogHeight : Real.log (archimedeanAsymptoticHeight c x) =
      Real.log (Real.pi / Real.log c) + Real.log x := by
    rw [hHeight, Real.log_mul (ne_of_gt hRatio) (ne_of_gt hx)]
  calc
    archimedeanDiagonalAsymptoticLower c x =
        -logarithmicArchimedeanKappa c - logarithmicArchimedeanPoleJ c +
          (archimedeanDigammaAsymptoticFloor c x -
            (Complex.digamma (1 / 4 : ℂ)).re -
            4 * archimedeanGeometricMass c) +
          (2 / Real.log c) *
            ((1 / 4) * archimedeanTrigammaSeriesFloor c x -
              Real.log c *
                (archimedeanGeometricFirstMoment c /
                  archimedeanFrequency c x ^ 2) -
              archimedeanGeometricMass c /
                archimedeanFrequency c x ^ 2) := by
      unfold archimedeanDiagonalAsymptoticLower
        archimedeanDiagonalAsymptoticConstant
        archimedeanDiagonalAsymptoticError
        archimedeanDigammaAsymptoticFloor
        archimedeanTrigammaSeriesFloor
      dsimp only
      rw [hLogHeight]
      field_simp [ne_of_gt hL, ne_of_gt hy, hw]
      ring
    _ ≤ -logarithmicArchimedeanDiagonal c x := hRaw


theorem neg_logarithmicArchimedeanDiagonal_ge_log_sub_of_asymptotic_bounds
    (c x₀ x offset : ℝ) (hc : 1 < c) (hx₀ : 0 < x₀) (hxx : x₀ ≤ x)
    (hDigammaRemainder :
      ‖Complex.digamma (archimedeanArgument c x) -
          (Complex.log (archimedeanArgument c x) -
            1 / (2 * archimedeanArgument c x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight c x ^ 2))
    (hTrigamma : archimedeanTrigammaSeriesFloor c x ≤
      (deriv Complex.digamma (archimedeanArgument c x)).re)
    (hEndpoint : -offset ≤
      archimedeanDiagonalAsymptoticConstant c -
        archimedeanDiagonalAsymptoticError c x₀) :
    Real.log x - offset ≤ -logarithmicArchimedeanDiagonal c x := by
  have hx : 0 < x := hx₀.trans_le hxx
  have hError := archimedeanDiagonalAsymptoticError_antitone
    c x₀ x hc hx₀ hxx
  have hConstant : -offset ≤
      archimedeanDiagonalAsymptoticConstant c -
        archimedeanDiagonalAsymptoticError c x := by
    linarith
  have hDiagonal := neg_logarithmicArchimedeanDiagonal_ge_of_asymptotic_bounds
    c x hc hx hDigammaRemainder hTrigamma
  unfold archimedeanDiagonalAsymptoticLower at hDiagonal
  linarith

theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hDigammaRemainder :
      ‖Complex.digamma (archimedeanArgument 13 x) -
          (Complex.log (archimedeanArgument 13 x) -
            1 / (2 * archimedeanArgument 13 x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13 x ^ 2))
    (hTrigamma : archimedeanTrigammaSeriesFloor 13 x ≤
      (deriv Complex.digamma (archimedeanArgument 13 x)).re)
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    Real.log x - 19 / 20 ≤ -logarithmicArchimedeanDiagonal 13 x := by
  exact neg_logarithmicArchimedeanDiagonal_ge_log_sub_of_asymptotic_bounds
    13 960 x (19 / 20) (by norm_num) (by norm_num) hx
      hDigammaRemainder hTrigamma hEndpoint

/-- The cutoff-13 diagonal route with the trigamma hypothesis reduced to its
canonical complex series identity. -/
theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hDigammaRemainder :
      ‖Complex.digamma (archimedeanArgument 13 x) -
          (Complex.log (archimedeanArgument 13 x) -
            1 / (2 * archimedeanArgument 13 x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13 x ^ 2))
    (hTrigammaSeries : HasSum (archimedeanTrigammaSeriesTerm 13 x)
      (deriv Complex.digamma (archimedeanArgument 13 x)))
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    Real.log x - 19 / 20 ≤ -logarithmicArchimedeanDiagonal 13 x := by
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 960).trans_le hx
  exact c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth
    x hx hDigammaRemainder
      (archimedeanTrigammaSeriesFloor_le_of_hasSum
        13 x (by norm_num) hxPos hTrigammaSeries)
      hEndpoint

/-- The cutoff-13 diagonal route with the canonical trigamma series discharged
by decay of the shifted digamma derivative. -/
theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaTail
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hDigammaRemainder :
      ‖Complex.digamma (archimedeanArgument 13 x) -
          (Complex.log (archimedeanArgument 13 x) -
            1 / (2 * archimedeanArgument 13 x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13 x ^ 2))
    (hTrigammaTail : Tendsto (fun N : ℕ =>
      deriv Complex.digamma
        (archimedeanArgument 13 x + (N : ℂ))) atTop (𝓝 0))
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    Real.log x - 19 / 20 ≤ -logarithmicArchimedeanDiagonal 13 x := by
  exact
    c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries
      x hx hDigammaRemainder
        (archimedeanTrigammaSeries_hasSum_of_tendsto_deriv_digamma
          13 x hTrigammaTail)
        hEndpoint

/-- The cutoff-13 diagonal route with both the pointwise digamma floor and the
trigamma series discharged by one global DLMF-form quadratic remainder bound. -/
theorem c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_quadratic_remainder_bound
    (x : ℝ) (hx : (960 : ℝ) ≤ x)
    (hRemainder : ∀ w : ℂ, 0 < w.re →
      ‖Complex.digamma w - (Complex.log w - 1 / (2 * w))‖ ≤
        (Real.sqrt 2 / 6) / ‖w‖ ^ 2)
    (hEndpoint : -(19 / 20 : ℝ) ≤
      archimedeanDiagonalAsymptoticConstant 13 -
        archimedeanDiagonalAsymptoticError 13 960) :
    Real.log x - 19 / 20 ≤ -logarithmicArchimedeanDiagonal 13 x := by
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 960).trans_le hx
  have hC : 0 ≤ Real.sqrt 2 / 6 :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hPointRaw :=
    archimedean_digamma_remainder_le_of_quadratic_remainder_bound
      13 x (Real.sqrt 2 / 6) (by norm_num) hxPos hC hRemainder
  have hPoint :
      ‖Complex.digamma (archimedeanArgument 13 x) -
          (Complex.log (archimedeanArgument 13 x) -
            1 / (2 * archimedeanArgument 13 x))‖ ≤
        Real.sqrt 2 /
          (6 * archimedeanAsymptoticHeight 13 x ^ 2) := by
    calc
      _ ≤ (Real.sqrt 2 / 6) /
          archimedeanAsymptoticHeight 13 x ^ 2 := hPointRaw
      _ = _ := by ring
  exact
    c13_neg_logarithmicArchimedeanDiagonal_ge_log_sub_nineteenTwentieth_of_trigammaSeries
      x hx hPoint
        (archimedeanTrigammaSeries_hasSum_of_quadratic_remainder_bound
          13 x (Real.sqrt 2 / 6) hC hRemainder)
        hEndpoint

theorem logarithmicArchimedeanDiagonal_neg (c x : ℝ) :
    logarithmicArchimedeanDiagonal c (-x) =
      logarithmicArchimedeanDiagonal c x := by
  unfold logarithmicArchimedeanDiagonal
  rw [archimedeanCosineCorrection_neg, archimedeanCrossCorrection_neg]

/-- The fully concrete cutoff-free kernel is invariant under simultaneous
reflection of both signed Fourier modes. -/
theorem logarithmicCutoffFreeKernel_actual_neg_neg
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (p q : ℝ) :
    logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c)
        c location base (-p) (-q) =
      logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c)
        c location base p q := by
  have hSymbol : Function.Odd
      (fourierNormalizedSymbol
        (logarithmicCombinedSymbol
          (logarithmicArchimedeanSymbol c) c location base)) :=
    fourierNormalizedSymbol_odd
      (logarithmicCombinedSymbol
        (logarithmicArchimedeanSymbol c) c location base)
      (logarithmicCombinedSymbol_odd
        (logarithmicArchimedeanSymbol c) c location base
        (logarithmicArchimedeanSymbol_odd c))
  have hPrimeDiagonal : Function.Even
      (finiteLogarithmicPrimeDiagonal c location base) :=
    finiteLogarithmicPrimeDiagonal_even c location base
  have hDiagonal : Function.Even (fun x =>
      logarithmicArchimedeanDiagonal c x +
        finiteLogarithmicPrimeDiagonal c location base x) := by
    intro x
    change logarithmicArchimedeanDiagonal c (-x) +
        finiteLogarithmicPrimeDiagonal c location base (-x) = _
    rw [logarithmicArchimedeanDiagonal_neg, hPrimeDiagonal x]
  rw [logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicCutoffFreeKernel_eq_pole_sub_oddDifferenceKernel,
    logarithmicPoleKernel_neg_neg,
    CvSParityDisplacement.oddDifferenceKernel_neg_neg _ _ hSymbol hDiagonal]

theorem logarithmicCutoffFreeKernel_actualArchimedean_law
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (hc : 1 < c) :
    CvSParityDisplacement.DisplacementLaw
      (logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c) c location base) := by
  exact logarithmicCutoffFreeKernel_archimedean_law
    (logarithmicArchimedeanDiagonal c) c location base hc

/-!
### Exact signed-integer finite-builder restriction

The Python/Arb matrix is indexed by centered signed integers and evaluates the
Archimedean diagonal at an absolute mode.  The following literal entry and
matrix definitions prove that those implementation branches are exactly the
signed-integer restriction of the complete Lean cutoff-free kernel.
-/
/-- Signed extension used by the finite Python/Arb builder. -/
noncomputable def signedLogarithmicArchimedeanSymbol (c x : ℝ) : ℝ :=
  if 0 ≤ x then logarithmicArchimedeanSymbol c x
  else -logarithmicArchimedeanSymbol c (-x)

theorem signedLogarithmicArchimedeanSymbol_eq (c x : ℝ) :
    signedLogarithmicArchimedeanSymbol c x =
      logarithmicArchimedeanSymbol c x := by
  by_cases hx : 0 ≤ x
  · simp [signedLogarithmicArchimedeanSymbol, hx]
  · simp only [signedLogarithmicArchimedeanSymbol, hx, if_false]
    rw [logarithmicArchimedeanSymbol_odd c x]
    ring

theorem logarithmicArchimedeanDiagonal_abs (c x : ℝ) :
    logarithmicArchimedeanDiagonal c |x| =
      logarithmicArchimedeanDiagonal c x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos (le_of_not_ge hx), logarithmicArchimedeanDiagonal_neg]

/-- Literal rational entry used in the finite cutoff-free builder. -/
noncomputable def logarithmicCvSPoleEntry (c : ℝ) (n m : ℤ) : ℝ :=
  (32 * Real.log c * Real.sinh (Real.log c / 4) ^ 2) *
      ((Real.log c) ^ 2 - 16 * Real.pi ^ 2 * (n : ℝ) * (m : ℝ)) /
    (((Real.log c) ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2) *
      ((Real.log c) ^ 2 + 16 * Real.pi ^ 2 * (m : ℝ) ^ 2))

theorem logarithmicCvSPoleEntry_eq_kernel (c : ℝ) (n m : ℤ) :
    logarithmicCvSPoleEntry c n m =
      logarithmicPoleKernel c (n : ℝ) (m : ℝ) := by
  rfl

/-- Literal diagonal/off-diagonal Archimedean branch of the finite builder. -/
noncomputable def logarithmicCvSArchimedeanEntry
    (c : ℝ) (n m : ℤ) : ℝ :=
  if n = m then logarithmicArchimedeanDiagonal c |(n : ℝ)|
  else
    (signedLogarithmicArchimedeanSymbol c (m : ℝ) -
        signedLogarithmicArchimedeanSymbol c (n : ℝ)) /
      (Real.pi * ((n : ℝ) - (m : ℝ)))

theorem logarithmicCvSArchimedeanEntry_eq_source
    (c : ℝ) (n m : ℤ) :
    logarithmicCvSArchimedeanEntry c n m =
      normalizedLoewnerSourceEntry
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c) (n : ℝ) (m : ℝ) := by
  by_cases hnm : n = m
  · subst m
    simp [logarithmicCvSArchimedeanEntry, normalizedLoewnerSourceEntry,
      logarithmicArchimedeanDiagonal_abs]
  · have hcast : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
    simp [logarithmicCvSArchimedeanEntry, normalizedLoewnerSourceEntry,
      hnm, hcast, signedLogarithmicArchimedeanSymbol_eq]

/-- Literal finite CvS builder entry `W_02 - W_R - W_p`. -/
noncomputable def logarithmicCvSBuilderEntry
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) : ℝ :=
  logarithmicCvSPoleEntry c n m -
    (logarithmicCvSArchimedeanEntry c n m +
      finiteLogarithmicPrimeEntry c location base (n : ℝ) (m : ℝ))

theorem logarithmicCvSBuilderEntry_eq_cutoffFreeKernel
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    logarithmicCvSBuilderEntry c location base n m =
      logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c)
        c location base (n : ℝ) (m : ℝ) := by
  unfold logarithmicCvSBuilderEntry logarithmicCutoffFreeKernel
    logarithmicArchPrimeEntry
  rw [logarithmicCvSPoleEntry_eq_kernel,
    logarithmicCvSArchimedeanEntry_eq_source]

theorem logarithmicCvSBuilderEntry_symm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    logarithmicCvSBuilderEntry c location base n m =
      logarithmicCvSBuilderEntry c location base m n := by
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]
  exact logarithmicCutoffFreeKernel_symm _ _ _ _ _ _ _

theorem logarithmicCvSBuilderEntry_neg_neg
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    logarithmicCvSBuilderEntry c location base (-n) (-m) =
      logarithmicCvSBuilderEntry c location base n m := by
  rw [logarithmicCvSBuilderEntry_eq_cutoffFreeKernel,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]
  simpa using logarithmicCutoffFreeKernel_actual_neg_neg
    c location base (n : ℝ) (m : ℝ)

theorem logarithmicCvSBuilderEntry_neg_right_eq_neg_left
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (n m : ℤ) :
    logarithmicCvSBuilderEntry c location base n (-m) =
      logarithmicCvSBuilderEntry c location base (-n) m := by
  simpa using logarithmicCvSBuilderEntry_neg_neg
    c location base (-n) m

/-- Mode attached to row `i` in the `(2*N+1)` centered finite builder. -/
def centeredIntegerMode (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i : ℤ) - (N : ℤ)

noncomputable def logarithmicCvSBuilderMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => logarithmicCvSBuilderEntry c location base
    (centeredIntegerMode N i) (centeredIntegerMode N j)

theorem logarithmicCvSBuilderMatrix_eq_kernelRestriction
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    logarithmicCvSBuilderMatrix c location base N i j =
      logarithmicCutoffFreeKernel
        (logarithmicArchimedeanSymbol c)
        (logarithmicArchimedeanDiagonal c)
        c location base
        (centeredIntegerMode N i : ℝ)
        (centeredIntegerMode N j : ℝ) := by
  exact logarithmicCvSBuilderEntry_eq_cutoffFreeKernel c location base
    (centeredIntegerMode N i) (centeredIntegerMode N j)

/-!
### Exact orthonormal parity compression

The finite cosine and sine matrices used by the operator argument are the
orthonormal even and odd compressions of the signed-integer builder.  These
literal definitions close that coordinate conversion entry by entry.
-/
noncomputable def positiveIntegerMode {N : ℕ} (i : Fin N) : ℤ :=
  (i : ℕ) + 1

noncomputable def logarithmicCvSBuilderEvenMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    Matrix (Option (Fin N)) (Option (Fin N)) ℝ :=
  fun i j =>
    match i, j with
    | none, none => logarithmicCvSBuilderEntry c location base 0 0
    | none, some k => Real.sqrt 2 *
        logarithmicCvSBuilderEntry c location base 0 (positiveIntegerMode k)
    | some k, none => Real.sqrt 2 *
        logarithmicCvSBuilderEntry c location base (positiveIntegerMode k) 0
    | some k, some l =>
        logarithmicCvSBuilderEntry c location base
            (positiveIntegerMode k) (positiveIntegerMode l) +
          logarithmicCvSBuilderEntry c location base
            (positiveIntegerMode k) (-positiveIntegerMode l)

noncomputable def logarithmicCvSBuilderOddMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    logarithmicCvSBuilderEntry c location base
        (positiveIntegerMode i) (positiveIntegerMode j) -
      logarithmicCvSBuilderEntry c location base
        (positiveIntegerMode i) (-positiveIntegerMode j)

/-- The literal orthonormal even compression is a symmetric real matrix. -/
theorem logarithmicCvSBuilderEvenMatrix_symm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ)
    (i j : Option (Fin N)) :
    logarithmicCvSBuilderEvenMatrix c location base N i j =
      logarithmicCvSBuilderEvenMatrix c location base N j i := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [logarithmicCvSBuilderEvenMatrix,
      logarithmicCvSBuilderEntry_symm,
      logarithmicCvSBuilderEntry_neg_right_eq_neg_left]

/-- The literal orthonormal odd compression is a symmetric real matrix. -/
theorem logarithmicCvSBuilderOddMatrix_symm
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ)
    (i j : Fin N) :
    logarithmicCvSBuilderOddMatrix c location base N i j =
      logarithmicCvSBuilderOddMatrix c location base N j i := by
  simp [logarithmicCvSBuilderOddMatrix,
    logarithmicCvSBuilderEntry_symm,
    logarithmicCvSBuilderEntry_neg_right_eq_neg_left]

theorem logarithmicCvSBuilderEvenMatrix_eq_evenParityMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    logarithmicCvSBuilderEvenMatrix c location base N =
      CvSParityDisplacement.evenParityMatrix
        (logarithmicCutoffFreeKernel
          (logarithmicArchimedeanSymbol c)
          (logarithmicArchimedeanDiagonal c) c location base)
        (fun i : Fin N => (positiveIntegerMode i : ℝ)) := by
  ext i j
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [logarithmicCvSBuilderEvenMatrix,
      CvSParityDisplacement.evenParityMatrix,
      logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]

theorem logarithmicCvSBuilderOddMatrix_eq_oddParityMatrix
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (N : ℕ) :
    logarithmicCvSBuilderOddMatrix c location base N =
      CvSParityDisplacement.oddParityMatrix
        (logarithmicCutoffFreeKernel
          (logarithmicArchimedeanSymbol c)
          (logarithmicArchimedeanDiagonal c) c location base)
        (fun i : Fin N => (positiveIntegerMode i : ℝ)) := by
  ext i j
  simp [logarithmicCvSBuilderOddMatrix,
    CvSParityDisplacement.oddParityMatrix,
    logarithmicCvSBuilderEntry_eq_cutoffFreeKernel]

/-!
### Exact newest-band coordinates

Write `B = K / 2` in the notation of the scalar certificate.  The historical
rows are precisely the `B` positive modes in `(B, 2B]`, while the newest
columns are the `4B` positive modes in `(4B, 8B]`.  The following finite
coordinates exhaust those intervals and restrict the literal builder parity
matrices to exactly that rectangular channel.
-/
noncomputable def historicalBandMode (B : ℕ) (i : Fin B) : ℕ :=
  B + 1 + (i : ℕ)

noncomputable def newestShellMode (B : ℕ) (j : Fin (4 * B)) : ℕ :=
  4 * B + 1 + (j : ℕ)

theorem exists_historicalBandMode_iff
    (B n : ℕ) :
    (∃ i : Fin B, historicalBandMode B i = n) ↔
      B < n ∧ n ≤ 2 * B := by
  constructor
  · rintro ⟨i, rfl⟩
    simp only [historicalBandMode]
    omega
  · rintro ⟨hLower, hUpper⟩
    let i : Fin B := ⟨n - (B + 1), by omega⟩
    refine ⟨i, ?_⟩
    simp only [historicalBandMode, i]
    omega

theorem exists_newestShellMode_iff
    (B n : ℕ) :
    (∃ j : Fin (4 * B), newestShellMode B j = n) ↔
      4 * B < n ∧ n ≤ 8 * B := by
  constructor
  · rintro ⟨j, rfl⟩
    simp only [newestShellMode]
    omega
  · rintro ⟨hLower, hUpper⟩
    let j : Fin (4 * B) := ⟨n - (4 * B + 1), by omega⟩
    refine ⟨j, ?_⟩
    simp only [newestShellMode, j]
    omega

noncomputable def historicalBandIndex
    (B : ℕ) (i : Fin B) : Fin (8 * B) :=
  ⟨B + (i : ℕ), by omega⟩

noncomputable def newestShellIndex
    (B : ℕ) (j : Fin (4 * B)) : Fin (8 * B) :=
  ⟨4 * B + (j : ℕ), by omega⟩

theorem positiveIntegerMode_historicalBandIndex
    (B : ℕ) (i : Fin B) :
    positiveIntegerMode (historicalBandIndex B i) =
      (historicalBandMode B i : ℤ) := by
  simp [positiveIntegerMode, historicalBandIndex, historicalBandMode]
  ring

theorem positiveIntegerMode_newestShellIndex
    (B : ℕ) (j : Fin (4 * B)) :
    positiveIntegerMode (newestShellIndex B j) =
      (newestShellMode B j : ℤ) := by
  simp [positiveIntegerMode, newestShellIndex, newestShellMode]
  ring

noncomputable def logarithmicCvSBuilderEvenNewestBand
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    Matrix (Fin B) (Fin (4 * B)) ℝ :=
  fun i j =>
    logarithmicCvSBuilderEvenMatrix c location base (8 * B)
      (some (historicalBandIndex B i)) (some (newestShellIndex B j))

noncomputable def logarithmicCvSBuilderOddNewestBand
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    Matrix (Fin B) (Fin (4 * B)) ℝ :=
  fun i j =>
    logarithmicCvSBuilderOddMatrix c location base (8 * B)
      (historicalBandIndex B i) (newestShellIndex B j)

theorem logarithmicCvSBuilderEvenNewestBand_eq_evenParityRestriction
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    logarithmicCvSBuilderEvenNewestBand c location base B =
      fun i j =>
        CvSParityDisplacement.evenParityMatrix
          (logarithmicCutoffFreeKernel
            (logarithmicArchimedeanSymbol c)
            (logarithmicArchimedeanDiagonal c) c location base)
          (fun k : Fin (8 * B) => (positiveIntegerMode k : ℝ))
          (some (historicalBandIndex B i)) (some (newestShellIndex B j)) := by
  ext i j
  change logarithmicCvSBuilderEvenMatrix c location base (8 * B)
      (some (historicalBandIndex B i)) (some (newestShellIndex B j)) = _
  rw [logarithmicCvSBuilderEvenMatrix_eq_evenParityMatrix]

theorem logarithmicCvSBuilderOddNewestBand_eq_oddParityRestriction
    {ι : Type*} [Fintype ι]
    (c : ℝ) (location base : ι → ℝ) (B : ℕ) :
    logarithmicCvSBuilderOddNewestBand c location base B =
      fun i j =>
        CvSParityDisplacement.oddParityMatrix
          (logarithmicCutoffFreeKernel
            (logarithmicArchimedeanSymbol c)
            (logarithmicArchimedeanDiagonal c) c location base)
          (fun k : Fin (8 * B) => (positiveIntegerMode k : ℝ))
          (historicalBandIndex B i) (newestShellIndex B j) := by
  ext i j
  change logarithmicCvSBuilderOddMatrix c location base (8 * B)
      (historicalBandIndex B i) (newestShellIndex B j) = _
  rw [logarithmicCvSBuilderOddMatrix_eq_oddParityMatrix]

/-- Every strict interior event `1 < q < c` has a positive half-angle sine,
so its finite geometric sums are nonresonant without numerical phase testing. -/
theorem logarithmicPrimePhase_half_sin_pos
    (c q : ℝ) (hc : 1 < c) (hq : 1 < q) (hqc : q < c) :
    0 < Real.sin (logarithmicPrimePhase c q / 2) := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hqPos : 0 < q := lt_trans zero_lt_one hq
  have hLogC : 0 < Real.log c := Real.log_pos hc
  have hLogQ : 0 < Real.log q := Real.log_pos hq
  have hLogLt : Real.log q < Real.log c :=
    Real.strictMonoOn_log hqPos hcPos hqc
  have hRatioPos : 0 < Real.log q / Real.log c :=
    div_pos hLogQ hLogC
  have hRatioLt : Real.log q / Real.log c < 1 :=
    (div_lt_one hLogC).2 hLogLt
  rw [show logarithmicPrimePhase c q / 2 =
      Real.pi * (Real.log q / Real.log c) by
    unfold logarithmicPrimePhase
    ring]
  exact Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hRatioPos)
    (by nlinarith [Real.pi_pos])

/-- Concrete shifted sine sums for one strict interior prime-power event obey
the exact reciprocal half-angle bound consumed by the Arb certificate. -/
theorem abs_shifted_logarithmicPrime_sine_sum_le
    (c q : ℝ) (start count : ℕ)
    (hc : 1 < c) (hq : 1 < q) (hqc : q < c) :
    |∑ j ∈ Finset.range count,
        Real.sin (((start + j : ℕ) : ℝ) * logarithmicPrimePhase c q)| ≤
      1 / |Real.sin (logarithmicPrimePhase c q / 2)| := by
  exact abs_shifted_sine_sum_le_inv_abs_sin_half
    (logarithmicPrimePhase c q) start count
    (ne_of_gt (logarithmicPrimePhase_half_sin_pos c q hc hq hqc))

/-- The parallel concrete cosine-sum bound for one strict interior event. -/
theorem abs_shifted_logarithmicPrime_cosine_sum_le
    (c q : ℝ) (start count : ℕ)
    (hc : 1 < c) (hq : 1 < q) (hqc : q < c) :
    |∑ j ∈ Finset.range count,
        Real.cos (((start + j : ℕ) : ℝ) * logarithmicPrimePhase c q)| ≤
      1 / |Real.sin (logarithmicPrimePhase c q / 2)| := by
  exact abs_shifted_cosine_sum_le_inv_abs_sin_half
    (logarithmicPrimePhase c q) start count
    (ne_of_gt (logarithmicPrimePhase_half_sin_pos c q hc hq hqc))

/-!
### Composite phases and the tracked cutoff-13 event list

The square expansion also contains doubled, pair-difference, and pair-sum
phases.  Their only possible pair-sum resonance is `q*r=c`.  The following
generic lemmas isolate that condition, then a finite `Fin 8` enumeration proves
all actual cutoff-13 phase denominators nonzero in Lean.
-/

/-- Distinct strict-interior logarithmic phases have a negative, nonzero
half-difference sine. -/
theorem logarithmicPrimePhase_sub_half_sin_neg
    (c q r : ℝ) (hc : 1 < c) (hq : 1 < q) (hqr : q < r) (hrc : r < c) :
    Real.sin
        ((logarithmicPrimePhase c q - logarithmicPrimePhase c r) / 2) < 0 := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hqPos : 0 < q := lt_trans zero_lt_one hq
  have hrPos : 0 < r := lt_trans hqPos hqr
  have hLogC : 0 < Real.log c := Real.log_pos hc
  have hLogQ : 0 < Real.log q := Real.log_pos hq
  have hLogQLtR : Real.log q < Real.log r :=
    Real.strictMonoOn_log hqPos hrPos hqr
  have hLogRLtC : Real.log r < Real.log c :=
    Real.strictMonoOn_log hrPos hcPos hrc
  have hRatioNeg :
      (Real.log q - Real.log r) / Real.log c < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr hLogQLtR) hLogC
  have hRatioLower :
      -1 < (Real.log q - Real.log r) / Real.log c := by
    apply (lt_div_iff₀ hLogC).2
    nlinarith
  rw [show (logarithmicPrimePhase c q - logarithmicPrimePhase c r) / 2 =
      Real.pi * ((Real.log q - Real.log r) / Real.log c) by
    unfold logarithmicPrimePhase
    ring]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · exact mul_neg_of_pos_of_neg Real.pi_pos hRatioNeg
  · have h := mul_lt_mul_of_pos_left hRatioLower Real.pi_pos
    nlinarith

/-- If the product of two strict-interior event locations remains below the
cutoff, their half-sum phase has positive sine. -/
theorem logarithmicPrimePhase_add_half_sin_pos_of_mul_lt
    (c q r : ℝ) (hc : 1 < c) (hq : 1 < q) (hr : 1 < r)
    (hMul : q * r < c) :
    0 < Real.sin
      ((logarithmicPrimePhase c q + logarithmicPrimePhase c r) / 2) := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hqPos : 0 < q := lt_trans zero_lt_one hq
  have hrPos : 0 < r := lt_trans zero_lt_one hr
  have hLogC : 0 < Real.log c := Real.log_pos hc
  have hLogQ : 0 < Real.log q := Real.log_pos hq
  have hLogR : 0 < Real.log r := Real.log_pos hr
  have hMulPos : 0 < q * r := mul_pos hqPos hrPos
  have hLogSumLt : Real.log q + Real.log r < Real.log c := by
    rw [← Real.log_mul (ne_of_gt hqPos) (ne_of_gt hrPos)]
    exact Real.strictMonoOn_log hMulPos hcPos hMul
  have hRatioPos :
      0 < (Real.log q + Real.log r) / Real.log c :=
    div_pos (add_pos hLogQ hLogR) hLogC
  have hRatioLt :
      (Real.log q + Real.log r) / Real.log c < 1 :=
    (div_lt_one hLogC).2 hLogSumLt
  rw [show (logarithmicPrimePhase c q + logarithmicPrimePhase c r) / 2 =
      Real.pi * ((Real.log q + Real.log r) / Real.log c) by
    unfold logarithmicPrimePhase
    ring]
  exact Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hRatioPos)
    (by nlinarith [mul_lt_mul_of_pos_left hRatioLt Real.pi_pos])

/-- If the product lies strictly between `c` and `c^2`, the half-sum phase
lies in `(pi,2*pi)` and has negative sine. -/
theorem logarithmicPrimePhase_add_half_sin_neg_of_cutoff_lt_mul
    (c q r : ℝ) (hc : 1 < c) (hq : 1 < q) (hr : 1 < r)
    (hLower : c < q * r) (hUpper : q * r < c ^ 2) :
    Real.sin
        ((logarithmicPrimePhase c q + logarithmicPrimePhase c r) / 2) < 0 := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hqPos : 0 < q := lt_trans zero_lt_one hq
  have hrPos : 0 < r := lt_trans zero_lt_one hr
  have hMulPos : 0 < q * r := mul_pos hqPos hrPos
  have hSqPos : 0 < c ^ 2 := sq_pos_of_pos hcPos
  have hLogC : 0 < Real.log c := Real.log_pos hc
  have hLogLower : Real.log c < Real.log q + Real.log r := by
    rw [← Real.log_mul (ne_of_gt hqPos) (ne_of_gt hrPos)]
    exact Real.strictMonoOn_log hcPos hMulPos hLower
  have hLogUpper : Real.log q + Real.log r < 2 * Real.log c := by
    calc
      Real.log q + Real.log r = Real.log (q * r) := by
        rw [Real.log_mul (ne_of_gt hqPos) (ne_of_gt hrPos)]
      _ < Real.log (c ^ 2) :=
        Real.strictMonoOn_log hMulPos hSqPos hUpper
      _ = 2 * Real.log c := by norm_num [Real.log_pow]
  have hRatioLower :
      1 < (Real.log q + Real.log r) / Real.log c :=
    (lt_div_iff₀ hLogC).2 (by simpa using hLogLower)
  have hRatioUpper :
      (Real.log q + Real.log r) / Real.log c < 2 :=
    (div_lt_iff₀ hLogC).2 (by simpa [mul_comm] using hLogUpper)
  let x := Real.pi * ((Real.log q + Real.log r) / Real.log c)
  have hxPi : Real.pi < x := by
    dsimp [x]
    nlinarith [mul_lt_mul_of_pos_left hRatioLower Real.pi_pos]
  have hxTwoPi : x < 2 * Real.pi := by
    dsimp [x]
    nlinarith [mul_lt_mul_of_pos_left hRatioUpper Real.pi_pos]
  have hShift : Real.sin (x - 2 * Real.pi) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  rw [Real.sin_sub_two_pi] at hShift
  rw [show (logarithmicPrimePhase c q + logarithmicPrimePhase c r) / 2 = x by
    dsimp [x]
    unfold logarithmicPrimePhase
    ring]
  exact hShift

/-- For strict-interior locations, exclusion of the sole resonance
`q*r=c` proves nonresonance of every pair-sum phase. -/
theorem logarithmicPrimePhase_add_half_sin_ne_zero
    (c q r : ℝ) (hc : 1 < c) (hq : 1 < q) (hr : 1 < r)
    (hqc : q < c) (hrc : r < c) (hMulNe : q * r ≠ c) :
    Real.sin
        ((logarithmicPrimePhase c q + logarithmicPrimePhase c r) / 2) ≠ 0 := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hMulUpper : q * r < c ^ 2 := by
    rw [sq]
    exact mul_lt_mul hqc (le_of_lt hrc) (lt_trans zero_lt_one hr)
      (le_of_lt hcPos)
  rcases lt_or_gt_of_ne hMulNe with hMulLt | hMulGt
  · exact ne_of_gt
      (logarithmicPrimePhase_add_half_sin_pos_of_mul_lt
        c q r hc hq hr hMulLt)
  · exact ne_of_lt
      (logarithmicPrimePhase_add_half_sin_neg_of_cutoff_lt_mul
        c q r hc hq hr hMulGt hMulUpper)

/-- The doubled phase for one event is nonresonant whenever `q^2 != c`. -/
theorem logarithmicPrimePhase_sin_ne_zero
    (c q : ℝ) (hc : 1 < c) (hq : 1 < q) (hqc : q < c)
    (hSqNe : q ^ 2 ≠ c) :
    Real.sin (logarithmicPrimePhase c q) ≠ 0 := by
  have h := logarithmicPrimePhase_add_half_sin_ne_zero
    c q q hc hq hq hqc hqc (by simpa [pow_two] using hSqNe)
  rw [show (logarithmicPrimePhase c q + logarithmicPrimePhase c q) / 2 =
      logarithmicPrimePhase c q by ring] at h
  exact h

/-- Prime-power locations strictly below the cutoff `13`. -/
def c13PrimePowerLocation : Fin 8 → ℝ :=
  ![2, 3, 4, 5, 7, 8, 9, 11]

/-- Underlying prime at each tracked prime-power location. -/
def c13PrimePowerBase : Fin 8 → ℝ :=
  ![2, 3, 2, 5, 7, 2, 3, 11]

/-- The exact tracked finite prime symbol at cutoff `13`. -/
noncomputable def c13FiniteLogarithmicPrimeSymbol : ℝ → ℝ :=
  finiteLogarithmicPrimeSymbol 13 c13PrimePowerLocation c13PrimePowerBase

theorem c13PrimePowerLocation_bounds (i : Fin 8) :
    1 < c13PrimePowerLocation i ∧ c13PrimePowerLocation i < 13 := by
  fin_cases i <;> norm_num [c13PrimePowerLocation]

theorem c13PrimePowerLocation_injective :
    Function.Injective c13PrimePowerLocation := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [c13PrimePowerLocation]

theorem c13PrimePowerLocation_mul_ne_thirteen (i j : Fin 8) :
    c13PrimePowerLocation i * c13PrimePowerLocation j ≠ 13 := by
  fin_cases i <;> fin_cases j <;> norm_num [c13PrimePowerLocation]

theorem c13PrimePhase_half_sin_pos (i : Fin 8) :
    0 < Real.sin
      (logarithmicPrimePhase 13 (c13PrimePowerLocation i) / 2) := by
  rcases c13PrimePowerLocation_bounds i with ⟨hiOne, hiThirteen⟩
  exact logarithmicPrimePhase_half_sin_pos
    13 (c13PrimePowerLocation i) (by norm_num) hiOne hiThirteen

theorem c13PrimePhase_sin_ne_zero (i : Fin 8) :
    Real.sin (logarithmicPrimePhase 13 (c13PrimePowerLocation i)) ≠ 0 := by
  rcases c13PrimePowerLocation_bounds i with ⟨hiOne, hiThirteen⟩
  exact logarithmicPrimePhase_sin_ne_zero
    13 (c13PrimePowerLocation i) (by norm_num) hiOne hiThirteen
    (by simpa [pow_two] using c13PrimePowerLocation_mul_ne_thirteen i i)

theorem c13PrimePhase_add_half_sin_ne_zero (i j : Fin 8) :
    Real.sin
        ((logarithmicPrimePhase 13 (c13PrimePowerLocation i) +
          logarithmicPrimePhase 13 (c13PrimePowerLocation j)) / 2) ≠ 0 := by
  rcases c13PrimePowerLocation_bounds i with ⟨hiOne, hiThirteen⟩
  rcases c13PrimePowerLocation_bounds j with ⟨hjOne, hjThirteen⟩
  exact logarithmicPrimePhase_add_half_sin_ne_zero
    13 (c13PrimePowerLocation i) (c13PrimePowerLocation j)
    (by norm_num) hiOne hjOne hiThirteen hjThirteen
    (c13PrimePowerLocation_mul_ne_thirteen i j)

theorem c13PrimePhase_sub_half_sin_ne_zero
    (i j : Fin 8) (hij : i ≠ j) :
    Real.sin
        ((logarithmicPrimePhase 13 (c13PrimePowerLocation i) -
          logarithmicPrimePhase 13 (c13PrimePowerLocation j)) / 2) ≠ 0 := by
  have hLocationNe : c13PrimePowerLocation i ≠ c13PrimePowerLocation j :=
    fun h => hij (c13PrimePowerLocation_injective h)
  rcases c13PrimePowerLocation_bounds i with ⟨hiOne, hiThirteen⟩
  rcases c13PrimePowerLocation_bounds j with ⟨hjOne, hjThirteen⟩
  rcases lt_or_gt_of_ne hLocationNe with hlt | hgt
  · exact ne_of_lt (logarithmicPrimePhase_sub_half_sin_neg
      13 (c13PrimePowerLocation i) (c13PrimePowerLocation j)
      (by norm_num) hiOne hlt hjThirteen)
  · have hneg := logarithmicPrimePhase_sub_half_sin_neg
      13 (c13PrimePowerLocation j) (c13PrimePowerLocation i)
      (by norm_num) hjOne hgt hiThirteen
    rw [show (logarithmicPrimePhase 13 (c13PrimePowerLocation i) -
        logarithmicPrimePhase 13 (c13PrimePowerLocation j)) / 2 =
        -((logarithmicPrimePhase 13 (c13PrimePowerLocation j) -
          logarithmicPrimePhase 13 (c13PrimePowerLocation i)) / 2) by ring,
      Real.sin_neg]
    exact neg_ne_zero.mpr (ne_of_lt hneg)

/-- All single, doubled, pair-difference, and pair-sum phase denominators used
by the cutoff-13 certificate are symbolically nonresonant. -/
theorem c13PrimePhase_all_nonresonant :
    (∀ i : Fin 8,
      Real.sin (logarithmicPrimePhase 13 (c13PrimePowerLocation i) / 2) ≠ 0) ∧
    (∀ i : Fin 8,
      Real.sin (logarithmicPrimePhase 13 (c13PrimePowerLocation i)) ≠ 0) ∧
    (∀ i j : Fin 8, i ≠ j →
      Real.sin
        ((logarithmicPrimePhase 13 (c13PrimePowerLocation i) -
          logarithmicPrimePhase 13 (c13PrimePowerLocation j)) / 2) ≠ 0) ∧
    (∀ i j : Fin 8,
      Real.sin
        ((logarithmicPrimePhase 13 (c13PrimePowerLocation i) +
          logarithmicPrimePhase 13 (c13PrimePowerLocation j)) / 2) ≠ 0) := by
  exact ⟨fun i => ne_of_gt (c13PrimePhase_half_sin_pos i),
    c13PrimePhase_sin_ne_zero,
    c13PrimePhase_sub_half_sin_ne_zero,
    c13PrimePhase_add_half_sin_ne_zero⟩

/-- The even-parity weighted numerator is controlled by pointwise symbol
amplitudes. -/
theorem evenWeightedNumerator_abs_le
    (symbol : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M) :
    |q * symbol q - p * symbol p| ≤ (p + q) * M := by
  calc
    |q * symbol q - p * symbol p| ≤
        |q * symbol q| + |p * symbol p| := abs_sub _ _
    _ = q * |symbol q| + p * |symbol p| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hp]
    _ ≤ q * M + p * M :=
      add_le_add
        (mul_le_mul_of_nonneg_left hqSymbol hq)
        (mul_le_mul_of_nonneg_left hpSymbol hp)
    _ = (p + q) * M := by ring

/-- The odd-parity weighted numerator obeys the same amplitude bound. -/
theorem oddWeightedNumerator_abs_le
    (symbol : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M) :
    |p * symbol q - q * symbol p| ≤ (p + q) * M := by
  calc
    |p * symbol q - q * symbol p| ≤
        |p * symbol q| + |q * symbol p| := abs_sub _ _
    _ = p * |symbol q| + q * |symbol p| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ p * M + q * M :=
      add_le_add
        (mul_le_mul_of_nonneg_left hqSymbol hp)
        (mul_le_mul_of_nonneg_left hpSymbol hq)
    _ = (p + q) * M := by ring

/-- Off the reflection diagonals, an even-parity Loewner entry is at most
`2*M/(q-p)` for positive ordered modes. -/
theorem oddDifferenceKernel_evenParity_abs_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hpq : p < q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      2 * M / (q - p) := by
  have hq : 0 ≤ q := le_trans hp (le_of_lt hpq)
  have hpNeQ : p ≠ q := ne_of_lt hpq
  have hpNeNegQ : p ≠ -q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hAdd : 0 < p + q := by linarith
  have hDen : 0 < (q - p) * (p + q) := mul_pos hSub hAdd
  have hDenAbs : |p ^ 2 - q ^ 2| = (q - p) * (p + q) := by
    rw [abs_of_neg]
    · ring
    · nlinarith
  rw [CvSParityDisplacement.oddDifferenceKernel_evenParity_offDiagonal
    symbol diagonal p q hpNeQ hpNeNegQ hOdd, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hDenAbs]
  have hNum := evenWeightedNumerator_abs_le symbol p q M hp hq
    hpSymbol hqSymbol
  calc
    2 * |q * symbol q - p * symbol p| / ((q - p) * (p + q)) ≤
        2 * ((p + q) * M) / ((q - p) * (p + q)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNum (by norm_num)) (le_of_lt hDen)
    _ = 2 * M / (q - p) := by
      field_simp [ne_of_gt hSub, ne_of_gt hAdd]

/-- Off the reflection diagonals, an odd-parity Loewner entry has the same
ordered-mode bound. -/
theorem oddDifferenceKernel_oddParity_abs_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hpq : p < q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      2 * M / (q - p) := by
  have hq : 0 ≤ q := le_trans hp (le_of_lt hpq)
  have hpNeQ : p ≠ q := ne_of_lt hpq
  have hpNeNegQ : p ≠ -q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hAdd : 0 < p + q := by linarith
  have hDen : 0 < (q - p) * (p + q) := mul_pos hSub hAdd
  have hDenAbs : |p ^ 2 - q ^ 2| = (q - p) * (p + q) := by
    rw [abs_of_neg]
    · ring
    · nlinarith
  rw [CvSParityDisplacement.oddDifferenceKernel_oddParity_offDiagonal
    symbol diagonal p q hpNeQ hpNeNegQ hOdd, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hDenAbs]
  have hNum := oddWeightedNumerator_abs_le symbol p q M hp hq
    hpSymbol hqSymbol
  calc
    2 * |p * symbol q - q * symbol p| / ((q - p) * (p + q)) ≤
        2 * ((p + q) * M) / ((q - p) * (p + q)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNum (by norm_num)) (le_of_lt hDen)
    _ = 2 * M / (q - p) := by
      field_simp [ne_of_gt hSub, ne_of_gt hAdd]

/-- A factor-two mode separation improves the even-parity entry to `4*M/q`. -/
theorem oddDifferenceKernel_evenParity_abs_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      4 * M / q := by
  have hpq : p < q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  calc
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
        2 * M / (q - p) :=
      oddDifferenceKernel_evenParity_abs_le symbol diagonal p q M hp hpq
        hpSymbol hqSymbol hOdd
    _ ≤ 4 * M / q := by
      rw [div_le_div_iff₀ hSub hq]
      have hProduct : 0 ≤ 2 * M * (q - 2 * p) := by positivity
      nlinarith

/-- A factor-two mode separation gives the same `4*M/q` odd-parity bound. -/
theorem oddDifferenceKernel_oddParity_abs_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
      4 * M / q := by
  have hpq : p < q := by linarith
  have hSub : 0 < q - p := sub_pos.mpr hpq
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  calc
    |CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)| ≤
        2 * M / (q - p) :=
      oddDifferenceKernel_oddParity_abs_le symbol diagonal p q M hp hpq
        hpSymbol hqSymbol hOdd
    _ ≤ 4 * M / q := by
      rw [div_le_div_iff₀ hSub hq]
      have hProduct : 0 ≤ 2 * M * (q - 2 * p) := by positivity
      nlinarith

/-- Squared even-parity entry budget on a factor-two separated block. -/
theorem oddDifferenceKernel_evenParity_sq_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (4 * M / q) ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  have hRight : 0 ≤ 4 * M / q := by positivity
  have hAbs := oddDifferenceKernel_evenParity_abs_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSq := (sq_le_sq₀
    (abs_nonneg
      (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)))
    hRight).2 hAbs
  simpa only [sq_abs] using hSq

/-- Squared odd-parity entry budget on a factor-two separated block. -/
theorem oddDifferenceKernel_oddParity_sq_le_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q M : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hpSymbol : |symbol p| ≤ M) (hqSymbol : |symbol q| ≤ M)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      (4 * M / q) ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (symbol p)).trans hpSymbol
  have hRight : 0 ≤ 4 * M / q := by positivity
  have hAbs := oddDifferenceKernel_oddParity_abs_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSq := (sq_le_sq₀
    (abs_nonneg
      (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)))
    hRight).2 hAbs
  simpa only [sq_abs] using hSq

/-- Squaring the sum of two absolute values costs at most a factor two. -/
theorem abs_add_sq_le_two_mul_sum_sq (a b : ℝ) :
    (|a| + |b|) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (|a| - |b|)]

/-- A separated even-parity entry is controlled directly by the two symbol
squares carrying the dyadic reciprocal-square weight. -/
theorem oddDifferenceKernel_evenParity_sq_le_symbolSquares_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
  let M := |symbol p| + |symbol q|
  have hpSymbol : |symbol p| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol q)]
  have hqSymbol : |symbol q| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol p)]
  have hEntry := oddDifferenceKernel_evenParity_sq_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSumSq : M ^ 2 ≤ 2 * (symbol p ^ 2 + symbol q ^ 2) := by
    simpa only [M] using abs_add_sq_le_two_mul_sum_sq (symbol p) (symbol q)
  have hNumerator : 16 * M ^ 2 ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) := by
    nlinarith
  have hDen : 0 ≤ q ^ 2 := sq_nonneg q
  calc
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
        (4 * M / q) ^ 2 := hEntry
    _ = 16 * M ^ 2 / q ^ 2 := by ring
    _ ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) / q ^ 2 :=
      div_le_div_of_nonneg_right hNumerator hDen
    _ = 32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
      ring

/-- The same symbol-square dyadic weight controls a separated odd-parity
entry. -/
theorem oddDifferenceKernel_oddParity_sq_le_symbolSquares_of_two_mul_le
    (symbol diagonal : ℝ → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hsep : 2 * p ≤ q)
    (hOdd : Function.Odd symbol) :
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
      32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
  let M := |symbol p| + |symbol q|
  have hpSymbol : |symbol p| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol q)]
  have hqSymbol : |symbol q| ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (symbol p)]
  have hEntry := oddDifferenceKernel_oddParity_sq_le_of_two_mul_le
    symbol diagonal p q M hp hq hsep hpSymbol hqSymbol hOdd
  have hSumSq : M ^ 2 ≤ 2 * (symbol p ^ 2 + symbol q ^ 2) := by
    simpa only [M] using abs_add_sq_le_two_mul_sum_sq (symbol p) (symbol q)
  have hNumerator : 16 * M ^ 2 ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) := by
    nlinarith
  have hDen : 0 ≤ q ^ 2 := sq_nonneg q
  calc
    (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p q -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p (-q)) ^ 2 ≤
        (4 * M / q) ^ 2 := hEntry
    _ = 16 * M ^ 2 / q ^ 2 := by ring
    _ ≤ 32 * (symbol p ^ 2 + symbol q ^ 2) / q ^ 2 :=
      div_le_div_of_nonneg_right hNumerator hDen
    _ = 32 * (symbol q ^ 2 / q ^ 2 + symbol p ^ 2 / q ^ 2) := by
      ring

/-- A column-wise entry-square budget sums with only the row cardinality. -/
theorem rectangular_sum_sq_le_card_mul_columnBudget
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (columnBudget : κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      (entry i j) ^ 2 ≤ columnBudget j) :
    (∑ i ∈ rows, ∑ j ∈ columns, (entry i j) ^ 2) ≤
      rows.card * ∑ j ∈ columns, columnBudget j := by
  calc
    (∑ i ∈ rows, ∑ j ∈ columns, (entry i j) ^ 2) ≤
        ∑ i ∈ rows, ∑ j ∈ columns, columnBudget j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hEntry i hi j hj
    _ = rows.card * ∑ j ∈ columns, columnBudget j := by
      simp

/-- Finite Cauchy--Schwarz for a rectangular bilinear form. -/
theorem rectangular_bilinear_sq_le_entry_sq_mul_norms
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (∑ ij ∈ rows ×ˢ columns,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) *
        ((∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2) := by
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (rows ×ˢ columns)
    (fun ij => entry ij.1 ij.2)
    (fun ij => x ij.1 * y ij.2)
  have hFactor :
      (∑ ij ∈ rows ×ˢ columns, (x ij.1 * y ij.2) ^ 2) =
        (∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2 := by
    rw [Finset.sum_product]
    simpa only [mul_pow] using
      (Finset.sum_mul_sum rows columns
        (fun i => (x i) ^ 2) (fun j => (y j) ^ 2)).symm
  rw [hFactor] at hCauchy
  exact hCauchy

/-- Rectangular Cauchy--Schwarz after applying a column-wise square budget. -/
theorem rectangular_bilinear_sq_le_card_mul_columnBudget_mul_norms
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (columnBudget : κ → ℝ)
    (x : ι → ℝ) (y : κ → ℝ)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      (entry i j) ^ 2 ≤ columnBudget j) :
    (∑ ij ∈ rows ×ˢ columns,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (rows.card * ∑ j ∈ columns, columnBudget j) *
        ((∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2) := by
  have hBilinear := rectangular_bilinear_sq_le_entry_sq_mul_norms
    rows columns entry x y
  have hEntries := rectangular_sum_sq_le_card_mul_columnBudget
    rows columns entry columnBudget hEntry
  have hEntriesProduct :
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) ≤
        rows.card * ∑ j ∈ columns, columnBudget j := by
    rw [Finset.sum_product]
    exact hEntries
  have hNorms :
      0 ≤ (∑ i ∈ rows, (x i) ^ 2) * ∑ j ∈ columns, (y j) ^ 2 := by
    positivity
  have hScale := mul_le_mul_of_nonneg_right hEntriesProduct hNorms
  exact hBilinear.trans hScale

/-- The reciprocal-square mass of one dyadic shell is at most `1/(2*N)`. -/
theorem dyadic_sum_inv_sq_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹)) ≤
      1 / (2 * (N : ℝ)) := by
  have hNle : N ≤ 2 * N := by omega
  have hBase := sum_Ioc_inv_sq_le_sub (α := ℝ) hN hNle
  calc
    (∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹)) ≤
        ((N : ℝ)⁻¹ - ((2 * N : ℕ) : ℝ)⁻¹) := hBase
    _ = 1 / (2 * (N : ℝ)) := by
      have hNReal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      push_cast
      field_simp [hNReal]
      ring

/-- Scaled reciprocal-square dyadic mass. -/
theorem dyadic_sum_scaled_inv_sq_le
    (N : ℕ) (hN : N ≠ 0) (C : ℝ) (hC : 0 ≤ C) :
    (∑ j ∈ Ioc N (2 * N), C * (((j : ℝ) ^ 2)⁻¹)) ≤
      C / (2 * (N : ℝ)) := by
  rw [← Finset.mul_sum]
  have hBase := dyadic_sum_inv_sq_le N hN
  have hScaled := mul_le_mul_of_nonneg_left hBase hC
  calc
    C * ∑ j ∈ Ioc N (2 * N), (((j : ℝ) ^ 2)⁻¹) ≤
        C * (1 / (2 * (N : ℝ))) := hScaled
    _ = C / (2 * (N : ℝ)) := by simp [div_eq_mul_inv]

/-- Abel upper bound supplied by an affine bound for every inclusive prefix. -/
theorem weightedSum_le_of_prefix_le_affine
    (r weight : ℕ → ℝ) (N : ℕ) (A B : ℝ)
    (hPrefix : ∀ j, j ≤ N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B)
    (hLastWeight : 0 ≤ weight N)
    (hWeightDecreasing : ∀ j, j < N → weight (j + 1) ≤ weight j) :
    (∑ j ∈ Finset.range (N + 1), r j * weight j) ≤
      A * (∑ j ∈ Finset.range (N + 1), weight j) + B * weight 0 := by
  let upper : ℕ → ℝ := fun j => A + if j = 0 then B else 0
  have hUpperPrefix : ∀ j,
      BoundaryWeylCumulative.prefixSum upper j = A * (j + 1) + B := by
    intro j
    induction j with
    | zero =>
        simp [BoundaryWeylCumulative.prefixSum, upper]
    | succ j ih =>
        rw [BoundaryWeylCumulative.prefixSum_succ, ih]
        simp [upper]
        ring
  have hFinal :
      BoundaryWeylCumulative.prefixSum r N * weight N ≤
        BoundaryWeylCumulative.prefixSum upper N * weight N := by
    apply mul_le_mul_of_nonneg_right _ hLastWeight
    rw [hUpperPrefix]
    exact hPrefix N le_rfl
  have hDrops :
      (∑ j ∈ Finset.range N,
          BoundaryWeylCumulative.prefixSum r j *
            (weight j - weight (j + 1))) ≤
        ∑ j ∈ Finset.range N,
          BoundaryWeylCumulative.prefixSum upper j *
            (weight j - weight (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    apply mul_le_mul_of_nonneg_right
    · rw [hUpperPrefix]
      exact hPrefix j (Nat.le_of_lt hjN)
    · exact sub_nonneg.mpr (hWeightDecreasing j hjN)
  calc
    (∑ j ∈ Finset.range (N + 1), r j * weight j) =
        BoundaryWeylCumulative.prefixSum r N * weight N +
          ∑ j ∈ Finset.range N,
            BoundaryWeylCumulative.prefixSum r j *
              (weight j - weight (j + 1)) :=
      BoundaryWeylCumulative.finiteAbelSummation r weight N
    _ ≤ BoundaryWeylCumulative.prefixSum upper N * weight N +
          ∑ j ∈ Finset.range N,
            BoundaryWeylCumulative.prefixSum upper j *
              (weight j - weight (j + 1)) :=
      add_le_add hFinal hDrops
    _ = ∑ j ∈ Finset.range (N + 1), upper j * weight j :=
      (BoundaryWeylCumulative.finiteAbelSummation upper weight N).symm
    _ = A * (∑ j ∈ Finset.range (N + 1), weight j) +
          B * weight 0 := by
      simp only [upper, add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp

/-- Reindex the positive dyadic shell as a zero-based range. -/
theorem dyadic_shifted_weight_sum_eq
    (N : ℕ) :
    (∑ k ∈ range N, ((((N + 1 + k : ℕ) : ℝ) ^ 2)⁻¹)) =
      ∑ j ∈ Ioc N (2 * N), ((((j : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hSets : Ioc N (2 * N) = Ico (N + 1) (2 * N + 1) := by
    ext j
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hSets, sum_Ico_eq_sum_range]
  have hLength : 2 * N + 1 - (N + 1) = N := by omega
  rw [hLength]

/-- Zero-based form of the dyadic reciprocal-square estimate. -/
theorem dyadic_shifted_weight_sum_le
    (N : ℕ) (hN : N ≠ 0) :
    (∑ k ∈ range N, ((((N + 1 + k : ℕ) : ℝ) ^ 2)⁻¹)) ≤
      1 / (2 * (N : ℝ)) := by
  rw [dyadic_shifted_weight_sum_eq]
  exact dyadic_sum_inv_sq_le N hN

/-- Affine prefix control plus Abel summation gives an explicit weighted
dyadic estimate. -/
theorem dyadic_weighted_sum_le_of_prefix_le_affine
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0) (A B : ℝ) (hA : 0 ≤ A)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
      A / (2 * (N : ℝ)) +
        B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  let weight : ℕ → ℝ :=
    fun j => ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hLength : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  have hLastWeight : 0 ≤ weight (N - 1) := by
    positivity
  have hWeightDecreasing : ∀ j, j < N - 1 →
      weight (j + 1) ≤ weight j := by
    intro j _hj
    dsimp only [weight]
    have hBasePos : 0 < ((N + 1 + j : ℕ) : ℝ) := by positivity
    have hStep :
        ((N + 1 + j : ℕ) : ℝ) ≤
          ((N + 1 + (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ (N + 1 + j))
    have hSq :
        (((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
          (((N + 1 + (j + 1) : ℕ) : ℝ) ^ 2) := by
      nlinarith
    exact inv_anti₀ (sq_pos_of_pos hBasePos) hSq
  have hAbel := weightedSum_le_of_prefix_le_affine
    r weight (N - 1) A B
    (fun j hj => hPrefix j (by omega))
    hLastWeight hWeightDecreasing
  rw [hLength] at hAbel
  have hWeights :
      (∑ j ∈ range N, weight j) ≤ 1 / (2 * (N : ℝ)) := by
    simpa only [weight] using dyadic_shifted_weight_sum_le N hN
  have hScaled := mul_le_mul_of_nonneg_left hWeights hA
  calc
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        A * (∑ j ∈ range N, weight j) + B * weight 0 := by
      simpa only [weight] using hAbel
    _ ≤ A * (1 / (2 * (N : ℝ))) + B * weight 0 :=
      add_le_add hScaled le_rfl
    _ = A / (2 * (N : ℝ)) +
          B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      simp [weight, div_eq_mul_inv]

/-- A strict scaled endpoint check turns the Abel upper bound into the target
`sum < 1/N`. -/
theorem dyadic_weighted_sum_lt_one_div_of_prefix_le_affine
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0) (A B : ℝ) (hA : 0 ≤ A)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤ A * (j + 1) + B)
    (hScaled :
      A / 2 + B * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  have hUpper := dyadic_weighted_sum_le_of_prefix_le_affine
    r N hN A B hA hPrefix
  have hNReal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        A / (2 * (N : ℝ)) +
          B * ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := hUpper
    _ = (1 / (N : ℝ)) *
          (A / 2 + B * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2)) := by
      field_simp [hNReal]
    _ < (1 / (N : ℝ)) * 1 :=
      mul_lt_mul_of_pos_left hScaled (by positivity)
    _ = 1 / (N : ℝ) := by ring

/-- Exact endpoint expression certified by the companion Arb script. -/
noncomputable def dyadicEndpointScaledUpper
    (main linear quadratic geometric : ℝ) (N : ℕ) : ℝ :=
  (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) / 2 +
    geometric * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2)

/-- The factor `N/(N+1)^2` decreases on positive natural modes. -/
theorem natCast_div_succ_sq_antitone
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (M : ℝ) / (((M + 1 : ℕ) : ℝ) ^ 2) ≤
      (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNMReal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hMReal : (1 : ℝ) ≤ M := hNReal.trans hNMReal
  have hNDen : 0 < (((N + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hMDen : 0 < (((M + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [div_le_div_iff₀ hMDen hNDen]
  push_cast
  have hFirst : 0 ≤ (M : ℝ) - N := sub_nonneg.mpr hNMReal
  have hSecond : 0 ≤ (N : ℝ) * M - 1 := by nlinarith
  have hProduct :
      0 ≤ ((M : ℝ) - N) * ((N : ℝ) * M - 1) :=
    mul_nonneg hFirst hSecond
  nlinarith

/-- The complete scaled endpoint is antitone once all decaying coefficients
are nonnegative. -/
theorem dyadicEndpointScaledUpper_antitone
    (main linear quadratic geometric : ℝ) (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M)
    (hLinear : 0 ≤ linear) (hQuadratic : 0 ≤ quadratic)
    (hGeometric : 0 ≤ geometric) :
    dyadicEndpointScaledUpper main linear quadratic geometric M ≤
      dyadicEndpointScaledUpper main linear quadratic geometric N := by
  have hNPos : 0 < (N : ℝ) := by positivity
  have hNMReal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hInv :
      1 / (M : ℝ) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNPos hNMReal
  have hInvSq :
      1 / (M : ℝ) ^ 2 ≤ 1 / (N : ℝ) ^ 2 := by
    have hNInv : 0 ≤ 1 / (N : ℝ) := by positivity
    have hMInv : 0 ≤ 1 / (M : ℝ) := by positivity
    have hSq := (sq_le_sq₀ hMInv hNInv).2 hInv
    simpa [one_div, inv_pow] using hSq
  have hLinearTerm :
      linear / (M : ℝ) ≤ linear / (N : ℝ) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInv hLinear
  have hQuadraticTerm :
      quadratic / (M : ℝ) ^ 2 ≤ quadratic / (N : ℝ) ^ 2 := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hInvSq hQuadratic
  have hGeometricRatio := natCast_div_succ_sq_antitone N M hN hNM
  have hGeometricTerm :
      geometric * (M : ℝ) / (((M + 1 : ℕ) : ℝ) ^ 2) ≤
        geometric * (N : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hGeometricRatio hGeometric
  unfold dyadicEndpointScaledUpper
  have hSlope :
      main + linear / (M : ℝ) + quadratic / (M : ℝ) ^ 2 ≤
        main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2 :=
    add_le_add (add_le_add le_rfl hLinearTerm) hQuadraticTerm
  exact add_le_add
    (div_le_div_of_nonneg_right hSlope (by norm_num))
    hGeometricTerm

/-- One strict endpoint certificate controls every later natural mode. -/
theorem dyadicEndpointScaledUpper_lt_one_of_start
    (main linear quadratic geometric : ℝ) (start N : ℕ)
    (hStart : 1 ≤ start) (hStartN : start ≤ N)
    (hLinear : 0 ≤ linear) (hQuadratic : 0 ≤ quadratic)
    (hGeometric : 0 ≤ geometric)
    (hEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric start < 1) :
    dyadicEndpointScaledUpper main linear quadratic geometric N < 1 :=
  (dyadicEndpointScaledUpper_antitone
    main linear quadratic geometric start N hStart hStartN
    hLinear hQuadratic hGeometric).trans_lt hEndpoint

/-- Direct interface from the Arb endpoint expression to one weighted shell. -/
theorem dyadic_weighted_sum_lt_one_div_of_endpoint
    (r : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0)
    (main linear quadratic geometric : ℝ)
    (hSlope :
      0 ≤ main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤
        (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) *
          (j + 1) + geometric)
    (hEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric N < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  apply dyadic_weighted_sum_lt_one_div_of_prefix_le_affine
    r N hN
    (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2)
    geometric hSlope hPrefix
  simpa only [dyadicEndpointScaledUpper] using hEndpoint

/-- A strict start-mode endpoint plus nonnegative coefficients controls every
later weighted shell once its source prefix bound has been identified. -/
theorem dyadic_weighted_sum_lt_one_div_of_start_endpoint
    (r : ℕ → ℝ) (start N : ℕ)
    (main linear quadratic geometric : ℝ)
    (hStart : 1 ≤ start) (hStartN : start ≤ N)
    (hMain : 0 ≤ main) (hLinear : 0 ≤ linear)
    (hQuadratic : 0 ≤ quadratic) (hGeometric : 0 ≤ geometric)
    (hPrefix : ∀ j, j < N →
      BoundaryWeylCumulative.prefixSum r j ≤
        (main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2) *
          (j + 1) + geometric)
    (hStartEndpoint :
      dyadicEndpointScaledUpper main linear quadratic geometric start < 1) :
    (∑ j ∈ range N,
        r j * ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) <
      1 / (N : ℝ) := by
  have hN : N ≠ 0 := by omega
  have hSlope :
      0 ≤ main + linear / (N : ℝ) + quadratic / (N : ℝ) ^ 2 := by
    positivity
  have hEndpoint := dyadicEndpointScaledUpper_lt_one_of_start
    main linear quadratic geometric start N hStart hStartN
    hLinear hQuadratic hGeometric hStartEndpoint
  exact dyadic_weighted_sum_lt_one_div_of_endpoint
    r N hN main linear quadratic geometric hSlope hPrefix hEndpoint

/-!
## Rowwise matrix and relative-energy bridge

The following adapters turn the dyadic symbol-square estimate into finite
matrix, coercive-energy, newest-band, and exact half-transport budgets.
-/

/-- A finite family of absolute perturbation bounds yields the exact coercive
floor used by the relative-energy adapters.  This separates the concrete CvS
component estimates from the universal real-algebra step. -/
theorem coerciveFloor_of_componentBounds
    {ι : Type*} [Fintype ι]
    (energy diagonal normSq diagonalFloor shift floor : ℝ)
    (error errorBound : ι → ℝ)
    (hNormSq : 0 ≤ normSq)
    (hEnergy :
      energy = diagonal + (∑ i, error i) + shift * normSq)
    (hDiagonal : diagonalFloor * normSq ≤ diagonal)
    (hError : ∀ i, |error i| ≤ errorBound i * normSq)
    (hFloor :
      floor ≤ diagonalFloor - (∑ i, errorBound i) + shift) :
    floor * normSq ≤ energy := by
  have hEach : ∀ i, -(errorBound i * normSq) ≤ error i := by
    intro i
    exact neg_le_of_abs_le (hError i)
  have hErrorSum :
      (∑ i, -(errorBound i * normSq)) ≤ ∑ i, error i := by
    exact Finset.sum_le_sum fun i _hi => hEach i
  have hErrorLower :
      -(∑ i, errorBound i) * normSq ≤ ∑ i, error i := by
    calc
      -(∑ i, errorBound i) * normSq =
          ∑ i, -(errorBound i * normSq) := by
        rw [← Finset.sum_neg_distrib, Finset.sum_mul]
        simp only [neg_mul]
      _ ≤ ∑ i, error i := hErrorSum
  have hFloorScaled := mul_le_mul_of_nonneg_right hFloor hNormSq
  rw [hEnergy]
  nlinarith

/-- Scaling the concrete symbol scales its dyadic square budget by the exact
square of the normalization factor.  In the CvS source identification this
retains the Fourier normalization `1 / π` as `1 / π²`. -/
theorem scaled_shifted_symbolSquareBudget
    (symbol : ℝ → ℝ) (scale C : ℝ) (N : ℕ)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (scale * symbol ((N + 1 + j : ℕ) : ℝ)) ^ 2 /
          ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      (scale ^ 2 * C) / (N : ℝ) := by
  have hRewrite :
      (∑ j ∈ range N,
          (scale * symbol ((N + 1 + j : ℕ) : ℝ)) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) =
        scale ^ 2 *
          ∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hRewrite]
  calc
    scale ^ 2 *
        (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      scale ^ 2 * (C / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hSymbol (sq_nonneg scale)
    _ = (scale ^ 2 * C) / (N : ℝ) := by ring

/-- On a dyadic band `(N,2N]`, a weighted symbol-square budget controls the
ordinary square sum with the sharp elementary loss `(2N)²`. -/
theorem shifted_symbolSquare_sum_le_four_mul
    (symbol : ℝ → ℝ) (C : ℝ) (N : ℕ) (hN : N ≠ 0)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      4 * C * (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hBand : ∀ j ∈ range N,
      (((N + 1 + j : ℕ) : ℝ) ^ 2) ≤ (2 * (N : ℝ)) ^ 2 := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hNat : N + 1 + j ≤ 2 * N := by omega
    have hReal : ((N + 1 + j : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hNat
    exact sq_le_sq₀ (by positivity) (by positivity) |>.2 hReal
  have hTermwise :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        (2 * (N : ℝ)) ^ 2 *
          ∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    let mode : ℝ := ((N + 1 + j : ℕ) : ℝ)
    have hModePos : 0 < mode := by
      dsimp only [mode]
      positivity
    have hModeNe : mode ≠ 0 := ne_of_gt hModePos
    have hWeightNonnegative :
        0 ≤ symbol mode ^ 2 / mode ^ 2 := by positivity
    calc
      symbol mode ^ 2 = mode ^ 2 * (symbol mode ^ 2 / mode ^ 2) := by
        field_simp [hModeNe]
      _ ≤ (2 * (N : ℝ)) ^ 2 * (symbol mode ^ 2 / mode ^ 2) :=
        mul_le_mul_of_nonneg_right (hBand j hj) hWeightNonnegative
  calc
    (∑ j ∈ range N,
        symbol ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
      (2 * (N : ℝ)) ^ 2 *
        ∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2 := hTermwise
    _ ≤ (2 * (N : ℝ)) ^ 2 * (C / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hSymbol (sq_nonneg (2 * (N : ℝ)))
    _ = 4 * C * (N : ℝ) := by
      field_simp [hNR]
      ring

theorem shifted_entry_sum_sq_le_of_symbolSquareBudget
    (entry : ℕ → ℝ) (symbol : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hEntry : ∀ j ∈ range N,
      entry j ^ 2 ≤
        32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2 +
            symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2))
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N, entry j ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  have hEntries :
      (∑ j ∈ range N, entry j ^ 2) ≤
        ∑ j ∈ range N,
          32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
                ((N + 1 + j : ℕ) : ℝ) ^ 2 +
              symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hEntry j hj
  have hReciprocal := dyadic_shifted_weight_sum_le N hN
  have hFixed :
      symbol p ^ 2 *
          (∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        symbol p ^ 2 * (1 / (2 * (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hReciprocal (sq_nonneg (symbol p))
  have hFixedRewrite :
      (∑ j ∈ range N,
          symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) =
        symbol p ^ 2 *
          ∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [div_eq_mul_inv]
  calc
    (∑ j ∈ range N, entry j ^ 2) ≤
        ∑ j ∈ range N,
          32 * (symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
                ((N + 1 + j : ℕ) : ℝ) ^ 2 +
              symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := hEntries
    _ = 32 *
          (∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2) +
        32 *
          (∑ j ∈ range N,
            symbol p ^ 2 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 32 * (
          (∑ j ∈ range N,
            symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
              ((N + 1 + j : ℕ) : ℝ) ^ 2) +
          symbol p ^ 2 *
            ∑ j ∈ range N, ((((N + 1 + j : ℕ) : ℝ) ^ 2)⁻¹)) := by
      rw [hFixedRewrite]
      ring
    _ ≤ 32 * (C / (N : ℝ) + symbol p ^ 2 * (1 / (2 * (N : ℝ)))) := by
      gcongr
    _ = 32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
      simp [div_eq_mul_inv]

theorem evenParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    (symbol diagonal : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hp : 0 ≤ p)
    (hsep : ∀ j, j < N → 2 * p ≤ ((N + 1 + j : ℕ) : ℝ))
    (hOdd : Function.Odd symbol)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            ((N + 1 + j : ℕ) : ℝ) +
          CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            (-((N + 1 + j : ℕ) : ℝ))) ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  apply shifted_entry_sum_sq_le_of_symbolSquareBudget
    (fun j =>
      CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          ((N + 1 + j : ℕ) : ℝ) +
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          (-((N + 1 + j : ℕ) : ℝ)))
    symbol p N hN C
  · intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact oddDifferenceKernel_evenParity_sq_le_symbolSquares_of_two_mul_le
      symbol diagonal p ((N + 1 + j : ℕ) : ℝ) hp (by positivity)
      (hsep j hjN) hOdd
  · exact hSymbol

theorem oddParity_fixedRow_sum_sq_le_of_symbolSquareBudget
    (symbol diagonal : ℝ → ℝ) (p : ℝ)
    (N : ℕ) (hN : N ≠ 0) (C : ℝ)
    (hp : 0 ≤ p)
    (hsep : ∀ j, j < N → 2 * p ≤ ((N + 1 + j : ℕ) : ℝ))
    (hOdd : Function.Odd symbol)
    (hSymbol :
      (∑ j ∈ range N,
          symbol ((N + 1 + j : ℕ) : ℝ) ^ 2 /
            ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤
        C / (N : ℝ)) :
    (∑ j ∈ range N,
        (CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            ((N + 1 + j : ℕ) : ℝ) -
          CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
            (-((N + 1 + j : ℕ) : ℝ))) ^ 2) ≤
      32 * (C / (N : ℝ) + symbol p ^ 2 / (2 * (N : ℝ))) := by
  apply shifted_entry_sum_sq_le_of_symbolSquareBudget
    (fun j =>
      CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          ((N + 1 + j : ℕ) : ℝ) -
        CvSParityDisplacement.oddDifferenceKernel symbol diagonal p
          (-((N + 1 + j : ℕ) : ℝ)))
    symbol p N hN C
  · intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact oddDifferenceKernel_oddParity_sq_le_symbolSquares_of_two_mul_le
      symbol diagonal p ((N + 1 + j : ℕ) : ℝ) hp (by positivity)
      (hsep j hjN) hOdd
  · exact hSymbol

theorem rectangular_sum_sq_le_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (N : ℕ) (C : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ)))) :
    (∑ i ∈ rows, ∑ j ∈ range N, entry i j ^ 2) ≤
      32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
  have hDivSum :
      (∑ i ∈ rows, oldSymbol i ^ 2 / (2 * (N : ℝ))) =
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  calc
    (∑ i ∈ rows, ∑ j ∈ range N, entry i j ^ 2) ≤
        ∑ i ∈ rows,
          32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hRow i hi
    _ = 32 * (rows.card * (C / (N : ℝ)) +
          (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hDivSum]
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem rectangular_bilinear_sq_le_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ)))) :
    (∑ ij ∈ rows ×ˢ range N,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))) *
      ((∑ i ∈ rows, x i ^ 2) * ∑ j ∈ range N, y j ^ 2) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    rows (range N) entry x y
  have hEntries := rectangular_sum_sq_le_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol N C hRow
  have hEntryProduct :
      (∑ ij ∈ rows ×ˢ range N, entry ij.1 ij.2 ^ 2) ≤
        32 * (rows.card * (C / (N : ℝ)) +
          (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) := by
    rw [Finset.sum_product]
    exact hEntries
  have hNorms :
      0 ≤ (∑ i ∈ rows, x i ^ 2) * ∑ j ∈ range N, y j ^ 2 := by
    positivity
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntryProduct hNorms)

theorem relativeCoupling_of_squaredNormBudget
    (lowEnergy highEnergy cross lowGap highGap entrySqBudget q
      lowNormSq highNormSq : ℝ)
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hq : 0 ≤ q)
    (hLowNormSq : 0 ≤ lowNormSq) (hHighNormSq : 0 ≤ highNormSq)
    (hLowEnergy : lowGap * lowNormSq ≤ lowEnergy)
    (hHighEnergy : highGap * highNormSq ≤ highEnergy)
    (hCross : cross ^ 2 ≤ entrySqBudget * (lowNormSq * highNormSq))
    (hBudget : entrySqBudget ≤ q * lowGap * highGap) :
    cross ^ 2 ≤ q * lowEnergy * highEnergy := by
  have hLowReference : 0 ≤ lowGap * lowNormSq :=
    mul_nonneg hLowGap hLowNormSq
  have hHighReference : 0 ≤ highGap * highNormSq :=
    mul_nonneg hHighGap hHighNormSq
  have hLowEnergyNonnegative : 0 ≤ lowEnergy :=
    hLowReference.trans hLowEnergy
  have hReferenceProduct :
      (lowGap * lowNormSq) * (highGap * highNormSq) ≤
        lowEnergy * highEnergy := by
    calc
      (lowGap * lowNormSq) * (highGap * highNormSq) ≤
          lowEnergy * (highGap * highNormSq) :=
        mul_le_mul_of_nonneg_right hLowEnergy hHighReference
      _ ≤ lowEnergy * highEnergy :=
        mul_le_mul_of_nonneg_left hHighEnergy hLowEnergyNonnegative
  have hNormProduct : 0 ≤ lowNormSq * highNormSq :=
    mul_nonneg hLowNormSq hHighNormSq
  have hBudgetScaled := mul_le_mul_of_nonneg_right hBudget hNormProduct
  have hReferenceScaled := mul_le_mul_of_nonneg_left hReferenceProduct hq
  calc
    cross ^ 2 ≤ entrySqBudget * (lowNormSq * highNormSq) := hCross
    _ ≤ (q * lowGap * highGap) * (lowNormSq * highNormSq) := hBudgetScaled
    _ = q * ((lowGap * lowNormSq) * (highGap * highNormSq)) := by ring
    _ ≤ q * (lowEnergy * highEnergy) := hReferenceScaled
    _ = q * lowEnergy * highEnergy := by ring

theorem rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (lowEnergy highEnergy lowGap highGap q : ℝ)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range N, entry i j ^ 2) ≤
        32 * (C / (N : ℝ) + oldSymbol i ^ 2 / (2 * (N : ℝ))))
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap) (hq : 0 ≤ q)
    (hLowEnergy :
      lowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hHighEnergy :
      highGap * (∑ j ∈ range N, y j ^ 2) ≤ highEnergy)
    (hBudget :
      32 * (rows.card * (C / (N : ℝ)) +
        (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ))) ≤
          q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range N,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      q * lowEnergy * highEnergy := by
  let entrySqBudget :=
    32 * (rows.card * (C / (N : ℝ)) +
      (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))
  have hCross := rectangular_bilinear_sq_le_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y N C hRow
  exact relativeCoupling_of_squaredNormBudget
    lowEnergy highEnergy
    (∑ ij ∈ rows ×ˢ range N,
      entry ij.1 ij.2 * (x ij.1 * y ij.2))
    lowGap highGap entrySqBudget q
    (∑ i ∈ rows, x i ^ 2) (∑ j ∈ range N, y j ^ 2)
    hLowGap hHighGap hq (by positivity) (by positivity)
    hLowEnergy hHighEnergy (by simpa only [entrySqBudget] using hCross)
    (by simpa only [entrySqBudget] using hBudget)

/-- Frobenius-square budget produced by the separated-row symbol estimate. -/
noncomputable def rectangularSymbolSquareBudget
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ) : ℝ :=
  32 * (rows.card * (C / (N : ℝ)) +
    (∑ i ∈ rows, oldSymbol i ^ 2) / (2 * (N : ℝ)))

/-- Newest-band specialization of the matrix budget.  If the historical band
has at most `B` rows, its ordinary symbol-square sum is at most `4*C*B`, and
the target shell has length `4B`, then the complete Frobenius-square budget is
at most `24*C`. -/
theorem rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (B : ℕ) (C : ℝ)
    (hB : B ≠ 0) (hC : 0 ≤ C)
    (hCard : rows.card ≤ B)
    (hOldSymbol :
      (∑ i ∈ rows, oldSymbol i ^ 2) ≤ 4 * C * (B : ℝ)) :
    rectangularSymbolSquareBudget rows oldSymbol (4 * B) C ≤ 24 * C := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  have hCardReal : (rows.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hCard
  have hCardScaled : (rows.card : ℝ) * C ≤ (B : ℝ) * C :=
    mul_le_mul_of_nonneg_right hCardReal hC
  have hNumerator :
      8 * ((rows.card : ℝ) * C) +
          4 * (∑ i ∈ rows, oldSymbol i ^ 2) ≤
        24 * C * (B : ℝ) := by
    nlinarith
  have hIdentity :
      rectangularSymbolSquareBudget rows oldSymbol (4 * B) C =
        (8 * ((rows.card : ℝ) * C) +
          4 * (∑ i ∈ rows, oldSymbol i ^ 2)) / (B : ℝ) := by
    simp only [rectangularSymbolSquareBudget, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hBR]
    ring
  rw [hIdentity]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ))).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hNumerator)

/-- End-to-end newest-band adapter.  The dyadic symbol estimates reduce the
matrix side to `24*C`; one scalar comparison with the two coercive floors then
produces the relative-energy coefficient `q`. -/
theorem rectangular_relativeCoupling_newestBand_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (B : ℕ) (C : ℝ)
    (lowEnergy highEnergy lowGap highGap q : ℝ)
    (hB : B ≠ 0) (hC : 0 ≤ C) (hCard : rows.card ≤ B)
    (hOldSymbol :
      (∑ i ∈ rows, oldSymbol i ^ 2) ≤ 4 * C * (B : ℝ))
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range (4 * B), entry i j ^ 2) ≤
        32 * (C / ((4 * B : ℕ) : ℝ) +
          oldSymbol i ^ 2 / (2 * ((4 * B : ℕ) : ℝ))))
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap) (hq : 0 ≤ q)
    (hLowEnergy :
      lowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hHighEnergy :
      highGap * (∑ j ∈ range (4 * B), y j ^ 2) ≤ highEnergy)
    (hScalarBudget : 24 * C ≤ q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range (4 * B),
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      q * lowEnergy * highEnergy := by
  have hMatrixBudget :
      rectangularSymbolSquareBudget rows oldSymbol (4 * B) C ≤
        q * lowGap * highGap :=
    (rectangularSymbolSquareBudget_four_mul_le_twentyFour_mul
      rows oldSymbol B C hB hC hCard hOldSymbol).trans hScalarBudget
  apply rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y (4 * B) C lowEnergy highEnergy
      lowGap highGap q hRow hLowGap hHighGap hq hLowEnergy hHighEnergy
  simpa only [rectangularSymbolSquareBudget] using hMatrixBudget

/-- With the historical rows fixed, doubling the target-shell length halves
the separated-symbol Frobenius-square budget exactly. -/
theorem rectangularSymbolSquareBudget_two_mul
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ)
    (hN : N ≠ 0) :
    rectangularSymbolSquareBudget rows oldSymbol (2 * N) C =
      rectangularSymbolSquareBudget rows oldSymbol N C / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [rectangularSymbolSquareBudget, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNR]

/-- A fixed-row separated-symbol budget transports with coefficient one half
when the target shell doubles and both coercive floors grow. -/
theorem rectangularSymbolSquareBudget_halfTransport
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (oldSymbol : ι → ℝ) (N : ℕ) (C : ℝ)
    (q lowGap highGap nextLowGap nextHighGap : ℝ)
    (hN : N ≠ 0) (hq : 0 ≤ q)
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (hBudget : rectangularSymbolSquareBudget rows oldSymbol N C ≤
      q * lowGap * highGap) :
    rectangularSymbolSquareBudget rows oldSymbol (2 * N) C ≤
      (q / 2) * nextLowGap * nextHighGap := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hGapProduct : lowGap * highGap ≤ nextLowGap * nextHighGap := by
    calc
      lowGap * highGap ≤ nextLowGap * highGap :=
        mul_le_mul_of_nonneg_right hLowGrowth hHighGap
      _ ≤ nextLowGap * nextHighGap :=
        mul_le_mul_of_nonneg_left hHighGrowth hNextLowGap
  rw [rectangularSymbolSquareBudget_two_mul rows oldSymbol N C hN]
  calc
    rectangularSymbolSquareBudget rows oldSymbol N C / 2 ≤
        (q * lowGap * highGap) / 2 := by gcongr
    _ = (q / 2) * (lowGap * highGap) := by ring
    _ ≤ (q / 2) * (nextLowGap * nextHighGap) :=
      mul_le_mul_of_nonneg_left hGapProduct (div_nonneg hq (by norm_num))
    _ = (q / 2) * nextLowGap * nextHighGap := by ring

/-- End-to-end half-transport adapter: the doubled-shell row estimates and the
previous scalar budget imply the next relative-energy coupling with coefficient
`q/2`. -/
theorem rectangular_relativeCoupling_halfTransport_of_shifted_symbolSquareRowBudgets
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (entry : ι → ℕ → ℝ) (oldSymbol : ι → ℝ)
    (x : ι → ℝ) (y : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (lowEnergy nextHighEnergy lowGap highGap nextLowGap nextHighGap q : ℝ)
    (hN : N ≠ 0)
    (hRow : ∀ i ∈ rows,
      (∑ j ∈ range (2 * N), entry i j ^ 2) ≤
        32 * (C / ((2 * N : ℕ) : ℝ) +
          oldSymbol i ^ 2 / (2 * ((2 * N : ℕ) : ℝ))))
    (hq : 0 ≤ q) (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hLowGrowth : lowGap ≤ nextLowGap)
    (hHighGrowth : highGap ≤ nextHighGap)
    (hLowEnergy :
      nextLowGap * (∑ i ∈ rows, x i ^ 2) ≤ lowEnergy)
    (hNextHighEnergy :
      nextHighGap * (∑ j ∈ range (2 * N), y j ^ 2) ≤ nextHighEnergy)
    (hPreviousBudget : rectangularSymbolSquareBudget rows oldSymbol N C ≤
      q * lowGap * highGap) :
    (∑ ij ∈ rows ×ˢ range (2 * N),
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      (q / 2) * lowEnergy * nextHighEnergy := by
  have hNextLowGap : 0 ≤ nextLowGap := hLowGap.trans hLowGrowth
  have hNextHighGap : 0 ≤ nextHighGap := hHighGap.trans hHighGrowth
  have hNextBudget :
      rectangularSymbolSquareBudget rows oldSymbol (2 * N) C ≤
        (q / 2) * nextLowGap * nextHighGap :=
    rectangularSymbolSquareBudget_halfTransport
      rows oldSymbol N C q lowGap highGap nextLowGap nextHighGap
      hN hq hLowGap hHighGap hLowGrowth hHighGrowth hPreviousBudget
  apply rectangular_relativeCoupling_of_shifted_symbolSquareRowBudgets
    rows entry oldSymbol x y (2 * N) C lowEnergy nextHighEnergy
      nextLowGap nextHighGap (q / 2) hRow hNextLowGap hNextHighGap
      (div_nonneg hq (by norm_num)) hLowEnergy hNextHighEnergy
  simpa only [rectangularSymbolSquareBudget] using hNextBudget

end RiemannCvs.CombinedSymbolDyadicL2
