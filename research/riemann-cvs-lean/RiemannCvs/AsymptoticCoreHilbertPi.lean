import RiemannCvs.AsymptoticCoreHilbert
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The sharp pi-weighted Hilbert row bound

This module replaces the elementary constant `4` in the historical-core
Hilbert estimate by the classical constant `Real.pi`.  The route is deliberately
kept separate from `AsymptoticCoreHilbert`: first compare the discrete row with
an improper integral, then evaluate that integral by the substitutions
`t = u ^ 2` and `u = sqrt p * v`.
-/

noncomputable section

namespace RiemannCvs.V23BoundaryWeylMainline

open scoped BigOperators
open Set MeasureTheory
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.CombinedSymbolDyadicL2

private noncomputable def hilbertPiIntegrand (p t : ℝ) : ℝ :=
  1 / ((p + t) * Real.sqrt t)

lemma hilbertPiIntegrand_antitoneOn_Ici
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    AntitoneOn (hilbertPiIntegrand p) (Set.Ici a) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hsxy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hpx : 0 < p + x := by positivity
  have hpy : 0 < p + y := by positivity
  have hden : (p + x) * Real.sqrt x ≤ (p + y) * Real.sqrt y := by
    exact mul_le_mul (by linarith) hsxy (Real.sqrt_nonneg _) hpy.le
  unfold hilbertPiIntegrand
  exact one_div_le_one_div_of_le (mul_pos hpx (Real.sqrt_pos.2 hx0)) hden

lemma integral_hilbertPiIntegrand
    (p : ℝ) (hp : 0 < p) :
    (∫ t in Set.Ioi 0, hilbertPiIntegrand p t) =
      Real.pi / Real.sqrt p := by
  have hsquare :
      (∫ t in Set.Ioi 0, hilbertPiIntegrand p t) =
        ∫ u in Set.Ioi 0, 2 / (p + u ^ 2) := by
    rw [← integral_comp_rpow_Ioi_of_pos
      (g := hilbertPiIntegrand p) (p := (2 : ℝ)) (by norm_num)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    simp only [hilbertPiIntegrand, Real.rpow_two]
    rw [Real.sqrt_sq hu0.le]
    norm_num
    field_simp
  rw [hsquare]
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hscaled :
      (∫ u in Set.Ioi 0,
          2 / (p + (Real.sqrt p * u) ^ 2)) =
        Real.pi / p := by
    calc
      (∫ u in Set.Ioi 0,
          2 / (p + (Real.sqrt p * u) ^ 2)) =
          ∫ u in Set.Ioi 0,
            (2 / p) * (1 + u ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change 2 / (p + (Real.sqrt p * u) ^ 2) =
          (2 / p) * (1 + u ^ 2)⁻¹
        rw [mul_pow, hsq]
        field_simp [ne_of_gt hp]
      _ = (2 / p) *
          ∫ u in Set.Ioi 0, (1 + u ^ 2)⁻¹ := by
        rw [MeasureTheory.integral_const_mul]
      _ = Real.pi / p := by
        rw [integral_Ioi_inv_one_add_sq]
        simp
  have hchange := integral_comp_mul_left_Ioi'
    (g := fun u : ℝ => 2 / (p + u ^ 2)) 0 hs
  have heq :
      Real.sqrt p *
          (∫ u in Set.Ioi 0,
            2 / (p + (Real.sqrt p * u) ^ 2)) =
        ∫ u in Set.Ioi 0, 2 / (p + u ^ 2) := by
    simpa [smul_eq_mul] using hchange
  rw [← heq, hscaled]
  field_simp [ne_of_gt hp, ne_of_gt hs]
  nlinarith

lemma integrableOn_hilbertPiIntegrand
    (p : ℝ) (hp : 0 < p) :
    IntegrableOn (hilbertPiIntegrand p) (Set.Ioi 0) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  let h : ℝ → ℝ := fun u => 2 / (p + u ^ 2)
  have hbase :
      IntegrableOn (fun u : ℝ => (2 / p) * (1 + u ^ 2)⁻¹)
        (Set.Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul (2 / p)).integrableOn
  have hscaled :
      IntegrableOn (fun u : ℝ => h (Real.sqrt p * u))
        (Set.Ioi 0) := by
    refine hbase.congr_fun (fun u hu => ?_) measurableSet_Ioi
    change (2 / p) * (1 + u ^ 2)⁻¹ =
      2 / (p + (Real.sqrt p * u) ^ 2)
    rw [mul_pow, hsq]
    field_simp [ne_of_gt hp]
  have hh : IntegrableOn h (Set.Ioi 0) :=
    by simpa using (integrableOn_Ioi_comp_mul_left_iff h 0 hs).mp hscaled
  apply (integrableOn_Ioi_comp_rpow_iff
    (hilbertPiIntegrand p) (p := (2 : ℝ)) (by norm_num)).mp
  refine hh.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : 0 < u := hu
  change 2 / (p + u ^ 2) =
    ((|(2 : ℝ)| * u ^ ((2 : ℝ) - 1)) •
      hilbertPiIntegrand p (u ^ (2 : ℝ)))
  simp only [hilbertPiIntegrand, Real.rpow_two]
  rw [Real.sqrt_sq hu0.le]
  norm_num
  field_simp

/-- The exact integral comparison improves the elementary Schur row constant
from `4` to `Real.pi`.  The assumption `1 ≤ M` keeps the comparison interval
away from the removable endpoint convention at zero. -/
lemma c13CoreHilbertKernel_row_le_pi
    (M L : ℕ) (hM : 1 ≤ M) (i : Fin L) :
    (∑ j, c13CoreHilbertKernel M L i j *
        c13CoreHilbertWeight M L j) ≤
      Real.pi * c13CoreHilbertWeight M L i := by
  let p : ℕ := M + (i : ℕ) + 1
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p by simp [p])
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hanti :
      AntitoneOn (hilbertPiIntegrand (p : ℝ)) (Set.Ici (M : ℝ)) :=
    hilbertPiIntegrand_antitoneOn_Ici (p : ℝ) (M : ℝ) hpR hMR
  have hsum :
      (∑ j ∈ Finset.range L,
          hilbertPiIntegrand (p : ℝ)
            ((M : ℝ) + ((j + 1 : ℕ) : ℝ))) ≤
        ∫ t in (M : ℝ)..(M : ℝ) + (L : ℝ),
          hilbertPiIntegrand (p : ℝ) t := by
    exact (hanti.mono Set.Icc_subset_Ici_self).sum_le_integral
  have hint := integrableOn_hilbertPiIntegrand (p : ℝ) hpR
  have hinterval :
      (∫ t in (M : ℝ)..(M : ℝ) + (L : ℝ),
          hilbertPiIntegrand (p : ℝ) t) ≤
        ∫ t in Set.Ioi 0, hilbertPiIntegrand (p : ℝ) t := by
    rw [intervalIntegral.integral_of_le
      (le_add_of_nonneg_right (Nat.cast_nonneg L))]
    apply setIntegral_mono_set hint _
      (show Set.Ioc (M : ℝ) ((M : ℝ) + (L : ℝ)) ⊆ Set.Ioi 0 by
        intro t ht
        exact lt_trans hMR ht.1).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    unfold hilbertPiIntegrand
    exact one_div_nonneg.mpr
      (mul_nonneg (add_nonneg hpR.le ht.le) (Real.sqrt_nonneg _))
  have hfinal :
      (∑ j ∈ Finset.range L,
        hilbertPiIntegrand (p : ℝ)
          ((M : ℝ) + (((j : ℕ) + 1 : ℕ) : ℝ))) ≤
        Real.pi * (1 / Real.sqrt (p : ℝ)) := by
    calc
      (∑ j ∈ Finset.range L,
          hilbertPiIntegrand (p : ℝ)
            ((M : ℝ) + (((j : ℕ) + 1 : ℕ) : ℝ))) ≤
        ∫ t in (M : ℝ)..(M : ℝ) + (L : ℝ),
          hilbertPiIntegrand (p : ℝ) t := hsum
      _ ≤ ∫ t in Set.Ioi 0, hilbertPiIntegrand (p : ℝ) t := hinterval
      _ = Real.pi / Real.sqrt (p : ℝ) :=
        integral_hilbertPiIntegrand (p : ℝ) hpR
      _ = Real.pi * (1 / Real.sqrt (p : ℝ)) := by ring
  have hsumEq :
      (∑ j : Fin L, c13CoreHilbertKernel M L i j *
          c13CoreHilbertWeight M L j) =
        ∑ j : Fin L, hilbertPiIntegrand (p : ℝ)
          ((M : ℝ) + ((((j : Fin L) : ℕ) + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [c13CoreHilbertKernel, c13CoreHilbertWeight,
      hilbertPiIntegrand]
    rw [one_div_mul_one_div_rev]
    congr 1
    push_cast
    simp [p]
    ring_nf
  rw [hsumEq]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => hilbertPiIntegrand (p : ℝ)
      ((M : ℝ) + (((j + 1 : ℕ)) : ℝ))) L]
  simpa [c13CoreHilbertWeight, p] using hfinal

/-- Sharp weighted-Schur control of the finite positive Hilbert matrix. -/
theorem c13CoreHilbertKernel_energy_abs_le_pi
    (M L : ℕ) (hM : 1 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy (c13CoreHilbertKernel M L) x| ≤
      Real.pi * finiteVectorEuclideanNormSq x := by
  have h := RiemannCvs.WeightedSchurSupersolution.weightedSchur_quadratic
    (c13CoreHilbertKernel M L) x (c13CoreHilbertWeight M L) Real.pi
    (c13CoreHilbertKernel_nonneg M L)
    (c13CoreHilbertKernel_symm M L)
    (c13CoreHilbertWeight_pos M L)
    (c13CoreHilbertKernel_row_le_pi M L hM)
  simpa only [weightedSchurEnergy_eq_finiteMatrixQuadraticEnergy,
    weightedSchurNormSq_eq_finiteVectorEuclideanNormSq] using h

/-- The reflected leading Archimedean kernel therefore costs only `pi / 2`. -/
theorem c13CoreReflectedHilbertLeading_energy_abs_le_piHalf
    (M L : ℕ) (hM : 1 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreReflectedHilbertLeadingMatrix M L) x| ≤
      (Real.pi / 2) * finiteVectorEuclideanNormSq x := by
  have h := c13CoreHilbertKernel_energy_abs_le_pi M L hM x
  have heq :
      finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x =
        (1 / 2 : ℝ) * finiteMatrixQuadraticEnergy
          (c13CoreHilbertKernel M L) x := by
    unfold c13CoreReflectedHilbertLeadingMatrix finiteMatrixQuadraticEnergy
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, abs_mul]
  norm_num at h ⊢
  nlinarith [Real.pi_pos]

lemma real_pi_lt_twentyTwoSevenths :
    Real.pi < (22 / 7 : ℝ) := by
  exact Real.pi_lt_d4.trans (by norm_num)

/-- Rational adapter used by the downstream exact arithmetic budget. -/
theorem c13CoreReflectedHilbertLeading_energy_abs_le_elevenSevenths
    (M L : ℕ) (hM : 1 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13CoreReflectedHilbertLeadingMatrix M L) x| ≤
      (11 / 7 : ℝ) * finiteVectorEuclideanNormSq x := by
  exact (c13CoreReflectedHilbertLeading_energy_abs_le_piHalf M L hM x).trans
    (mul_le_mul_of_nonneg_right
      (by linarith [real_pi_lt_twentyTwoSevenths])
      (finiteVectorEuclideanNormSq_nonneg x))

theorem c13OddCoreReflectedHilbertLeading_energy_abs_le_elevenSevenths
    (M L : ℕ) (hM : 1 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (c13OddCoreReflectedHilbertLeadingMatrix M L) x| ≤
      (11 / 7 : ℝ) * finiteVectorEuclideanNormSq x := by
  have h := c13CoreReflectedHilbertLeading_energy_abs_le_elevenSevenths
    M L hM x
  have heq :
      finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x =
        -finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x := by
    unfold c13OddCoreReflectedHilbertLeadingMatrix finiteMatrixQuadraticEnergy
    simp only [Matrix.neg_apply, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
  rw [heq, abs_neg]
  exact h

/-!
## Improved global core and no-crossing constants

The centered residual remains `43 / 3840`; only the leading reflected Hilbert
term changes.  The resulting rational Archimedean cost is `42541 / 26880`, and
the historical-core floor becomes `19283 / 26880`.
-/

theorem c13EvenCoreArchimedeanRemainder_energy_abs_le_42541Over26880
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (42541 / 26880 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13EvenCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13CoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13EvenCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ (11 / 7 : ℝ) * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13CoreReflectedHilbertLeading_energy_abs_le_elevenSevenths
          M L (by omega) x)
        (c13EvenCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M L hM x)
    _ = (42541 / 26880 : ℝ) * finiteVectorEuclideanNormSq x := by ring

theorem c13OddCoreArchimedeanRemainder_energy_abs_le_42541Over26880
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    |finiteMatrixQuadraticEnergy
        (logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
          13 (finGlobalShellPositiveMode M L)) x| ≤
      (42541 / 26880 : ℝ) * finiteVectorEuclideanNormSq x := by
  rw [c13OddCoreArchimedeanRemainder_eq_leading_add_centered,
    finiteMatrixQuadraticEnergy_add]
  calc
    |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x +
        finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| ≤
        |finiteMatrixQuadraticEnergy
          (c13OddCoreReflectedHilbertLeadingMatrix M L) x| +
        |finiteMatrixQuadraticEnergy
          (c13OddCoreArchimedeanCenteredResidualMatrix M L) x| :=
      abs_add_le _ _
    _ ≤ (11 / 7 : ℝ) * finiteVectorEuclideanNormSq x +
        (43 / 3840 : ℝ) * finiteVectorEuclideanNormSq x :=
      add_le_add
        (c13OddCoreReflectedHilbertLeading_energy_abs_le_elevenSevenths
          M L (by omega) x)
        (c13OddCoreArchimedeanCenteredResidual_energy_abs_le_fortyThreeOver3840
          M L hM x)
    _ = (42541 / 26880 : ℝ) * finiteVectorEuclideanNormSq x := by ring

lemma c13_globalCore_scalar_reserve_ge_19283Over26880
    (M : ℕ) (hM : 960 ≤ M) :
    (19283 / 26880 : ℝ) ≤ Real.log (M : ℝ) - 19 / 20 -
      (logarithmicCvSPoleScale 13 /
          (8 * Real.pi ^ 2 * (M : ℝ)) +
        42541 / 26880 + 10 / 3) := by
  nlinarith [c13_shell_complete_scalar_reserve_ge_nineFifths M hM]

theorem c13_logarithmicCvSBuilderEvenCore_energy_ge_19283Over26880
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (19283 / 26880 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderEvenPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch :=
    c13EvenCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM x
  have h := c13_logarithmicCvSBuilderEvenShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (19283 / 26880) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_19283Over26880 M hM)
  simpa using h

theorem c13_logarithmicCvSBuilderOddCore_energy_ge_19283Over26880
    (M L : ℕ) (hM : 960 ≤ M) (x : Fin L → ℝ) :
    (19283 / 26880 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixQuadraticEnergy
        (logarithmicCvSBuilderOddPositiveModeMatrix
          13 c13PrimePowerLocation c13PrimePowerBase
          (finGlobalShellPositiveMode M L)) x := by
  have hArch :=
    c13OddCoreArchimedeanRemainder_energy_abs_le_42541Over26880
      M L hM x
  have h := c13_logarithmicCvSBuilderOddShell_coerciveFloor_primeClosed
    M L (by omega) x
    (Real.log (M : ℝ) - 19 / 20) 0
    (19283 / 26880) (42541 / 26880)
    (c13_logarithmicCvSArchimedeanShellDiagonal_ge_log_sub_nineteenTwentieth_closed
      M L hM)
    hArch
    (by simpa using c13_globalCore_scalar_reserve_ge_19283Over26880 M hM)
  simpa using h

theorem c13EvenBuilderCoreNewestBaseEnergy_ge_19283Over26880
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (19283 / 26880 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderEvenCore_energy_ge_19283Over26880
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13OddBuilderCoreNewestBaseEnergy_ge_19283Over26880
    (M N : ℕ) (hM : 960 ≤ M) (x : Fin (N - M) → ℝ) :
    (19283 / 26880 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x := by
  have h := c13_logarithmicCvSBuilderOddCore_energy_ge_19283Over26880
    M (N - M) hM x
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using h

theorem c13EvenBuilderCoreNewest_relative_19283Over26880
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (19283 / 26880 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M N) y := by
  exact c13EvenBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (19283 / 26880) q (by norm_num) hq
    (c13EvenBuilderCoreNewestBaseEnergy_ge_19283Over26880 M N hM x)
    hBudget

theorem c13OddBuilderCoreNewest_relative_19283Over26880
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hBudget : (4217 / 1000 : ℝ) ^ 2 ≤
      q * (19283 / 26880 : ℝ) * c13ShellDynamicGap N) :
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M N) x y) ^ 2 ≤
      q * finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M N) x *
        finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M N) y := by
  exact c13OddBuilderCoreNewest_relative_of_coreFloor
    M N hM hMN x y (19283 / 26880) q (by norm_num) hq
    (c13OddBuilderCoreNewestBaseEnergy_ge_19283Over26880 M N hM x)
    hBudget

theorem c13CoreNewestRelativeEnvelope_19283Over26880_lt_fourNinth
    (n : ℕ) (hn : 70 ≤ n) :
    c13CoreNewestRelativeEnvelope (19283 / 26880) n < (4 / 9 : ℝ) := by
  have hnR : (70 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < c13DyadicGapLower n := c13DyadicGapLower_pos n
  unfold c13CoreNewestRelativeEnvelope
  apply (div_lt_iff₀ (mul_pos (by norm_num) hgap)).2
  have hscaled : (70 : ℝ) * (69 / 100 : ℝ) ≤
      (n : ℝ) * (69 / 100 : ℝ) :=
    mul_le_mul_of_nonneg_right hnR (by norm_num)
  unfold c13DyadicGapLower
  norm_num at hscaled ⊢
  nlinarith

/-- The new integer cutoff is sharp for this exact rational envelope. -/
theorem c13CoreNewestRelativeEnvelope_19283Over26880_ge_fourNinth_at_69 :
    (4 / 9 : ℝ) ≤
      c13CoreNewestRelativeEnvelope (19283 / 26880) 69 := by
  unfold c13CoreNewestRelativeEnvelope c13DyadicGapLower
  norm_num

theorem c13EvenBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13EvenBuilderCoreNewestBaseEnergy_ge_19283Over26880
    960 (c13DyadicShellBase n) (by norm_num) x
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13EvenBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13EvenBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (19283 / 26880) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt
          (c13CoreNewestRelativeEnvelope_19283Over26880_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

theorem c13OddBuilderDyadicCoreNewest_relative_fourNinth_of_ge_70
    (n : ℕ) (hn : 70 ≤ n)
    (x : Fin (c13DyadicShellBase n - 960) → ℝ)
    (y : Fin (c13DyadicShellBase n) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x y) ^ 2 ≤
      (4 / 9 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y := by
  have hMN : 960 ≤ c13DyadicShellBase n := by
    unfold c13DyadicShellBase
    have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hCore := c13OddBuilderCoreNewestBaseEnergy_ge_19283Over26880
    960 (c13DyadicShellBase n) (by norm_num) x
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    960 (c13DyadicShellBase n) (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith) y
  have hBaseNonneg : 0 ≤ finiteMatrixBlockBaseEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) x :=
    (mul_nonneg (by norm_num) (finiteVectorEuclideanNormSq_nonneg x)).trans hCore
  have hTailNonneg : 0 ≤ finiteMatrixBlockTailEnergy
      (c13OddBuilderCoreNewestBlock 960 (c13DyadicShellBase n)) y :=
    (mul_nonneg (c13ShellDynamicGap_nonneg _ (by
      unfold c13DyadicShellBase
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith)) (finiteVectorEuclideanNormSq_nonneg y)).trans hTail
  have hRelative := c13OddBuilderDyadicCoreNewest_relative_vanishingEnvelope
    960 n (by norm_num) hMN x y (19283 / 26880) (by norm_num) hCore
  exact hRelative.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_of_lt
          (c13CoreNewestRelativeEnvelope_19283Over26880_lt_fourNinth n hn))
        hBaseNonneg)
      hTailNonneg)

end RiemannCvs.V23BoundaryWeylMainline
