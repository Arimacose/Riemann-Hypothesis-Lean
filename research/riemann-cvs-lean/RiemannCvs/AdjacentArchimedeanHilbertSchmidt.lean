import RiemannCvs.AsymptoticAdjacentCoreHilbertPi
import RiemannCvs.PoleSeparatedBands

/-!
# Initial adjacent-shell bridge from the certified cutoff

The whole-core estimate in `AsymptoticCoreNewestArchimedean` bounds every
Archimedean entry separately and therefore pays amplitude `667/1000`.  At the
first unresolved analytic scale this is too expensive once the prime channel
is added.

For the genuinely adjacent rectangle

* rows `p in (M,2M]`,
* columns `q in (2M,4M]`,

this file preserves the exact reflected decomposition instead:

1. the leading positive Hankel kernel `1 / (2 * (p + q))`;
2. the same-sign centered quotient, retaining its `1 / (q - p)` decay;
3. the reflected centered quotient, retaining its rank-one
   `1 / (p*q)` envelope.

Finite Hilbert--Schmidt sums give amplitudes `237/1000`, `39/10000`, and
`1/10000`, hence the common even/odd Archimedean amplitude `241/1000` for
every `M >= 3840`.  Combining it with the already separated pole amplitude
`51/1000`, the prime amplitude `10/3`, and the actual dynamic diagonal gaps
proves a complete adjacent builder coefficient `24/25 < 1` beginning at the
current rigorous cutoff `3840`.

No numerical oracle enters these bounds: all reciprocal-square and rational
inequalities are proved in Lean.
-/

noncomputable section

open scoped BigOperators Real

namespace RiemannCvs.V23BoundaryWeylMainline

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.PoleSeparatedBands

lemma centered_sameSign_adjacent_scalar_le
    (p q M d : ℝ) (hM : 0 < M) (hMp : M ≤ p)
    (hpq : p ≤ q) (hd : 0 < d) (hdpq : d ≤ q - p) :
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (q - p)) ≤
      1 / (6 * M * d) := by
  have hp : 0 < p := hM.trans_le hMp
  have hq : 0 < q := hp.trans_le hpq
  have hdiff : 0 < q - p := hd.trans_le hdpq
  have hqinv : 1 / q ≤ 1 / p := one_div_le_one_div_of_le hp hpq
  have hprod : M * d ≤ p * (q - p) :=
    mul_le_mul hMp hdpq hd.le hp.le
  have hinv : 1 / (p * (q - p)) ≤ 1 / (M * d) :=
    one_div_le_one_div_of_le (mul_pos hM hd) hprod
  calc
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (q - p)) ≤
        (1 / (4 * p) + 1 / (4 * p)) / (3 * (q - p)) := by
      gcongr
    _ = (1 / 6 : ℝ) * (1 / (p * (q - p))) := by field_simp; ring
    _ ≤ (1 / 6 : ℝ) * (1 / (M * d)) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 1 / (6 * M * d) := by ring

noncomputable def c13AdjacentSameSignMatrix (M : ℕ) :
    Matrix (Fin (2 * M - M)) (Fin (2 * M)) ℝ :=
  fun i j => logarithmicCvSArchimedeanEntry 13
    (c13CoreMode M (2 * M) i : ℤ) (c13NewestMode (2 * M) j : ℤ)

lemma c13AdjacentSameSignMatrix_entry_abs_le
    (M : ℕ) (hM : 960 ≤ M)
    (i : Fin (2 * M - M)) (j : Fin (2 * M)) :
    |c13AdjacentSameSignMatrix M i j| ≤
      (1 / (6 * (M : ℝ))) * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) := by
  let p := c13CoreMode M (2 * M) i
  let q := c13NewestMode (2 * M) j
  have hMN : M ≤ 2 * M := by omega
  have hpM : M ≤ p := (c13CoreMode_bounds M (2 * M) hMN i).1
  have hpN : p ≤ 2 * M := (c13CoreMode_bounds M (2 * M) hMN i).2
  have hNq : 2 * M < q := c13NewestMode_gt (2 * M) j
  have hpq : p < q := hpN.trans_lt hNq
  have hdistNat : (j : ℕ) + 1 ≤ q - p := by
    dsimp [p, q, c13CoreMode, c13NewestMode]
    have hi : (i : ℕ) < M := by omega
    omega
  have hMReal : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpMReal : (M : ℝ) ≤ p := by exact_mod_cast hpM
  have hpqReal : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have hdReal : (0 : ℝ) < ((j : ℕ) + 1 : ℕ) := by positivity
  have hdistReal : (((j : ℕ) + 1 : ℕ) : ℝ) ≤
      (q : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpq.le]
    exact_mod_cast hdistNat
  have hRaw := c13_archimedean_sameSign_nat_abs_le p q (by omega) hpq
  have hScalar := centered_sameSign_adjacent_scalar_le
    (p : ℝ) (q : ℝ) (M : ℝ) (((j : ℕ) + 1 : ℕ) : ℝ)
    hMReal hpMReal hpqReal hdReal hdistReal
  unfold c13AdjacentSameSignMatrix
  dsimp [p, q] at hRaw hScalar ⊢
  exact hRaw.trans (hScalar.trans_eq (by ring))

lemma adjacent_reciprocal_sq_sum_le_two (M : ℕ) :
    (∑ j : Fin (2 * M),
      (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ 2) ≤ (2 : ℝ) := by
  have h := RiemannCvs.PoleSeparatedBands.fixedPrefix_inv_sq_sum_le_two
    (2 * M) 0
  simpa [RiemannCvs.PrimeTranslationSeparatedBands.fixedRemotePositiveMode,
    one_div, inv_pow] using h

lemma c13AdjacentSameSignMatrix_entry_sq_sum_le
    (M : ℕ) (hM : 960 ≤ M) :
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
      (c13AdjacentSameSignMatrix M i j) ^ 2) ≤
        1 / (18 * (M : ℝ)) := by
  let a : ℝ := 1 / (6 * (M : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint : ∀ i : Fin (2 * M - M), ∀ j : Fin (2 * M),
      (c13AdjacentSameSignMatrix M i j) ^ 2 ≤
        (a * (1 / (((j : ℕ) + 1 : ℕ) : ℝ))) ^ 2 := by
    intro i j
    have h := c13AdjacentSameSignMatrix_entry_abs_le M hM i j
    have hbound : |c13AdjacentSameSignMatrix M i j| ≤
        a * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) := by
      simpa only [a] using h
    have hnonneg : 0 ≤ a * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) :=
      mul_nonneg ha (by positivity)
    have hs := (sq_le_sq₀ (abs_nonneg (c13AdjacentSameSignMatrix M i j))
      hnonneg).2 hbound
    simpa only [sq_abs] using hs
  have hrow : ∀ i : Fin (2 * M - M),
      (∑ j : Fin (2 * M), (c13AdjacentSameSignMatrix M i j) ^ 2) ≤
        a ^ 2 * 2 := by
    intro i
    calc
      (∑ j : Fin (2 * M), (c13AdjacentSameSignMatrix M i j) ^ 2) ≤
          ∑ j : Fin (2 * M),
            (a * (1 / (((j : ℕ) + 1 : ℕ) : ℝ))) ^ 2 := by
        exact Finset.sum_le_sum (fun j _ => hpoint i j)
      _ = a ^ 2 * ∑ j : Fin (2 * M),
          (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 := by
        simp_rw [mul_pow, Finset.mul_sum]
      _ ≤ a ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (adjacent_reciprocal_sq_sum_le_two M)
          (sq_nonneg a)
  have hdim : 2 * M - M = M := by omega
  calc
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
        (c13AdjacentSameSignMatrix M i j) ^ 2) ≤
        ∑ _i : Fin (2 * M - M), a ^ 2 * 2 := by
      exact Finset.sum_le_sum (fun i _ => hrow i)
    _ = (M : ℝ) * (a ^ 2 * 2) := by simp [hdim]
    _ = 1 / (18 * (M : ℝ)) := by
      dsimp [a]
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem c13AdjacentSameSignBilinear_sq_le
    (M : ℕ) (hM : 960 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13AdjacentSameSignMatrix M) x y) ^ 2 ≤
      (1 / (18 * (M : ℝ))) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin (2 * M - M)))
    (Finset.univ : Finset (Fin (2 * M)))
    (c13AdjacentSameSignMatrix M) x y
  rw [← finiteRectangularBilinearEnergy_eq_product_sum] at hCauchy
  rw [Finset.sum_product] at hCauchy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right
    (c13AdjacentSameSignMatrix_entry_sq_sum_le M hM)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

noncomputable def c13AdjacentReflectedLeadingMatrix (M : ℕ) :
    Matrix (Fin (2 * M - M)) (Fin (2 * M)) ℝ :=
  fun i j => 1 / (2 *
    ((c13CoreMode M (2 * M) i : ℝ) + (c13NewestMode (2 * M) j : ℝ)))

lemma c13AdjacentReflectedLeadingMatrix_entry_le
    (M : ℕ) (hM : 1 ≤ M)
    (i : Fin (2 * M - M)) (j : Fin (2 * M)) :
    0 ≤ c13AdjacentReflectedLeadingMatrix M i j ∧
      c13AdjacentReflectedLeadingMatrix M i j ≤ 1 / (6 * (M : ℝ)) := by
  let p := c13CoreMode M (2 * M) i
  let q := c13NewestMode (2 * M) j
  have hMN : M ≤ 2 * M := by omega
  have hpM : M ≤ p := (c13CoreMode_bounds M (2 * M) hMN i).1
  have hqN : 2 * M < q := c13NewestMode_gt (2 * M) j
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpMR : (M : ℝ) ≤ p := by exact_mod_cast hpM
  have hqNR : (2 * M : ℕ) ≤ q := hqN.le
  have hqNR' : ((2 * M : ℕ) : ℝ) ≤ q := by exact_mod_cast hqNR
  have hden : 6 * (M : ℝ) ≤ 2 * ((p : ℝ) + (q : ℝ)) := by
    push_cast at hqNR'
    nlinarith
  have hden0 : 0 < 6 * (M : ℝ) := by positivity
  dsimp [c13AdjacentReflectedLeadingMatrix, p, q]
  constructor
  · positivity
  · exact one_div_le_one_div_of_le hden0 hden

lemma c13AdjacentReflectedLeadingMatrix_entry_sq_sum_le
    (M : ℕ) (hM : 1 ≤ M) :
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
      (c13AdjacentReflectedLeadingMatrix M i j) ^ 2) ≤ (1 / 18 : ℝ) := by
  let a : ℝ := 1 / (6 * (M : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint : ∀ i : Fin (2 * M - M), ∀ j : Fin (2 * M),
      (c13AdjacentReflectedLeadingMatrix M i j) ^ 2 ≤ a ^ 2 := by
    intro i j
    have h := (c13AdjacentReflectedLeadingMatrix_entry_le M hM i j).2
    have hs := (sq_le_sq₀
      (c13AdjacentReflectedLeadingMatrix_entry_le M hM i j).1 ha).2
      (by simpa only [a] using h)
    exact hs
  have hdim : 2 * M - M = M := by omega
  calc
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
        (c13AdjacentReflectedLeadingMatrix M i j) ^ 2) ≤
        ∑ _i : Fin (2 * M - M), ∑ _j : Fin (2 * M), a ^ 2 := by
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = (M : ℝ) * ((2 * M : ℕ) : ℝ) * a ^ 2 := by
      simp [hdim]
      ring
    _ = 1 / 18 := by
      dsimp [a]
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem c13AdjacentReflectedLeadingBilinear_sq_le
    (M : ℕ) (hM : 1 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13AdjacentReflectedLeadingMatrix M) x y) ^ 2 ≤
      (1 / 18 : ℝ) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin (2 * M - M)))
    (Finset.univ : Finset (Fin (2 * M)))
    (c13AdjacentReflectedLeadingMatrix M) x y
  rw [← finiteRectangularBilinearEnergy_eq_product_sum] at hCauchy
  rw [Finset.sum_product] at hCauchy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right
    (c13AdjacentReflectedLeadingMatrix_entry_sq_sum_le M hM)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

noncomputable def c13AdjacentReflectedCenteredMatrix (M : ℕ) :
    Matrix (Fin (2 * M - M)) (Fin (2 * M)) ℝ :=
  fun i j =>
    (centeredArchimedeanSymbol 13 (c13CoreMode M (2 * M) i : ℤ) +
      centeredArchimedeanSymbol 13 (c13NewestMode (2 * M) j : ℤ)) /
      (Real.pi *
        ((c13CoreMode M (2 * M) i : ℝ) + (c13NewestMode (2 * M) j : ℝ)))

lemma c13AdjacentReflectedCenteredMatrix_entry_abs_le
    (M : ℕ) (hM : 960 ≤ M)
    (i : Fin (2 * M - M)) (j : Fin (2 * M)) :
    |c13AdjacentReflectedCenteredMatrix M i j| ≤
      1 / (24 * (M : ℝ) ^ 2) := by
  let p := c13CoreMode M (2 * M) i
  let q := c13NewestMode (2 * M) j
  have hMN : M ≤ 2 * M := by omega
  have hpM : M ≤ p := (c13CoreMode_bounds M (2 * M) hMN i).1
  have hqN : 2 * M < q := c13NewestMode_gt (2 * M) j
  have hp : 960 ≤ p := hM.trans hpM
  have hq : 960 ≤ q := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h2MR : (0 : ℝ) < (2 * M : ℕ) := by positivity
  have hpMR : (M : ℝ) ≤ p := by exact_mod_cast hpM
  have hqNR : ((2 * M : ℕ) : ℝ) ≤ q := by exact_mod_cast hqN.le
  have hcp := c13_centeredArchimedeanSymbol_nat_abs_le p hp
  have hcq := c13_centeredArchimedeanSymbol_nat_abs_le q hq
  have hnum :
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
        1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by
    calc
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
          |centeredArchimedeanSymbol 13 (p : ℤ)| +
            |centeredArchimedeanSymbol 13 (q : ℤ)| := abs_add_le _ _
      _ ≤ (1 / 4 : ℝ) / (p : ℝ) + (1 / 4 : ℝ) / (q : ℝ) :=
        add_le_add hcp hcq
      _ = 1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by ring
  have hsum : (0 : ℝ) < (p : ℝ) + (q : ℝ) := by positivity
  have hden : 3 * ((p : ℝ) + (q : ℝ)) ≤
      Real.pi * ((p : ℝ) + (q : ℝ)) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le hsum.le
  have hscalar := centered_reflected_scalar_le
    (p : ℝ) (q : ℝ) (M : ℝ) ((2 * M : ℕ) : ℝ)
    hMR hpMR h2MR hqNR
  dsimp [c13AdjacentReflectedCenteredMatrix, p, q]
  rw [abs_div, abs_of_pos (mul_pos Real.pi_pos hsum)]
  calc
    |centeredArchimedeanSymbol 13 (p : ℤ) +
        centeredArchimedeanSymbol 13 (q : ℤ)| /
        (Real.pi * ((p : ℝ) + (q : ℝ))) ≤
      (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
        (Real.pi * ((p : ℝ) + (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
        (3 * ((p : ℝ) + (q : ℝ))) := by gcongr
    _ ≤ 1 / (12 * (M : ℝ) * ((2 * M : ℕ) : ℝ)) := hscalar
    _ = 1 / (24 * (M : ℝ) ^ 2) := by push_cast; ring

lemma c13AdjacentReflectedCenteredMatrix_entry_sq_sum_le
    (M : ℕ) (hM : 960 ≤ M) :
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
      (c13AdjacentReflectedCenteredMatrix M i j) ^ 2) ≤
        1 / (288 * (M : ℝ) ^ 2) := by
  let a : ℝ := 1 / (24 * (M : ℝ) ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint : ∀ i : Fin (2 * M - M), ∀ j : Fin (2 * M),
      (c13AdjacentReflectedCenteredMatrix M i j) ^ 2 ≤ a ^ 2 := by
    intro i j
    have h : |c13AdjacentReflectedCenteredMatrix M i j| ≤ a := by
      simpa only [a] using
        c13AdjacentReflectedCenteredMatrix_entry_abs_le M hM i j
    have hs := (sq_le_sq₀
      (abs_nonneg (c13AdjacentReflectedCenteredMatrix M i j)) ha).2 h
    simpa only [sq_abs] using hs
  have hdim : 2 * M - M = M := by omega
  calc
    (∑ i : Fin (2 * M - M), ∑ j : Fin (2 * M),
        (c13AdjacentReflectedCenteredMatrix M i j) ^ 2) ≤
        ∑ _i : Fin (2 * M - M), ∑ _j : Fin (2 * M), a ^ 2 := by
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = (M : ℝ) * ((2 * M : ℕ) : ℝ) * a ^ 2 := by
      simp [hdim]
      ring
    _ = 1 / (288 * (M : ℝ) ^ 2) := by
      dsimp [a]
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem c13AdjacentReflectedCenteredBilinear_sq_le
    (M : ℕ) (hM : 960 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13AdjacentReflectedCenteredMatrix M) x y) ^ 2 ≤
      (1 / (288 * (M : ℝ) ^ 2)) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    (Finset.univ : Finset (Fin (2 * M - M)))
    (Finset.univ : Finset (Fin (2 * M)))
    (c13AdjacentReflectedCenteredMatrix M) x y
  rw [← finiteRectangularBilinearEnergy_eq_product_sum] at hCauchy
  rw [Finset.sum_product] at hCauchy
  exact hCauchy.trans (mul_le_mul_of_nonneg_right
    (c13AdjacentReflectedCenteredMatrix_entry_sq_sum_le M hM)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

lemma c13EvenArchimedeanCoreNewestMatrix_adjacent_entry_eq
    (M : ℕ) (i : Fin (2 * M - M)) (j : Fin (2 * M)) :
    c13EvenArchimedeanCoreNewestMatrix M (2 * M) i j =
      -c13AdjacentSameSignMatrix M i j +
        c13AdjacentReflectedLeadingMatrix M i j +
          c13AdjacentReflectedCenteredMatrix M i j := by
  let p := c13CoreMode M (2 * M) i
  let q := c13NewestMode (2 * M) j
  have hp : 0 < p := by dsimp [p, c13CoreMode]; omega
  have hq : 0 < q := by dsimp [q, c13NewestMode]; omega
  have href := logarithmicCvSArchimedeanEntry_reflected_eq 13
    (p : ℤ) (q : ℤ) (by exact_mod_cast hp) (by exact_mod_cast hq)
  simp only [c13EvenArchimedeanCoreNewestMatrix,
    c13EvenArchimedeanCoreNewestEntry,
    c13AdjacentSameSignMatrix, c13AdjacentReflectedLeadingMatrix,
    c13AdjacentReflectedCenteredMatrix]
  dsimp [p, q] at href ⊢
  simp only [Int.cast_natCast] at href ⊢
  rw [href]
  have hsum : (0 : ℝ) <
      (c13CoreMode M (2 * M) i : ℝ) + (c13NewestMode (2 * M) j : ℝ) := by
    positivity
  field_simp [ne_of_gt hsum, Real.pi_ne_zero]
  ring_nf

lemma c13OddArchimedeanCoreNewestMatrix_adjacent_entry_eq
    (M : ℕ) (i : Fin (2 * M - M)) (j : Fin (2 * M)) :
    c13OddArchimedeanCoreNewestMatrix M (2 * M) i j =
      -c13AdjacentSameSignMatrix M i j -
        c13AdjacentReflectedLeadingMatrix M i j -
          c13AdjacentReflectedCenteredMatrix M i j := by
  let p := c13CoreMode M (2 * M) i
  let q := c13NewestMode (2 * M) j
  have hp : 0 < p := by dsimp [p, c13CoreMode]; omega
  have hq : 0 < q := by dsimp [q, c13NewestMode]; omega
  have href := logarithmicCvSArchimedeanEntry_reflected_eq 13
    (p : ℤ) (q : ℤ) (by exact_mod_cast hp) (by exact_mod_cast hq)
  simp only [c13OddArchimedeanCoreNewestMatrix,
    c13OddArchimedeanCoreNewestEntry,
    c13AdjacentSameSignMatrix, c13AdjacentReflectedLeadingMatrix,
    c13AdjacentReflectedCenteredMatrix]
  dsimp [p, q] at href ⊢
  simp only [Int.cast_natCast] at href ⊢
  rw [href]
  have hsum : (0 : ℝ) <
      (c13CoreMode M (2 * M) i : ℝ) + (c13NewestMode (2 * M) j : ℝ) := by
    positivity
  field_simp [ne_of_gt hsum, Real.pi_ne_zero]
  ring_nf

lemma finiteRectangularBilinearEnergy_add
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    finiteRectangularBilinearEnergy (A + B) x y =
      finiteRectangularBilinearEnergy A x y +
        finiteRectangularBilinearEnergy B x y := by
  unfold finiteRectangularBilinearEnergy
  simp_rw [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma finiteRectangularBilinearEnergy_neg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    finiteRectangularBilinearEnergy (-A) x y =
      -finiteRectangularBilinearEnergy A x y := by
  unfold finiteRectangularBilinearEnergy
  simp only [Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

lemma c13EvenArchimedeanCoreNewestMatrix_adjacent_eq (M : ℕ) :
    c13EvenArchimedeanCoreNewestMatrix M (2 * M) =
      -c13AdjacentSameSignMatrix M + c13AdjacentReflectedLeadingMatrix M +
        c13AdjacentReflectedCenteredMatrix M := by
  ext i j
  exact c13EvenArchimedeanCoreNewestMatrix_adjacent_entry_eq M i j

lemma c13OddArchimedeanCoreNewestMatrix_adjacent_eq (M : ℕ) :
    c13OddArchimedeanCoreNewestMatrix M (2 * M) =
      -c13AdjacentSameSignMatrix M - c13AdjacentReflectedLeadingMatrix M -
        c13AdjacentReflectedCenteredMatrix M := by
  ext i j
  exact c13OddArchimedeanCoreNewestMatrix_adjacent_entry_eq M i j

lemma oneOverEighteen_le_237Thousandths_sq :
    (1 / 18 : ℝ) ≤ (237 / 1000 : ℝ) ^ 2 := by norm_num

lemma oneOverEighteenM_le_39TenThousandths_sq
    (M : ℕ) (hM : 3840 ≤ M) :
    1 / (18 * (M : ℝ)) ≤ (39 / 10000 : ℝ) ^ 2 := by
  have hMR : (3840 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : (69120 : ℝ) ≤ 18 * (M : ℝ) := by nlinarith
  have hInv : 1 / (18 * (M : ℝ)) ≤ 1 / 69120 :=
    one_div_le_one_div_of_le (by norm_num) hden
  exact hInv.trans (by norm_num)

lemma oneOver288MSq_le_oneTenThousandth_sq
    (M : ℕ) (hM : 3840 ≤ M) :
    1 / (288 * (M : ℝ) ^ 2) ≤ (1 / 10000 : ℝ) ^ 2 := by
  have hMR : (3840 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : (100000000 : ℝ) ≤ 288 * (M : ℝ) ^ 2 := by nlinarith
  calc
    1 / (288 * (M : ℝ) ^ 2) ≤ 1 / (100000000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hden
    _ = (1 / 10000 : ℝ) ^ 2 := by norm_num

theorem c13EvenArchimedeanAdjacentBilinear_sq_le_241Thousandths
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13EvenArchimedeanCoreNewestMatrix M (2 * M)) x y) ^ 2 ≤
      (241 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let same := finiteRectangularBilinearEnergy (c13AdjacentSameSignMatrix M) x y
  let lead := finiteRectangularBilinearEnergy
    (c13AdjacentReflectedLeadingMatrix M) x y
  let centered := finiteRectangularBilinearEnergy
    (c13AdjacentReflectedCenteredMatrix M) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hSameRaw := c13AdjacentSameSignBilinear_sq_le M (by omega) x y
  have hLeadRaw := c13AdjacentReflectedLeadingBilinear_sq_le M (by omega) x y
  have hCenteredRaw := c13AdjacentReflectedCenteredBilinear_sq_le M (by omega) x y
  have hSame : (-same) ^ 2 ≤ (39 / 10000 : ℝ) ^ 2 * E := by
    rw [neg_sq]
    exact hSameRaw.trans (mul_le_mul_of_nonneg_right
      (oneOverEighteenM_le_39TenThousandths_sq M hM) hE)
  have hLead : lead ^ 2 ≤ (237 / 1000 : ℝ) ^ 2 * E :=
    hLeadRaw.trans (mul_le_mul_of_nonneg_right
      oneOverEighteen_le_237Thousandths_sq hE)
  have hCentered : centered ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 * E :=
    hCenteredRaw.trans (mul_le_mul_of_nonneg_right
      (oneOver288MSq_le_oneTenThousandth_sq M hM) hE)
  have hTotal := three_cross_sq_le_sum_amplitudes
    (-same) lead centered (39 / 10000 : ℝ) (237 / 1000 : ℝ)
      (1 / 10000 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hSame hLead hCentered
  rw [show (241 / 1000 : ℝ) = 39 / 10000 + 237 / 1000 + 1 / 10000 by
    norm_num]
  rw [c13EvenArchimedeanCoreNewestMatrix_adjacent_eq,
    finiteRectangularBilinearEnergy_add,
    finiteRectangularBilinearEnergy_add,
    finiteRectangularBilinearEnergy_neg]
  simpa [same, lead, centered] using hTotal

theorem c13OddArchimedeanAdjacentBilinear_sq_le_241Thousandths
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13OddArchimedeanCoreNewestMatrix M (2 * M)) x y) ^ 2 ≤
      (241 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let same := finiteRectangularBilinearEnergy (c13AdjacentSameSignMatrix M) x y
  let lead := finiteRectangularBilinearEnergy
    (c13AdjacentReflectedLeadingMatrix M) x y
  let centered := finiteRectangularBilinearEnergy
    (c13AdjacentReflectedCenteredMatrix M) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hSameRaw := c13AdjacentSameSignBilinear_sq_le M (by omega) x y
  have hLeadRaw := c13AdjacentReflectedLeadingBilinear_sq_le M (by omega) x y
  have hCenteredRaw := c13AdjacentReflectedCenteredBilinear_sq_le M (by omega) x y
  have hSame : (-same) ^ 2 ≤ (39 / 10000 : ℝ) ^ 2 * E := by
    rw [neg_sq]
    exact hSameRaw.trans (mul_le_mul_of_nonneg_right
      (oneOverEighteenM_le_39TenThousandths_sq M hM) hE)
  have hLead : (-lead) ^ 2 ≤ (237 / 1000 : ℝ) ^ 2 * E := by
    rw [neg_sq]
    exact hLeadRaw.trans (mul_le_mul_of_nonneg_right
      oneOverEighteen_le_237Thousandths_sq hE)
  have hCentered : (-centered) ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 * E := by
    rw [neg_sq]
    exact hCenteredRaw.trans (mul_le_mul_of_nonneg_right
      (oneOver288MSq_le_oneTenThousandth_sq M hM) hE)
  have hTotal := three_cross_sq_le_sum_amplitudes
    (-same) (-lead) (-centered) (39 / 10000 : ℝ) (237 / 1000 : ℝ)
      (1 / 10000 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hSame hLead hCentered
  rw [show (241 / 1000 : ℝ) = 39 / 10000 + 237 / 1000 + 1 / 10000 by
    norm_num]
  rw [c13OddArchimedeanCoreNewestMatrix_adjacent_eq]
  simp only [sub_eq_add_neg]
  rw [finiteRectangularBilinearEnergy_add,
    finiteRectangularBilinearEnergy_add,
    finiteRectangularBilinearEnergy_neg,
    finiteRectangularBilinearEnergy_neg,
    finiteRectangularBilinearEnergy_neg]
  simpa [same, lead, centered] using hTotal

theorem c13EvenArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenArchimedeanCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (241 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenArchimedeanCoreNewestBlock_crossEnergy M (2 * M) (by omega)]
  exact c13EvenArchimedeanAdjacentBilinear_sq_le_241Thousandths M hM x y

theorem c13OddArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddArchimedeanCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (241 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddArchimedeanCoreNewestBlock_crossEnergy M (2 * M) (by omega)]
  exact c13OddArchimedeanAdjacentBilinear_sq_le_241Thousandths M hM x y

theorem c13EvenCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_2719Over750
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenCoreNewestTotalErrorBlock M (2 * M)) x y) ^ 2 ≤
      (2719 / 750 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy
    (c13EvenPoleCoreNewestBlock M (2 * M)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13EvenArchimedeanCoreNewestBlock M (2 * M)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13EvenPrimeCoreNewestBlock M (2 * M)) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hPole : pole ^ 2 ≤ (51 / 1000 : ℝ) ^ 2 * E :=
    c13EvenPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths
      M (2 * M) hM (by omega) x y
  have hArch : arch ^ 2 ≤ (241 / 1000 : ℝ) ^ 2 * E :=
    c13EvenArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths M hM x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13EvenPrimeCoreNewestCrossEnergy_sq_le_tenThird M (2 * M) (by omega)
      (by omega) x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (51 / 1000 : ℝ) (241 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (2719 / 750 : ℝ) = 51 / 1000 + 241 / 1000 + 10 / 3 by
    norm_num]
  rw [c13EvenCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13OddCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_2719Over750
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddCoreNewestTotalErrorBlock M (2 * M)) x y) ^ 2 ≤
      (2719 / 750 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let E := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let pole := finiteMatrixBlockCrossEnergy
    (c13OddPoleCoreNewestBlock M (2 * M)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13OddArchimedeanCoreNewestBlock M (2 * M)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13OddPrimeCoreNewestBlock M (2 * M)) x y
  have hE : 0 ≤ E := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hPole : pole ^ 2 ≤ (51 / 1000 : ℝ) ^ 2 * E :=
    c13OddPoleCoreNewestCrossEnergy_sq_le_fiftyOneThousandths
      M (2 * M) hM (by omega) x y
  have hArch : arch ^ 2 ≤ (241 / 1000 : ℝ) ^ 2 * E :=
    c13OddArchimedeanAdjacentCrossEnergy_sq_le_241Thousandths M hM x y
  have hPrime : prime ^ 2 ≤ (10 / 3 : ℝ) ^ 2 * E :=
    c13OddPrimeCoreNewestCrossEnergy_sq_le_tenThird M (2 * M) (by omega)
      (by omega) x y
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (51 / 1000 : ℝ) (241 / 1000 : ℝ) (10 / 3 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (2719 / 750 : ℝ) = 51 / 1000 + 241 / 1000 + 10 / 3 by
    norm_num]
  rw [c13OddCoreNewestTotalErrorBlock,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  exact hTotal

theorem c13EvenBuilderAdjacentCrossEnergy_sq_le_2719Over750
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (2719 / 750 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13EvenCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_2719Over750
    M hM x y

theorem c13OddBuilderAdjacentCrossEnergy_sq_le_2719Over750
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (2719 / 750 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddBuilderCoreNewestBlock_crossEnergy_eq_totalError]
  exact c13OddCoreNewestAdjacentTotalErrorCrossEnergy_sq_le_2719Over750
    M hM x y

lemma c13ShellDynamicGap_ge_27Over8_of_ge_3840
    (M : ℕ) (hM : 3840 ≤ M) :
    (27 / 8 : ℝ) ≤ c13ShellDynamicGap M := by
  have hLog := eightHundredTwentyOneHundredths_lt_log_nat_of_ge_3840 M hM
  have hPole := c13_logarithmicCvSPoleTail_le_fiftyOneThousandths M hM
  unfold c13ShellDynamicGap
  nlinarith

lemma c13ShellDynamicGap_two_mul_ge_813Over200_of_ge_3840
    (M : ℕ) (hM : 3840 ≤ M) :
    (813 / 200 : ℝ) ≤ c13ShellDynamicGap (2 * M) := by
  have hLogM := eightHundredTwentyOneHundredths_lt_log_nat_of_ge_3840 M hM
  have hLogTwo := log_two_gt_sixtyNineHundredths
  have hMPos : (0 : ℝ) < M := by positivity
  have hLogMul : Real.log ((2 * M : ℕ) : ℝ) =
      Real.log 2 + Real.log (M : ℝ) := by
    rw [show ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) by norm_num,
      Real.log_mul (by norm_num) (ne_of_gt hMPos)]
  have hPole := c13_logarithmicCvSPoleTail_le_fiftyOneThousandths
    (2 * M) (by omega)
  unfold c13ShellDynamicGap
  rw [hLogMul]
  nlinarith

theorem c13EvenBuilderAdjacentBaseEnergy_ge_27Over8
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin (2 * M - M) → ℝ) :
    (27 / 8 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x := by
  have hShell := c13_logarithmicCvSBuilderEvenShell_energy_ge_dynamicGap_normSq
    M (2 * M - M) (by omega) (by omega) x
  have hGap := c13ShellDynamicGap_ge_27Over8_of_ge_3840 M hM
  have hScaled := mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg x)
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13EvenBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using hScaled.trans hShell

theorem c13OddBuilderAdjacentBaseEnergy_ge_27Over8
    (M : ℕ) (hM : 3840 ≤ M) (x : Fin (2 * M - M) → ℝ) :
    (27 / 8 : ℝ) * finiteVectorEuclideanNormSq x ≤
      finiteMatrixBlockBaseEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x := by
  have hShell := c13_logarithmicCvSBuilderOddShell_energy_ge_dynamicGap_normSq
    M (2 * M - M) (by omega) (by omega) x
  have hGap := c13ShellDynamicGap_ge_27Over8_of_ge_3840 M hM
  have hScaled := mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg x)
  unfold finiteMatrixBlockBaseEnergy
  simpa only [c13OddBuilderCoreNewestBlock_inl_inl,
    finiteMatrixQuadraticEnergy] using hScaled.trans hShell

theorem c13EvenBuilderAdjacentTailEnergy_ge_813Over200
    (M : ℕ) (hM : 3840 ≤ M) (y : Fin (2 * M) → ℝ) :
    (813 / 200 : ℝ) * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  have hTail := c13EvenBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    M (2 * M) (by omega) y
  have hGap := c13ShellDynamicGap_two_mul_ge_813Over200_of_ge_3840 M hM
  exact (mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg y)).trans hTail

theorem c13OddBuilderAdjacentTailEnergy_ge_813Over200
    (M : ℕ) (hM : 3840 ≤ M) (y : Fin (2 * M) → ℝ) :
    (813 / 200 : ℝ) * finiteVectorEuclideanNormSq y ≤
      finiteMatrixBlockTailEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  have hTail := c13OddBuilderCoreNewestTailEnergy_ge_dynamicGap_normSq
    M (2 * M) (by omega) y
  have hGap := c13ShellDynamicGap_two_mul_ge_813Over200_of_ge_3840 M hM
  exact (mul_le_mul_of_nonneg_right hGap
    (finiteVectorEuclideanNormSq_nonneg y)).trans hTail

lemma c13_adjacentImprovedCrossBudget_le_24Over25_gapProduct :
    (2719 / 750 : ℝ) ^ 2 ≤
      (24 / 25 : ℝ) * (27 / 8 : ℝ) * (813 / 200 : ℝ) := by
  norm_num

/-- Starting at the current certified frontier, one complete adjacent
dyadic shell couples to the next with coefficient `24/25`.  This is the
first strict-below-one bridge at scale `3840`; the earlier Frobenius
Archimedean estimate did not close here. -/
theorem c13EvenBuilderAdjacent_relative_24Over25
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (24 / 25 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) x *
        finiteMatrixBlockTailEnergy
          (c13EvenBuilderCoreNewestBlock M (2 * M)) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) y)
    (finiteMatrixBlockCrossEnergy (c13EvenBuilderCoreNewestBlock M (2 * M)) x y)
    (27 / 8) (813 / 200) ((2719 / 750) ^ 2) (24 / 25)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (by norm_num) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    (c13EvenBuilderAdjacentBaseEnergy_ge_27Over8 M hM x)
    (c13EvenBuilderAdjacentTailEnergy_ge_813Over200 M hM y)
    (c13EvenBuilderAdjacentCrossEnergy_sq_le_2719Over750 M hM x y)
    c13_adjacentImprovedCrossBudget_le_24Over25_gapProduct

/-- Odd-parity companion of the initial analytic bridge. -/
theorem c13OddBuilderAdjacent_relative_24Over25
    (M : ℕ) (hM : 3840 ≤ M)
    (x : Fin (2 * M - M) → ℝ) (y : Fin (2 * M) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddBuilderCoreNewestBlock M (2 * M)) x y) ^ 2 ≤
      (24 / 25 : ℝ) *
        finiteMatrixBlockBaseEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) x *
        finiteMatrixBlockTailEnergy
          (c13OddBuilderCoreNewestBlock M (2 * M)) y := by
  apply relativeCoupling_of_squaredNormBudget
    (finiteMatrixBlockBaseEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) x)
    (finiteMatrixBlockTailEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) y)
    (finiteMatrixBlockCrossEnergy (c13OddBuilderCoreNewestBlock M (2 * M)) x y)
    (27 / 8) (813 / 200) ((2719 / 750) ^ 2) (24 / 25)
    (finiteVectorEuclideanNormSq x) (finiteVectorEuclideanNormSq y)
    (by norm_num) (by norm_num) (by norm_num)
    (finiteVectorEuclideanNormSq_nonneg x) (finiteVectorEuclideanNormSq_nonneg y)
    (c13OddBuilderAdjacentBaseEnergy_ge_27Over8 M hM x)
    (c13OddBuilderAdjacentTailEnergy_ge_813Over200 M hM y)
    (c13OddBuilderAdjacentCrossEnergy_sq_le_2719Over750 M hM x y)
    c13_adjacentImprovedCrossBudget_le_24Over25_gapProduct

end RiemannCvs.V23BoundaryWeylMainline
