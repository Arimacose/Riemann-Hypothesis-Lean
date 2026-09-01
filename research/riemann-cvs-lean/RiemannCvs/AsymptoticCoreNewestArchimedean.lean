import RiemannCvs.AsymptoticTailOperatorBound

noncomputable section

/-!
# Full-core/newest-shell Archimedean compression

This module controls a rectangular block that is substantially larger than the
adjacent-shell block in `AsymptoticTailOperatorBound`.  Fix `960 ≤ M ≤ N`.
The rows exhaust the whole historical interval `(M,N]`, while the columns are
the newest dyadic shell `(N,2N]`.

The centered Archimedean symbol satisfies `|S_n-π/4| ≤ 1/(4n)`.  For
`p ≤ N < q`, the same-sign quotient gains the elementary separation factor

`p * (q-p) ≥ N`,

and the reflected centered quotient collapses algebraically to a multiple of
`1/(p*q)`.  Together with the explicit reflected Hilbert term, every entry is
at most

`(2/3 + 1/(12M))/N`.

There are at most `N^2` entries, so rectangular Cauchy--Schwarz removes the
dimension exactly.  The resulting even and odd cross-block operator amplitude
is at most `2/3 + 1/(12M)`, hence at most `667/1000` for every `M ≥ 960`.
This is uniform in the length of the historical core and therefore supplies a
new source route for the previously open old-core/new-shell channel.
-/

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail

lemma separated_product_ge_split
    (p q N : ℝ) (hp : 1 ≤ p) (hpN : p ≤ N) (hNq : N + 1 ≤ q) :
    N ≤ p * (q - p) := by
  have h1 : 0 ≤ (p - 1) * (N - p) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma centered_sameSign_scalar_le
    (p q N : ℝ) (hp : 1 ≤ p) (hpN : p ≤ N) (hNq : N + 1 ≤ q) :
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (q - p)) ≤ 1 / (6 * N) := by
  have hN : 0 < N := lt_of_lt_of_le (by linarith : 0 < p) hpN
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hqp : 0 < q - p := by linarith
  have hprod : N ≤ p * (q - p) := separated_product_ge_split p q N hp hpN hNq
  have hinvqp : 1 / (p * (q - p)) ≤ 1 / N :=
    one_div_le_one_div_of_le hN hprod
  have hqinv : 1 / q ≤ 1 / p := one_div_le_one_div_of_le hp0 (by linarith)
  have hpq : p ≤ q := by linarith
  calc
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (q - p))
        ≤ (1 / (4 * p) + 1 / (4 * p)) / (3 * (q - p)) := by gcongr
    _ = (1 / 6) * (1 / (p * (q - p))) := by field_simp; ring
    _ ≤ (1 / 6) * (1 / N) := mul_le_mul_of_nonneg_left hinvqp (by norm_num)
    _ = 1 / (6 * N) := by ring

lemma centered_reflected_scalar_le
    (p q M N : ℝ) (hM : 0 < M) (hMp : M ≤ p) (hN : 0 < N) (hNq : N ≤ q) :
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (p + q)) ≤ 1 / (12 * M * N) := by
  have hp : 0 < p := hM.trans_le hMp
  have hq : 0 < q := hN.trans_le hNq
  have hprod : M * N ≤ p * q := mul_le_mul hMp hNq hN.le hp.le
  have hinv : 1 / (p * q) ≤ 1 / (M * N) :=
    one_div_le_one_div_of_le (mul_pos hM hN) hprod
  calc
    (1 / (4 * p) + 1 / (4 * q)) / (3 * (p + q)) =
        (1 / 12) * (1 / (p * q)) := by field_simp; ring
    _ ≤ (1 / 12) * (1 / (M * N)) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 1 / (12 * M * N) := by ring

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2

noncomputable def c13EvenArchimedeanCoreNewestEntry (p q : ℕ) : ℝ :=
  -logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ) -
    logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))

noncomputable def c13OddArchimedeanCoreNewestEntry (p q : ℕ) : ℝ :=
  -logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ) +
    logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))

lemma c13_centeredArchimedeanSymbol_nat_abs_le
    (n : ℕ) (hn : 960 ≤ n) :
    |centeredArchimedeanSymbol 13 (n : ℤ)| ≤ (1 / 4 : ℝ) / (n : ℝ) := by
  simpa [centeredArchimedeanSymbol] using
    c13_centeredLogarithmicArchimedeanSymbol_abs_le (n : ℝ) (by exact_mod_cast hn)

lemma c13_archimedean_sameSign_nat_abs_le
    (p q : ℕ) (hp : 960 ≤ p) (hpq : p < q) :
    |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)| ≤
      (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
        (3 * ((q : ℝ) - (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hcp := c13_centeredArchimedeanSymbol_nat_abs_le p hp
  have hcq := c13_centeredArchimedeanSymbol_nat_abs_le q (by omega)
  rw [logarithmicCvSArchimedeanEntry_sameSign_eq 13 (p : ℤ) (q : ℤ)
    (by exact_mod_cast (Nat.ne_of_lt hpq))]
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  have hdiff : |((p : ℤ) : ℝ) - ((q : ℤ) : ℝ)| =
      (q : ℝ) - (p : ℝ) := by
    change |(p : ℝ) - (q : ℝ)| = (q : ℝ) - (p : ℝ)
    simpa only [neg_sub] using abs_of_neg (sub_neg.mpr hpqR)
  rw [hdiff]
  have hnum :
      |centeredArchimedeanSymbol 13 (q : ℤ) -
          centeredArchimedeanSymbol 13 (p : ℤ)| ≤
        1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ)) := by
    calc
      |centeredArchimedeanSymbol 13 (q : ℤ) -
          centeredArchimedeanSymbol 13 (p : ℤ)| ≤
          |centeredArchimedeanSymbol 13 (q : ℤ)| +
            |centeredArchimedeanSymbol 13 (p : ℤ)| := abs_sub _ _
      _ ≤ (1 / 4 : ℝ) / (q : ℝ) + (1 / 4 : ℝ) / (p : ℝ) := add_le_add hcq hcp
      _ = 1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ)) := by ring
  have hden : 3 * ((q : ℝ) - (p : ℝ)) ≤
      Real.pi * ((q : ℝ) - (p : ℝ)) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith)
  have hden0 : 0 < 3 * ((q : ℝ) - (p : ℝ)) := by positivity
  calc
    |centeredArchimedeanSymbol 13 (q : ℤ) -
        centeredArchimedeanSymbol 13 (p : ℤ)| /
        (Real.pi * ((q : ℝ) - (p : ℝ))) ≤
      (1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ))) /
        (Real.pi * ((q : ℝ) - (p : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (1 / (4 * (q : ℝ)) + 1 / (4 * (p : ℝ))) /
        (3 * ((q : ℝ) - (p : ℝ))) := by
      gcongr
    _ = _ := by ring

lemma c13_archimedean_reflected_nat_abs_le
    (p q M N : ℕ) (hM : 960 ≤ M) (hMp : M ≤ p)
    (hN : 1 ≤ N) (hNq : N < q) (hpq : p < q) :
    |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))| ≤
      1 / (2 * (N : ℝ)) + 1 / (12 * (M : ℝ) * (N : ℝ)) := by
  have hpNat : 0 < p := by omega
  have hqNat : 0 < q := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpNat
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpR : (M : ℝ) ≤ p := by exact_mod_cast hMp
  have hNqR : (N : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt hNq)
  have hcp := c13_centeredArchimedeanSymbol_nat_abs_le p (by omega)
  have hcq := c13_centeredArchimedeanSymbol_nat_abs_le q (by omega)
  rw [logarithmicCvSArchimedeanEntry_reflected_eq 13 (p : ℤ) (q : ℤ)
    (by exact_mod_cast hpNat) (by exact_mod_cast hqNat)]
  have hsum : (0 : ℝ) < (p : ℝ) + (q : ℝ) := by positivity
  have hlead : 1 / (2 * ((p : ℝ) + (q : ℝ))) ≤ 1 / (2 * (N : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hcenterNum :
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
        1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by
    calc
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| ≤
          |centeredArchimedeanSymbol 13 (p : ℤ)| +
            |centeredArchimedeanSymbol 13 (q : ℤ)| := abs_add_le _ _
      _ ≤ (1 / 4 : ℝ) / (p : ℝ) + (1 / 4 : ℝ) / (q : ℝ) := add_le_add hcp hcq
      _ = 1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ)) := by ring
  have hden : 3 * ((p : ℝ) + (q : ℝ)) ≤
      Real.pi * ((p : ℝ) + (q : ℝ)) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le hsum.le
  have hcenter :
      |(centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)) /
            (Real.pi * ((p : ℝ) + (q : ℝ)))| ≤
        1 / (12 * (M : ℝ) * (N : ℝ)) := by
    rw [abs_div, abs_of_pos (mul_pos Real.pi_pos hsum)]
    calc
      |centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)| /
          (Real.pi * ((p : ℝ) + (q : ℝ))) ≤
        (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
          (Real.pi * ((p : ℝ) + (q : ℝ))) :=
        div_le_div_of_nonneg_right hcenterNum (by positivity)
      _ ≤ (1 / (4 * (p : ℝ)) + 1 / (4 * (q : ℝ))) /
          (3 * ((p : ℝ) + (q : ℝ))) := by
        gcongr
      _ ≤ 1 / (12 * (M : ℝ) * (N : ℝ)) :=
        centered_reflected_scalar_le (p : ℝ) (q : ℝ) (M : ℝ) (N : ℝ)
          hMR hMpR hNR hNqR
  calc
    |-(1 / (2 * ((p : ℝ) + (q : ℝ)))) -
        (centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)) /
            (Real.pi * ((p : ℝ) + (q : ℝ)))| ≤
      |-(1 / (2 * ((p : ℝ) + (q : ℝ))))| +
        |(centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)) /
            (Real.pi * ((p : ℝ) + (q : ℝ)))| := abs_sub _ _
    _ = 1 / (2 * ((p : ℝ) + (q : ℝ))) +
        |(centeredArchimedeanSymbol 13 (p : ℤ) +
          centeredArchimedeanSymbol 13 (q : ℤ)) /
            (Real.pi * ((p : ℝ) + (q : ℝ)))| := by
      rw [abs_neg, abs_of_pos]
      positivity
    _ ≤ 1 / (2 * (N : ℝ)) + 1 / (12 * (M : ℝ) * (N : ℝ)) :=
      add_le_add hlead hcenter

end RiemannCvs.V23BoundaryWeylMainline


namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2

lemma c13_archimedean_sameSign_coreNewest_abs_le
    (p q N : ℕ) (hp : 960 ≤ p) (hpN : p ≤ N) (hNq : N < q) :
    |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)| ≤
      1 / (6 * (N : ℝ)) := by
  have hRaw := c13_archimedean_sameSign_nat_abs_le p q hp (by omega)
  exact hRaw.trans (centered_sameSign_scalar_le
    (p : ℝ) (q : ℝ) (N : ℝ)
    (by exact_mod_cast (show 1 ≤ p by omega))
    (by exact_mod_cast hpN)
    (by exact_mod_cast (show N + 1 ≤ q by omega)))

lemma c13EvenArchimedeanCoreNewestEntry_abs_le
    (p q M N : ℕ) (hM : 960 ≤ M) (hMp : M ≤ p)
    (hpN : p ≤ N) (hNq : N < q) :
    |c13EvenArchimedeanCoreNewestEntry p q| ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by
  have hN : 1 ≤ N := by omega
  have hsame := c13_archimedean_sameSign_coreNewest_abs_le p q N (by omega) hpN hNq
  have href := c13_archimedean_reflected_nat_abs_le p q M N hM hMp hN hNq (by omega)
  unfold c13EvenArchimedeanCoreNewestEntry
  calc
    |-logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ) -
        logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))| ≤
      |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)| +
        |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))| := by
      simpa only [abs_neg] using abs_sub
        (-logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ))
        (logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ)))
    _ ≤ 1 / (6 * (N : ℝ)) +
        (1 / (2 * (N : ℝ)) + 1 / (12 * (M : ℝ) * (N : ℝ))) :=
      add_le_add hsame href
    _ = (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by ring

lemma c13OddArchimedeanCoreNewestEntry_abs_le
    (p q M N : ℕ) (hM : 960 ≤ M) (hMp : M ≤ p)
    (hpN : p ≤ N) (hNq : N < q) :
    |c13OddArchimedeanCoreNewestEntry p q| ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by
  have hN : 1 ≤ N := by omega
  have hsame := c13_archimedean_sameSign_coreNewest_abs_le p q N (by omega) hpN hNq
  have href := c13_archimedean_reflected_nat_abs_le p q M N hM hMp hN hNq (by omega)
  unfold c13OddArchimedeanCoreNewestEntry
  calc
    |-logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ) +
        logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))| ≤
      |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ)| +
        |logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ))| := by
      simpa only [abs_neg] using abs_add_le
        (-logarithmicCvSArchimedeanEntry 13 (p : ℤ) (q : ℤ))
        (logarithmicCvSArchimedeanEntry 13 (p : ℤ) (-(q : ℤ)))
    _ ≤ 1 / (6 * (N : ℝ)) +
        (1 / (2 * (N : ℝ)) + 1 / (12 * (M : ℝ) * (N : ℝ))) :=
      add_le_add hsame href
    _ = (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by ring

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open Finset
open RiemannCvs.CombinedSymbolDyadicL2

lemma rectangular_bilinear_sq_le_of_entry_abs_le_div
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (columns : Finset κ)
    (entry : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (N : ℕ) (B : ℝ) (hN : N ≠ 0) (hB : 0 ≤ B)
    (hRows : rows.card ≤ N) (hColumns : columns.card ≤ N)
    (hEntry : ∀ i ∈ rows, ∀ j ∈ columns,
      |entry i j| ≤ B / (N : ℝ)) :
    (∑ ij ∈ rows ×ˢ columns,
        entry ij.1 ij.2 * (x ij.1 * y ij.2)) ^ 2 ≤
      B ^ 2 * ((∑ i ∈ rows, x i ^ 2) * ∑ j ∈ columns, y j ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hEntrySq : ∀ i ∈ rows, ∀ j ∈ columns,
      (entry i j) ^ 2 ≤ (B / (N : ℝ)) ^ 2 := by
    intro i hi j hj
    have h := (sq_le_sq₀ (abs_nonneg (entry i j))
      (div_nonneg hB hNR.le)).2 (hEntry i hi j hj)
    simpa only [sq_abs] using h
  have hCard : (rows.card : ℝ) * (columns.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hr : (rows.card : ℝ) ≤ N := by exact_mod_cast hRows
    have hc : (columns.card : ℝ) ≤ N := by exact_mod_cast hColumns
    have hr0 : (0 : ℝ) ≤ (rows.card : ℝ) := by positivity
    have hc0 : (0 : ℝ) ≤ (columns.card : ℝ) := by positivity
    nlinarith
  have hEntries :
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) ≤ B ^ 2 := by
    calc
      (∑ ij ∈ rows ×ˢ columns, (entry ij.1 ij.2) ^ 2) ≤
          ∑ _ij ∈ rows ×ˢ columns, (B / (N : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij hij
        exact hEntrySq ij.1 (Finset.mem_product.mp hij).1
          ij.2 (Finset.mem_product.mp hij).2
      _ = ((rows.card : ℝ) * (columns.card : ℝ)) *
          (B / (N : ℝ)) ^ 2 := by simp [mul_assoc]
      _ ≤ (N : ℝ) ^ 2 * (B / (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
      _ = B ^ 2 := by field_simp [ne_of_gt hNR]
  have hCauchy := rectangular_bilinear_sq_le_entry_sq_mul_norms
    rows columns entry x y
  exact hCauchy.trans (mul_le_mul_of_nonneg_right hEntries (by positivity))

noncomputable def c13CoreMode (M N : ℕ) (i : Fin (N - M)) : ℕ :=
  M + 1 + (i : ℕ)

noncomputable def c13NewestMode (N : ℕ) (j : Fin N) : ℕ :=
  N + 1 + (j : ℕ)

noncomputable def c13EvenArchimedeanCoreNewestMatrix (M N : ℕ) :
    Matrix (Fin (N - M)) (Fin N) ℝ :=
  fun i j => c13EvenArchimedeanCoreNewestEntry (c13CoreMode M N i) (c13NewestMode N j)

noncomputable def c13OddArchimedeanCoreNewestMatrix (M N : ℕ) :
    Matrix (Fin (N - M)) (Fin N) ℝ :=
  fun i j => c13OddArchimedeanCoreNewestEntry (c13CoreMode M N i) (c13NewestMode N j)

lemma c13CoreMode_bounds
    (M N : ℕ) (hMN : M ≤ N) (i : Fin (N - M)) :
    M ≤ c13CoreMode M N i ∧ c13CoreMode M N i ≤ N := by
  unfold c13CoreMode
  omega

lemma c13NewestMode_gt
    (N : ℕ) (j : Fin N) : N < c13NewestMode N j := by
  unfold c13NewestMode
  omega

lemma c13EvenArchimedeanCoreNewestMatrix_entry_abs_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (i : Fin (N - M)) (j : Fin N) :
    |c13EvenArchimedeanCoreNewestMatrix M N i j| ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by
  apply c13EvenArchimedeanCoreNewestEntry_abs_le
  · exact hM
  · exact (c13CoreMode_bounds M N hMN i).1
  · exact (c13CoreMode_bounds M N hMN i).2
  · exact c13NewestMode_gt N j

lemma c13OddArchimedeanCoreNewestMatrix_entry_abs_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (i : Fin (N - M)) (j : Fin N) :
    |c13OddArchimedeanCoreNewestMatrix M N i j| ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) / (N : ℝ) := by
  apply c13OddArchimedeanCoreNewestEntry_abs_le
  · exact hM
  · exact (c13CoreMode_bounds M N hMN i).1
  · exact (c13CoreMode_bounds M N hMN i).2
  · exact c13NewestMode_gt N j

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open Finset

noncomputable def finiteRectangularBilinearEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * y j

lemma finiteRectangularBilinearEnergy_eq_product_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    finiteRectangularBilinearEnergy A x y =
      ∑ ij ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset κ),
        A ij.1 ij.2 * (x ij.1 * y ij.2) := by
  unfold finiteRectangularBilinearEnergy
  rw [Finset.sum_product]
  simp only [mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

 theorem c13EvenArchimedeanCoreNewestBilinear_sq_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13EvenArchimedeanCoreNewestMatrix M N) x y) ^ 2 ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : N ≠ 0 := by omega
  have h := rectangular_bilinear_sq_le_of_entry_abs_le_div
    (Finset.univ : Finset (Fin (N - M))) (Finset.univ : Finset (Fin N))
    (c13EvenArchimedeanCoreNewestMatrix M N) x y N
    (2 / 3 + 1 / (12 * (M : ℝ))) hN (by positivity)
    (by simp) (by simp)
    (fun i _hi j _hj =>
      c13EvenArchimedeanCoreNewestMatrix_entry_abs_le M N hM hMN i j)
  rw [finiteRectangularBilinearEnergy_eq_product_sum]
  simpa only [finiteVectorEuclideanNormSq] using h

 theorem c13OddArchimedeanCoreNewestBilinear_sq_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteRectangularBilinearEnergy
        (c13OddArchimedeanCoreNewestMatrix M N) x y) ^ 2 ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : N ≠ 0 := by omega
  have h := rectangular_bilinear_sq_le_of_entry_abs_le_div
    (Finset.univ : Finset (Fin (N - M))) (Finset.univ : Finset (Fin N))
    (c13OddArchimedeanCoreNewestMatrix M N) x y N
    (2 / 3 + 1 / (12 * (M : ℝ))) hN (by positivity)
    (by simp) (by simp)
    (fun i _hi j _hj =>
      c13OddArchimedeanCoreNewestMatrix_entry_abs_le M N hM hMN i j)
  rw [finiteRectangularBilinearEnergy_eq_product_sum]
  simpa only [finiteVectorEuclideanNormSq] using h

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.CombinedSymbolDyadicL2

lemma logarithmicCvSArchimedeanEntry_symm
    (c : ℝ) (n m : ℤ) :
    logarithmicCvSArchimedeanEntry c n m =
      logarithmicCvSArchimedeanEntry c m n := by
  by_cases h : n = m
  · subst m
    rfl
  · have hcast : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast h
    simp only [logarithmicCvSArchimedeanEntry, h, if_false, Ne.symm h]
    field_simp [Real.pi_ne_zero, hcast]
    ring

lemma logarithmicCvSArchimedeanEntry_reflected_pos_symm
    (c : ℝ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) :
    logarithmicCvSArchimedeanEntry c n (-m) =
      logarithmicCvSArchimedeanEntry c m (-n) := by
  rw [logarithmicCvSArchimedeanEntry_reflected_eq c n m hn hm,
    logarithmicCvSArchimedeanEntry_reflected_eq c m n hm hn]
  ring

lemma logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix_symm_of_pos
    {κ : Type*} [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) (hMode : ∀ i, 0 < mode i)
    (i j : κ) :
    logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c mode i j =
      logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix c mode j i := by
  unfold logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix
  rw [logarithmicCvSArchimedeanEntry_symm c (mode i) (mode j),
    logarithmicCvSArchimedeanEntry_reflected_pos_symm c (mode i) (mode j)
      (hMode i) (hMode j)]
  by_cases h : i = j
  · subst j
    rfl
  · simp [h, Ne.symm h]

lemma logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix_symm_of_pos
    {κ : Type*} [DecidableEq κ]
    (c : ℝ) (mode : κ → ℤ) (hMode : ∀ i, 0 < mode i)
    (i j : κ) :
    logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c mode i j =
      logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix c mode j i := by
  unfold logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix
  rw [logarithmicCvSArchimedeanEntry_symm c (mode i) (mode j),
    logarithmicCvSArchimedeanEntry_reflected_pos_symm c (mode i) (mode j)
      (hMode i) (hMode j)]
  by_cases h : i = j
  · subst j
    rfl
  · simp [h, Ne.symm h]

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail

noncomputable def c13CoreNewestPositiveMode (M N : ℕ) :
    Fin (N - M) ⊕ Fin N → ℤ :=
  Sum.elim
    (fun i => (c13CoreMode M N i : ℤ))
    (fun j => (c13NewestMode N j : ℤ))

noncomputable def c13EvenArchimedeanCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix 13
    (c13CoreNewestPositiveMode M N)

noncomputable def c13OddArchimedeanCoreNewestBlock (M N : ℕ) :
    Matrix (Fin (N - M) ⊕ Fin N) (Fin (N - M) ⊕ Fin N) ℝ :=
  logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix 13
    (c13CoreNewestPositiveMode M N)

lemma c13CoreNewestPositiveMode_pos
    (M N : ℕ) (hM : 960 ≤ M) (i : Fin (N - M) ⊕ Fin N) :
    0 < c13CoreNewestPositiveMode M N i := by
  cases i with
  | inl i =>
      simp only [c13CoreNewestPositiveMode, c13CoreMode, Sum.elim_inl]
      exact_mod_cast (show 0 < M + 1 + (i : ℕ) by omega)
  | inr j =>
      simp only [c13CoreNewestPositiveMode, c13NewestMode, Sum.elim_inr]
      exact_mod_cast (show 0 < N + 1 + (j : ℕ) by omega)

@[simp] lemma c13EvenArchimedeanCoreNewestBlock_inl_inr
    (M N : ℕ) (i : Fin (N - M)) (j : Fin N) :
    c13EvenArchimedeanCoreNewestBlock M N (Sum.inl i) (Sum.inr j) =
      c13EvenArchimedeanCoreNewestMatrix M N i j := by
  simp only [c13EvenArchimedeanCoreNewestBlock,
    logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
    Sum.inl_ne_inr, if_false,
    c13CoreNewestPositiveMode, Sum.elim_inl, Sum.elim_inr,
    c13EvenArchimedeanCoreNewestMatrix,
    c13EvenArchimedeanCoreNewestEntry]

@[simp] lemma c13OddArchimedeanCoreNewestBlock_inl_inr
    (M N : ℕ) (i : Fin (N - M)) (j : Fin N) :
    c13OddArchimedeanCoreNewestBlock M N (Sum.inl i) (Sum.inr j) =
      c13OddArchimedeanCoreNewestMatrix M N i j := by
  simp only [c13OddArchimedeanCoreNewestBlock,
    logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
    Sum.inl_ne_inr, if_false,
    c13CoreNewestPositiveMode, Sum.elim_inl, Sum.elim_inr,
    c13OddArchimedeanCoreNewestMatrix,
    c13OddArchimedeanCoreNewestEntry]

lemma c13EvenArchimedeanCoreNewestBlock_symm
    (M N : ℕ) (hM : 960 ≤ M)
    (i j : Fin (N - M) ⊕ Fin N) :
    c13EvenArchimedeanCoreNewestBlock M N i j =
      c13EvenArchimedeanCoreNewestBlock M N j i := by
  exact logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix_symm_of_pos
    13 (c13CoreNewestPositiveMode M N)
    (c13CoreNewestPositiveMode_pos M N hM) i j

lemma c13OddArchimedeanCoreNewestBlock_symm
    (M N : ℕ) (hM : 960 ≤ M)
    (i j : Fin (N - M) ⊕ Fin N) :
    c13OddArchimedeanCoreNewestBlock M N i j =
      c13OddArchimedeanCoreNewestBlock M N j i := by
  exact logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix_symm_of_pos
    13 (c13CoreNewestPositiveMode M N)
    (c13CoreNewestPositiveMode_pos M N hM) i j

lemma c13EvenArchimedeanCoreNewestBlock_crossEnergy
    (M N : ℕ) (hM : 960 ≤ M)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13EvenArchimedeanCoreNewestBlock M N) x y =
      finiteRectangularBilinearEnergy
        (c13EvenArchimedeanCoreNewestMatrix M N) x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13EvenArchimedeanCoreNewestBlock M N) x y
    (c13EvenArchimedeanCoreNewestBlock_symm M N hM)]
  rfl

lemma c13OddArchimedeanCoreNewestBlock_crossEnergy
    (M N : ℕ) (hM : 960 ≤ M)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy
        (c13OddArchimedeanCoreNewestBlock M N) x y =
      finiteRectangularBilinearEnergy
        (c13OddArchimedeanCoreNewestMatrix M N) x y := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13OddArchimedeanCoreNewestBlock M N) x y
    (c13OddArchimedeanCoreNewestBlock_symm M N hM)]
  rfl

 theorem c13EvenArchimedeanCoreNewestCrossEnergy_sq_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenArchimedeanCoreNewestBlock M N) x y) ^ 2 ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13EvenArchimedeanCoreNewestBlock_crossEnergy M N hM]
  exact c13EvenArchimedeanCoreNewestBilinear_sq_le M N hM hMN x y

 theorem c13OddArchimedeanCoreNewestCrossEnergy_sq_le
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddArchimedeanCoreNewestBlock M N) x y) ^ 2 ≤
      (2 / 3 + 1 / (12 * (M : ℝ))) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13OddArchimedeanCoreNewestBlock_crossEnergy M N hM]
  exact c13OddArchimedeanCoreNewestBilinear_sq_le M N hM hMN x y

end RiemannCvs.V23BoundaryWeylMainline

namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail

lemma c13_archimedeanCoreNewestAmplitude_le_sixHundredSixtySevenThousandths
    (M : ℕ) (hM : 960 ≤ M) :
    (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) ≤ 667 / 1000 := by
  have hMR : (960 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMPos : (0 : ℝ) < (M : ℝ) := by positivity
  have hInv : 1 / (M : ℝ) ≤ 1 / 960 :=
    one_div_le_one_div_of_le (by norm_num) hMR
  have hScaled := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : ℝ) ≤ 1 / 12)
  calc
    (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) = 2 / 3 + (1 / 12) * (1 / (M : ℝ)) := by ring
    _ ≤ 2 / 3 + (1 / 12) * (1 / 960) := by linarith
    _ ≤ 667 / 1000 := by norm_num

 theorem c13EvenArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13EvenArchimedeanCoreNewestBlock M N) x y) ^ 2 ≤
      (667 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13EvenArchimedeanCoreNewestCrossEnergy_sq_le M N hM hMN x y
  have hAmp := c13_archimedeanCoreNewestAmplitude_le_sixHundredSixtySevenThousandths M hM
  have hAmp0 : 0 ≤ (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) := by positivity
  have hSquare : (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) ^ 2 ≤
      (667 / 1000 : ℝ) ^ 2 := by nlinarith
  exact hRaw.trans (mul_le_mul_of_nonneg_right hSquare
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

 theorem c13OddArchimedeanCoreNewestCrossEnergy_sq_le_sixHundredSixtySevenThousandths
    (M N : ℕ) (hM : 960 ≤ M) (hMN : M ≤ N)
    (x : Fin (N - M) → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13OddArchimedeanCoreNewestBlock M N) x y) ^ 2 ≤
      (667 / 1000 : ℝ) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13OddArchimedeanCoreNewestCrossEnergy_sq_le M N hM hMN x y
  have hAmp := c13_archimedeanCoreNewestAmplitude_le_sixHundredSixtySevenThousandths M hM
  have hAmp0 : 0 ≤ (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) := by positivity
  have hSquare : (2 / 3 + 1 / (12 * (M : ℝ)) : ℝ) ^ 2 ≤
      (667 / 1000 : ℝ) ^ 2 := by nlinarith
  exact hRaw.trans (mul_le_mul_of_nonneg_right hSquare
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

end RiemannCvs.V23BoundaryWeylMainline
