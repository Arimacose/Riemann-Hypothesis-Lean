import Mathlib
import RiemannCvs.BoundaryWeylUniformLimit

/-!
# Normalized far-left boundary-Weyl asymptotic

For nonnegative poles and total residue one, expanding each resolvent weight
around `1/t` at `x = -t` gives a completely explicit exterior bound.  A first
absolute spectral moment `moment` controls the remainder by `moment/t²`.
The final theorem passes the resulting positive margin through pointwise
Galerkin convergence whenever the same moment budget is eventual in the
cutoff.
-/

namespace RiemannCvs.BoundaryWeylFarLeft

open scoped BigOperators
open Filter
open RiemannCvs.BoundaryWeylCumulative

/-- With total residue one and nonnegative poles, the far-left Weyl function
is within `moment / t²` of its normalized leading term `1 / t`. -/
theorem finiteBoundaryWeyl_sub_oneDiv_abs_le
    (poles residues : ℕ → ℝ) (N : ℕ) (t moment : ℝ)
    (ht : 0 < t)
    (hPoles : ∀ j, j ≤ N → 0 ≤ poles j)
    (hTotal : prefixSum residues N = 1)
    (hMoment :
      (∑ j ∈ Finset.range (N + 1), |residues j| * poles j) ≤ moment) :
    |finiteBoundaryWeyl poles residues N (-t) - 1 / t| ≤
      moment / t ^ 2 := by
  have hTotal' : (∑ j ∈ Finset.range (N + 1), residues j) = 1 := hTotal
  have hRewrite :
      finiteBoundaryWeyl poles residues N (-t) - 1 / t =
        ∑ j ∈ Finset.range (N + 1),
          (residues j / (poles j + t) - residues j / t) := by
    rw [finiteBoundaryWeyl]
    simp only [sub_neg_eq_add]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hTotal']
  rw [hRewrite]
  calc
    |∑ j ∈ Finset.range (N + 1),
        (residues j / (poles j + t) - residues j / t)| ≤
        ∑ j ∈ Finset.range (N + 1),
          |residues j / (poles j + t) - residues j / t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          (|residues j| * poles j) / t ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := by
        have hlt : j < N + 1 := Finset.mem_range.mp hj
        omega
      have hp : 0 ≤ poles j := hPoles j hjN
      have hpt : 0 < poles j + t := add_pos_of_nonneg_of_pos hp ht
      have hden : t ^ 2 ≤ t * (poles j + t) := by
        nlinarith [mul_nonneg (le_of_lt ht) hp]
      have hnum : 0 ≤ |residues j| * poles j :=
        mul_nonneg (abs_nonneg _) hp
      calc
        |residues j / (poles j + t) - residues j / t| =
            (|residues j| * poles j) / (t * (poles j + t)) := by
              have htne : t ≠ 0 := ne_of_gt ht
              have hptne : poles j + t ≠ 0 := ne_of_gt hpt
              rw [show residues j / (poles j + t) - residues j / t =
                    -(residues j * poles j) / (t * (poles j + t)) by
                  field_simp [htne, hptne]
                  ring]
              rw [abs_div, abs_neg, abs_mul (residues j) (poles j),
                abs_mul t (poles j + t), abs_of_pos ht,
                abs_of_pos hpt, abs_of_nonneg hp]
        _ ≤ (|residues j| * poles j) / t ^ 2 :=
          div_le_div_of_nonneg_left hnum (sq_pos_of_pos ht) hden
    _ = (∑ j ∈ Finset.range (N + 1), |residues j| * poles j) / t ^ 2 := by
      rw [Finset.sum_div]
    _ ≤ moment / t ^ 2 := by
      exact div_le_div_of_nonneg_right hMoment (sq_nonneg t)

/-- Explicit far-left lower bound.  In particular, a uniform first absolute
spectral moment below `t` leaves the Weyl value strictly positive. -/
theorem finiteBoundaryWeyl_ge_farLeftMargin
    (poles residues : ℕ → ℝ) (N : ℕ) (t moment : ℝ)
    (ht : 0 < t)
    (hPoles : ∀ j, j ≤ N → 0 ≤ poles j)
    (hTotal : prefixSum residues N = 1)
    (hMoment :
      (∑ j ∈ Finset.range (N + 1), |residues j| * poles j) ≤ moment) :
    1 / t - moment / t ^ 2 ≤
      finiteBoundaryWeyl poles residues N (-t) := by
  exact sub_le_of_abs_sub_le_left
    (finiteBoundaryWeyl_sub_oneDiv_abs_le
      poles residues N t moment ht hPoles hTotal hMoment)

/-- A pointwise limit of normalized finite Weyl functions is positive at every
far-left point where a common absolute-moment budget is smaller than `t`. -/
theorem boundaryWeylLimit_pos_of_uniformFarLeftMoment
    (poles residues : ℕ → ℕ → ℝ) (cutoff : ℕ → ℕ)
    (t moment limitValue : ℝ)
    (ht : moment < t)
    (hMomentNonneg : 0 ≤ moment)
    (hPoles : ∀ n j, j ≤ cutoff n → 0 ≤ poles n j)
    (hTotal : ∀ n, prefixSum (residues n) (cutoff n) = 1)
    (hMoment : ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (cutoff n + 1),
        |residues n j| * poles n j) ≤ moment)
    (hTendsto :
      Tendsto
        (fun n => finiteBoundaryWeyl
          (poles n) (residues n) (cutoff n) (-t))
        atTop (nhds limitValue)) :
    0 < limitValue := by
  have htPos : 0 < t := lt_of_le_of_lt hMomentNonneg ht
  have hMarginPos : 0 < 1 / t - moment / t ^ 2 := by
    have hRewrite : 1 / t - moment / t ^ 2 = (t - moment) / t ^ 2 := by
      field_simp [ne_of_gt htPos]
    rw [hRewrite]
    exact div_pos (sub_pos.mpr ht) (sq_pos_of_pos htPos)
  apply lt_of_lt_of_le hMarginPos
  apply ge_of_tendsto hTendsto
  exact hMoment.mono (fun n hn =>
    finiteBoundaryWeyl_ge_farLeftMargin
      (poles n) (residues n) (cutoff n) t moment htPos
      (hPoles n) (hTotal n) hn)

/-- Glue an exterior estimate to one compact negative window.  The far-left
hypothesis covers `x < -moment`; the compact hypothesis covers the remaining
points up to the chosen negative right endpoint. -/
theorem positiveOn_openNegativeTail_of_compact_and_farLeft
    (limit : ℝ → ℝ) (moment delta : ℝ)
    (hCompact : ∀ x ∈ Set.Icc (-moment) (-delta), 0 < limit x)
    (hFarLeft : ∀ t, moment < t → 0 < limit (-t)) :
    ∀ x, x < -delta → 0 < limit x := by
  intro x hx
  by_cases hExterior : x < -moment
  · have ht : moment < -x := by linarith
    simpa using hFarLeft (-x) ht
  · exact hCompact x ⟨le_of_not_gt hExterior, le_of_lt hx⟩

end RiemannCvs.BoundaryWeylFarLeft
