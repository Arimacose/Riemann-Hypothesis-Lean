import RiemannCvs.AdjacentAdiShiftBinding

/-!
# Literal K=3840 ADI shift binding

The second finite adjacent bridge uses 64 same-sign and 12 reflected ADI
factors.  The root and pole expressions are literal logarithmic shifts; the
two integer tables are the unit-cell transcript checked independently by Arb
at 256 and 384 bits.  The interval inequalities remain explicit fields of
`LiteralShiftCertificate`, while all resulting grid noncollision and exact
ADI factorization statements are proved here through the generic binding.
-/

namespace RiemannCvs
namespace K3840AdiShiftBinding

open scoped BigOperators Real
open RiemannCvs.CvSParityDisplacement
open RiemannCvs.AdjacentAdiShiftBinding

/-- Literal 64 same-sign shifts for `[3841/3840,2]` versus `[7681/3840,4]`. -/
noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (3841 / 3840 : ℝ) 2 (7681 / 3840 : ℝ) 4

/-- Literal 12 reflected shifts for `[-4,-7681/3840]` versus `[3841/3840,2]`. -/
noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-7681 / 3840 : ℝ) (3841 / 3840 : ℝ) 2

/-- Arb-certified integer cells containing `3840 * sameShifts[i].pole`. -/
def samePoleCellList : List ℕ :=
  [7681, 7681, 7681, 7681, 7681, 7681, 7681, 7681,
    7682, 7682, 7682, 7683, 7683, 7684, 7684, 7685,
    7685, 7686, 7687, 7688, 7690, 7691, 7693, 7695,
    7697, 7700, 7703, 7706, 7711, 7715, 7721, 7727,
    7735, 7743, 7753, 7764, 7777, 7793, 7810, 7831,
    7854, 7882, 7914, 7951, 7993, 8043, 8101, 8169,
    8247, 8339, 8446, 8572, 8720, 8894, 9100, 9345,
    9636, 9985, 10406, 10919, 11548, 12330, 13317, 14585]

/-- Arb-certified integer cells containing `3840 * (-reflectedShifts[i].pole)`. -/
def reflectedPoleCellList : List ℕ :=
  [7883, 8309, 8767, 9258, 9786, 10355, 10968, 11630, 12345, 13120, 13960, 14873]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by
  rfl

@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by
  rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by
  norm_num

abbrev SameGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop :=
  AdjacentAdiShiftBinding.SameGridCertificate 3840 shifts cells

abbrev ReflectedGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop :=
  AdjacentAdiShiftBinding.ReflectedGridCertificate 3840 shifts cells

structure LiteralShiftCertificate : Prop where
  same : SameGridCertificate sameShifts samePoleCells
  reflected : ReflectedGridCertificate reflectedShifts reflectedPoleCells

theorem gridCell_ne (m q : ℕ) (x : ℝ)
    (hLower : (m : ℝ) < 3840 * x)
    (hUpper : 3840 * x < (m : ℝ) + 1) :
    (q : ℝ) / 3840 ≠ x := by
  exact AdjacentAdiShiftBinding.gridCell_ne 3840 m q x
    (by norm_num) hLower hUpper

theorem same_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : SameGridCertificate shifts cells)
    (p q : ℕ) (hp : p ≤ 7680) (hq : 7681 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 3840 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 3840 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 3840 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.same_noncollision
    3840 (by norm_num) shifts cells hcert p q hp hq

theorem reflected_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : ReflectedGridCertificate shifts cells)
    (p q : ℕ) (hp : 3841 ≤ p) (hq : 7681 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 3840 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 3840 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 3840 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.reflected_noncollision
    3840 (by norm_num) shifts cells hcert p q hp hq

theorem same_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : SameGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 7680) (hq : 7681 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 3840) /
          adiRationalProduct (List.ofFn shifts) ((q : ℝ) / 3840)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 3840) ((q : ℝ) / 3840)
          (-symbol p * (1 / Real.sqrt 3840)) (1 / Real.sqrt 3840) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 3840) ((q : ℝ) / 3840)
          (1 / Real.sqrt 3840) (symbol q * (1 / Real.sqrt 3840)) := by
  exact AdjacentAdiShiftBinding.same_factorization_of_gridCertificate
    3840 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

theorem reflected_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : ReflectedGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 3841 ≤ p) (hq : 7681 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 3840) /
          adiRationalProduct (List.ofFn shifts) (-(q : ℝ) / 3840)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 3840) (-(q : ℝ) / 3840)
          (-symbol p * (1 / Real.sqrt 3840)) (1 / Real.sqrt 3840) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 3840) (-(q : ℝ) / 3840)
          (1 / Real.sqrt 3840)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 3840)) := by
  exact AdjacentAdiShiftBinding.reflected_factorization_of_gridCertificate
    3840 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

theorem same_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 7680) (hq : 7681 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn sameShifts) ((p : ℝ) / 3840) /
          adiRationalProduct (List.ofFn sameShifts) ((q : ℝ) / 3840)) =
      adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 3840) ((q : ℝ) / 3840)
          (-symbol p * (1 / Real.sqrt 3840)) (1 / Real.sqrt 3840) +
        adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 3840) ((q : ℝ) / 3840)
          (1 / Real.sqrt 3840) (symbol q * (1 / Real.sqrt 3840)) :=
  same_factorization_of_gridCertificate
    sameShifts samePoleCells hcert.same symbol diagonal p q hp hq

theorem reflected_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 3841 ≤ p) (hq : 7681 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn reflectedShifts) ((p : ℝ) / 3840) /
          adiRationalProduct (List.ofFn reflectedShifts) (-(q : ℝ) / 3840)) =
      adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 3840) (-(q : ℝ) / 3840)
          (-symbol p * (1 / Real.sqrt 3840)) (1 / Real.sqrt 3840) +
        adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 3840) (-(q : ℝ) / 3840)
          (1 / Real.sqrt 3840)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 3840)) :=
  reflected_factorization_of_gridCertificate
    reflectedShifts reflectedPoleCells hcert.reflected symbol diagonal p q hp hq

end K3840AdiShiftBinding
end RiemannCvs
