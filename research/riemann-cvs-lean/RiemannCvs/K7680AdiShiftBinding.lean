import RiemannCvs.AdjacentAdiShiftBinding

/-!
# Literal K=7680 ADI shift binding

The third finite adjacent bridge uses 64 same-sign and 12 reflected ADI
factors.  The root and pole expressions are literal logarithmic shifts; the
two integer tables are the unit-cell transcript checked independently by Arb
at 256 and 384 bits.  The interval inequalities remain explicit fields of
`LiteralShiftCertificate`, while all resulting grid noncollision and exact
ADI factorization statements are proved here through the generic binding.
-/

namespace RiemannCvs
namespace K7680AdiShiftBinding

open scoped BigOperators Real
open RiemannCvs.CvSParityDisplacement
open RiemannCvs.AdjacentAdiShiftBinding

/-- Literal 64 same-sign shifts for `[7681/7680,2]` versus `[15361/7680,4]`. -/
noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (7681 / 7680 : ℝ) 2 (15361 / 7680 : ℝ) 4

/-- Literal 12 reflected shifts for `[-4,-15361/7680]` versus `[7681/7680,2]`. -/
noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-15361 / 7680 : ℝ) (7681 / 7680 : ℝ) 2

/-- Arb-certified integer cells containing `7680 * sameShifts[i].pole`. -/
def samePoleCellList : List ℕ :=
  [15361, 15361, 15361, 15361, 15361, 15361, 15361, 15362,
    15362, 15362, 15363, 15363, 15363, 15364, 15365, 15366,
    15366, 15368, 15369, 15370, 15372, 15374, 15376, 15379,
    15382, 15386, 15391, 15396, 15402, 15409, 15417, 15426,
    15438, 15451, 15466, 15484, 15504, 15529, 15557, 15591,
    15630, 15676, 15729, 15792, 15866, 15952, 16054, 16173,
    16314, 16480, 16675, 16907, 17182, 17509, 17900, 18368,
    18931, 19613, 20445, 21468, 22739, 24339, 26387, 29062]

/-- Arb-certified integer cells containing `7680 * (-reflectedShifts[i].pole)`. -/
def reflectedPoleCellList : List ℕ :=
  [15765, 16618, 17533, 18515, 19572, 20710,
    21936, 23260, 24690, 26240, 27920, 29747]

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
  AdjacentAdiShiftBinding.SameGridCertificate 7680 shifts cells

abbrev ReflectedGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop :=
  AdjacentAdiShiftBinding.ReflectedGridCertificate 7680 shifts cells

structure LiteralShiftCertificate : Prop where
  same : SameGridCertificate sameShifts samePoleCells
  reflected : ReflectedGridCertificate reflectedShifts reflectedPoleCells

theorem gridCell_ne (m q : ℕ) (x : ℝ)
    (hLower : (m : ℝ) < 7680 * x)
    (hUpper : 7680 * x < (m : ℝ) + 1) :
    (q : ℝ) / 7680 ≠ x := by
  exact AdjacentAdiShiftBinding.gridCell_ne 7680 m q x
    (by norm_num) hLower hUpper

theorem same_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : SameGridCertificate shifts cells)
    (p q : ℕ) (hp : p ≤ 15360) (hq : 15361 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 7680 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 7680 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 7680 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.same_noncollision
    7680 (by norm_num) shifts cells hcert p q hp hq

theorem reflected_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : ReflectedGridCertificate shifts cells)
    (p q : ℕ) (hp : 7681 ≤ p) (hq : 15361 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 7680 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 7680 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 7680 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.reflected_noncollision
    7680 (by norm_num) shifts cells hcert p q hp hq

theorem same_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : SameGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 15360) (hq : 15361 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 7680) /
          adiRationalProduct (List.ofFn shifts) ((q : ℝ) / 7680)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 7680) ((q : ℝ) / 7680)
          (-symbol p * (1 / Real.sqrt 7680)) (1 / Real.sqrt 7680) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 7680) ((q : ℝ) / 7680)
          (1 / Real.sqrt 7680) (symbol q * (1 / Real.sqrt 7680)) := by
  exact AdjacentAdiShiftBinding.same_factorization_of_gridCertificate
    7680 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

theorem reflected_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : ReflectedGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 7681 ≤ p) (hq : 15361 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 7680) /
          adiRationalProduct (List.ofFn shifts) (-(q : ℝ) / 7680)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 7680) (-(q : ℝ) / 7680)
          (-symbol p * (1 / Real.sqrt 7680)) (1 / Real.sqrt 7680) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 7680) (-(q : ℝ) / 7680)
          (1 / Real.sqrt 7680)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 7680)) := by
  exact AdjacentAdiShiftBinding.reflected_factorization_of_gridCertificate
    7680 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

theorem same_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 15360) (hq : 15361 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn sameShifts) ((p : ℝ) / 7680) /
          adiRationalProduct (List.ofFn sameShifts) ((q : ℝ) / 7680)) =
      adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 7680) ((q : ℝ) / 7680)
          (-symbol p * (1 / Real.sqrt 7680)) (1 / Real.sqrt 7680) +
        adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 7680) ((q : ℝ) / 7680)
          (1 / Real.sqrt 7680) (symbol q * (1 / Real.sqrt 7680)) :=
  same_factorization_of_gridCertificate
    sameShifts samePoleCells hcert.same symbol diagonal p q hp hq

theorem reflected_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 7681 ≤ p) (hq : 15361 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn reflectedShifts) ((p : ℝ) / 7680) /
          adiRationalProduct (List.ofFn reflectedShifts) (-(q : ℝ) / 7680)) =
      adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 7680) (-(q : ℝ) / 7680)
          (-symbol p * (1 / Real.sqrt 7680)) (1 / Real.sqrt 7680) +
        adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 7680) (-(q : ℝ) / 7680)
          (1 / Real.sqrt 7680)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 7680)) :=
  reflected_factorization_of_gridCertificate
    reflectedShifts reflectedPoleCells hcert.reflected symbol diagonal p q hp hq

end K7680AdiShiftBinding
end RiemannCvs
