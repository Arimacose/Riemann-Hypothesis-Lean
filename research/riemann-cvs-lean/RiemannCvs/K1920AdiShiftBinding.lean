import RiemannCvs.AdjacentAdiShiftBinding

/-!
# Literal K=1920 ADI shift binding

The first adjacent-shell certificate uses 31 same-sign and 12 reflected ADI
factors.  This module records the literal logarithmic shifts and the two Arb
cell transcripts.  `AdjacentAdiShiftBinding` proves that the corresponding
range and unit-cell premises imply every noncollision condition in the exact
ADI telescope.
-/

namespace RiemannCvs
namespace K1920AdiShiftBinding

open scoped BigOperators Real
open RiemannCvs.CvSParityDisplacement
open RiemannCvs.AdjacentAdiShiftBinding

/-- Literal 31 same-sign shifts for `[1921/1920,2]` versus `[3841/1920,4]`. -/
noncomputable def sameShifts : Fin 31 → ℝ × ℝ :=
  directShiftForEndpoints (1921 / 1920 : ℝ) 2 (3841 / 1920 : ℝ) 4

/-- Literal 12 reflected shifts for `[-4,-3841/1920]` versus `[1921/1920,2]`. -/
noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-3841 / 1920 : ℝ) (1921 / 1920 : ℝ) 2

/-- Arb-certified integer cells containing `1920 * sameShifts[i].pole`. -/
def samePoleCellList : List ℕ :=
  [3841, 3841, 3841, 3841, 3842, 3842, 3843, 3844, 3845, 3847,
    3849, 3852, 3856, 3861, 3867, 3876, 3887, 3903, 3923, 3949,
    3985, 4031, 4094, 4178, 4292, 4447, 4660, 4958, 5384, 6012, 6983]

/-- Arb-certified integer cells containing `1920 * (-reflectedShifts[i].pole)`. -/
def reflectedPoleCellList : List ℕ :=
  [3942, 4155, 4384, 4629, 4893, 5178, 5484, 5815, 6173, 6560, 6980, 7436]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 31 := by
  rfl

@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by
  rfl

def samePoleCells (i : Fin 31) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

theorem combinedRank_eq : 2 * 31 + 2 * 12 = 86 := by
  norm_num

abbrev SameGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop :=
  AdjacentAdiShiftBinding.SameGridCertificate 1920 shifts cells

abbrev ReflectedGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop :=
  AdjacentAdiShiftBinding.ReflectedGridCertificate 1920 shifts cells

structure LiteralShiftCertificate : Prop where
  same : SameGridCertificate sameShifts samePoleCells
  reflected : ReflectedGridCertificate reflectedShifts reflectedPoleCells

/-- Compatibility wrapper for the specialized K=1920 cell theorem. -/
theorem gridCell_ne (m q : ℕ) (x : ℝ)
    (hLower : (m : ℝ) < 1920 * x)
    (hUpper : 1920 * x < (m : ℝ) + 1) :
    (q : ℝ) / 1920 ≠ x := by
  exact AdjacentAdiShiftBinding.gridCell_ne 1920 m q x
    (by norm_num) hLower hUpper

/-- Compatibility wrapper for the specialized same-sign noncollision theorem. -/
theorem same_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : SameGridCertificate shifts cells)
    (p q : ℕ) (hp : p ≤ 3840) (hq : 3841 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 1920 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 1920 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 1920 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.same_noncollision
    1920 (by norm_num) shifts cells hcert p q hp hq

/-- Compatibility wrapper for the specialized reflected noncollision theorem. -/
theorem reflected_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : ReflectedGridCertificate shifts cells)
    (p q : ℕ) (hp : 1921 ≤ p) (hq : 3841 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 1920 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 1920 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 1920 ≠ shift.2) := by
  exact AdjacentAdiShiftBinding.reflected_noncollision
    1920 (by norm_num) shifts cells hcert p q hp hq

/-- Specialized exact telescope for any certified K=1920 same-sign family. -/
theorem same_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : SameGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 3840) (hq : 3841 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 1920) /
          adiRationalProduct (List.ofFn shifts) ((q : ℝ) / 1920)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 1920) ((q : ℝ) / 1920)
          (-symbol p * (1 / Real.sqrt 1920)) (1 / Real.sqrt 1920) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 1920) ((q : ℝ) / 1920)
          (1 / Real.sqrt 1920) (symbol q * (1 / Real.sqrt 1920)) := by
  exact AdjacentAdiShiftBinding.same_factorization_of_gridCertificate
    1920 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

/-- Specialized exact telescope for any certified K=1920 reflected family. -/
theorem reflected_factorization_of_gridCertificate
    {n : ℕ} (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : ReflectedGridCertificate shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 1921 ≤ p) (hq : 3841 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / 1920) /
          adiRationalProduct (List.ofFn shifts) (-(q : ℝ) / 1920)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / 1920) (-(q : ℝ) / 1920)
          (-symbol p * (1 / Real.sqrt 1920)) (1 / Real.sqrt 1920) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / 1920) (-(q : ℝ) / 1920)
          (1 / Real.sqrt 1920)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 1920)) := by
  exact AdjacentAdiShiftBinding.reflected_factorization_of_gridCertificate
    1920 (by norm_num) shifts cells hcert symbol diagonal p q hp hq

theorem same_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 3840) (hq : 3841 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn sameShifts) ((p : ℝ) / 1920) /
          adiRationalProduct (List.ofFn sameShifts) ((q : ℝ) / 1920)) =
      adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 1920) ((q : ℝ) / 1920)
          (-symbol p * (1 / Real.sqrt 1920)) (1 / Real.sqrt 1920) +
        adiFactorDot (List.ofFn sameShifts) ((p : ℝ) / 1920) ((q : ℝ) / 1920)
          (1 / Real.sqrt 1920) (symbol q * (1 / Real.sqrt 1920)) :=
  same_factorization_of_gridCertificate
    sameShifts samePoleCells hcert.same symbol diagonal p q hp hq

theorem reflected_factorization (hcert : LiteralShiftCertificate)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : 1921 ≤ p) (hq : 3841 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn reflectedShifts) ((p : ℝ) / 1920) /
          adiRationalProduct (List.ofFn reflectedShifts) (-(q : ℝ) / 1920)) =
      adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 1920) (-(q : ℝ) / 1920)
          (-symbol p * (1 / Real.sqrt 1920)) (1 / Real.sqrt 1920) +
        adiFactorDot (List.ofFn reflectedShifts) ((p : ℝ) / 1920) (-(q : ℝ) / 1920)
          (1 / Real.sqrt 1920)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt 1920)) :=
  reflected_factorization_of_gridCertificate
    reflectedShifts reflectedPoleCells hcert.reflected symbol diagonal p q hp hq

end K1920AdiShiftBinding
end RiemannCvs
