import RiemannCvs.CvSLoewnerAdiInstantiation

/-!
# Literal K=1920 ADI shift binding

The adjacent-shell rank-86 certificate uses 31 same-sign and 12 reflected ADI
factors.  `CvSLoewnerAdiInstantiation` proves the exact telescoping identity for
an arbitrary finite shift list, subject to four elementary noncollision
hypotheses.  This module closes the discrete part of that interface at the
first `K = 1920` bridge.

The roots and poles below are *literal real expressions*: the endpoint cross
ratio determines `alpha`, the logarithmic nodes are

`exp (log alpha * (2*i+1)/(2*n))`,

and `inverseEndpointMap` is a closed inverse Mobius formula.  The accompanying
Arb transcript `certify_k1920_adi_shift_cells.py` certifies the remaining
transcendental inequalities at 256 and 384 bits.  They are deliberately kept as
the small `SameGridCertificate` / `ReflectedGridCertificate` premise boundary;
everything from those interval fields to the generic Lean ADI factorization is
proved here without a user axiom.
-/

namespace RiemannCvs
namespace K1920AdiShiftBinding

open scoped BigOperators Real
open RiemannCvs.CvSParityDisplacement

/-- Cross ratio used to normalize two disjoint real intervals. -/
noncomputable def endpointCrossRatio (a b c d : ℝ) : ℝ :=
  ((c - a) * (d - b)) / ((c - b) * (d - a))

/-- Positive normalization parameter associated with four ordered endpoints. -/
noncomputable def endpointAlpha (a b c d : ℝ) : ℝ :=
  let gamma := endpointCrossRatio a b c d
  (-1 : ℝ) + 2 * gamma + 2 * Real.sqrt (gamma * gamma - gamma)

/--
Closed inverse of the endpoint Mobius map
`(a,b,c,d) -> (-alpha,-1,1,alpha)`.

The fourth endpoint enters through `alpha`; only `a,b,c` are needed once
`alpha` is fixed.
-/
noncomputable def inverseEndpointMap (a b c alpha y : ℝ) : ℝ :=
  let t := -2 * (y + alpha) / ((alpha - 1) * (y - 1))
  let u := t * (b - a) / (b - c)
  (u * c - a) / (u - 1)

/-- The `(2*i+1)/(2*n)` logarithmic Zolotarev node. -/
noncomputable def logarithmicNode {n : ℕ} (alpha : ℝ) (i : Fin n) : ℝ :=
  Real.exp
    (Real.log alpha *
      (((2 * (i : ℕ) + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)))

/-- Direct root/pole ordering for the same-sign interval pair. -/
noncomputable def directShiftForEndpoints {n : ℕ}
    (a b c d : ℝ) (i : Fin n) : ℝ × ℝ :=
  let alpha := endpointAlpha a b c d
  let shift := logarithmicNode alpha i
  (inverseEndpointMap a b c alpha (-shift),
    inverseEndpointMap a b c alpha shift)

/-- Reciprocal root/pole ordering for the reflected interval pair. -/
noncomputable def inverseShiftForEndpoints {n : ℕ}
    (a b c d : ℝ) (i : Fin n) : ℝ × ℝ :=
  let alpha := endpointAlpha a b c d
  let shift := logarithmicNode alpha i
  (inverseEndpointMap a b c alpha shift,
    inverseEndpointMap a b c alpha (-shift))

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

/-- Fin-indexed form of the literal 31-cell transcript. -/
def samePoleCells (i : Fin 31) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

/-- Fin-indexed form of the literal 12-cell transcript. -/
def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

/-- The `31+12` rank-two displacement factors give rank at most `86`. -/
theorem combinedRank_eq : 2 * 31 + 2 * 12 = 86 := by
  norm_num

/--
Minimal interval premise for a same-sign shift family.  It mirrors exactly the
fields emitted by the Arb shift-cell certificate.
-/
structure SameGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop where
  root_lt_two : ∀ i, (shifts i).1 < 2
  two_lt_pole : ∀ i, 2 < (shifts i).2
  pole_cell : ∀ i,
    (cells i : ℝ) < 1920 * (shifts i).2 ∧
      1920 * (shifts i).2 < cells i + 1

/-- Minimal interval premise for a reflected shift family. -/
structure ReflectedGridCertificate {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop where
  root_pos : ∀ i, 0 < (shifts i).1
  pole_neg : ∀ i, (shifts i).2 < 0
  neg_pole_cell : ∀ i,
    (cells i : ℝ) < 1920 * (-(shifts i).2) ∧
      1920 * (-(shifts i).2) < cells i + 1

/-- The complete external interval premise for the literal K=1920 shifts. -/
structure LiteralShiftCertificate : Prop where
  same : SameGridCertificate sameShifts samePoleCells
  reflected : ReflectedGridCertificate reflectedShifts reflectedPoleCells

/-- A strict unit-width cell excludes every natural grid point. -/
theorem gridCell_ne (m q : ℕ) (x : ℝ)
    (hLower : (m : ℝ) < 1920 * x)
    (hUpper : 1920 * x < (m : ℝ) + 1) :
    (q : ℝ) / 1920 ≠ x := by
  intro h
  rw [← h] at hLower hUpper
  have hCancel : (1920 : ℝ) * ((q : ℝ) / 1920) = q := by
    field_simp
  rw [hCancel] at hLower hUpper
  have hLowerNat : m < q := by exact_mod_cast hLower
  have hUpperNat : q < m + 1 := by exact_mod_cast hUpper
  omega

/--
The same-sign range and cell fields imply all three shift-list noncollisions
needed at an old/middle-to-new K=1920 bridge.
-/
theorem same_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : SameGridCertificate shifts cells)
    (p q : ℕ) (hp : p ≤ 3840) (hq : 3841 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 1920 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 1920 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / 1920 ≠ shift.2) := by
  have hpReal : (p : ℝ) ≤ 3840 := by exact_mod_cast hp
  have hqReal : (3841 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hpScaled : (p : ℝ) / 1920 ≤ 2 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1920)).2
      nlinarith
    exact ne_of_lt (lt_of_le_of_lt hpScaled (hcert.two_lt_pole i))
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hqScaled : 2 < (q : ℝ) / 1920 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1920)).2
      linarith
    exact ne_of_gt (lt_trans (hcert.root_lt_two i) hqScaled)
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    exact gridCell_ne (cells i) q (shifts i).2
      (hcert.pole_cell i).1 (hcert.pole_cell i).2

/-- Reflected sign and cell fields imply all three required noncollisions. -/
theorem reflected_noncollision {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) (hcert : ReflectedGridCertificate shifts cells)
    (p q : ℕ) (hp : 1921 ≤ p) (hq : 3841 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / 1920 ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 1920 ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / 1920 ≠ shift.2) := by
  have hpReal : (1921 : ℝ) ≤ p := by exact_mod_cast hp
  have hqReal : (3841 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hpScaled : 0 < (p : ℝ) / 1920 := by
      exact div_pos (by linarith) (by norm_num)
    exact ne_of_gt (lt_trans (hcert.pole_neg i) hpScaled)
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hqScaled : -(q : ℝ) / 1920 < 0 := by
      exact div_neg_of_neg_of_pos (by linarith) (by norm_num)
    exact ne_of_lt (lt_trans hqScaled (hcert.root_pos i))
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hGrid := gridCell_ne
      (cells i) q (-(shifts i).2)
      (hcert.neg_pole_cell i).1 (hcert.neg_pole_cell i).2
    intro hEqual
    apply hGrid
    linarith

/--
Instantiate the exact generic ADI telescope for an arbitrary certified
same-sign K=1920 shift family.
-/
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
  have hNoncollision := same_noncollision shifts cells hcert p q hp hq
  have hpq : (p : ℝ) ≠ q := by
    have hpqNat : p < q := by omega
    exact_mod_cast ne_of_lt hpqNat
  exact oddDifferenceKernel_adi_factorization_rescaled
    symbol diagonal (List.ofFn shifts) 1920 p q
    (by norm_num) hpq hNoncollision.1 hNoncollision.2.1 hNoncollision.2.2

/-- Instantiate the exact telescope for a certified reflected K=1920 family. -/
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
  have hNoncollision := reflected_noncollision shifts cells hcert p q hp hq
  have hpReal : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega) hp)
  have hqReal : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega) hq)
  have hpq : (p : ℝ) ≠ -(q : ℝ) := by linarith
  exact oddDifferenceKernel_adi_factorization_rescaled
    symbol diagonal (List.ofFn shifts) 1920 p (-(q : ℝ))
    (by norm_num) hpq hNoncollision.1 hNoncollision.2.1 hNoncollision.2.2

/-- Exact same-sign factorization for the literal 31-shift transcript. -/
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

/-- Exact reflected factorization for the literal 12-shift transcript. -/
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
