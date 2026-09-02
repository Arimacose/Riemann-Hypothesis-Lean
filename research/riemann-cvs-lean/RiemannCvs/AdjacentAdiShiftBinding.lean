import RiemannCvs.CvSLoewnerAdiInstantiation

/-!
# Generic adjacent-shell ADI shift binding

This module contains the mode-independent part of the literal ADI bridge.  It
defines the endpoint normalization and logarithmic shifts, turns strict Arb
unit-cell enclosures into grid noncollision, and instantiates the exact Lean
ADI telescope at an arbitrary positive natural mode `K`.

Concrete modules still list their literal cells and retain the transcendental
range inequalities as named finite certificate premises.
-/

namespace RiemannCvs
namespace AdjacentAdiShiftBinding

open scoped BigOperators Real
open RiemannCvs.CvSParityDisplacement

/-- Cross ratio used to normalize two disjoint real intervals. -/
noncomputable def endpointCrossRatio (a b c d : ℝ) : ℝ :=
  ((c - a) * (d - b)) / ((c - b) * (d - a))

/-- Positive normalization parameter associated with four ordered endpoints. -/
noncomputable def endpointAlpha (a b c d : ℝ) : ℝ :=
  let gamma := endpointCrossRatio a b c d
  (-1 : ℝ) + 2 * gamma + 2 * Real.sqrt (gamma * gamma - gamma)

/-- Closed inverse of the endpoint Mobius map to `(-alpha,-1,1,alpha)`. -/
noncomputable def inverseEndpointMap (a b c alpha y : ℝ) : ℝ :=
  let t := -2 * (y + alpha) / ((alpha - 1) * (y - 1))
  let u := t * (b - a) / (b - c)
  (u * c - a) / (u - 1)

/-- The `(2*i+1)/(2*n)` logarithmic Zolotarev node. -/
noncomputable def logarithmicNode {n : ℕ} (alpha : ℝ) (i : Fin n) : ℝ :=
  Real.exp
    (Real.log alpha *
      (((2 * (i : ℕ) + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)))

/-- Direct root/pole ordering for a same-sign interval pair. -/
noncomputable def directShiftForEndpoints {n : ℕ}
    (a b c d : ℝ) (i : Fin n) : ℝ × ℝ :=
  let alpha := endpointAlpha a b c d
  let shift := logarithmicNode alpha i
  (inverseEndpointMap a b c alpha (-shift),
    inverseEndpointMap a b c alpha shift)

/-- Reciprocal root/pole ordering for a reflected interval pair. -/
noncomputable def inverseShiftForEndpoints {n : ℕ}
    (a b c d : ℝ) (i : Fin n) : ℝ × ℝ :=
  let alpha := endpointAlpha a b c d
  let shift := logarithmicNode alpha i
  (inverseEndpointMap a b c alpha shift,
    inverseEndpointMap a b c alpha (-shift))

/-- Minimal interval premise for a same-sign shift family at mode `K`. -/
structure SameGridCertificate (K : ℕ) {n : ℕ} (shifts : Fin n → ℝ × ℝ)
    (cells : Fin n → ℕ) : Prop where
  root_lt_two : ∀ i, (shifts i).1 < 2
  two_lt_pole : ∀ i, 2 < (shifts i).2
  pole_cell : ∀ i,
    (cells i : ℝ) < K * (shifts i).2 ∧
      K * (shifts i).2 < cells i + 1

/-- Minimal interval premise for a reflected shift family at mode `K`. -/
structure ReflectedGridCertificate (K : ℕ) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ) : Prop where
  root_pos : ∀ i, 0 < (shifts i).1
  pole_neg : ∀ i, (shifts i).2 < 0
  neg_pole_cell : ∀ i,
    (cells i : ℝ) < K * (-(shifts i).2) ∧
      K * (-(shifts i).2) < cells i + 1

/-- A strict unit-width scaled cell excludes every natural grid point. -/
theorem gridCell_ne (K m q : ℕ) (x : ℝ) (hK : 0 < K)
    (hLower : (m : ℝ) < K * x)
    (hUpper : K * x < (m : ℝ) + 1) :
    (q : ℝ) / K ≠ x := by
  intro h
  rw [← h] at hLower hUpper
  have hKReal : (K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  have hCancel : (K : ℝ) * ((q : ℝ) / K) = q := by
    field_simp [hKReal]
  rw [hCancel] at hLower hUpper
  have hLowerNat : m < q := by exact_mod_cast hLower
  have hUpperNat : q < m + 1 := by exact_mod_cast hUpper
  omega

/-- Same-sign ranges and cells imply all three adjacent-grid noncollisions. -/
theorem same_noncollision (K : ℕ) (hK : 0 < K) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : SameGridCertificate K shifts cells)
    (p q : ℕ) (hp : p ≤ 2 * K) (hq : 2 * K + 1 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / K ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / K ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, (q : ℝ) / K ≠ shift.2) := by
  have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
  have hpReal : (p : ℝ) ≤ 2 * K := by exact_mod_cast hp
  have hqReal : (2 : ℝ) * K + 1 ≤ q := by exact_mod_cast hq
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hpScaled : (p : ℝ) / K ≤ 2 := by
      apply (div_le_iff₀ hKReal).2
      nlinarith
    exact ne_of_lt (lt_of_le_of_lt hpScaled (hcert.two_lt_pole i))
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hqScaled : 2 < (q : ℝ) / K := by
      apply (lt_div_iff₀ hKReal).2
      nlinarith
    exact ne_of_gt (lt_trans (hcert.root_lt_two i) hqScaled)
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    exact gridCell_ne K (cells i) q (shifts i).2 hK
      (hcert.pole_cell i).1 (hcert.pole_cell i).2

/-- Reflected signs and cells imply all three adjacent-grid noncollisions. -/
theorem reflected_noncollision (K : ℕ) (hK : 0 < K) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : ReflectedGridCertificate K shifts cells)
    (p q : ℕ) (hp : K + 1 ≤ p) (hq : 2 * K + 1 ≤ q) :
    (∀ shift ∈ List.ofFn shifts, (p : ℝ) / K ≠ shift.2) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / K ≠ shift.1) ∧
    (∀ shift ∈ List.ofFn shifts, -(q : ℝ) / K ≠ shift.2) := by
  have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
  have hpReal : (K : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hqReal : (2 : ℝ) * K + 1 ≤ q := by exact_mod_cast hq
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hpScaled : 0 < (p : ℝ) / K := by
      exact div_pos (by linarith) hKReal
    exact ne_of_gt (lt_trans (hcert.pole_neg i) hpScaled)
  constructor
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hqScaled : -(q : ℝ) / K < 0 := by
      exact div_neg_of_neg_of_pos (by linarith) hKReal
    exact ne_of_lt (lt_trans hqScaled (hcert.root_pos i))
  · intro shift hmem
    rcases List.mem_ofFn.mp hmem with ⟨i, rfl⟩
    have hGrid := gridCell_ne K (cells i) q (-(shifts i).2) hK
      (hcert.neg_pole_cell i).1 (hcert.neg_pole_cell i).2
    intro hEqual
    apply hGrid
    have hNeg := congrArg (fun z : ℝ => -z) hEqual
    simpa [neg_div] using hNeg

/-- Instantiate the exact ADI telescope for a certified same-sign family. -/
theorem same_factorization_of_gridCertificate
    (K : ℕ) (hK : 0 < K) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : SameGridCertificate K shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : p ≤ 2 * K) (hq : 2 * K + 1 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / K) /
          adiRationalProduct (List.ofFn shifts) ((q : ℝ) / K)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) ((q : ℝ) / K)
          (-symbol p * (1 / Real.sqrt K)) (1 / Real.sqrt K) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) ((q : ℝ) / K)
          (1 / Real.sqrt K) (symbol q * (1 / Real.sqrt K)) := by
  have hNoncollision := same_noncollision K hK shifts cells hcert p q hp hq
  have hpq : (p : ℝ) ≠ q := by
    have hpqNat : p < q := by omega
    exact_mod_cast ne_of_lt hpqNat
  exact oddDifferenceKernel_adi_factorization_rescaled
    symbol diagonal (List.ofFn shifts) K p q
    (by exact_mod_cast hK) hpq
    hNoncollision.1 hNoncollision.2.1 hNoncollision.2.2

/-- Instantiate the exact ADI telescope for a certified reflected family. -/
theorem reflected_factorization_of_gridCertificate
    (K : ℕ) (hK : 0 < K) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) (cells : Fin n → ℕ)
    (hcert : ReflectedGridCertificate K shifts cells)
    (symbol diagonal : ℝ → ℝ) (p q : ℕ)
    (hp : K + 1 ≤ p) (hq : 2 * K + 1 ≤ q) :
    oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
        (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / K) /
          adiRationalProduct (List.ofFn shifts) (-(q : ℝ) / K)) =
      adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) (-(q : ℝ) / K)
          (-symbol p * (1 / Real.sqrt K)) (1 / Real.sqrt K) +
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) (-(q : ℝ) / K)
          (1 / Real.sqrt K)
          (symbol (-(q : ℝ)) * (1 / Real.sqrt K)) := by
  have hNoncollision := reflected_noncollision K hK shifts cells hcert p q hp hq
  have hpReal : (0 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ K) hp)
  have hqReal : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2 * K + 1) hq)
  have hpq : (p : ℝ) ≠ -(q : ℝ) := by linarith
  exact oddDifferenceKernel_adi_factorization_rescaled
    symbol diagonal (List.ofFn shifts) K p (-(q : ℝ))
    (by exact_mod_cast hK) hpq
    hNoncollision.1 hNoncollision.2.1 hNoncollision.2.2

end AdjacentAdiShiftBinding
end RiemannCvs
