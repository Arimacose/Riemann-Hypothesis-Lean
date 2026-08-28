import Mathlib

/-!
# Residual scales required by an exponentially small prolate ground state

The fixed-index odd reference energy has the form `energy = defect * logScale`,
while the next constrained prolate level is larger by a polynomial factor
`gapFactor * lambda^8`.  A termwise operator estimate typically gives a
residual norm of order `logScale * sqrt(defect)`.  Temple then loses the
exponentially small defect factor and cannot preserve the ground scale.

These lemmas record that obstruction and the stronger, defect-linear residual
scale that would be sufficient.  They are scalar algebra only.
-/

namespace RiemannCvs.TempleResidualScale

/-- If the residual square is on the natural termwise scale
`K² L² d`, while the spectral gap is `G lambda^8 d L`, then the Temple
correction loses the factor `d`. -/
theorem squareRootDefectResidualLoss
    (loss residualSq gap K L d G lambda : ℝ)
    (hd : 0 < d)
    (hL : 0 < L)
    (hG : 0 < G)
    (hlambda : 0 < lambda)
    (hResidual : residualSq = K ^ 2 * L ^ 2 * d)
    (hGap : gap = G * lambda ^ 8 * d * L)
    (hLoss : loss * gap = residualSq) :
    G * lambda ^ 8 * loss = K ^ 2 * L := by
  rw [hResidual, hGap] at hLoss
  have hdl : d * L ≠ 0 := mul_ne_zero (ne_of_gt hd) (ne_of_gt hL)
  apply (mul_right_cancel₀ hdl)
  nlinarith

/-- Relative to the ground scale `energy = d L`, the same Temple correction is
larger by the factor `K² / (G lambda^8 d)`.  This multiplication-only form is
convenient when `d` is exponentially small. -/
theorem squareRootResidualRelativeIdentity
    (loss energy residualSq gap K L d G lambda : ℝ)
    (hd : 0 < d)
    (hL : 0 < L)
    (hG : 0 < G)
    (hlambda : 0 < lambda)
    (hEnergy : energy = d * L)
    (hResidual : residualSq = K ^ 2 * L ^ 2 * d)
    (hGap : gap = G * lambda ^ 8 * energy)
    (hLoss : loss * gap = residualSq) :
    G * lambda ^ 8 * d * loss = K ^ 2 * energy := by
  rw [hEnergy, hResidual, hGap] at hLoss ⊢
  have hdl : d * L ≠ 0 := mul_ne_zero (ne_of_gt hd) (ne_of_gt hL)
  field_simp [hdl] at hLoss ⊢
  nlinarith

/-- A strict Temple loss smaller than the ground energy on the square-root
residual scale forces `K² < G lambda^8 d`.  For fixed `K,G`, this is incompatible
with an exponentially small `d`. -/
theorem squareRootResidualNecessaryCondition
    (loss energy residualSq gap K L d G lambda : ℝ)
    (hd : 0 < d)
    (hL : 0 < L)
    (hG : 0 < G)
    (hlambda : 0 < lambda)
    (hEnergy : energy = d * L)
    (hResidual : residualSq = K ^ 2 * L ^ 2 * d)
    (hGap : gap = G * lambda ^ 8 * energy)
    (hLoss : loss * gap = residualSq)
    (hSmall : loss < energy) :
    K ^ 2 < G * lambda ^ 8 * d := by
  have hid := squareRootResidualRelativeIdentity
    loss energy residualSq gap K L d G lambda
    hd hL hG hlambda hEnergy hResidual hGap hLoss
  have hpos : 0 < G * lambda ^ 8 * d := by positivity
  have hscaled := mul_lt_mul_of_pos_left hSmall hpos
  nlinarith

/-- In contrast, a residual square of order `K² d² L²` retains one factor of
the defect after division by the polynomially enlarged gap. -/
theorem defectLinearResidualLoss
    (loss residualSq gap energy K L d G lambda : ℝ)
    (hd : 0 < d)
    (hL : 0 < L)
    (hG : 0 < G)
    (hlambda : 0 < lambda)
    (hEnergy : energy = d * L)
    (hResidual : residualSq ≤ K ^ 2 * d ^ 2 * L ^ 2)
    (hGap : gap = G * lambda ^ 8 * energy)
    (hLoss : loss * gap ≤ residualSq) :
    G * lambda ^ 8 * loss ≤ K ^ 2 * energy := by
  rw [hEnergy, hGap] at hLoss ⊢
  have hgapPos : 0 < G * lambda ^ 8 * (d * L) := by positivity
  have hchain :
      loss * (G * lambda ^ 8 * (d * L)) ≤
        K ^ 2 * d ^ 2 * L ^ 2 := le_trans hLoss hResidual
  have hdl : 0 < d * L := mul_pos hd hL
  nlinarith

/-- A defect-linear residual with polynomially bounded coefficient preserves a
fixed fraction of the ground scale once `K²` is smaller than that fraction of
`G lambda^8`. -/
theorem defectLinearResidualPreservesFraction
    (loss residualSq gap energy K L d G lambda eta : ℝ)
    (hd : 0 < d)
    (hL : 0 < L)
    (hG : 0 < G)
    (hlambda : 0 < lambda)
    (heta : 0 ≤ eta)
    (hEnergy : energy = d * L)
    (hResidual : residualSq ≤ K ^ 2 * d ^ 2 * L ^ 2)
    (hGap : gap = G * lambda ^ 8 * energy)
    (hLoss : loss * gap ≤ residualSq)
    (hBudget : K ^ 2 ≤ eta * G * lambda ^ 8) :
    loss ≤ eta * energy := by
  have hbase := defectLinearResidualLoss
    loss residualSq gap energy K L d G lambda
    hd hL hG hlambda hEnergy hResidual hGap hLoss
  have hscalePos : 0 < G * lambda ^ 8 := by positivity
  have hbudgetEnergy :=
    mul_le_mul_of_nonneg_right hBudget (le_of_lt (by rw [hEnergy]; positivity))
  nlinarith

end RiemannCvs.TempleResidualScale
