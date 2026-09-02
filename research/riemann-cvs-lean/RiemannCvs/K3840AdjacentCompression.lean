import RiemannCvs.AdjacentShellRebalancedCompression
import RiemannCvs.K3840AdiShiftBinding

/-!
# The second finite adjacent compression bridge at K=3840

The Arb artifact for the block from source modes `(3840,7680]` to target
modes `(7680,15360]` certifies compressed operator caps `99/100`, `1/4`, and
`199/200` with 64 same-sign and 12 reflected shifts.  The already uniform
rational residual caps are `1/200` and `1/4000`.

This file kernel-checks the complete scalar posterior and converts it through
the coercive floors `428/125` and `207/50` into relative coefficient `2/27`.
The finite Gram and transcendental shift-cell inequalities remain explicit
certificate premises; no numerical artifact is promoted to a Lean axiom.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline

/-- The `64+12` rank-two ADI split has combined rank cap 152. -/
lemma v23_k3840_adjacentLoewnerCompression_rankLedger :
    2 * 64 + 2 * 12 = 152 := by
  norm_num

/-- Exact posterior from the three compressed caps and two residual inflations. -/
lemma v23_k3840_compressionPosteriorLedger :
    (199 / 200 : ℝ) + (1 / 199) * (99 / 100) +
        (1 / 3999) * (1 / 4) =
      159166151 / 159160200 := by
  norm_num

/-- Exact positive reserve inside the `2/27` relative-energy budget. -/
lemma v23_k3840_compressionPosterior_budgetSlack :
    (2 / 27 : ℝ) * (428 / 125) * (207 / 50) -
        (159166151 / 159160200) ^ 2 =
      6326898111337867 / 126659846320200000 := by
  norm_num

/-- The exact K3840 posterior fits the `2/27` intermediate-channel budget. -/
lemma v23_k3840_compressionPosterior_fits_twoOver27 :
    (159166151 / 159160200 : ℝ) ^ 2 ≤
      (2 / 27 : ℝ) * (428 / 125) * (207 / 50) := by
  norm_num

/-- Specialize the two-Loewner posterior to the K3840 finite artifact. -/
theorem v23_k3840_twoLoewnerCompression_posterior
    (sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (99 / 100 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (199 / 200 : ℝ)) :
    totalNorm ≤ 159166151 / 159160200 := by
  have hPosterior := twoLoewnerCompression_posterior
    sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
    residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
    (1 / 200 : ℝ) (1 / 4000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSameSplit hReflectedSplit hSameResidual hReflectedResidual hTotalSplit
  calc
    totalNorm ≤ compressedTotalNorm +
        ((1 / 200 : ℝ) / (1 - 1 / 200)) * compressedSameNorm +
        ((1 / 4000 : ℝ) / (1 - 1 / 4000)) *
          compressedReflectedNorm := hPosterior
    _ = compressedTotalNorm + (1 / 199 : ℝ) * compressedSameNorm +
        (1 / 3999 : ℝ) * compressedReflectedNorm := by norm_num
    _ ≤ (199 / 200 : ℝ) + (1 / 199) * (99 / 100) +
        (1 / 3999) * (1 / 4) := by
      gcongr
    _ = 159166151 / 159160200 :=
      v23_k3840_compressionPosteriorLedger

/-- End-to-end relative-energy consequence of the K3840 rank-152 certificate.
All large-dimensional and transcendental facts stay visible as premises. -/
theorem relativeCoupling_of_k3840_rank152Compression
    (lowEnergy highEnergy cross lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hLowNorm : 0 ≤ lowNorm) (hHighNorm : 0 ≤ highNorm)
    (hLowEnergy : (428 / 125 : ℝ) * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy : (207 / 50 : ℝ) * highNorm ^ 2 ≤ highEnergy)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (99 / 100 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (199 / 200 : ℝ))
    (hCross : |cross| ≤ totalNorm * lowNorm * highNorm) :
    cross ^ 2 ≤ (2 / 27 : ℝ) * lowEnergy * highEnergy := by
  let epsilon : ℝ := 159166151 / 159160200
  have hPosteriorBudget :
      compressedTotalNorm +
          ((1 / 200 : ℝ) / (1 - 1 / 200)) * compressedSameNorm +
          ((1 / 4000 : ℝ) / (1 - 1 / 4000)) * compressedReflectedNorm ≤
        epsilon := by
    calc
      compressedTotalNorm +
          ((1 / 200 : ℝ) / (1 - 1 / 200)) * compressedSameNorm +
          ((1 / 4000 : ℝ) / (1 - 1 / 4000)) * compressedReflectedNorm =
        compressedTotalNorm + (1 / 199 : ℝ) * compressedSameNorm +
          (1 / 3999 : ℝ) * compressedReflectedNorm := by norm_num
      _ ≤ (199 / 200 : ℝ) + (1 / 199) * (99 / 100) +
          (1 / 3999) * (1 / 4) := by
        gcongr
      _ = epsilon := by
        simpa [epsilon] using v23_k3840_compressionPosteriorLedger
  exact relativeCoupling_of_twoLoewnerCompression
    lowEnergy highEnergy cross
    (428 / 125) (207 / 50) (2 / 27) lowNorm highNorm
    sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
    residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
    (1 / 200) (1 / 4000) epsilon
    (by norm_num) (by norm_num) (by norm_num) hLowNorm hHighNorm
    (by norm_num) hLowEnergy hHighEnergy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSameSplit hReflectedSplit hSameResidual hReflectedResidual hTotalSplit
    hPosteriorBudget hCross
    (by
      simpa [epsilon] using
        v23_k3840_compressionPosterior_fits_twoOver27)

end RiemannCvs.V23BoundaryWeylMainline
