import RiemannCvs.AdjacentShellRebalancedCompression
import RiemannCvs.K7680AdiShiftBinding

/-!
# The third finite adjacent compression bridge at K=7680

The Arb artifact for the block from source modes `(7680,15360]` to target
modes `(15360,30720]` certifies compressed operator caps `107/100`, `1/4`,
and `27/25` with 64 same-sign and 12 reflected shifts.  The already uniform
rational residual caps are `1/200` and `1/4000`.

This file kernel-checks the complete scalar posterior and converts it through
the coercive floors `428/125` and `24/5` into relative coefficient `2/27`.
The finite Gram and transcendental shift-cell inequalities remain explicit
certificate premises; no numerical artifact is promoted to a Lean axiom.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline

/-- The `64+12` rank-two ADI split has combined rank cap 152. -/
lemma v23_k7680_adjacentLoewnerCompression_rankLedger :
    2 * 64 + 2 * 12 = 152 := by
  norm_num

/-- Exact posterior from the three compressed caps and two residual inflations. -/
lemma v23_k7680_compressionPosteriorLedger :
    (27 / 25 : ℝ) + (1 / 199) * (107 / 100) +
        (1 / 3999) * (1 / 4) =
      21594844 / 19895025 := by
  norm_num

/-- Exact positive reserve inside the `2/27` relative-energy budget. -/
lemma v23_k7680_compressionPosterior_budgetSlack :
    (2 / 27 : ℝ) * (428 / 125) * (24 / 5) -
        (21594844 / 19895025) ^ 2 =
      15533061282736 / 395812019750625 := by
  norm_num

/-- The exact K7680 posterior fits the `2/27` intermediate-channel budget. -/
lemma v23_k7680_compressionPosterior_fits_twoOver27 :
    (21594844 / 19895025 : ℝ) ^ 2 ≤
      (2 / 27 : ℝ) * (428 / 125) * (24 / 5) := by
  norm_num

/-- Specialize the two-Loewner posterior to the K7680 finite artifact. -/
theorem v23_k7680_twoLoewnerCompression_posterior
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
    (hCompressedSame : compressedSameNorm ≤ (107 / 100 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (27 / 25 : ℝ)) :
    totalNorm ≤ 21594844 / 19895025 := by
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
    _ ≤ (27 / 25 : ℝ) + (1 / 199) * (107 / 100) +
        (1 / 3999) * (1 / 4) := by
      gcongr
    _ = 21594844 / 19895025 :=
      v23_k7680_compressionPosteriorLedger

/-- End-to-end relative-energy consequence of the K7680 rank-152 certificate.
All large-dimensional and transcendental facts stay visible as premises. -/
theorem relativeCoupling_of_k7680_rank152Compression
    (lowEnergy highEnergy cross lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hLowNorm : 0 ≤ lowNorm) (hHighNorm : 0 ≤ highNorm)
    (hLowEnergy : (428 / 125 : ℝ) * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy : (24 / 5 : ℝ) * highNorm ^ 2 ≤ highEnergy)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (107 / 100 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (27 / 25 : ℝ))
    (hCross : |cross| ≤ totalNorm * lowNorm * highNorm) :
    cross ^ 2 ≤ (2 / 27 : ℝ) * lowEnergy * highEnergy := by
  let epsilon : ℝ := 21594844 / 19895025
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
      _ ≤ (27 / 25 : ℝ) + (1 / 199) * (107 / 100) +
          (1 / 3999) * (1 / 4) := by
        gcongr
      _ = epsilon := by
        simpa [epsilon] using v23_k7680_compressionPosteriorLedger
  exact relativeCoupling_of_twoLoewnerCompression
    lowEnergy highEnergy cross
    (428 / 125) (24 / 5) (2 / 27) lowNorm highNorm
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
        v23_k7680_compressionPosterior_fits_twoOver27)

end RiemannCvs.V23BoundaryWeylMainline
