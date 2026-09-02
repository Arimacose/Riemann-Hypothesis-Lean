import RiemannCvs.FiniteFixedSourceGramTransport

/-!
# A posteriori compression bridge for the adjacent Loewner channel

The same-sign and reflected adjacent blocks are rectangular Loewner matrices.
A rational Sylvester/ADI compression writes each block as a low-rank part plus
a residual whose operator norm is at most a scalar `z < 1` times the norm of
the original block.  This file records the dimension-free posterior argument:

* recover each original block norm from its compressed norm and `z`;
* retain cancellation by certifying the sum of the two compressed blocks;
* charge only the two small residual inflations separately;
* feed the resulting full operator-norm cap to the existing coercive-energy
  adapter.

The concrete rational shifts and interval Gram certificates remain external
finite data.  No numerical value is promoted to a theorem here.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.BoundaryWeylSchurTail

/-- A compression `compressed` with residual at most `z` times the unknown
full norm yields the standard a posteriori factor `1 / (1-z)`. -/
lemma compression_norm_le_of_relative_residual
    (full compressed residual z : ℝ)
    (hSplit : full ≤ compressed + residual)
    (hResidual : residual ≤ z * full)
    (hzOne : z < 1) :
    full ≤ compressed / (1 - z) := by
  have hDen : 0 < 1 - z := sub_pos.mpr hzOne
  apply (le_div_iff₀ hDen).2
  have hCompressed : full ≤ compressed + z * full := by
    exact hSplit.trans (add_le_add_right hResidual compressed)
  nlinarith

/-- Posterior norm bound for the parity sum of a same-sign and a reflected
Loewner block.  The compressed total is bounded as one object, so cancellation
between the two low-rank pieces is preserved. -/
theorem twoLoewnerCompression_posterior
    (sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
      zSame zReflected : ℝ)
    (hzSame : 0 ≤ zSame) (hzSameOne : zSame < 1)
    (hzReflected : 0 ≤ zReflected) (hzReflectedOne : zReflected < 1)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ zSame * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ zReflected * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm) :
    totalNorm ≤
      compressedTotalNorm +
        (zSame / (1 - zSame)) * compressedSameNorm +
        (zReflected / (1 - zReflected)) * compressedReflectedNorm := by
  have hSame := compression_norm_le_of_relative_residual
    sameNorm compressedSameNorm residualSameNorm zSame
    hSameSplit hSameResidual hzSameOne
  have hReflected := compression_norm_le_of_relative_residual
    reflectedNorm compressedReflectedNorm residualReflectedNorm zReflected
    hReflectedSplit hReflectedResidual hzReflectedOne
  have hSameResidual' :
      residualSameNorm ≤
        (zSame / (1 - zSame)) * compressedSameNorm := by
    calc
      residualSameNorm ≤ zSame * sameNorm := hSameResidual
      _ ≤ zSame * (compressedSameNorm / (1 - zSame)) :=
        mul_le_mul_of_nonneg_left hSame hzSame
      _ = (zSame / (1 - zSame)) * compressedSameNorm := by ring
  have hReflectedResidual' :
      residualReflectedNorm ≤
        (zReflected / (1 - zReflected)) * compressedReflectedNorm := by
    calc
      residualReflectedNorm ≤ zReflected * reflectedNorm := hReflectedResidual
      _ ≤ zReflected *
          (compressedReflectedNorm / (1 - zReflected)) :=
        mul_le_mul_of_nonneg_left hReflected hzReflected
      _ = (zReflected / (1 - zReflected)) *
          compressedReflectedNorm := by ring
  exact hTotalSplit.trans
    (add_le_add
      (add_le_add_right hSameResidual' compressedTotalNorm)
      hReflectedResidual')

/-- Feed a two-Loewner compression posterior into the ordinary shell
coercivity adapter.  All large-dimensional work is isolated in the norm and
compression premises; the final relative-energy inequality is kernel checked.
-/
theorem relativeCoupling_of_twoLoewnerCompression
    (lowEnergy highEnergy cross lowGap highGap q lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
      zSame zReflected epsilon : ℝ)
    (hLowGap : 0 ≤ lowGap) (hHighGap : 0 ≤ highGap)
    (hq : 0 ≤ q) (hLowNorm : 0 ≤ lowNorm) (hHighNorm : 0 ≤ highNorm)
    (hEpsilon : 0 ≤ epsilon)
    (hLowEnergy : lowGap * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy : highGap * highNorm ^ 2 ≤ highEnergy)
    (hzSame : 0 ≤ zSame) (hzSameOne : zSame < 1)
    (hzReflected : 0 ≤ zReflected) (hzReflectedOne : zReflected < 1)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ zSame * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ zReflected * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hPosteriorBudget :
      compressedTotalNorm +
          (zSame / (1 - zSame)) * compressedSameNorm +
          (zReflected / (1 - zReflected)) * compressedReflectedNorm ≤ epsilon)
    (hCross : |cross| ≤ totalNorm * lowNorm * highNorm)
    (hBudget : epsilon ^ 2 ≤ q * lowGap * highGap) :
    cross ^ 2 ≤ q * lowEnergy * highEnergy := by
  have hPosterior := twoLoewnerCompression_posterior
    sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
    residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm
    zSame zReflected hzSame hzSameOne hzReflected hzReflectedOne
    hSameSplit hReflectedSplit hSameResidual hReflectedResidual hTotalSplit
  have hTotalEpsilon : totalNorm ≤ epsilon :=
    hPosterior.trans hPosteriorBudget
  have hCross' : |cross| ≤ epsilon * lowNorm * highNorm := by
    calc
      |cross| ≤ totalNorm * lowNorm * highNorm := hCross
      _ ≤ epsilon * lowNorm * highNorm := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hTotalEpsilon hLowNorm)
          hHighNorm
  exact relativeCoupling_of_coerciveNormBounds
    lowEnergy highEnergy cross lowGap highGap epsilon q lowNorm highNorm
    hLowGap hHighGap hEpsilon hq hLowEnergy hHighEnergy hCross'
    hLowNorm hHighNorm hBudget

/-- The planned logarithmic-shift compression uses 64 factors for the
same-sign block and 12 for the better-separated reflected block.  Displacement
rank two turns these into a combined rank cap of 152. -/
lemma v23_adjacentLoewnerCompression_rankLedger :
    2 * 64 + 2 * 12 = 152 := by
  norm_num

lemma oneOverTwoHundred_posteriorInflation :
    (1 / 200 : ℝ) / (1 - 1 / 200) = 1 / 199 := by
  norm_num

lemma oneOverFourThousand_posteriorInflation :
    (1 / 4000 : ℝ) / (1 - 1 / 4000) = 1 / 3999 := by
  norm_num

end RiemannCvs.V23BoundaryWeylMainline
