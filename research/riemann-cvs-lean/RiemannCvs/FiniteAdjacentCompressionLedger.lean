import RiemannCvs.AdjacentShellRebalancedCompression
import RiemannCvs.FiniteAdjacentAdiShiftBindings

/-!
# Common compression ledger for the final eleven finite adjacent bridges

The scalable Arb certificates use the common compressed caps `5/4`, `1/4`,
and `5/4` with the already uniform residual caps `1/200` and `1/4000`.
Both adjacent shell floors are `24/5` from `K=15360` onward.  This module
kernel-checks the common posterior and relative-energy conversion once, then
exports a named theorem family for every remaining finite bridge.

The finite Gram bounds and transcendental shift-cell inequalities stay as
explicit certificate premises.  No external numerical fact is introduced as
a Lean axiom.
-/

noncomputable section
open scoped BigOperators Real
namespace RiemannCvs.V23BoundaryWeylMainline

lemma v23_finiteAdjacent_rankLedger :
    2 * 64 + 2 * 12 = 152 := by
  norm_num

lemma v23_finiteAdjacent_compressionPosteriorLedger :
    (5 / 4 : ℝ) + (1 / 199) * (5 / 4) + (1 / 3999) * (1 / 4) =
      3999199 / 3183204 := by
  norm_num

lemma v23_finiteAdjacent_compressionPosterior_budgetSlack :
    (2 / 27 : ℝ) * (24 / 5) * (24 / 5) -
        (3999199 / 3183204) ^ 2 =
      32492459399591 / 253319692640400 := by
  norm_num

lemma v23_finiteAdjacent_compressionPosterior_fits_twoOver27 :
    (3999199 / 3183204 : ℝ) ^ 2 ≤
      (2 / 27 : ℝ) * (24 / 5) * (24 / 5) := by
  norm_num

theorem v23_finiteAdjacent_twoLoewnerCompression_posterior
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
    (hCompressedSame : compressedSameNorm ≤ (5 / 4 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (5 / 4 : ℝ)) :
    totalNorm ≤ 3999199 / 3183204 := by
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
    _ ≤ (5 / 4 : ℝ) + (1 / 199) * (5 / 4) + (1 / 3999) * (1 / 4) := by
      gcongr
    _ = 3999199 / 3183204 :=
      v23_finiteAdjacent_compressionPosteriorLedger

theorem relativeCoupling_of_finiteAdjacent_rank152Compression
    (lowEnergy highEnergy cross lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ)
    (hLowNorm : 0 ≤ lowNorm) (hHighNorm : 0 ≤ highNorm)
    (hLowEnergy : (24 / 5 : ℝ) * lowNorm ^ 2 ≤ lowEnergy)
    (hHighEnergy : (24 / 5 : ℝ) * highNorm ^ 2 ≤ highEnergy)
    (hSameSplit : sameNorm ≤ compressedSameNorm + residualSameNorm)
    (hReflectedSplit :
      reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm)
    (hSameResidual : residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm)
    (hReflectedResidual :
      residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm)
    (hTotalSplit :
      totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm)
    (hCompressedSame : compressedSameNorm ≤ (5 / 4 : ℝ))
    (hCompressedReflected : compressedReflectedNorm ≤ (1 / 4 : ℝ))
    (hCompressedTotal : compressedTotalNorm ≤ (5 / 4 : ℝ))
    (hCross : |cross| ≤ totalNorm * lowNorm * highNorm) :
    cross ^ 2 ≤ (2 / 27 : ℝ) * lowEnergy * highEnergy := by
  let epsilon : ℝ := 3999199 / 3183204
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
      _ ≤ (5 / 4 : ℝ) + (1 / 199) * (5 / 4) + (1 / 3999) * (1 / 4) := by
        gcongr
      _ = epsilon := by
        simpa [epsilon] using v23_finiteAdjacent_compressionPosteriorLedger
  exact relativeCoupling_of_twoLoewnerCompression
    lowEnergy highEnergy cross
    (24 / 5) (24 / 5) (2 / 27) lowNorm highNorm
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
        v23_finiteAdjacent_compressionPosterior_fits_twoOver27)

abbrev FiniteAdjacentRankStatement : Prop :=
  2 * 64 + 2 * 12 = 152

abbrev FiniteAdjacentPosteriorLedgerStatement : Prop :=
  (5 / 4 : ℝ) + (1 / 199) * (5 / 4) + (1 / 3999) * (1 / 4) =
    3999199 / 3183204

abbrev FiniteAdjacentBudgetSlackStatement : Prop :=
  (2 / 27 : ℝ) * (24 / 5) * (24 / 5) -
      (3999199 / 3183204) ^ 2 =
    32492459399591 / 253319692640400

abbrev FiniteAdjacentFitsStatement : Prop :=
  (3999199 / 3183204 : ℝ) ^ 2 ≤
    (2 / 27 : ℝ) * (24 / 5) * (24 / 5)

abbrev FiniteAdjacentPosteriorStatement : Prop :=
  ∀ (sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ),
    sameNorm ≤ compressedSameNorm + residualSameNorm →
    reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm →
    residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm →
    residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm →
    totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm →
    compressedSameNorm ≤ (5 / 4 : ℝ) →
    compressedReflectedNorm ≤ (1 / 4 : ℝ) →
    compressedTotalNorm ≤ (5 / 4 : ℝ) →
    totalNorm ≤ 3999199 / 3183204

abbrev FiniteAdjacentRelativeCouplingStatement : Prop :=
  ∀ (lowEnergy highEnergy cross lowNorm highNorm
      sameNorm reflectedNorm compressedSameNorm compressedReflectedNorm
      residualSameNorm residualReflectedNorm compressedTotalNorm totalNorm : ℝ),
    0 ≤ lowNorm → 0 ≤ highNorm →
    (24 / 5 : ℝ) * lowNorm ^ 2 ≤ lowEnergy →
    (24 / 5 : ℝ) * highNorm ^ 2 ≤ highEnergy →
    sameNorm ≤ compressedSameNorm + residualSameNorm →
    reflectedNorm ≤ compressedReflectedNorm + residualReflectedNorm →
    residualSameNorm ≤ (1 / 200 : ℝ) * sameNorm →
    residualReflectedNorm ≤ (1 / 4000 : ℝ) * reflectedNorm →
    totalNorm ≤ compressedTotalNorm + residualSameNorm + residualReflectedNorm →
    compressedSameNorm ≤ (5 / 4 : ℝ) →
    compressedReflectedNorm ≤ (1 / 4 : ℝ) →
    compressedTotalNorm ≤ (5 / 4 : ℝ) →
    |cross| ≤ totalNorm * lowNorm * highNorm →
    cross ^ 2 ≤ (2 / 27 : ℝ) * lowEnergy * highEnergy

theorem v23_finiteAdjacent_rankStatement : FiniteAdjacentRankStatement := by
  exact v23_finiteAdjacent_rankLedger

theorem v23_finiteAdjacent_posteriorLedgerStatement :
    FiniteAdjacentPosteriorLedgerStatement := by
  simpa only [FiniteAdjacentPosteriorLedgerStatement] using
    v23_finiteAdjacent_compressionPosteriorLedger

theorem v23_finiteAdjacent_budgetSlackStatement :
    FiniteAdjacentBudgetSlackStatement := by
  simpa only [FiniteAdjacentBudgetSlackStatement] using
    v23_finiteAdjacent_compressionPosterior_budgetSlack

theorem v23_finiteAdjacent_fitsStatement : FiniteAdjacentFitsStatement := by
  simpa only [FiniteAdjacentFitsStatement] using
    v23_finiteAdjacent_compressionPosterior_fits_twoOver27

theorem v23_finiteAdjacent_posteriorStatement :
    FiniteAdjacentPosteriorStatement := by
  simpa only [FiniteAdjacentPosteriorStatement] using
    v23_finiteAdjacent_twoLoewnerCompression_posterior

theorem v23_finiteAdjacent_relativeCouplingStatement :
    FiniteAdjacentRelativeCouplingStatement := by
  simpa only [FiniteAdjacentRelativeCouplingStatement] using
    relativeCoupling_of_finiteAdjacent_rank152Compression

lemma v23_k15360_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k15360_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k15360_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k15360_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k15360_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k15360_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k30720_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k30720_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k30720_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k30720_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k30720_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k30720_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k61440_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k61440_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k61440_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k61440_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k61440_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k61440_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k122880_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k122880_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k122880_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k122880_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k122880_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k122880_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k245760_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k245760_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k245760_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k245760_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k245760_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k245760_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k491520_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k491520_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k491520_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k491520_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k491520_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k491520_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k983040_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k983040_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k983040_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k983040_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k983040_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k983040_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k1966080_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k1966080_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k1966080_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k1966080_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k1966080_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k1966080_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k3932160_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k3932160_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k3932160_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k3932160_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k3932160_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k3932160_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k7864320_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k7864320_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k7864320_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k7864320_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k7864320_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k7864320_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

lemma v23_k15728640_adjacentLoewnerCompression_rankLedger :
    FiniteAdjacentRankStatement := v23_finiteAdjacent_rankStatement
lemma v23_k15728640_compressionPosteriorLedger :
    FiniteAdjacentPosteriorLedgerStatement := v23_finiteAdjacent_posteriorLedgerStatement
lemma v23_k15728640_compressionPosterior_budgetSlack :
    FiniteAdjacentBudgetSlackStatement := v23_finiteAdjacent_budgetSlackStatement
lemma v23_k15728640_compressionPosterior_fits_twoOver27 :
    FiniteAdjacentFitsStatement := v23_finiteAdjacent_fitsStatement
theorem v23_k15728640_twoLoewnerCompression_posterior :
    FiniteAdjacentPosteriorStatement := v23_finiteAdjacent_posteriorStatement
theorem relativeCoupling_of_k15728640_rank152Compression :
    FiniteAdjacentRelativeCouplingStatement := v23_finiteAdjacent_relativeCouplingStatement

end RiemannCvs.V23BoundaryWeylMainline
