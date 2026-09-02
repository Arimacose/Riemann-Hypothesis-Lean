import RiemannCvs.LoewnerAdiTelescope
import RiemannCvs.CvSParityDisplacement

namespace RiemannCvs

open RiemannCvs.CvSParityDisplacement

noncomputable section

lemma oddDifferenceKernel_eq_scaledLoewnerEntry_rescaled
    (symbol diagonal : ℝ → ℝ) (K p q : ℝ)
    (hK : 0 < K) (hpq : p ≠ q) :
    oddDifferenceKernel symbol diagonal p q =
      scaledLoewnerEntry (1 / Real.sqrt K) (1 / Real.sqrt K)
        (fun x => symbol (K * x)) (p / K) (q / K) := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hSqrt0 : Real.sqrt K ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hK)
  have hpqScaled : p / K ≠ q / K := by
    intro h
    apply hpq
    exact (div_left_inj' hK0).mp h
  unfold oddDifferenceKernel
  rw [if_neg hpq]
  unfold scaledLoewnerEntry
  simp only [one_div]
  rw [show K * (p / K) = p by field_simp,
    show K * (q / K) = q by field_simp]
  have hSqrtSq : (Real.sqrt K) ^ 2 = K :=
    Real.sq_sqrt (le_of_lt hK)
  field_simp
  rw [hSqrtSq]

/-- Direct certificate-facing factorization of any off-diagonal CvS Loewner
entry after the balanced `1/sqrt K` coordinate rescaling. -/
theorem oddDifferenceKernel_adi_factorization_rescaled
    (symbol diagonal : ℝ → ℝ) (shifts : List (ℝ × ℝ)) (K p q : ℝ)
    (hK : 0 < K) (hpq : p ≠ q)
    (hpPole : ∀ shift ∈ shifts, p / K ≠ shift.2)
    (hqRoot : ∀ shift ∈ shifts, q / K ≠ shift.1)
    (hqPole : ∀ shift ∈ shifts, q / K ≠ shift.2) :
    oddDifferenceKernel symbol diagonal p q *
        (1 - adiRationalProduct shifts (p / K) /
          adiRationalProduct shifts (q / K)) =
      adiFactorDot shifts (p / K) (q / K)
          (-symbol p * (1 / Real.sqrt K)) (1 / Real.sqrt K) +
        adiFactorDot shifts (p / K) (q / K)
          (1 / Real.sqrt K) (symbol q * (1 / Real.sqrt K)) := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hpqScaled : p / K ≠ q / K := by
    intro h
    apply hpq
    exact (div_left_inj' hK0).mp h
  rw [oddDifferenceKernel_eq_scaledLoewnerEntry_rescaled
    symbol diagonal K p q hK hpq]
  have hpScale : K * (p / K) = p := by field_simp
  have hqScale : K * (q / K) = q := by field_simp
  have h := scaledLoewnerEntry_adi_factorization_rationalProduct
    shifts (1 / Real.sqrt K) (1 / Real.sqrt K)
    (fun x => symbol (K * x)) (p / K) (q / K)
    hpqScaled hpPole hqRoot hqPole
  rw [hpScale, hqScale] at h
  exact h

end
end RiemannCvs
