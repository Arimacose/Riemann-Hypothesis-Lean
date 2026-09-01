import RiemannCvs.PoleSeparatedBands
import RiemannCvs.AsymptoticCoreNewestTotalError

/-!
# Fixed-prefix / remote-shell Archimedean channel

The dyadic shell estimate in `ArchimedeanRemainderSchur` treats both indices
at the remote scale.  Here the first index stays in the certified finite
prefix.  A uniform `2/5` centered-symbol bound on every positive mode,
together with the inverse-mode remote bound and the actual Fourier gap,
recovers an entry envelope of order `1/N`.
-/

noncomputable section

open scoped BigOperators Real

namespace RiemannCvs.ArchimedeanSeparatedBands

open RiemannCvs.CombinedSymbolDyadicL2
open RiemannCvs.C13ArchimedeanEndpoint
open RiemannCvs.BoundaryWeylSchurTail
open RiemannCvs.V23BoundaryWeylMainline
open RiemannCvs.PrimeTranslationSeparatedBands
open RiemannCvs.PoleSeparatedBands

/-- A premise-free centered-symbol bound valid from the very first positive
mode.  The constant is intentionally rational and slightly loose. -/
theorem c13_centeredLogarithmicArchimedeanSymbol_abs_le_twoFifths
    (x : ℝ) (hx : 1 ≤ x) :
    |logarithmicArchimedeanSymbol 13 x - Real.pi / 4| ≤ (2 / 5 : ℝ) := by
  let y : ℝ := archimedeanAsymptoticHeight 13 x
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hLogPos : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have hLogPi : Real.log (13 : ℝ) < Real.pi := by
    nlinarith [log_thirteen_lt, Real.pi_gt_three]
  have hPiX : Real.pi ≤ Real.pi * x := by
    nlinarith [Real.pi_pos]
  have hy : (1 : ℝ) ≤ y := by
    dsimp [y, archimedeanAsymptoticHeight]
    rw [le_div_iff₀ hLogPos]
    nlinarith
  have hyPos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hySq : (1 : ℝ) ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hInv : 1 / y ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hy
  have hInvSq : 1 / y ^ 2 ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hySq
  have hQuarter : 1 / (4 * y) ≤ (1 / 4 : ℝ) := by
    calc
      1 / (4 * y) = (1 / 4 : ℝ) * (1 / y) := by ring
      _ ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = 1 / 4 := by ring
  have hEighth : 1 / (8 * y) ≤ (1 / 8 : ℝ) := by
    calc
      1 / (8 * y) = (1 / 8 : ℝ) * (1 / y) := by ring
      _ ≤ (1 / 8 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = 1 / 8 := by ring
  have hSqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := sqrt_two_upper
  have hSqrtCoeff : Real.sqrt 2 / 12 ≤ (1 / 8 : ℝ) := by
    nlinarith
  have hRemainder : Real.sqrt 2 / (12 * y ^ 2) ≤ (1 / 8 : ℝ) := by
    calc
      Real.sqrt 2 / (12 * y ^ 2) =
          (Real.sqrt 2 / 12) * (1 / y ^ 2) := by ring
      _ ≤ (1 / 8 : ℝ) * (1 / y ^ 2) :=
        mul_le_mul_of_nonneg_right hSqrtCoeff (by positivity)
      _ ≤ (1 / 8 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hInvSq (by norm_num)
      _ = 1 / 8 := by ring
  have hMass : archimedeanGeometricMass 13 / (2 * y) ≤ (7 / 50 : ℝ) := by
    have hMassBound := c13_geometricMass_le_sevenTwentyFive
    have hMassCoeff : archimedeanGeometricMass 13 / 2 ≤ (7 / 50 : ℝ) := by
      nlinarith
    calc
      archimedeanGeometricMass 13 / (2 * y) =
          (archimedeanGeometricMass 13 / 2) * (1 / y) := by ring
      _ ≤ (7 / 50 : ℝ) * (1 / y) :=
        mul_le_mul_of_nonneg_right hMassCoeff (by positivity)
      _ ≤ (7 / 50 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = 7 / 50 := by ring
  have hBounds := centeredLogarithmicArchimedeanSymbol_bounds
    13 x (by norm_num) hxPos
  rw [abs_le]
  constructor
  · nlinarith [hBounds.2, hEighth, hRemainder, hMass]
  · nlinarith [hBounds.1, hQuarter, hRemainder]

/-- Every member of the fixed positive prefix inherits the global rational
centered-symbol bound. -/
theorem c13_fixedPrefix_centeredArchimedeanSymbol_abs_le_twoFifths
    (F N : ℕ) (i : Fin F) :
    |centeredArchimedeanSymbol 13
        (fixedRemotePositiveMode F N (Sum.inl i))| ≤ (2 / 5 : ℝ) := by
  have hMode : (1 : ℝ) ≤
      ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) := by
    exact_mod_cast fixedRemotePositiveMode_inl_pos F N i
  simpa [centeredArchimedeanSymbol] using
    c13_centeredLogarithmicArchimedeanSymbol_abs_le_twoFifths
      ((fixedRemotePositiveMode F N (Sum.inl i) : ℤ) : ℝ) hMode

/-- The remote member uses the sharper inverse-mode estimate; `1/4` is kept
here only as a convenient common rational envelope for the entry algebra. -/
theorem c13_remote_centeredArchimedeanSymbol_abs_le_oneFourth
    (F N : ℕ) (hN : 960 ≤ N) (j : Fin N) :
    |centeredArchimedeanSymbol 13
        (fixedRemotePositiveMode F N (Sum.inr j))| ≤ (1 / 4 : ℝ) := by
  let m := fixedRemotePositiveMode F N (Sum.inr j)
  have hmNat : 960 ≤ N + (j : ℕ) + 1 := by omega
  have hm : (960 : ℝ) ≤ (m : ℝ) := by
    dsimp [m, fixedRemotePositiveMode]
    exact_mod_cast hmNat
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hPoint : |centeredArchimedeanSymbol 13 m| ≤
      (1 / 4 : ℝ) / (m : ℝ) := by
    simpa [centeredArchimedeanSymbol, m] using
      c13_centeredLogarithmicArchimedeanSymbol_abs_le (m : ℝ) hm
  exact hPoint.trans (by
    calc
      (1 / 4 : ℝ) / (m : ℝ) = (1 / 4 : ℝ) * (1 / (m : ℝ)) := by ring
      _ ≤ (1 / 4 : ℝ) * 1 := by
        gcongr
        simpa using one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 1) hmOne
      _ = 1 / 4 := by ring)

/-- The same-sign Archimedean entry between the fixed prefix and the remote
band retains the actual Fourier gap. -/
theorem c13_fixedRemoteArchimedeanSameSignEntry_abs_le
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (i : Fin F) (j : Fin N) :
    |logarithmicCvSArchimedeanEntry 13
        (fixedRemotePositiveMode F N (Sum.inl i))
        (fixedRemotePositiveMode F N (Sum.inr j))| ≤
      (13 / 60 : ℝ) / ((N : ℝ) + 1 - (F : ℝ)) := by
  let a := fixedRemotePositiveMode F N (Sum.inl i)
  let b := fixedRemotePositiveMode F N (Sum.inr j)
  let g : ℝ := (N : ℝ) + 1 - (F : ℝ)
  have habZ : a < b := fixedRemotePositiveMode_inl_lt_inr F N hFN i j
  have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast habZ
  have hne : a ≠ b := ne_of_lt habZ
  have hiFNat : (i : ℕ) + 1 ≤ F := by omega
  have hiF : ((i : ℕ) : ℝ) + 1 ≤ (F : ℝ) := by exact_mod_cast hiFNat
  have hjNonneg : (0 : ℝ) ≤ (j : ℕ) := by positivity
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have haEq : (a : ℝ) = ((i : ℕ) : ℝ) + 1 := by
    simp [a, fixedRemotePositiveMode]
  have hbEq : (b : ℝ) = (N : ℝ) + (j : ℕ) + 1 := by
    simp [b, finGlobalShellPositiveMode]
    ring
  have hgPos : 0 < g := by dsimp [g]; linarith
  have hGapDiff : g ≤ (b : ℝ) - (a : ℝ) := by
    dsimp [g]
    rw [haEq, hbEq]
    linarith
  have hLow : |centeredArchimedeanSymbol 13 a| ≤ (2 / 5 : ℝ) := by
    simpa [a] using
      c13_fixedPrefix_centeredArchimedeanSymbol_abs_le_twoFifths F N i
  have hHigh : |centeredArchimedeanSymbol 13 b| ≤ (1 / 4 : ℝ) := by
    simpa [b] using
      c13_remote_centeredArchimedeanSymbol_abs_le_oneFourth F N hN j
  have hNum : |centeredArchimedeanSymbol 13 b -
      centeredArchimedeanSymbol 13 a| ≤ (13 / 20 : ℝ) := by
    calc
      |centeredArchimedeanSymbol 13 b - centeredArchimedeanSymbol 13 a| ≤
          |centeredArchimedeanSymbol 13 b| +
            |centeredArchimedeanSymbol 13 a| := abs_sub _ _
      _ ≤ 1 / 4 + 2 / 5 := add_le_add hHigh hLow
      _ = 13 / 20 := by norm_num
  have hDen : 3 * g ≤ |Real.pi * ((a : ℝ) - (b : ℝ))| := by
    rw [abs_mul, abs_of_pos Real.pi_pos,
      abs_of_neg (sub_neg.mpr hab)]
    rw [show -((a : ℝ) - (b : ℝ)) = (b : ℝ) - (a : ℝ) by ring]
    have hFirst : 3 * g ≤ 3 * ((b : ℝ) - (a : ℝ)) :=
      mul_le_mul_of_nonneg_left hGapDiff (by norm_num)
    have hSecond : 3 * ((b : ℝ) - (a : ℝ)) ≤
        Real.pi * ((b : ℝ) - (a : ℝ)) :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sub_nonneg.mpr hab.le)
    exact hFirst.trans hSecond
  have hDenPos : 0 < |Real.pi * ((a : ℝ) - (b : ℝ))| :=
    lt_of_lt_of_le (mul_pos (by norm_num) hgPos) hDen
  rw [logarithmicCvSArchimedeanEntry_sameSign_eq 13 a b hne, abs_div]
  calc
    |centeredArchimedeanSymbol 13 b - centeredArchimedeanSymbol 13 a| /
        |Real.pi * ((a : ℝ) - (b : ℝ))| ≤
        (13 / 20 : ℝ) / |Real.pi * ((a : ℝ) - (b : ℝ))| :=
      div_le_div_of_nonneg_right hNum hDenPos.le
    _ ≤ (13 / 20 : ℝ) / (3 * g) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hgPos) hDen
    _ = (13 / 60 : ℝ) / g := by
      field_simp [ne_of_gt hgPos]
      norm_num
    _ = (13 / 60 : ℝ) / ((N : ℝ) + 1 - (F : ℝ)) := rfl

/-- The reflected entry has the same gap decay; its explicit `43/60` bound
includes the rational Cauchy-kernel leading term. -/
theorem c13_fixedRemoteArchimedeanReflectedEntry_abs_le
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (i : Fin F) (j : Fin N) :
    |logarithmicCvSArchimedeanEntry 13
        (fixedRemotePositiveMode F N (Sum.inl i))
        (-fixedRemotePositiveMode F N (Sum.inr j))| ≤
      (43 / 60 : ℝ) / ((N : ℝ) + 1 - (F : ℝ)) := by
  let a := fixedRemotePositiveMode F N (Sum.inl i)
  let b := fixedRemotePositiveMode F N (Sum.inr j)
  let g : ℝ := (N : ℝ) + 1 - (F : ℝ)
  have haZ : 0 < a := fixedRemotePositiveMode_inl_pos F N i
  have hbZ : 0 < b := fixedRemotePositiveMode_inr_pos F N j
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast haZ
  have hb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbZ
  have hiFNat : (i : ℕ) + 1 ≤ F := by omega
  have hiF : ((i : ℕ) : ℝ) + 1 ≤ (F : ℝ) := by exact_mod_cast hiFNat
  have hjNonneg : (0 : ℝ) ≤ (j : ℕ) := by positivity
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have haEq : (a : ℝ) = ((i : ℕ) : ℝ) + 1 := by
    simp [a, fixedRemotePositiveMode]
  have hbEq : (b : ℝ) = (N : ℝ) + (j : ℕ) + 1 := by
    simp [b, finGlobalShellPositiveMode]
    ring
  have hgPos : 0 < g := by dsimp [g]; linarith
  have hGapSum : g ≤ (a : ℝ) + (b : ℝ) := by
    dsimp [g]
    rw [haEq, hbEq]
    linarith
  have hLow : |centeredArchimedeanSymbol 13 a| ≤ (2 / 5 : ℝ) := by
    simpa [a] using
      c13_fixedPrefix_centeredArchimedeanSymbol_abs_le_twoFifths F N i
  have hHigh : |centeredArchimedeanSymbol 13 b| ≤ (1 / 4 : ℝ) := by
    simpa [b] using
      c13_remote_centeredArchimedeanSymbol_abs_le_oneFourth F N hN j
  have hNum : |centeredArchimedeanSymbol 13 a +
      centeredArchimedeanSymbol 13 b| ≤ (13 / 20 : ℝ) := by
    calc
      |centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b| ≤
          |centeredArchimedeanSymbol 13 a| +
            |centeredArchimedeanSymbol 13 b| := abs_add_le _ _
      _ ≤ 2 / 5 + 1 / 4 := add_le_add hLow hHigh
      _ = 13 / 20 := by norm_num
  have hLead : 1 / (2 * ((a : ℝ) + (b : ℝ))) ≤ 1 / (2 * g) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hDen : 3 * g ≤ |Real.pi * ((a : ℝ) + (b : ℝ))| := by
    rw [abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (add_pos ha hb)]
    have hFirst : 3 * g ≤ 3 * ((a : ℝ) + (b : ℝ)) :=
      mul_le_mul_of_nonneg_left hGapSum (by norm_num)
    have hSecond : 3 * ((a : ℝ) + (b : ℝ)) ≤
        Real.pi * ((a : ℝ) + (b : ℝ)) :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (add_pos ha hb).le
    exact hFirst.trans hSecond
  have hDenPos : 0 < |Real.pi * ((a : ℝ) + (b : ℝ))| :=
    lt_of_lt_of_le (mul_pos (by norm_num) hgPos) hDen
  have hFrac :
      |(centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b) /
          (Real.pi * ((a : ℝ) + (b : ℝ)))| ≤
        (13 / 60 : ℝ) / g := by
    rw [abs_div]
    calc
      |centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b| /
          |Real.pi * ((a : ℝ) + (b : ℝ))| ≤
          (13 / 20 : ℝ) / |Real.pi * ((a : ℝ) + (b : ℝ))| :=
        div_le_div_of_nonneg_right hNum hDenPos.le
      _ ≤ (13 / 20 : ℝ) / (3 * g) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hgPos) hDen
      _ = (13 / 60 : ℝ) / g := by
        field_simp [ne_of_gt hgPos]
        norm_num
  rw [logarithmicCvSArchimedeanEntry_reflected_eq 13 a b haZ hbZ]
  calc
    |-(1 / (2 * ((a : ℝ) + (b : ℝ)))) -
        (centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b) /
          (Real.pi * ((a : ℝ) + (b : ℝ)))| ≤
        |-(1 / (2 * ((a : ℝ) + (b : ℝ))))| +
          |(centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b) /
            (Real.pi * ((a : ℝ) + (b : ℝ)))| := abs_sub _ _
    _ = 1 / (2 * ((a : ℝ) + (b : ℝ))) +
          |(centeredArchimedeanSymbol 13 a + centeredArchimedeanSymbol 13 b) /
            (Real.pi * ((a : ℝ) + (b : ℝ)))| := by
      rw [abs_neg, abs_of_pos]
      positivity
    _ ≤ 1 / (2 * g) + (13 / 60 : ℝ) / g :=
      add_le_add hLead hFrac
    _ = (43 / 60 : ℝ) / g := by
      field_simp [ne_of_gt hgPos]
      norm_num
    _ = (43 / 60 : ℝ) / ((N : ℝ) + 1 - (F : ℝ)) := rfl

/-- The two even-parity Archimedean pieces fit under the simple unit gap
kernel. -/
theorem c13_fixedRemoteEvenArchimedeanEntry_abs_le_one_div_gap
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (i : Fin F) (j : Fin N) :
    |logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix 13
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
      1 / ((N : ℝ) + 1 - (F : ℝ)) := by
  let g : ℝ := (N : ℝ) + 1 - (F : ℝ)
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have hgPos : 0 < g := by dsimp [g]; linarith
  have hSame := c13_fixedRemoteArchimedeanSameSignEntry_abs_le
    F N hFN hN i j
  have hReflect := c13_fixedRemoteArchimedeanReflectedEntry_abs_le
    F N hFN hN i j
  simp only [logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix,
    reduceCtorEq, if_false]
  calc
    |-logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j)) -
        logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j))| ≤
        |logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j))| +
        |logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j))| := by
      simpa only [abs_neg] using abs_sub
        (-logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j)))
        (logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j)))
    _ ≤ (13 / 60 : ℝ) / g + (43 / 60 : ℝ) / g := by
      simpa only [g] using add_le_add hSame hReflect
    _ = (14 / 15 : ℝ) / g := by ring
    _ ≤ 1 / g := div_le_div_of_nonneg_right (by norm_num) hgPos.le
    _ = 1 / ((N : ℝ) + 1 - (F : ℝ)) := rfl

/-- Odd-parity companion; the sign change does not alter the absolute
envelope. -/
theorem c13_fixedRemoteOddArchimedeanEntry_abs_le_one_div_gap
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (i : Fin F) (j : Fin N) :
    |logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix 13
        (fixedRemotePositiveMode F N) (Sum.inl i) (Sum.inr j)| ≤
      1 / ((N : ℝ) + 1 - (F : ℝ)) := by
  let g : ℝ := (N : ℝ) + 1 - (F : ℝ)
  have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
  have hgPos : 0 < g := by dsimp [g]; linarith
  have hSame := c13_fixedRemoteArchimedeanSameSignEntry_abs_le
    F N hFN hN i j
  have hReflect := c13_fixedRemoteArchimedeanReflectedEntry_abs_le
    F N hFN hN i j
  simp only [logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix,
    reduceCtorEq, if_false]
  calc
    |-logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j)) +
        logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j))| ≤
        |logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j))| +
        |logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j))| := by
      simpa only [abs_neg] using abs_add_le
        (-logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (fixedRemotePositiveMode F N (Sum.inr j)))
        (logarithmicCvSArchimedeanEntry 13
          (fixedRemotePositiveMode F N (Sum.inl i))
          (-fixedRemotePositiveMode F N (Sum.inr j)))
    _ ≤ (13 / 60 : ℝ) / g + (43 / 60 : ℝ) / g := by
      simpa only [g] using add_le_add hSame hReflect
    _ = (14 / 15 : ℝ) / g := by ring
    _ ≤ 1 / g := div_le_div_of_nonneg_right (by norm_num) hgPos.le
    _ = 1 / ((N : ℝ) + 1 - (F : ℝ)) := rfl

noncomputable def c13FixedRemoteEvenArchimedeanMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix 13
    (fixedRemotePositiveMode F N)

noncomputable def c13FixedRemoteOddArchimedeanMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix 13
    (fixedRemotePositiveMode F N)

/-- Literal identification with component one of the even builder error
vector. -/
@[simp] lemma c13_fixedRemoteEvenBuilderError_one (F N : ℕ) :
    logarithmicCvSBuilderEvenPositiveModeErrorMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) 1 =
      c13FixedRemoteEvenArchimedeanMatrix F N := by
  rfl

/-- Literal odd-parity builder identification. -/
@[simp] lemma c13_fixedRemoteOddBuilderError_one (F N : ℕ) :
    logarithmicCvSBuilderOddPositiveModeErrorMatrix
        13 c13PrimePowerLocation c13PrimePowerBase
        (fixedRemotePositiveMode F N) 1 =
      c13FixedRemoteOddArchimedeanMatrix F N := by
  rfl

lemma fixedRemotePositiveMode_pos (F N : ℕ)
    (q : Fin F ⊕ Fin N) : 0 < fixedRemotePositiveMode F N q := by
  cases q with
  | inl i => exact fixedRemotePositiveMode_inl_pos F N i
  | inr j => exact fixedRemotePositiveMode_inr_pos F N j

lemma c13FixedRemoteEvenArchimedeanMatrix_symm
    (F N : ℕ) (i j : Fin F ⊕ Fin N) :
    c13FixedRemoteEvenArchimedeanMatrix F N i j =
      c13FixedRemoteEvenArchimedeanMatrix F N j i := by
  exact logarithmicCvSArchimedeanEvenPositiveModeRemainderMatrix_symm_of_pos
    13 (fixedRemotePositiveMode F N) (fixedRemotePositiveMode_pos F N) i j

lemma c13FixedRemoteOddArchimedeanMatrix_symm
    (F N : ℕ) (i j : Fin F ⊕ Fin N) :
    c13FixedRemoteOddArchimedeanMatrix F N i j =
      c13FixedRemoteOddArchimedeanMatrix F N j i := by
  exact logarithmicCvSArchimedeanOddPositiveModeRemainderMatrix_symm_of_pos
    13 (fixedRemotePositiveMode F N) (fixedRemotePositiveMode_pos F N) i j

theorem c13_fixedRemoteEvenArchimedeanBilinear_sq_le
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin F)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13FixedRemoteEvenArchimedeanMatrix F N
            (Sum.inl ij.1) (Sum.inr ij.2) * (x ij.1 * y ij.2)) ^ 2 ≤
      ((F : ℝ) * (N : ℝ) *
          (1 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have h := rectangular_bilinear_sq_le_card_product_of_entry_abs_le
    (fun i j => c13FixedRemoteEvenArchimedeanMatrix F N
      (Sum.inl i) (Sum.inr j)) x y
    (1 / ((N : ℝ) + 1 - (F : ℝ))) (by
      have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
      exact div_nonneg (by norm_num) (by linarith)) (fun i j => by
        exact c13_fixedRemoteEvenArchimedeanEntry_abs_le_one_div_gap
          F N hFN hN i j)
  simpa [c13FixedRemoteEvenArchimedeanMatrix] using h

theorem c13_fixedRemoteOddArchimedeanBilinear_sq_le
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin F)) ×ˢ
          (Finset.univ : Finset (Fin N)),
        c13FixedRemoteOddArchimedeanMatrix F N
            (Sum.inl ij.1) (Sum.inr ij.2) * (x ij.1 * y ij.2)) ^ 2 ≤
      ((F : ℝ) * (N : ℝ) *
          (1 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2) *
        ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
  have h := rectangular_bilinear_sq_le_card_product_of_entry_abs_le
    (fun i j => c13FixedRemoteOddArchimedeanMatrix F N
      (Sum.inl i) (Sum.inr j)) x y
    (1 / ((N : ℝ) + 1 - (F : ℝ))) (by
      have hFNReal : (F : ℝ) ≤ (N : ℝ) := by exact_mod_cast hFN
      exact div_nonneg (by norm_num) (by linarith)) (fun i j => by
        exact c13_fixedRemoteOddArchimedeanEntry_abs_le_one_div_gap
          F N hFN hN i j)
  simpa [c13FixedRemoteOddArchimedeanMatrix] using h

/-- Squared Euclidean cross coefficient of the Archimedean fixed/remote
rectangle. -/
noncomputable def c13FixedRemoteArchimedeanCoefficient (F N : ℕ) : ℝ :=
  (F : ℝ) * (N : ℝ) *
    (1 / ((N : ℝ) + 1 - (F : ℝ))) ^ 2

/-- The unit-gap Archimedean coefficient is exactly one thirty-sixth of the
already transported prime coefficient. -/
lemma c13FixedRemoteArchimedeanCoefficient_eq_prime_div_thirtySix
    (F N : ℕ) :
    c13FixedRemoteArchimedeanCoefficient F N =
      (1 / 36 : ℝ) * c13FixedRemotePrimeCoefficient F N := by
  unfold c13FixedRemoteArchimedeanCoefficient c13FixedRemotePrimeCoefficient
  ring

theorem c13_fixedRemoteEvenArchimedeanCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenArchimedeanMatrix F N) x y) ^ 2 ≤
      c13FixedRemoteArchimedeanCoefficient F N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteEvenArchimedeanMatrix F N) x y
    (c13FixedRemoteEvenArchimedeanMatrix_symm F N)]
  have h := c13_fixedRemoteEvenArchimedeanBilinear_sq_le
    F N hFN hN x y
  simpa only [c13FixedRemoteArchimedeanCoefficient,
    finiteVectorEuclideanNormSq, Finset.sum_product,
    Finset.sum_const_zero, mul_assoc, mul_left_comm, mul_comm] using h

theorem c13_fixedRemoteOddArchimedeanCrossEnergy_sq_le_coefficient
    (F N : ℕ) (hFN : F ≤ N) (hN : 960 ≤ N)
    (x : Fin F → ℝ) (y : Fin N → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddArchimedeanMatrix F N) x y) ^ 2 ≤
      c13FixedRemoteArchimedeanCoefficient F N *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [finiteMatrixBlockCrossEnergy_eq_leftRight_of_symm
    (c13FixedRemoteOddArchimedeanMatrix F N) x y
    (c13FixedRemoteOddArchimedeanMatrix_symm F N)]
  have h := c13_fixedRemoteOddArchimedeanBilinear_sq_le
    F N hFN hN x y
  simpa only [c13FixedRemoteArchimedeanCoefficient,
    finiteVectorEuclideanNormSq, Finset.sum_product,
    Finset.sum_const_zero, mul_assoc, mul_left_comm, mul_comm] using h

/-- First-scale coefficient.  Reusing the prime transport theorem gives the
clean rational `1/90`; the exact decimal coefficient is smaller still. -/
theorem c13_fixed3840_remoteArchimedeanCoefficient_le_oneNinetieth
    (N : ℕ) (hN : 371293 ≤ N) :
    c13FixedRemoteArchimedeanCoefficient 3840 N ≤ (1 / 90 : ℝ) := by
  rw [c13FixedRemoteArchimedeanCoefficient_eq_prime_div_thirtySix]
  calc
    (1 / 36 : ℝ) * c13FixedRemotePrimeCoefficient 3840 N ≤
        (1 / 36 : ℝ) * (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (c13_fixed3840_remote_primeCoefficient_le_twoFifths N hN)
        (by norm_num)
    _ = 1 / 90 := by norm_num

theorem c13_fixed3840_remoteArchimedeanCoefficient_dyadic_le
    (k : ℕ) :
    c13FixedRemoteArchimedeanCoefficient 3840 (371293 * 2 ^ k) ≤
      (1 / 90 : ℝ) * (1 / 2 : ℝ) ^ k := by
  rw [c13FixedRemoteArchimedeanCoefficient_eq_prime_div_thirtySix]
  have hPrime := c13_fixed3840_remote_primeCoefficient_dyadic_le k
  calc
    (1 / 36 : ℝ) *
        c13FixedRemotePrimeCoefficient 3840 (371293 * 2 ^ k) ≤
        (1 / 36 : ℝ) * ((2 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hPrime (by norm_num)
    _ = (1 / 90 : ℝ) * (1 / 2 : ℝ) ^ k := by ring

theorem c13_fixed3840_remoteEvenArchimedeanCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenArchimedeanMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 90 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : 371293 ≤ 371293 * 2 ^ k :=
    Nat.le_mul_of_pos_right 371293 (Nat.pow_pos (by omega))
  have hRaw := c13_fixedRemoteEvenArchimedeanCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) (by omega) (by omega) x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixed3840_remoteArchimedeanCoefficient_dyadic_le k)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

theorem c13_fixed3840_remoteOddArchimedeanCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddArchimedeanMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((1 / 90 : ℝ) * (1 / 2 : ℝ) ^ k) *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hN : 371293 ≤ 371293 * 2 ^ k :=
    Nat.le_mul_of_pos_right 371293 (Nat.pow_pos (by omega))
  have hRaw := c13_fixedRemoteOddArchimedeanCrossEnergy_sq_le_coefficient
    3840 (371293 * 2 ^ k) (by omega) (by omega) x y
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (c13_fixed3840_remoteArchimedeanCoefficient_dyadic_le k)
    (mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)))

/-!
## Three-source fixed-prefix bridge

All three actual CvS error components now carry the same dyadic factor.  The
rational amplitudes `448/1000`, `106/1000`, and `633/1000` dominate the square
roots of the pole, Archimedean, and prime squared coefficients respectively.
-/

noncomputable def c13FixedRemoteEvenTotalErrorMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  c13FixedRemoteEvenPoleMatrix F N +
    c13FixedRemoteEvenArchimedeanMatrix F N +
      c13FixedRemoteEvenPrimeErrorMatrix F N

noncomputable def c13FixedRemoteOddTotalErrorMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  c13FixedRemoteOddPoleMatrix F N +
    c13FixedRemoteOddArchimedeanMatrix F N +
      c13FixedRemoteOddPrimeErrorMatrix F N

/-- The total error matrix is exactly the sum of the three even builder error
components. -/
lemma c13_fixedRemoteEvenBuilderError_sum_eq_total (F N : ℕ) :
    (∑ r, logarithmicCvSBuilderEvenPositiveModeErrorMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode F N) r) =
        c13FixedRemoteEvenTotalErrorMatrix F N := by
  ext i j
  simp [Fin.sum_univ_three, c13FixedRemoteEvenTotalErrorMatrix,
    c13FixedRemoteEvenPoleMatrix, c13FixedRemoteEvenArchimedeanMatrix,
    c13FixedRemoteEvenPrimeErrorMatrix,
    logarithmicCvSBuilderEvenPositiveModeErrorMatrix]

/-- Odd-parity component identity. -/
lemma c13_fixedRemoteOddBuilderError_sum_eq_total (F N : ℕ) :
    (∑ r, logarithmicCvSBuilderOddPositiveModeErrorMatrix
      13 c13PrimePowerLocation c13PrimePowerBase
      (fixedRemotePositiveMode F N) r) =
        c13FixedRemoteOddTotalErrorMatrix F N := by
  ext i j
  simp [Fin.sum_univ_three, c13FixedRemoteOddTotalErrorMatrix,
    c13FixedRemoteOddPoleMatrix, c13FixedRemoteOddArchimedeanMatrix,
    c13FixedRemoteOddPrimeErrorMatrix,
    logarithmicCvSBuilderOddPositiveModeErrorMatrix]

theorem c13_fixed3840_remoteEvenTotalErrorCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenTotalErrorMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let D : ℝ := (1 / 2 : ℝ) ^ k
  let Z : ℝ := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let E : ℝ := D * Z
  let pole := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteEvenPoleMatrix 3840 (371293 * 2 ^ k)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteEvenArchimedeanMatrix 3840 (371293 * 2 ^ k)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteEvenPrimeErrorMatrix 3840 (371293 * 2 ^ k)) x y
  have hZ : 0 ≤ Z := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := mul_nonneg hD hZ
  have hPoleRaw : pole ^ 2 ≤ (1 / 5 : ℝ) * D * Z := by
    simpa [pole, D, Z, mul_assoc] using
      c13_fixed3840_remoteEvenPoleCrossEnergy_sq_le_dyadic k x y
  have hArchRaw : arch ^ 2 ≤ (1 / 90 : ℝ) * D * Z := by
    simpa [arch, D, Z, mul_assoc] using
      c13_fixed3840_remoteEvenArchimedeanCrossEnergy_sq_le_dyadic k x y
  have hPrimeRaw : prime ^ 2 ≤ (2 / 5 : ℝ) * D * Z := by
    simpa [prime, D, Z, finiteVectorEuclideanNormSq, mul_assoc] using
      c13_fixed3840_remoteEvenPrimeErrorCrossEnergy_sq_le_dyadic k x y
  have hPole : pole ^ 2 ≤ (448 / 1000 : ℝ) ^ 2 * E :=
    hPoleRaw.trans (by
      dsimp [E]
      have hCoeff : (1 / 5 : ℝ) ≤ (448 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (1 / 5 : ℝ) * D * Z = (1 / 5 : ℝ) * (D * Z) := by ring
        _ ≤ (448 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hArch : arch ^ 2 ≤ (106 / 1000 : ℝ) ^ 2 * E :=
    hArchRaw.trans (by
      dsimp [E]
      have hCoeff : (1 / 90 : ℝ) ≤ (106 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (1 / 90 : ℝ) * D * Z = (1 / 90 : ℝ) * (D * Z) := by ring
        _ ≤ (106 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hPrime : prime ^ 2 ≤ (633 / 1000 : ℝ) ^ 2 * E :=
    hPrimeRaw.trans (by
      dsimp [E]
      have hCoeff : (2 / 5 : ℝ) ≤ (633 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (2 / 5 : ℝ) * D * Z = (2 / 5 : ℝ) * (D * Z) := by ring
        _ ≤ (633 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (448 / 1000 : ℝ) (106 / 1000 : ℝ)
      (633 / 1000 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (1187 / 1000 : ℝ) =
      448 / 1000 + 106 / 1000 + 633 / 1000 by norm_num]
  rw [c13FixedRemoteEvenTotalErrorMatrix,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  simpa [pole, arch, prime, E, D, Z, mul_assoc] using hTotal

theorem c13_fixed3840_remoteOddTotalErrorCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddTotalErrorMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  let D : ℝ := (1 / 2 : ℝ) ^ k
  let Z : ℝ := finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y
  let E : ℝ := D * Z
  let pole := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteOddPoleMatrix 3840 (371293 * 2 ^ k)) x y
  let arch := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteOddArchimedeanMatrix 3840 (371293 * 2 ^ k)) x y
  let prime := finiteMatrixBlockCrossEnergy
    (c13FixedRemoteOddPrimeErrorMatrix 3840 (371293 * 2 ^ k)) x y
  have hZ : 0 ≤ Z := mul_nonneg
    (finiteVectorEuclideanNormSq_nonneg x)
    (finiteVectorEuclideanNormSq_nonneg y)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := mul_nonneg hD hZ
  have hPoleRaw : pole ^ 2 ≤ (1 / 5 : ℝ) * D * Z := by
    simpa [pole, D, Z, mul_assoc] using
      c13_fixed3840_remoteOddPoleCrossEnergy_sq_le_dyadic k x y
  have hArchRaw : arch ^ 2 ≤ (1 / 90 : ℝ) * D * Z := by
    simpa [arch, D, Z, mul_assoc] using
      c13_fixed3840_remoteOddArchimedeanCrossEnergy_sq_le_dyadic k x y
  have hPrimeRaw : prime ^ 2 ≤ (2 / 5 : ℝ) * D * Z := by
    simpa [prime, D, Z, finiteVectorEuclideanNormSq, mul_assoc] using
      c13_fixed3840_remoteOddPrimeErrorCrossEnergy_sq_le_dyadic k x y
  have hPole : pole ^ 2 ≤ (448 / 1000 : ℝ) ^ 2 * E :=
    hPoleRaw.trans (by
      dsimp [E]
      have hCoeff : (1 / 5 : ℝ) ≤ (448 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (1 / 5 : ℝ) * D * Z = (1 / 5 : ℝ) * (D * Z) := by ring
        _ ≤ (448 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hArch : arch ^ 2 ≤ (106 / 1000 : ℝ) ^ 2 * E :=
    hArchRaw.trans (by
      dsimp [E]
      have hCoeff : (1 / 90 : ℝ) ≤ (106 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (1 / 90 : ℝ) * D * Z = (1 / 90 : ℝ) * (D * Z) := by ring
        _ ≤ (106 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hPrime : prime ^ 2 ≤ (633 / 1000 : ℝ) ^ 2 * E :=
    hPrimeRaw.trans (by
      dsimp [E]
      have hCoeff : (2 / 5 : ℝ) ≤ (633 / 1000 : ℝ) ^ 2 := by norm_num
      calc
        (2 / 5 : ℝ) * D * Z = (2 / 5 : ℝ) * (D * Z) := by ring
        _ ≤ (633 / 1000 : ℝ) ^ 2 * (D * Z) :=
          mul_le_mul_of_nonneg_right hCoeff hE)
  have hTotal := three_cross_sq_le_sum_amplitudes
    pole arch prime (448 / 1000 : ℝ) (106 / 1000 : ℝ)
      (633 / 1000 : ℝ) E
    (by norm_num) (by norm_num) (by norm_num) hE hPole hArch hPrime
  rw [show (1187 / 1000 : ℝ) =
      448 / 1000 + 106 / 1000 + 633 / 1000 by norm_num]
  rw [c13FixedRemoteOddTotalErrorMatrix,
    finiteMatrixBlockCrossEnergy_add, finiteMatrixBlockCrossEnergy_add]
  simpa [pole, arch, prime, E, D, Z, mul_assoc] using hTotal

/-- Full even CvS builder matrix on the fixed-prefix/remote split. -/
noncomputable def c13FixedRemoteEvenBuilderMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderEvenPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

/-- Full odd builder matrix. -/
noncomputable def c13FixedRemoteOddBuilderMatrix (F N : ℕ) :
    Matrix (Fin F ⊕ Fin N) (Fin F ⊕ Fin N) ℝ :=
  logarithmicCvSBuilderOddPositiveModeMatrix
    13 c13PrimePowerLocation c13PrimePowerBase (fixedRemotePositiveMode F N)

lemma c13FixedRemoteEvenBuilderMatrix_inl_inr_eq_totalError
    (F N : ℕ) (i : Fin F) (j : Fin N) :
    c13FixedRemoteEvenBuilderMatrix F N (Sum.inl i) (Sum.inr j) =
      c13FixedRemoteEvenTotalErrorMatrix F N (Sum.inl i) (Sum.inr j) := by
  rw [c13FixedRemoteEvenBuilderMatrix,
    logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition]
  simp [c13FixedRemoteEvenTotalErrorMatrix,
    c13FixedRemoteEvenPoleMatrix, c13FixedRemoteEvenArchimedeanMatrix,
    c13FixedRemoteEvenPrimeErrorMatrix,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderEvenPositiveModeErrorMatrix]

lemma c13FixedRemoteOddBuilderMatrix_inl_inr_eq_totalError
    (F N : ℕ) (i : Fin F) (j : Fin N) :
    c13FixedRemoteOddBuilderMatrix F N (Sum.inl i) (Sum.inr j) =
      c13FixedRemoteOddTotalErrorMatrix F N (Sum.inl i) (Sum.inr j) := by
  rw [c13FixedRemoteOddBuilderMatrix,
    logarithmicCvSBuilderOddPositiveModeMatrix_decomposition]
  simp [c13FixedRemoteOddTotalErrorMatrix,
    c13FixedRemoteOddPoleMatrix, c13FixedRemoteOddArchimedeanMatrix,
    c13FixedRemoteOddPrimeErrorMatrix,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderOddPositiveModeErrorMatrix]

lemma c13FixedRemoteEvenBuilderMatrix_inr_inl_eq_totalError
    (F N : ℕ) (j : Fin N) (i : Fin F) :
    c13FixedRemoteEvenBuilderMatrix F N (Sum.inr j) (Sum.inl i) =
      c13FixedRemoteEvenTotalErrorMatrix F N (Sum.inr j) (Sum.inl i) := by
  rw [c13FixedRemoteEvenBuilderMatrix,
    logarithmicCvSBuilderEvenPositiveModeMatrix_decomposition]
  simp [c13FixedRemoteEvenTotalErrorMatrix,
    c13FixedRemoteEvenPoleMatrix, c13FixedRemoteEvenArchimedeanMatrix,
    c13FixedRemoteEvenPrimeErrorMatrix,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderEvenPositiveModeErrorMatrix]

lemma c13FixedRemoteOddBuilderMatrix_inr_inl_eq_totalError
    (F N : ℕ) (j : Fin N) (i : Fin F) :
    c13FixedRemoteOddBuilderMatrix F N (Sum.inr j) (Sum.inl i) =
      c13FixedRemoteOddTotalErrorMatrix F N (Sum.inr j) (Sum.inl i) := by
  rw [c13FixedRemoteOddBuilderMatrix,
    logarithmicCvSBuilderOddPositiveModeMatrix_decomposition]
  simp [c13FixedRemoteOddTotalErrorMatrix,
    c13FixedRemoteOddPoleMatrix, c13FixedRemoteOddArchimedeanMatrix,
    c13FixedRemoteOddPrimeErrorMatrix,
    logarithmicCvSArchimedeanPositiveModeDiagonalMatrix,
    Fin.sum_univ_three, logarithmicCvSBuilderOddPositiveModeErrorMatrix]

lemma c13FixedRemoteEvenBuilderMatrix_crossEnergy_eq_totalError
    (F N : ℕ) (x : Fin F → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy (c13FixedRemoteEvenBuilderMatrix F N) x y =
      finiteMatrixBlockCrossEnergy (c13FixedRemoteEvenTotalErrorMatrix F N) x y := by
  unfold finiteMatrixBlockCrossEnergy
  simp_rw [c13FixedRemoteEvenBuilderMatrix_inl_inr_eq_totalError,
    c13FixedRemoteEvenBuilderMatrix_inr_inl_eq_totalError]

lemma c13FixedRemoteOddBuilderMatrix_crossEnergy_eq_totalError
    (F N : ℕ) (x : Fin F → ℝ) (y : Fin N → ℝ) :
    finiteMatrixBlockCrossEnergy (c13FixedRemoteOddBuilderMatrix F N) x y =
      finiteMatrixBlockCrossEnergy (c13FixedRemoteOddTotalErrorMatrix F N) x y := by
  unfold finiteMatrixBlockCrossEnergy
  simp_rw [c13FixedRemoteOddBuilderMatrix_inl_inr_eq_totalError,
    c13FixedRemoteOddBuilderMatrix_inr_inl_eq_totalError]

/-- Complete even-builder cross estimate from the certified prefix
`[1,3840]` to every analytic dyadic remote shell. -/
theorem c13_fixed3840_remoteEvenBuilderCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenBuilderMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13FixedRemoteEvenBuilderMatrix_crossEnergy_eq_totalError]
  exact c13_fixed3840_remoteEvenTotalErrorCrossEnergy_sq_le_dyadic k x y

/-- Complete odd-builder companion. -/
theorem c13_fixed3840_remoteOddBuilderCrossEnergy_sq_le_dyadic
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddBuilderMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  rw [c13FixedRemoteOddBuilderMatrix_crossEnergy_eq_totalError]
  exact c13_fixed3840_remoteOddTotalErrorCrossEnergy_sq_le_dyadic k x y

/-- A rational square-root envelope for the dyadic factor.  The deliberately
slightly larger ratio `3/4` makes the cross amplitudes themselves summable. -/
lemma half_pow_le_threeFourths_pow_sq (k : ℕ) :
    (1 / 2 : ℝ) ^ k ≤ ((3 / 4 : ℝ) ^ k) ^ 2 := by
  have hPow : (1 / 2 : ℝ) ^ k ≤ (9 / 16 : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  calc
    (1 / 2 : ℝ) ^ k ≤ (9 / 16 : ℝ) ^ k := hPow
    _ = ((3 / 4 : ℝ) ^ k) ^ 2 := by
      rw [pow_two, ← mul_pow]
      norm_num

theorem c13_fixed3840_remoteEvenBuilderCrossEnergy_sq_le_summableAmplitude
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteEvenBuilderMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((6 / 5 : ℝ) * (3 / 4 : ℝ) ^ k) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13_fixed3840_remoteEvenBuilderCrossEnergy_sq_le_dyadic k x y
  have hAmp : (1187 / 1000 : ℝ) ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by norm_num
  have hDyadic := half_pow_le_threeFourths_pow_sq k
  have hCoeff : (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k ≤
      (6 / 5 : ℝ) ^ 2 * ((3 / 4 : ℝ) ^ k) ^ 2 :=
    mul_le_mul hAmp hDyadic (by positivity) (by positivity)
  have hNorms : 0 ≤
      finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y :=
    mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)
  refine hRaw.trans ?_
  have hScaled := mul_le_mul_of_nonneg_right hCoeff hNorms
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hScaled

theorem c13_fixed3840_remoteOddBuilderCrossEnergy_sq_le_summableAmplitude
    (k : ℕ) (x : Fin 3840 → ℝ)
    (y : Fin (371293 * 2 ^ k) → ℝ) :
    (finiteMatrixBlockCrossEnergy
        (c13FixedRemoteOddBuilderMatrix 3840 (371293 * 2 ^ k)) x y) ^ 2 ≤
      ((6 / 5 : ℝ) * (3 / 4 : ℝ) ^ k) ^ 2 *
        (finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y) := by
  have hRaw := c13_fixed3840_remoteOddBuilderCrossEnergy_sq_le_dyadic k x y
  have hAmp : (1187 / 1000 : ℝ) ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by norm_num
  have hDyadic := half_pow_le_threeFourths_pow_sq k
  have hCoeff : (1187 / 1000 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k ≤
      (6 / 5 : ℝ) ^ 2 * ((3 / 4 : ℝ) ^ k) ^ 2 :=
    mul_le_mul hAmp hDyadic (by positivity) (by positivity)
  have hNorms : 0 ≤
      finiteVectorEuclideanNormSq x * finiteVectorEuclideanNormSq y :=
    mul_nonneg (finiteVectorEuclideanNormSq_nonneg x)
      (finiteVectorEuclideanNormSq_nonneg y)
  refine hRaw.trans ?_
  have hScaled := mul_le_mul_of_nonneg_right hCoeff hNorms
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hScaled

/-- The rational amplitude envelope has an exact finite total mass. -/
theorem summable_c13_fixedRemoteBuilderDyadicAmplitude :
    Summable (fun k : ℕ => (6 / 5 : ℝ) * (3 / 4 : ℝ) ^ k) := by
  exact (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).mul_left (6 / 5 : ℝ)

theorem tsum_c13_fixedRemoteBuilderDyadicAmplitude :
    ∑' k : ℕ, (6 / 5 : ℝ) * (3 / 4 : ℝ) ^ k = (24 / 5 : ℝ) := by
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)]
  norm_num

end RiemannCvs.ArchimedeanSeparatedBands
