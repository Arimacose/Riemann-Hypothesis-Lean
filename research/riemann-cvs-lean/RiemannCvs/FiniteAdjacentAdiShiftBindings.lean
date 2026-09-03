import RiemannCvs.AdjacentAdiShiftBinding

/-!
# Literal ADI shift bindings for the final eleven finite adjacent bridges

Each namespace fixes the 64 same-sign and 12 reflected logarithmic shifts for
one adjacent shell, together with the integer pole cells independently checked
by Arb at 256 and 384 bits.  The transcendental inequalities remain fields of
`LiteralShiftCertificate`; Lean turns those fields into grid noncollision and
the exact rank-two ADI factorizations.
-/

namespace RiemannCvs
namespace FiniteAdjacentAdiShiftBindings

open scoped BigOperators Real
open RiemannCvs.AdjacentAdiShiftBinding
open RiemannCvs.CvSParityDisplacement

structure LiteralShiftCertificate (K : ℕ)
    {sameFactors reflectedFactors : ℕ}
    (sameShifts : Fin sameFactors → ℝ × ℝ)
    (sameCells : Fin sameFactors → ℕ)
    (reflectedShifts : Fin reflectedFactors → ℝ × ℝ)
    (reflectedCells : Fin reflectedFactors → ℕ) : Prop where
  same : SameGridCertificate K sameShifts sameCells
  reflected : ReflectedGridCertificate K reflectedShifts reflectedCells

def SameFactorizationStatement (K : ℕ) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) : Prop :=
  ∀ (symbol diagonal : ℝ → ℝ) (p q : ℕ),
    p ≤ 2 * K → 2 * K + 1 ≤ q →
      oddDifferenceKernel symbol diagonal (p : ℝ) (q : ℝ) *
          (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / K) /
            adiRationalProduct (List.ofFn shifts) ((q : ℝ) / K)) =
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) ((q : ℝ) / K)
            (-symbol p * (1 / Real.sqrt K)) (1 / Real.sqrt K) +
          adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) ((q : ℝ) / K)
            (1 / Real.sqrt K) (symbol q * (1 / Real.sqrt K))

def ReflectedFactorizationStatement (K : ℕ) {n : ℕ}
    (shifts : Fin n → ℝ × ℝ) : Prop :=
  ∀ (symbol diagonal : ℝ → ℝ) (p q : ℕ),
    K + 1 ≤ p → 2 * K + 1 ≤ q →
      oddDifferenceKernel symbol diagonal (p : ℝ) (-(q : ℝ)) *
          (1 - adiRationalProduct (List.ofFn shifts) ((p : ℝ) / K) /
            adiRationalProduct (List.ofFn shifts) (-(q : ℝ) / K)) =
        adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) (-(q : ℝ) / K)
            (-symbol p * (1 / Real.sqrt K)) (1 / Real.sqrt K) +
          adiFactorDot (List.ofFn shifts) ((p : ℝ) / K) (-(q : ℝ) / K)
            (1 / Real.sqrt K)
            (symbol (-(q : ℝ)) * (1 / Real.sqrt K))

theorem same_factorization_of_literal
    (K : ℕ) (hK : 0 < K) {sameFactors reflectedFactors : ℕ}
    (sameShifts : Fin sameFactors → ℝ × ℝ)
    (sameCells : Fin sameFactors → ℕ)
    (reflectedShifts : Fin reflectedFactors → ℝ × ℝ)
    (reflectedCells : Fin reflectedFactors → ℕ)
    (hcert : LiteralShiftCertificate K
      sameShifts sameCells reflectedShifts reflectedCells) :
    SameFactorizationStatement K sameShifts := by
  intro symbol diagonal p q hp hq
  exact AdjacentAdiShiftBinding.same_factorization_of_gridCertificate
    K hK sameShifts sameCells hcert.same symbol diagonal p q hp hq

theorem reflected_factorization_of_literal
    (K : ℕ) (hK : 0 < K) {sameFactors reflectedFactors : ℕ}
    (sameShifts : Fin sameFactors → ℝ × ℝ)
    (sameCells : Fin sameFactors → ℕ)
    (reflectedShifts : Fin reflectedFactors → ℝ × ℝ)
    (reflectedCells : Fin reflectedFactors → ℕ)
    (hcert : LiteralShiftCertificate K
      sameShifts sameCells reflectedShifts reflectedCells) :
    ReflectedFactorizationStatement K reflectedShifts := by
  intro symbol diagonal p q hp hq
  exact AdjacentAdiShiftBinding.reflected_factorization_of_gridCertificate
    K hK reflectedShifts reflectedCells hcert.reflected
      symbol diagonal p q hp hq

namespace K15360

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (15361 / 15360 : ℝ) 2 (30721 / 15360 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-30721 / 15360 : ℝ) (15361 / 15360 : ℝ) 2

def samePoleCellList : List ℕ :=
  [30721, 30721, 30721, 30721, 30721, 30721, 30721, 30722,
    30722, 30722, 30723, 30723, 30724, 30725, 30726, 30727,
    30728, 30729, 30731, 30733, 30735, 30738, 30741, 30745,
    30749, 30754, 30761, 30768, 30777, 30787, 30799, 30813,
    30830, 30850, 30874, 30901, 30934, 30973, 31019, 31073,
    31138, 31213, 31303, 31410, 31536, 31686, 31863, 32074,
    32325, 32624, 32980, 33406, 33916, 34528, 35267, 36160,
    37246, 38575, 40212, 42246, 44804, 48064, 52293, 57911]

def reflectedPoleCellList : List ℕ :=
  [31530, 33235, 35065, 37030, 39144, 41419,
    43871, 46519, 49381, 52480, 55841, 59494]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 15360
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 15360 sameShifts :=
  same_factorization_of_literal 15360 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 15360 reflectedShifts :=
  reflected_factorization_of_literal 15360 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K15360

namespace K30720

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (30721 / 30720 : ℝ) 2 (61441 / 30720 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-61441 / 30720 : ℝ) (30721 / 30720 : ℝ) 2

def samePoleCellList : List ℕ :=
  [61441, 61441, 61441, 61441, 61441, 61441, 61442, 61442,
    61442, 61443, 61443, 61444, 61445, 61445, 61446, 61448,
    61449, 61451, 61453, 61456, 61459, 61462, 61467, 61472,
    61478, 61485, 61494, 61505, 61517, 61532, 61550, 61571,
    61597, 61627, 61663, 61706, 61758, 61820, 61893, 61981,
    62086, 62212, 62363, 62543, 62758, 63016, 63326, 63697,
    64143, 64679, 65326, 66105, 67049, 68193, 69585, 71286,
    73375, 75955, 79167, 83202, 88331, 94948, 103653, 115400]

def reflectedPoleCellList : List ℕ :=
  [63059, 66470, 70129, 74060, 78287, 82838,
    87743, 93038, 98762, 104959, 111682, 118988]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 30720
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 30720 sameShifts :=
  same_factorization_of_literal 30720 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 30720 reflectedShifts :=
  reflected_factorization_of_literal 30720 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K30720

namespace K61440

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (61441 / 61440 : ℝ) 2 (122881 / 61440 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-122881 / 61440 : ℝ) (61441 / 61440 : ℝ) 2

def samePoleCellList : List ℕ :=
  [122881, 122881, 122881, 122881, 122881, 122881, 122882, 122882,
    122882, 122883, 122884, 122884, 122885, 122886, 122888, 122889,
    122891, 122893, 122896, 122899, 122903, 122908, 122914, 122921,
    122930, 122940, 122952, 122967, 122985, 123007, 123033, 123064,
    123102, 123148, 123204, 123271, 123352, 123449, 123567, 123709,
    123881, 124089, 124340, 124643, 125010, 125454, 125992, 126644,
    127435, 128396, 129565, 130990, 132731, 134863, 137483, 140715,
    144722, 149722, 156008, 163987, 174243, 187635, 205489, 229963]

def reflectedPoleCellList : List ℕ :=
  [126117, 132939, 140258, 148120, 156574, 165675,
    175485, 186075, 197523, 209919, 223364, 237975]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 61440
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 61440 sameShifts :=
  same_factorization_of_literal 61440 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 61440 reflectedShifts :=
  reflected_factorization_of_literal 61440 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K61440

namespace K122880

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (122881 / 122880 : ℝ) 2 (245761 / 122880 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-245761 / 122880 : ℝ) (122881 / 122880 : ℝ) 2

def samePoleCellList : List ℕ :=
  [245761, 245761, 245761, 245761, 245761, 245761, 245762, 245762,
    245763, 245763, 245764, 245765, 245766, 245767, 245769, 245771,
    245773, 245776, 245780, 245784, 245789, 245796, 245803, 245813,
    245825, 245839, 245856, 245877, 245903, 245934, 245973, 246019,
    246076, 246146, 246230, 246334, 246460, 246614, 246802, 247031,
    247311, 247653, 248070, 248580, 249203, 249965, 250898, 252040,
    253440, 255158, 257269, 259868, 263074, 267039, 271958, 278087,
    285760, 295426, 307701, 323446, 343902, 370929, 407440, 458270]

def reflectedPoleCellList : List ℕ :=
  [252234, 265877, 280516, 296240, 313147, 331349,
    350970, 372150, 395046, 419838, 446728, 475951]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 122880
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 122880 sameShifts :=
  same_factorization_of_literal 122880 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 122880 reflectedShifts :=
  reflected_factorization_of_literal 122880 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K122880

namespace K245760

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (245761 / 245760 : ℝ) 2 (491521 / 245760 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-491521 / 245760 : ℝ) (245761 / 245760 : ℝ) 2

def samePoleCellList : List ℕ :=
  [491521, 491521, 491521, 491521, 491521, 491522, 491522, 491522,
    491523, 491524, 491525, 491526, 491527, 491528, 491530, 491533,
    491536, 491539, 491544, 491550, 491556, 491565, 491575, 491588,
    491604, 491624, 491648, 491678, 491715, 491760, 491816, 491885,
    491970, 492074, 492203, 492363, 492559, 492801, 493100, 493468,
    493923, 494484, 495177, 496032, 497088, 498393, 500007, 502003,
    504476, 507540, 511345, 516075, 521967, 529327, 538548, 550148,
    564813, 583469, 607395, 638397, 679110, 733525, 807992, 913261]

def reflectedPoleCellList : List ℕ :=
  [504467, 531753, 561031, 592479, 626294, 662698,
    701940, 744300, 790092, 839675, 893457, 951903]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 245760
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 245760 sameShifts :=
  same_factorization_of_literal 245760 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 245760 reflectedShifts :=
  reflected_factorization_of_literal 245760 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K245760

namespace K491520

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (491521 / 491520 : ℝ) 2 (983041 / 491520 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-983041 / 491520 : ℝ) (491521 / 491520 : ℝ) 2

def samePoleCellList : List ℕ :=
  [983041, 983041, 983041, 983041, 983041, 983042, 983042, 983043,
    983043, 983044, 983045, 983046, 983048, 983050, 983052, 983055,
    983059, 983064, 983069, 983077, 983086, 983097, 983111, 983128,
    983150, 983177, 983211, 983253, 983305, 983370, 983452, 983553,
    983679, 983837, 984033, 984278, 984582, 984963, 985436, 986027,
    986764, 987683, 988830, 990260, 992046, 994276, 997062, 1000545,
    1004902, 1010360, 1017202, 1025796, 1036609, 1050248, 1067506, 1089426,
    1117408, 1153354, 1199910, 1260846, 1341718, 1451043, 1602570, 1820028]

def reflectedPoleCellList : List ℕ :=
  [1008934, 1063506, 1122062, 1184957, 1252587, 1325396,
    1403880, 1488599, 1580184, 1679350, 1786914, 1903806]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 491520
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 491520 sameShifts :=
  same_factorization_of_literal 491520 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 491520 reflectedShifts :=
  reflected_factorization_of_literal 491520 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K491520

namespace K983040

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (983041 / 983040 : ℝ) 2 (1966081 / 983040 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-1966081 / 983040 : ℝ) (983041 / 983040 : ℝ) 2

def samePoleCellList : List ℕ :=
  [1966081, 1966081, 1966081, 1966081, 1966081, 1966082, 1966082, 1966083,
    1966084, 1966084, 1966086, 1966087, 1966089, 1966091, 1966094, 1966098,
    1966103, 1966108, 1966116, 1966125, 1966137, 1966152, 1966170, 1966194,
    1966223, 1966260, 1966307, 1966366, 1966441, 1966535, 1966653, 1966801,
    1966989, 1967225, 1967523, 1967897, 1968370, 1968965, 1969715, 1970661,
    1971852, 1973354, 1975248, 1977637, 1980650, 1984453, 1989254, 1995318,
    2002984, 2012684, 2024972, 2040560, 2060371, 2085609, 2117857, 2159220,
    2212535, 2281695, 2372147, 2491730, 2652098, 2871327, 3179015, 3627197]

def reflectedPoleCellList : List ℕ :=
  [2017867, 2127012, 2244123, 2369913, 2505174, 2650792,
    2807760, 2977198, 3160367, 3358700, 3573828, 3807613]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 983040
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 983040 sameShifts :=
  same_factorization_of_literal 983040 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 983040 reflectedShifts :=
  reflected_factorization_of_literal 983040 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K983040

namespace K1966080

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (1966081 / 1966080 : ℝ) 2 (3932161 / 1966080 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-3932161 / 1966080 : ℝ) (1966081 / 1966080 : ℝ) 2

def samePoleCellList : List ℕ :=
  [3932161, 3932161, 3932161, 3932161, 3932161, 3932162, 3932162, 3932163,
    3932164, 3932165, 3932166, 3932168, 3932170, 3932173, 3932177, 3932181,
    3932187, 3932194, 3932204, 3932216, 3932231, 3932250, 3932275, 3932307,
    3932347, 3932398, 3932463, 3932546, 3932651, 3932786, 3932957, 3933175,
    3933452, 3933806, 3934256, 3934829, 3935559, 3936490, 3937675, 3939184,
    3941107, 3943558, 3946681, 3950661, 3955736, 3962208, 3970466, 3981007,
    3994472, 4011686, 4033715, 4061947, 4098192, 4144826, 4205005, 4282952,
    4384404, 4517288, 4692788, 4927124, 5244643, 5683520, 6307133, 7228930]

def reflectedPoleCellList : List ℕ :=
  [4035734, 4254023, 4488246, 4739826, 5010348, 5301584,
    5615520, 5954395, 6320734, 6717401, 7147656, 7615227]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 1966080
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 1966080 sameShifts :=
  same_factorization_of_literal 1966080 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 1966080 reflectedShifts :=
  reflected_factorization_of_literal 1966080 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K1966080

namespace K3932160

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (3932161 / 3932160 : ℝ) 2 (7864321 / 3932160 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-7864321 / 3932160 : ℝ) (3932161 / 3932160 : ℝ) 2

def samePoleCellList : List ℕ :=
  [7864321, 7864321, 7864321, 7864321, 7864322, 7864322, 7864323, 7864323,
    7864324, 7864326, 7864327, 7864329, 7864332, 7864335, 7864339, 7864345,
    7864352, 7864362, 7864374, 7864389, 7864409, 7864434, 7864467, 7864509,
    7864564, 7864634, 7864724, 7864840, 7864989, 7865181, 7865429, 7865747,
    7866157, 7866685, 7867365, 7868240, 7869367, 7870818, 7872686, 7875092,
    7878190, 7882180, 7887320, 7893941, 7902473, 7913471, 7927652, 7945944,
    7969556, 8000057, 8039495, 8090556, 8156773, 8242833, 8354991, 8501700,
    8694519, 8949536, 9289633, 9748254, 10376052, 11253313, 12515092, 14407439]

def reflectedPoleCellList : List ℕ :=
  [8071468, 8508045, 8976492, 9479652, 10020696, 10603167,
    11231041, 11908790, 12641468, 13434802, 14295313, 15230454]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 3932160
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 3932160 sameShifts :=
  same_factorization_of_literal 3932160 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 3932160 reflectedShifts :=
  reflected_factorization_of_literal 3932160 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K3932160

namespace K7864320

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (7864321 / 7864320 : ℝ) 2 (15728641 / 7864320 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-15728641 / 7864320 : ℝ) (7864321 / 7864320 : ℝ) 2

def samePoleCellList : List ℕ :=
  [15728641, 15728641, 15728641, 15728641, 15728642, 15728642, 15728643, 15728644,
    15728645, 15728646, 15728648, 15728650, 15728653, 15728658, 15728663, 15728670,
    15728679, 15728690, 15728705, 15728725, 15728751, 15728784, 15728827, 15728884,
    15728958, 15729053, 15729178, 15729340, 15729551, 15729825, 15730182, 15730647,
    15731252, 15732040, 15733064, 15734398, 15736134, 15738393, 15741333, 15745160,
    15750142, 15756628, 15765073, 15776069, 15790391, 15809048, 15833361, 15865058,
    15906402, 15960369, 16030876, 16123103, 16243929, 16402548, 16611342, 16887158,
    17253221, 17742090, 18400419, 19296945, 20536687, 22287814, 24836897, 28715029]

def reflectedPoleCellList : List ℕ :=
  [16142935, 17016090, 17952984, 18959304, 20041391, 21206334,
    22462081, 23817581, 25282936, 26869604, 28590625, 30460909]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 7864320
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 7864320 sameShifts :=
  same_factorization_of_literal 7864320 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 7864320 reflectedShifts :=
  reflected_factorization_of_literal 7864320 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K7864320

namespace K15728640

noncomputable def sameShifts : Fin 64 → ℝ × ℝ :=
  directShiftForEndpoints (15728641 / 15728640 : ℝ) 2 (31457281 / 15728640 : ℝ) 4

noncomputable def reflectedShifts : Fin 12 → ℝ × ℝ :=
  inverseShiftForEndpoints (-4) (-31457281 / 15728640 : ℝ) (15728641 / 15728640 : ℝ) 2

def samePoleCellList : List ℕ :=
  [31457281, 31457281, 31457281, 31457281, 31457282, 31457282, 31457283, 31457284,
    31457285, 31457287, 31457289, 31457292, 31457295, 31457300, 31457307, 31457315,
    31457326, 31457341, 31457360, 31457385, 31457418, 31457462, 31457519, 31457595,
    31457694, 31457825, 31457997, 31458223, 31458520, 31458911, 31459426, 31460103,
    31460994, 31462166, 31463708, 31465737, 31468406, 31471918, 31476538, 31482617,
    31490616, 31501142, 31514995, 31533229, 31557232, 31588836, 31630462, 31685306,
    31757601, 31852960, 31978848, 32145223, 32365429, 32657453, 33045717, 33563714,
    34257966, 35194185, 36467224, 38217935, 40663344, 44154479, 49297009, 57232325]

def reflectedPoleCellList : List ℕ :=
  [32285870, 34032180, 35905967, 37918608, 40082782, 42412667,
    44924162, 47635161, 50565873, 53739209, 57181251, 60921819]

@[simp] theorem samePoleCellList_length : samePoleCellList.length = 64 := by rfl
@[simp] theorem reflectedPoleCellList_length : reflectedPoleCellList.length = 12 := by rfl

def samePoleCells (i : Fin 64) : ℕ :=
  samePoleCellList.get (Fin.cast samePoleCellList_length.symm i)

def reflectedPoleCells (i : Fin 12) : ℕ :=
  reflectedPoleCellList.get (Fin.cast reflectedPoleCellList_length.symm i)

abbrev LiteralShiftCertificate : Prop :=
  FiniteAdjacentAdiShiftBindings.LiteralShiftCertificate 15728640
    sameShifts samePoleCells reflectedShifts reflectedPoleCells

theorem combinedRank_eq : 2 * 64 + 2 * 12 = 152 := by norm_num

theorem same_factorization (hcert : LiteralShiftCertificate) :
    SameFactorizationStatement 15728640 sameShifts :=
  same_factorization_of_literal 15728640 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

theorem reflected_factorization (hcert : LiteralShiftCertificate) :
    ReflectedFactorizationStatement 15728640 reflectedShifts :=
  reflected_factorization_of_literal 15728640 (by norm_num)
    sameShifts samePoleCells reflectedShifts reflectedPoleCells hcert

end K15728640

end FiniteAdjacentAdiShiftBindings
end RiemannCvs
