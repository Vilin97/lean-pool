/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.Degree6ExamplesNativeDecide.Irreducible0

namespace RoiDegree6ExamplesNativeDecideNF0
open RoiDegree6ExamplesNativeDecideIrreducible0

-- Number field with label 6.2.7381125000000.77 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^6 - 15*X^4 - 140*X^3 - 270*X^2 + 96*X + 3220
lemma T_def : T = X^6 - 15*X^4 - 140*X^3 - 270*X^2 + 96*X + 3220 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [3220, 96, -270, -140, -15, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/2*a^4 - 1/2*a^2,
-- 1/15266*a^5 + 1265/15266*a^4 - 80/449*a^3 - 3045/7633*a^2 + 2605/7633*a - 2083/7633]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 6 ℤ  ℚ K T l where
 d :=  15266
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![15266, 0, 0, 0, 0, 0],
   ![0, 15266, 0, 0, 0, 0],
   ![0, 0, 15266, 0, 0, 0],
   ![0, 0, -7633, 7633, 0, 0],
   ![0, 0, -7633, 0, 7633, 0],
   ![-4166, 5210, -6090, -2720, 1265, 1]]
 a :=
   ![
     ![
       ![1, 0, 0, 0, 0, 0],
       ![0, 1, 0, 0, 0, 0],
       ![0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 1, 0, 0],
       ![0, 0, 0, 0, 1, 0],
       ![0, 0, 0, 0, 0, 1]
     ],
     ![
       ![0, 1, 0, 0, 0, 0],
       ![0, 0, 1, 0, 0, 0],
       ![0, 0, 1, 2, 0, 0],
       ![0, 0, 0, -1, 1, 0],
       ![2083, -2605, 3772, 2719, -1265, 7633],
       ![345, -432, 625, 450, -210, 1265]
     ],
     ![
       ![0, 0, 1, 0, 0, 0],
       ![0, 0, 1, 2, 0, 0],
       ![0, 0, 1, 0, 2, 0],
       ![2083, -2605, 3772, 2720, -1266, 7633],
       ![-1610, -48, 212, 140, 14, 0],
       ![-1005, 915, -1302, -940, 450, -2705]
     ],
     ![
       ![0, 0, 0, 1, 0, 0],
       ![0, 0, 0, -1, 1, 0],
       ![2083, -2605, 3772, 2720, -1266, 7633],
       ![-2888, 2581, -3666, -2650, 1273, -7633],
       ![15386, -19016, 26380, 19105, -8792, 53431],
       ![2565, -2805, 3845, 2788, -1295, 7865]
     ],
     ![
       ![0, 0, 0, 0, 1, 0],
       ![2083, -2605, 3772, 2719, -1265, 7633],
       ![-1610, -48, 212, 140, 14, 0],
       ![15386, -19016, 26380, 19105, -8792, 53431],
       ![135345, -182662, 264695, 191262, -88317, 534310],
       ![18505, -24445, 35770, 25835, -11982, 72355]
     ],
     ![
       ![0, 0, 0, 0, 0, 1],
       ![345, -432, 625, 450, -210, 1265],
       ![-1005, 915, -1302, -940, 450, -2705],
       ![2565, -2805, 3845, 2788, -1295, 7865],
       ![18505, -24445, 35770, 25835, -11982, 72355],
       ![2768, -3655, 5420, 3910, -1820, 10967]
     ]
   ]
 s :=
   ![
     ![[], [], [], [], [], []],
     ![[], [], [], [], [], [-15266]],
     ![[], [], [], [], [-116525378], [-19311490, -15266]],
     ![[], [], [], [-58262689], [58262689, -58262689], [30303010, -9648112, -7633]],
     ![
       [],
       [],
       [-116525378],
       [58262689, -58262689],
       [-757414957, 0, -58262689],
       [-89764080, 20654898, -9655745, -7633]
     ],
     ![
       [],
       [-15266],
       [-19311490, -15266],
       [30303010, -9648112, -7633],
       [-89764080, 20654898, -9655745, -7633],
       [-16277590, 6855690, -1594800, -2530, -1]
     ]
   ]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide +kernel
 hin := by decide +kernel
 hsymma := by decide +kernel
 hc_le := by decide +kernel

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| Irreducible (map (algebraMap ℤ ℚ) T) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible

/-- Auxiliary declaration for the worked example. -/
instance : IsDomain K := by
  have hmap : Irreducible (map (algebraMap ℤ ℚ) T) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible
  exact AdjoinRoot.isDomain_of_prime (Irreducible.prime hmap)

/-- Auxiliary declaration for the worked example. -/
instance : NoZeroSMulDivisors ℤ K := by
  haveI : IsAddTorsionFree K := IsDomain.instIsAddTorsionFreeOfCharZero K
  infer_instance

/-- Auxiliary declaration for the worked example. -/
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

/-- Auxiliary declaration for the worked example. -/
noncomputable def O := subalgebraOfBuilderLists T l BQ

lemma hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

/-- Auxiliary declaration for the worked example. -/
noncomputable def B : Basis (Fin 6) ℤ O := basisOfBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

/-- Auxiliary declaration for the worked example. -/
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
/-- Auxiliary declaration for the worked example. -/
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

/-- Auxiliary declaration for the worked example. -/
noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
def Table : Fin 6 → Fin 6 → List ℤ :=
 ![
   ![
     [1, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 0],
     [0, 0, 0, 1, 0, 0],
     [0, 0, 0, 0, 1, 0],
     [0, 0, 0, 0, 0, 1]
   ],
   ![
     [0, 1, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 0],
     [0, 0, 1, 2, 0, 0],
     [0, 0, 0, -1, 1, 0],
     [2083, -2605, 3772, 2719, -1265, 7633],
     [345, -432, 625, 450, -210, 1265]
   ],
   ![
     [0, 0, 1, 0, 0, 0],
     [0, 0, 1, 2, 0, 0],
     [0, 0, 1, 0, 2, 0],
     [2083, -2605, 3772, 2720, -1266, 7633],
     [-1610, -48, 212, 140, 14, 0],
     [-1005, 915, -1302, -940, 450, -2705]
   ],
   ![
     [0, 0, 0, 1, 0, 0],
     [0, 0, 0, -1, 1, 0],
     [2083, -2605, 3772, 2720, -1266, 7633],
     [-2888, 2581, -3666, -2650, 1273, -7633],
     [15386, -19016, 26380, 19105, -8792, 53431],
     [2565, -2805, 3845, 2788, -1295, 7865]
   ],
   ![
     [0, 0, 0, 0, 1, 0],
     [2083, -2605, 3772, 2719, -1265, 7633],
     [-1610, -48, 212, 140, 14, 0],
     [15386, -19016, 26380, 19105, -8792, 53431],
     [135345, -182662, 264695, 191262, -88317, 534310],
     [18505, -24445, 35770, 25835, -11982, 72355]
   ],
   ![
     [0, 0, 0, 0, 0, 1],
     [345, -432, 625, 450, -210, 1265],
     [-1005, 915, -1302, -940, 450, -2705],
     [2565, -2805, 3845, 2788, -1295, 7865],
     [18505, -24445, 35770, 25835, -11982, 72355],
     [2768, -3655, 5420, 3910, -1820, 10967]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp449 : Fact (Nat.Prime 449) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 6
 a' := []
 b' := [1]
 k := [1]
 f := [-1072, -30, 92, 48, 6, 1]
 g := [2, 1]
 h := [2, 2, 2, 1, 1, 1]
 a :=  [2]
 b :=  [0, 0, 1, 1, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := [1]
 b' := [1, 2]
 k := [0, 0, 0, 0, 1]
 f := [-644, -19, 55, 29, 4, 1]
 g := [0, 1, 1]
 h := [1, 4, 1, 4, 1]
 a :=  [1, 2]
 b :=  [2, 1, 0, 3, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [449, 2, 17] where
 n := 5
 p := ![2, 3, 5, 17, 449]
 exp := ![12, 10, 9, 2, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp17.out
  · exact hp449.out
 a :=
   [
     8544032856720000000,
     -173643426000000000,
     398958663600000000,
     23619600000000000,
     -32784792120000000
   ]
 b :=
   [
     115024827600000000,
     -2072728287720000000,
     -333865670400000000,
     -93813770700000000,
     -3936600000000000,
     5464132020000000
   ]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M449 : MaximalOrderCertificateOfUnramifiedLists 449 O Om hm where
 n := 6
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![
       [1, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 0, 1]
     ],
     ![
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 2, 0, 0],
       [0, 0, 0, 448, 1, 0],
       [287, 89, 180, 25, 82, 0],
       [345, 17, 176, 1, 239, 367]
     ],
     ![
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 2, 0, 0],
       [0, 0, 1, 0, 2, 0],
       [287, 89, 180, 26, 81, 0],
       [186, 401, 212, 140, 14, 0],
       [342, 17, 45, 407, 1, 438]
     ],
     ![
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 448, 1, 0],
       [287, 89, 180, 26, 81, 0],
       [255, 336, 375, 44, 375, 0],
       [120, 291, 338, 247, 188, 0],
       [320, 338, 253, 94, 52, 232]
     ],
     ![
       [0, 0, 0, 0, 1, 0],
       [287, 89, 180, 25, 82, 0],
       [186, 401, 212, 140, 14, 0],
       [120, 291, 338, 247, 188, 0],
       [196, 81, 234, 437, 136, 0],
       [96, 250, 299, 242, 141, 66]
     ],
     ![
       [0, 0, 0, 0, 0, 1],
       [345, 17, 176, 1, 239, 367],
       [342, 17, 45, 407, 1, 438],
       [320, 338, 253, 94, 52, 232],
       [96, 250, 299, 242, 141, 66],
       [74, 386, 32, 318, 425, 191]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0, 0],
   ![207, 446, 312, 379, 392, 0],
   ![242, 23, 274, 386, 149, 0],
   ![178, 430, 402, 94, 190, 0],
   ![180, 166, 387, 341, 84, 0],
   ![76, 156, 228, 310, 348, 448]]
 wFrob := ![![1, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0],
   ![0, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4, 5]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel
/-- Auxiliary declaration for the worked example. -/
noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 4
 t := 3
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![
       [1, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 0, 1]
     ],
     ![
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 0, 1, 1, 0],
       [1, 1, 0, 1, 1, 1],
       [1, 0, 1, 0, 0, 1]
     ],
     ![
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [1, 1, 0, 0, 0, 1],
       [0, 0, 0, 0, 0, 0],
       [1, 1, 0, 0, 0, 1]
     ],
     ![
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 1, 1, 0],
       [1, 1, 0, 0, 0, 1],
       [0, 1, 0, 0, 1, 1],
       [0, 0, 0, 1, 0, 1],
       [1, 1, 1, 0, 1, 1]
     ],
     ![
       [0, 0, 0, 0, 1, 0],
       [1, 1, 0, 1, 1, 1],
       [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 1],
       [1, 0, 1, 0, 1, 0],
       [1, 1, 0, 1, 0, 1]
     ],
     ![
       [0, 0, 0, 0, 0, 1],
       [1, 0, 1, 0, 0, 1],
       [1, 1, 0, 0, 0, 1],
       [1, 1, 1, 0, 1, 1],
       [1, 1, 0, 1, 0, 1],
       [0, 1, 0, 0, 0, 1]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 1, 1, 1, 1],![0, 1, 1, 0, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0, 0],![1, 1, 0, 1, 1, 0],![0, 1, 0, 0, 0, 0],![1, 1, 0, 0, 1, 0]]
 v := ![![1, 0, 1, 1, 1, 1],![0, 1, 1, 0, 0, 0]]
 w := ![![1, 0, 0, 0, 0, 0],![1, 1, 0, 1, 1, 0],![0, 1, 0, 0, 0, 0],![1, 1, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0, 0],![0, 1, 0, 0, 0, 1],![0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2, 4]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 1, 1, 1, 1],
   ![0, 0, 1, 1, 0, 0],
   ![0, 1, 0, 0, 0, 0],
   ![1, 0, 1, 0, 0, 1],
   ![0, 0, 1, 0, 0, 0],
   ![1, 0, 1, 1, 1, 1]]
 w1 := ![1, 0]
 w2 := ![2, 2, 0, 1]
 a := ![![5073961, -2560092],
   ![386810, -193803],
   ![54696, -27660],
   ![597134, -300590],
   ![35460, -16400],
   ![5073962, -2560092]]
 c := ![![1067100, -1628604, 3364950, -1327486],
   ![79782, -123580, 253032, -101582],
   ![11993, -17608, 36380, -14270],
   ![121548, -191511, 396782, -156432],
   ![1960, -10904, 22597, -9716],
   ![1067102, -1628602, 3364950, -1327485]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M17 : MaximalOrderCertificateOfUnramifiedLists 17 O Om hm where
 n := 6
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![
       [1, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 0, 1]
     ],
     ![
       [0, 1, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 2, 0, 0],
       [0, 0, 0, 16, 1, 0],
       [9, 13, 15, 16, 10, 0],
       [5, 10, 13, 8, 11, 7]
     ],
     ![
       [0, 0, 1, 0, 0, 0],
       [0, 0, 1, 2, 0, 0],
       [0, 0, 1, 0, 2, 0],
       [9, 13, 15, 0, 9, 0],
       [5, 3, 8, 4, 14, 0],
       [15, 14, 7, 12, 8, 15]
     ],
     ![
       [0, 0, 0, 1, 0, 0],
       [0, 0, 0, 16, 1, 0],
       [9, 13, 15, 0, 9, 0],
       [2, 14, 6, 2, 15, 0],
       [1, 7, 13, 14, 14, 0],
       [15, 0, 3, 0, 14, 11]
     ],
     ![
       [0, 0, 0, 0, 1, 0],
       [9, 13, 15, 16, 10, 0],
       [5, 3, 8, 4, 14, 0],
       [1, 7, 13, 14, 14, 0],
       [8, 3, 5, 12, 15, 0],
       [9, 1, 2, 12, 3, 3]
     ],
     ![
       [0, 0, 0, 0, 0, 1],
       [5, 10, 13, 8, 11, 7],
       [15, 14, 7, 12, 8, 15],
       [15, 0, 3, 0, 14, 11],
       [9, 1, 2, 12, 3, 3],
       [14, 0, 14, 0, 16, 2]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0, 0],
   ![11, 6, 5, 1, 7, 0],
   ![8, 4, 16, 7, 12, 0],
   ![10, 6, 6, 4, 4, 0],
   ![9, 8, 7, 12, 8, 0],
   ![14, 12, 13, 7, 7, 1]]
 wFrob := ![![1, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0],
   ![0, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4, 5]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [449, 2, 17]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 449 O Om hm M449
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 17 O Om hm M17
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [449, 2, 17] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree6ExamplesNativeDecideNF0
