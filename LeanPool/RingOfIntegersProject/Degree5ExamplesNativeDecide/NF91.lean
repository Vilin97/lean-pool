/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible91

namespace RoiDegree5ExamplesNativeDecideNF91
open RoiDegree5ExamplesNativeDecideIrreducible91

-- Number field with label 5.1.1215000000.2 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 + 35*X^3 - 90*X^2 + 270*X - 396
lemma T_def : T = X^5 + 35*X^3 - 90*X^2 + 270*X - 396 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-396, 270, -90, 35, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/282*a^4 + 7/94*a^3 -
-- 44/141*a^2 + 6/47*a - 17/47]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  282
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![282, 0, 0, 0, 0],
   ![0, 282, 0, 0, 0],
   ![0, 0, 282, 0, 0],
   ![0, 0, -141, 141, 0],
   ![-102, 36, -88, 21, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![51, -18, 33, -22, 141],
       ![9, -4, 5, -4, 21]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![102, -36, 67, -42, 282],
       ![147, -117, -6, -14, -141],
       ![-15, -3, -26, 14, -123]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![51, -18, 33, -22, 141],
       ![147, -117, -6, -14, -141],
       ![-1065, 540, -642, 437, -2397],
       ![-189, 114, -78, 59, -243]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![9, -4, 5, -4, 21],
       ![-15, -3, -26, 14, -123],
       ![-189, 114, -78, 59, -243],
       ![-19, 16, 0, 2, 16]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-282]],
   ![[], [], [], [-39762], [-5922, -282]],
   ![[], [], [-39762], [39762, -19881], [20304, -2820, -141]],
   ![[], [-282], [-5922, -282], [20304, -2820, -141], [5004, -230, -42, -1]]]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide +kernel
 hin := by decide +kernel
 hsymma := by decide +kernel
 hc_le := by decide +kernel

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

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
noncomputable def B : Basis (Fin 5) ℤ O := basisOfBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

/-- Auxiliary declaration for the worked example. -/
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
/-- Auxiliary declaration for the worked example. -/
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

/-- Auxiliary declaration for the worked example. -/
noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
def Table : Fin 5 → Fin 5 → List ℤ :=
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![
     [0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0],
     [0, 0, 1, 2, 0],
     [51, -18, 33, -22, 141],
     [9, -4, 5, -4, 21]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 1, 2, 0],
     [102, -36, 67, -42, 282],
     [147, -117, -6, -14, -141],
     [-15, -3, -26, 14, -123]
   ],
   ![
     [0, 0, 0, 1, 0],
     [51, -18, 33, -22, 141],
     [147, -117, -6, -14, -141],
     [-1065, 540, -642, 437, -2397],
     [-189, 114, -78, 59, -243]
   ],
   ![
     [0, 0, 0, 0, 1],
     [9, -4, 5, -4, 21],
     [-15, -3, -26, 14, -123],
     [-189, 114, -78, 59, -243],
     [-19, 16, 0, 2, 16]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [80, -53, 19, -6, 1]
 g := [4, 1]
 h := [1, 1, 1, 1, 1]
 a :=  [1]
 b :=  [4, 1, 0, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 47] where
 n := 4
 p := ![2, 3, 5, 47]
 exp := ![10, 7, 7, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp47.out
 a := [-783918000000, -540432000000, -85131000000, -20007000000]
 b := [281685600000, 179074800000, 164106000000, 17026200000, 4001400000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t := 3
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 1]],
![[0, 0, 0, 1, 0], [1, 0, 1, 0, 1], [1, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 1, 1]],
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 0, 0, 0, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 1, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 vInd := ![0, 1]
 wInd := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 1, 0, 0],![1, 0, 1, 0, 0],![1, 0, 0, 1, 0],![1, 1, 1, 0, 1],![0, 0, 0, 1, 1]]
 w1 := ![1, 0]
 w2 := ![1, 1, 1]
 a := ![![-101, 42],![-404, -31],![-4754, -1296],![-524, -104],![-5178, -1442]]
 c := ![![276, -156, -28],![348, -102, -4],![823, 1228, 448],![242, 35, 28],![788, 1418, 503]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 0, 2, 0], [0, 2, 2, 2, 0]],
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 2, 0]],
![[0, 0, 0, 1, 0], [0, 0, 0, 2, 0], [0, 0, 0, 1, 0], [0, 0, 0, 2, 0], [0, 0, 0, 2, 0]],
![[0, 0, 0, 0, 1], [0, 2, 2, 2, 0], [0, 0, 1, 2, 0], [0, 0, 0, 2, 0], [2, 1, 0, 2, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 1, 1, 1],![0, 1, 2, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 2, 1, 0, 0]]
 v := ![![1, 0, 1, 1, 1],![0, 1, 2, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 2, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 vInd := ![0, 1]
 wInd := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 2, 2, 2],![1, 2, 0, 1, 1],![0, 2, 2, 2, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![-10979, 12471],![-6321, 7279],![-8304, 9360],![1287, -1551],![-5742, 6570]]
 c := ![![3048, -3495, -2004],
   ![1560, -2139, -1110],
   ![2512, -2520, -1566],
   ![-132, 544, 183],
   ![1452, -1905, -1016]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M47 : MaximalOrderCertificateOfUnramifiedLists 47 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
     ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [4, 29, 33, 25, 0], [9, 43, 5, 43, 21]],
     ![
       [0, 0, 1, 0, 0],
       [0, 0, 1, 2, 0],
       [8, 11, 20, 5, 0],
       [6, 24, 41, 33, 0],
       [32, 44, 21, 14, 18]
     ],
     ![
       [0, 0, 0, 1, 0],
       [4, 29, 33, 25, 0],
       [6, 24, 41, 33, 0],
       [16, 23, 16, 14, 0],
       [46, 20, 16, 12, 39]
     ],
     ![
       [0, 0, 0, 0, 1],
       [9, 43, 5, 43, 21],
       [32, 44, 21, 14, 18],
       [46, 20, 16, 12, 39],
       [28, 16, 0, 2, 16]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],
   ![36, 43, 31, 20, 0],
   ![0, 0, 1, 0, 0],
   ![43, 11, 7, 4, 0],
   ![9, 34, 43, 5, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 wInd := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 47]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 47 O Om hm M47
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 47] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF91
