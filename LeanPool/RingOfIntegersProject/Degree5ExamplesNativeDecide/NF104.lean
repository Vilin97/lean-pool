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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible104

namespace RoiDegree5ExamplesNativeDecideNF104
open RoiDegree5ExamplesNativeDecideIrreducible104

-- Number field with label 5.3.2025000000.3 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 60*X^3 - 20*X^2 + 135*X + 816
lemma T_def : T = X^5 - 60*X^3 - 20*X^2 + 135*X + 816 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [816, 135, -20, -60, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/2172*a^4 -
-- 307/2172*a^3 + 793/2172*a^2 - 69/724*a + 58/181]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  2172
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2172, 0, 0, 0, 0],
   ![0, 2172, 0, 0, 0],
   ![0, 0, 2172, 0, 0],
   ![0, -1086, 0, 1086, 0],
   ![696, -207, 793, -307, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![-348, 257, -397, 307, 1086],
       ![98, -72, 112, -86, -307]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![-696, 514, -793, 614, 2172],
       ![-408, -38, 10, 59, 0],
       ![-158, 212, -314, 224, 853]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-348, 257, -397, 307, 1086],
       ![-408, -38, 10, 59, 0],
       ![-10092, 7254, -11532, 8913, 31494],
       ![2772, -2124, 3354, -2566, -9150]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![98, -72, 112, -86, -307],
       ![-158, 212, -314, 224, 853],
       ![2772, -2124, 3354, -2566, -9150],
       ![-868, 700, -1097, 833, 2992]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-2172]],
   ![[], [], [], [-2358792], [666804, -2172]],
   ![[], [], [-2358792], [0, -1179396], [-925272, 333402, -1086]],
   ![[], [-2172], [666804, -2172], [-925272, 333402, -1086], [524136, -95895, 614, -1]]]
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
     [0, 1, 0, 2, 0],
     [-348, 257, -397, 307, 1086],
     [98, -72, 112, -86, -307]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 1, 0, 2, 0],
     [-696, 514, -793, 614, 2172],
     [-408, -38, 10, 59, 0],
     [-158, 212, -314, 224, 853]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-348, 257, -397, 307, 1086],
     [-408, -38, 10, 59, 0],
     [-10092, 7254, -11532, 8913, 31494],
     [2772, -2124, 3354, -2566, -9150]
   ],
   ![
     [0, 0, 0, 0, 1],
     [98, -72, 112, -86, -307],
     [-158, 212, -314, 224, 853],
     [2772, -2124, 3354, -2566, -9150],
     [-868, 700, -1097, 833, 2992]
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
instance hp181 : Fact (Nat.Prime 181) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-163, -26, 5, 13, 1]
 g := [1, 1]
 h := [1, 4, 1, 4, 1]
 a :=  [1]
 b :=  [4, 2, 3, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 181] where
 n := 4
 p := ![2, 3, 5, 181]
 exp := ![12, 6, 8, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp181.out
 a := [48698415000000, -5927715000000, -1417365000000, 135945000000]
 b := [-11299824000000, -16216767000000, 1838079000000, 283473000000, -27189000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 1, 1, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 vInd := ![1, 2]
 wInd := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 1, 1, 1],![1, 1, 1, 1, 0],![1, 1, 1, 1, 1],![0, 1, 0, 1, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 0]
 w2 := ![0, 1, 1]
 a := ![![87481, -23416],![126188, -33793],![91508, -24492],![90370, -24208],![5164, -1360]]
 c := ![![-11094, -36428, -22842],
   ![-15438, -52488, -33028],
   ![-11567, -38092, -23900],
   ![-10876, -37575, -23678],
   ![-1164, -2182, -1281]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 0], [2, 0, 1, 1, 2]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 2, 0], [0, 1, 1, 2, 0], [1, 2, 1, 2, 1]],
![[0, 0, 0, 1, 0], [0, 2, 2, 1, 0], [0, 1, 1, 2, 0], [0, 0, 0, 0, 0], [0, 0, 0, 2, 0]],
![[0, 0, 0, 0, 1], [2, 0, 1, 1, 2], [1, 2, 1, 2, 1], [0, 0, 0, 2, 0], [2, 1, 1, 2, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 vInd := ![0, 1, 3]
 wInd := ![0, 1]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![2, 0, 2, 2, 0],![0, 2, 1, 1, 2],![2, 2, 1, 2, 1],![0, 0, 0, 1, 0],![0, 2, 2, 1, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![59428, -21702, 17082],
   ![18207, -6632, 5280],
   ![51429, -18777, 14770],
   ![26688, -9756, 7635],
   ![34296, -12510, 9891]]
 c := ![![-26730, 11778],![-8271, 3606],![-23097, 10197],![-11936, 5292],![-15480, 6796]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M181 : MaximalOrderCertificateOfUnramifiedLists 181 O Om hm where
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
     ![
       [0, 1, 0, 0, 0],
       [0, 0, 1, 0, 0],
       [0, 1, 0, 2, 0],
       [14, 76, 146, 126, 0],
       [98, 109, 112, 95, 55]
     ],
     ![
       [0, 0, 1, 0, 0],
       [0, 1, 0, 2, 0],
       [28, 152, 112, 71, 0],
       [135, 143, 10, 59, 0],
       [23, 31, 48, 43, 129]
     ],
     ![
       [0, 0, 0, 1, 0],
       [14, 76, 146, 126, 0],
       [135, 143, 10, 59, 0],
       [44, 14, 52, 44, 0],
       [57, 48, 96, 149, 81]
     ],
     ![
       [0, 0, 0, 0, 1],
       [98, 109, 112, 95, 55],
       [23, 31, 48, 43, 129],
       [57, 48, 96, 149, 81],
       [37, 157, 170, 109, 96]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],
   ![87, 118, 104, 22, 0],
   ![54, 160, 103, 126, 0],
   ![138, 67, 140, 142, 0],
   ![42, 104, 134, 63, 180]]
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
  by_cases hc : p ∈ [2, 3, 181]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 181 O Om hm M181
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 181] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF104
