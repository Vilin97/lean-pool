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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible115

namespace RoiDegree5ExamplesNF115
open RoiDegree5ExamplesIrreducible115

-- Number field with label 5.1.5695312500.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 350*X^2 + 1275*X - 390
lemma T_def : T = X^5 - 350*X^2 + 1275*X - 390 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-390, 1275, -350, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/1068*a^4 - 43/1068*a^3
-- - 287/1068*a^2 + 81/356*a + 73/178]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1068
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1068, 0, 0, 0, 0],
   ![0, 1068, 0, 0, 0],
   ![0, 0, 1068, 0, 0],
   ![0, -534, 0, 534, 0],
   ![438, 243, -287, -43, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![-219, -100, 143, 43, 534],
       ![18, 7, -11, -4, -43]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![-438, -200, 287, 86, 1068],
       ![195, -638, 175, -1, 0],
       ![102, 106, -92, -22, -287]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-219, -100, 143, 43, 534],
       ![195, -638, 175, -1, 0],
       ![219, 285, -462, 132, -534],
       ![-183, 97, 64, 11, 318]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![18, 7, -11, -4, -43],
       ![102, 106, -92, -22, -287],
       ![-183, 97, 64, 11, 318],
       ![-3, -33, 14, 3, 29]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-1068]],
   ![[], [], [], [-570312], [45924, -1068]],
   ![[], [], [-570312], [0, -285156], [153792, 22962, -534]],
   ![[], [-1068], [45924, -1068], [153792, 22962, -534], [-25518, -1275, 86, -1]]]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide +kernel

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

instance : Fact <| Irreducible (map (algebraMap ℤ ℚ) T) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible

instance : IsDomain K := by
  have hmap : Irreducible (map (algebraMap ℤ ℚ) T) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible
  exact AdjoinRoot.isDomain_of_prime (Irreducible.prime hmap)

instance : NoZeroSMulDivisors ℤ K := by
  haveI : IsAddTorsionFree K := IsDomain.instIsAddTorsionFreeOfCharZero K
  infer_instance

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B : Basis (Fin 5) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
def Table : Fin 5 → Fin 5 → List ℤ :=
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![
     [0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0],
     [0, 1, 0, 2, 0],
     [-219, -100, 143, 43, 534],
     [18, 7, -11, -4, -43]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 1, 0, 2, 0],
     [-438, -200, 287, 86, 1068],
     [195, -638, 175, -1, 0],
     [102, 106, -92, -22, -287]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-219, -100, 143, 43, 534],
     [195, -638, 175, -1, 0],
     [219, 285, -462, 132, -534],
     [-183, 97, 64, 11, 318]
   ],
   ![
     [0, 0, 0, 0, 1],
     [18, 7, -11, -4, -43],
     [102, 106, -92, -22, -287],
     [-183, 97, 64, 11, 318],
     [-3, -33, 14, 3, 29]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp89 : Fact (Nat.Prime 89) := fact_iff.2 (by norm_num)
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [78, -255, 70]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [89, 2, 3] where
 n := 4
 p := ![2, 3, 5, 89]
 exp := ![8, 8, 9, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp89.out
 a := [-52387762500000, 27835650000000, 6211687500000, 1257525000000]
 b := [4355775000000, 63293602500000, -5567130000000, -1242337500000, -251505000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M89 : MaximalOrderCertificateOfUnramifiedLists 89 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
     ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [48, 78, 54, 43, 0], [18, 7, 78, 85, 46]],
     ![
       [0, 0, 1, 0, 0],
       [0, 1, 0, 2, 0],
       [7, 67, 20, 86, 0],
       [17, 74, 86, 88, 0],
       [13, 17, 86, 67, 69]
     ],
     ![
       [0, 0, 0, 1, 0],
       [48, 78, 54, 43, 0],
       [17, 74, 86, 88, 0],
       [41, 18, 72, 43, 0],
       [84, 8, 64, 11, 51]
     ],
     ![
       [0, 0, 0, 0, 1],
       [18, 7, 78, 85, 46],
       [13, 17, 86, 67, 69],
       [84, 8, 64, 11, 51],
       [86, 56, 14, 3, 29]
     ]
   ]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],
   ![26, 32, 59, 54, 0],
   ![66, 29, 31, 7, 0],
   ![45, 70, 49, 26, 0],
   ![38, 42, 4, 31, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel
noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 1, 1, 0], [0, 1, 1, 0, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 0, 1]]
 v := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 1, 0, 0],![0, 1, 1, 1, 0],![0, 1, 0, 1, 1],![1, 1, 1, 1, 1],![1, 1, 0, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 1, 0]
 a := ![![89, 376],![354, 255],![246, -152],![336, 224],![46, 100]]
 c := ![![-700, -1140, 534],
   ![-1488, -1938, 1068],
   ![-775, -648, 508],
   ![-1474, -1787, 1042],
   ![-398, -364, 267]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 0], [0, 1, 1, 2, 2]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 2, 0], [0, 1, 1, 2, 0], [0, 1, 1, 2, 1]],
![[0, 0, 0, 1, 0], [0, 2, 2, 1, 0], [0, 1, 1, 2, 0], [0, 0, 0, 0, 0], [0, 1, 1, 2, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 2, 2], [0, 1, 1, 2, 1], [0, 1, 1, 2, 0], [0, 0, 2, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 1, 0, 0],![0, 0, 2, 0, 2],![1, 2, 0, 0, 1],![0, 1, 1, 0, 0],![0, 1, 1, 2, 0]]
 w1 := ![0, 1, 1]
 w2 := ![1, 0]
 a := ![![-68, 282, 42],![48, 562, 72],![504, 243, 70],![138, 402, 78],![978, 84, 390]]
 c := ![![-12, -186],![-84, -342],![-150, -177],![-74, -282],![-42, -668]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide


instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [89, 2, 3]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 89 O Om hm M89
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [89, 2, 3] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF115
