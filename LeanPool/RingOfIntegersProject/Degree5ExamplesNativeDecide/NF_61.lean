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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible61

-- Number field with label 5.1.405000000.7 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 + 20*X^3 + 180*X - 192
lemma T_def : T = X^5 + 20*X^3 + 180*X - 192 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-192, 180, 0, 20, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/8*a^3 - 1/4*a, 1/16*a^4 - 1/8*a^2 -
-- 1/2*a]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  16
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![16, 0, 0, 0, 0],
   ![0, 16, 0, 0, 0],
   ![0, 0, 8, 0, 0],
   ![0, -4, 0, 2, 0],
   ![0, -8, -2, 0, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 4, 0],![0, 1, 0, 0, 2],![12, -14, -1, -11, 0]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 4, 0],
       ![0, 2, 1, 0, 4],
       ![12, -14, 0, -11, 0],
       ![0, 0, -14, -2, -11]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![0, 1, 0, 0, 2],
       ![12, -14, 0, -11, 0],
       ![0, 0, -7, 0, -6],
       ![-36, 38, 3, 19, -1]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![12, -14, -1, -11, 0],
       ![0, 0, -14, -2, -11],
       ![-36, 38, 3, 19, -1],
       ![-12, 7, 39, 17, 19]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-16]],
   ![[], [], [], [-16], [0, -8]],
   ![[], [], [-16], [0, -4], [48, 0, -2]],
   ![[], [-16], [0, -8], [48, 0, -2], [16, 24, 0, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 4, 0], [0, 1, 0, 0, 2], [12, -14, -1, -11, 0]],
   ![[0, 0, 1, 0, 0], [0, 1, 0, 4, 0], [0, 2, 1, 0, 4], [12, -14, 0, -11, 0], [0, 0, -14, -2, -11]],
   ![
     [0, 0, 0, 1, 0],
     [0, 1, 0, 0, 2],
     [12, -14, 0, -11, 0],
     [0, 0, -7, 0, -6],
     [-36, 38, 3, 19, -1]
   ],
   ![
     [0, 0, 0, 0, 1],
     [12, -14, -1, -11, 0],
     [0, 0, -14, -2, -11],
     [-36, 38, 3, 19, -1],
     [-12, 7, 39, 17, 19]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := []
 b' := [2]
 k := [1, 0, 1, 0, 1]
 f := [64, -60, 0, -6]
 g := [0, 2, 0, 1]
 h := [0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [39, -34, 3, -2, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a :=  [2]
 b :=  [1, 4, 0, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![22, 4, 7]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-55296000000, -41472000000, 0, -2304000000]
 b := [88473600000, 11059200000, 11980800000, 0, 460800000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 1, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 1, 1, 1], [0, 1, 1, 1, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 1, 0, 0],![0, 1, 1, 1, 1],![1, 1, 1, 0, 0],![0, 1, 1, 1, 0],![0, 1, 0, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![3, 4],![-10, -5],![4, 4],![4, 6],![2, 0]]
 c := ![![0, 0, 0],![6, 2, 2],![1, 0, 0],![0, 1, -2],![0, 0, 1]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel


instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

