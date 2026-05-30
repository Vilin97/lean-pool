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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible40

-- Number field with label 5.3.125000000.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 100*X - 160
lemma T_def : T = X^5 - 100*X - 160 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-160, -100, 0, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/8*a^4 - 1/4*a^2]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  8
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![8, 0, 0, 0, 0], ![0, 8, 0, 0, 0], ![0, 0, 4, 0, 0], ![0, -4, 0, 2, 0], ![0, 0, -2, 0, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 2, 0],![0, 0, 0, 0, 2],![20, 12, 0, -1, 0]],
     ![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![0, 0, 1, 0, 2],![20, 12, 0, -1, 0],![0, 10, 12, 0, -1]],
     ![
       ![0, 0, 0, 1, 0],
       ![0, 0, 0, 0, 2],
       ![20, 12, 0, -1, 0],
       ![0, 10, 12, 0, -2],
       ![-20, -6, 10, 13, 0]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![20, 12, 0, -1, 0],
       ![0, 10, 12, 0, -1],
       ![-20, -6, 10, 13, 0],
       ![0, -5, -6, 10, 13]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-8]],
   ![[], [], [], [-8], [0, -4]],
   ![[], [], [-8], [0, -4], [8, 0, -2]],
   ![[], [-8], [0, -4], [8, 0, -2], [0, 4, 0, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 0, 0, 0, 2], [20, 12, 0, -1, 0]],
   ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 1, 0, 2], [20, 12, 0, -1, 0], [0, 10, 12, 0, -1]],
   ![
     [0, 0, 0, 1, 0],
     [0, 0, 0, 0, 2],
     [20, 12, 0, -1, 0],
     [0, 10, 12, 0, -2],
     [-20, -6, 10, 13, 0]
   ],
   ![
     [0, 0, 0, 0, 1],
     [20, 12, 0, -1, 0],
     [0, 10, 12, 0, -1],
     [-20, -6, 10, 13, 0],
     [0, -5, -6, 10, 13]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [32, 20]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [3]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 2
 p := ![2, 5]
 exp := ![18, 9]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp5.out
 a := [12800000000, -6400000000, 3200000000, -1600000000]
 b := [-25600000000, -2560000000, 1280000000, -640000000, 320000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 1, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 0, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 1, 0, 0],![0, 0, 0, 1, 1],![1, 1, 1, 0, 0],![0, 0, 0, 1, 0],![0, 1, 0, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![3, 2],![12, 1],![4, 2],![0, 2],![2, 0]]
 c := ![![0, 0, 2],![10, 2, 0],![1, 0, 2],![0, 1, 0],![0, 0, 1]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide


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

