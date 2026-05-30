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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible66

namespace RoiDegree5ExamplesNativeDecideNF66
open RoiDegree5ExamplesNativeDecideIrreducible66

-- Number field with label 5.1.607500000.4 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 100*X^2 + 150*X - 120
lemma T_def : T = X^5 + 15*X^3 - 100*X^2 + 150*X - 120 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-120, 150, -100, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/3*a^3 - 1/3*a^2, 1/54*a^4 - 1/27*a^3 +
-- 19/54*a^2 + 4/9*a - 1/9]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  54
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![54, 0, 0, 0, 0],
   ![0, 54, 0, 0, 0],
   ![0, 0, 54, 0, 0],
   ![0, 0, -18, 18, 0],
   ![-6, 24, 19, -2, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 3, 0],![2, -8, -6, 1, 18],![2, -2, 3, 0, -2]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 3, 0],
       ![6, -24, -17, 6, 54],
       ![38, -42, 34, -17, -18],
       ![-4, 6, -5, 9, 4]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![2, -8, -6, 1, 18],
       ![38, -42, 34, -17, -18],
       ![-36, 84, 2, 34, -84],
       ![10, -30, -12, -5, 50]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![2, -2, 3, 0, -2],
       ![-4, 6, -5, 9, 4],
       ![10, -30, -12, -5, 50],
       ![4, 0, 8, 1, -13]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-54]],
   ![[], [], [], [-972], [108, -54]],
   ![[], [], [-972], [648, -324], [-108, 54, -18]],
   ![[], [-54], [108, -54], [-108, 54, -18], [-132, -27, 4, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 3, 0], [2, -8, -6, 1, 18], [2, -2, 3, 0, -2]],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 1, 3, 0],
     [6, -24, -17, 6, 54],
     [38, -42, 34, -17, -18],
     [-4, 6, -5, 9, 4]
   ],
   ![
     [0, 0, 0, 1, 0],
     [2, -8, -6, 1, 18],
     [38, -42, 34, -17, -18],
     [-36, 84, 2, 34, -84],
     [10, -30, -12, -5, 50]
   ],
   ![
     [0, 0, 0, 0, 1],
     [2, -2, 3, 0, -2],
     [-4, 6, -5, 9, 4],
     [10, -30, -12, -5, 50],
     [4, 0, 8, 1, -13]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [24, -30, 20, -3]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [4]
 b :=  [0, 0, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![7, 13, 7]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-332424000000, 33716250000, -2916000000, 6378750000]
 b := [-159651000000, 146529000000, -14397750000, 583200000, -1275750000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0]],
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 3]
 w_ind := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 0, 1, 1],![0, 1, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 0, 1, 0],![0, 0, 1, 0, 1]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![29, -2],![2, 3],![28, -2],![28, -14],![-16, 18]]
 c := ![![20, -36, 2],![0, 0, 0],![19, -36, 2],![20, -39, 0],![2, -2, 29]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 1, 0, 1, 0], [2, 1, 0, 0, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 0, 1, 1, 0], [2, 0, 1, 0, 1]],
![[0, 0, 0, 1, 0], [2, 1, 0, 1, 0], [2, 0, 1, 1, 0], [0, 0, 2, 1, 0], [1, 0, 0, 1, 2]],
![[0, 0, 0, 0, 1], [2, 1, 0, 0, 1], [2, 0, 1, 0, 1], [1, 0, 0, 1, 2], [1, 0, 2, 1, 2]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 0, 2, 1],![0, 0, 1, 2, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 0, 2, 1],![0, 0, 1, 2, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1, 2]
 w_ind := ![0, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![8, 8, 0, 0, 4],![0, 8, 4, 0, 4],![4, 8, 4, 4, 4],![2, 4, 4, 4, 0],![2, 0, 2, 4, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![547, 114, -84],![549, -338, 324],![285, -6, 208],![-135, -72, 270],![-261, 108, 90]]
 c := ![![-57, -294],![129, -378],![141, -294],![179, -60],![105, 44]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide +kernel


instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF66
