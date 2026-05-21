/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible54

-- Number field with label 5.1.337500000.4 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 10*X^2 + 210*X + 432 
lemma T_def : T = X^5 - 15*X^3 - 10*X^2 + 210*X + 432 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [432, 210, -10, -15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/7*a^3 - 2/7*a^2 + 1/7*a - 1/7, 1/42*a^4 - 1/14*a^2 + 4/21*a + 2/7] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  42
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![42, 0, 0, 0, 0], ![0, 42, 0, 0, 0], ![0, 0, 42, 0, 0], ![-6, 6, -12, 6, 0], ![12, 8, -3, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![1, -1, 2, 7, 0],![-2, -1, 0, -2, 6],![-10, -5, 1, 2, 0]], 
![![0, 0, 1, 0, 0],![1, -1, 2, 7, 0],![-12, -8, 3, 0, 42],![-56, -30, 5, 16, -12],![-3, -13, -3, 3, 12]], 
![![0, 0, 0, 1, 0],![-2, -1, 0, -2, 6],![-56, -30, 5, 16, -12],![29, 6, -6, -8, 18],![-19, -6, 0, -1, -1]], 
![![0, 0, 0, 0, 1],![-10, -5, 1, 2, 0],![-3, -13, -3, 3, 12],![-19, -6, 0, -1, -1],![-6, -5, -1, 0, -1]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-42]],![[], [], [], [-252], [0, -42]],![[], [], [-252], [144, -36], [-78, 12, -6]],![[], [-42], [0, -42], [-78, 12, -6], [-26, -9, 0, -1]]]
 h := Adj
 honed := by native_decide
 hd := by norm_num
 hcc := by native_decide 
 hin := by native_decide
 hsymma := by native_decide
 hc_le := by native_decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

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
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, -1, 2, 7, 0], [-2, -1, 0, -2, 6], [-10, -5, 1, 2, 0]], 
 ![[0, 0, 1, 0, 0], [1, -1, 2, 7, 0], [-12, -8, 3, 0, 42], [-56, -30, 5, 16, -12], [-3, -13, -3, 3, 12]], 
 ![[0, 0, 0, 1, 0], [-2, -1, 0, -2, 6], [-56, -30, 5, 16, -12], [29, 6, -6, -8, 18], [-19, -6, 0, -1, -1]], 
 ![[0, 0, 0, 0, 1], [-10, -5, 1, 2, 0], [-3, -13, -3, 3, 12], [-19, -6, 0, -1, -1], [-6, -5, -1, 0, -1]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-86, -41, 4, 5, 1]
 g :=  [2, 1]
 h :=  [1, 2, 4, 3, 1]
 a :=  [2]
 b :=  [4, 4, 4, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![7, 5, 8, 4]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [-23152500000, 9922500000, 19845000000, -6615000000]
 b := [186543000000, 20506500000, -9922500000, -3969000000, 1323000000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 1, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 1, 0, 0],![0, 1, 0, 0, 1],![1, 0, 1, 0, 1],![0, 1, 1, 0, 0],![1, 1, 1, 1, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![27, 6],![20, 5],![36, 4],![38, 12],![48, 18]]
 c := ![![-20, 34, -54],![-42, 6, -32],![-47, 40, -78],![-36, 33, -62],![-90, 36, -89]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 2, 2, 1, 0], [1, 2, 0, 1, 0], [2, 1, 1, 2, 0]], 
![[0, 0, 1, 0, 0], [1, 2, 2, 1, 0], [0, 1, 0, 0, 0], [1, 0, 2, 1, 0], [0, 2, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [1, 2, 0, 1, 0], [1, 0, 2, 1, 0], [2, 0, 0, 1, 0], [2, 0, 0, 2, 2]], 
![[0, 0, 0, 0, 1], [2, 1, 1, 2, 0], [0, 2, 0, 0, 0], [2, 0, 0, 2, 2], [0, 1, 2, 0, 2]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 2, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 2],![0, 1, 0, 0, 1]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 2, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 2],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 2],![0, 0, 1, 0, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![2, 2, 2, 2, 4],![1, 0, 1, 2, 2],![2, 2, 2, 0, 0],![0, 4, 0, 2, 2],![0, 0, 2, 0, 2]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![230, 21],![114, 7],![144, 27],![132, 21],![132, 9]]
 c := ![![-693, 333, -546],![-408, 189, -315],![-275, 153, -228],![-393, 155, -276],![-351, 195, -302]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 6, 2, 0, 0], [5, 6, 0, 5, 6], [4, 2, 1, 2, 0]], 
![[0, 0, 1, 0, 0], [1, 6, 2, 0, 0], [2, 6, 3, 0, 0], [0, 5, 5, 2, 2], [4, 1, 4, 3, 5]], 
![[0, 0, 0, 1, 0], [5, 6, 0, 5, 6], [0, 5, 5, 2, 2], [1, 6, 1, 6, 4], [2, 1, 0, 6, 6]], 
![[0, 0, 0, 0, 1], [4, 2, 1, 2, 0], [4, 1, 4, 3, 5], [2, 1, 0, 6, 6], [1, 2, 6, 0, 6]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![2, 3, 2, 0, 0],![3, 3, 4, 0, 0],![1, 5, 6, 6, 2],![6, 5, 0, 6, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 7] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
