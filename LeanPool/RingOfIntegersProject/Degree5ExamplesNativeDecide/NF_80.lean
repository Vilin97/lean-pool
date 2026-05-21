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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible80

-- Number field with label 5.1.729000000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 170*X^2 + 60*X - 168 
lemma T_def : T = X^5 + 15*X^3 - 170*X^2 + 60*X - 168 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-168, 60, -170, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/888*a^4 + 67/444*a^3 + 211/888*a^2 - 13/37*a - 1/74] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  888
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![888, 0, 0, 0, 0], ![0, 888, 0, 0, 0], ![0, 0, 888, 0, 0], ![0, -444, 0, 444, 0], ![-12, -312, 211, 134, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![6, 89, -106, -134, 444],![2, 27, -32, -40, 134]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![12, 178, -211, -268, 888],![84, -38, 85, -16, 0],![28, 28, -21, -64, 196]], 
![![0, 0, 0, 1, 0],![6, 89, -106, -134, 444],![84, -38, 85, -16, 0],![-51, -672, 882, 1224, -3774],![3, -212, 286, 367, -1143]], 
![![0, 0, 0, 0, 1],![2, 27, -32, -40, 134],![28, 28, -21, -64, 196],![3, -212, 286, 367, -1143],![7, -58, 82, 97, -303]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-888]],![[], [], [], [-394272], [-118992, -888]],![[], [], [-394272], [0, -197136], [-86580, -59496, -444]],![[], [-888], [-118992, -888], [-86580, -59496, -444], [-52074, -18363, -268, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [6, 89, -106, -134, 444], [2, 27, -32, -40, 134]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [12, 178, -211, -268, 888], [84, -38, 85, -16, 0], [28, 28, -21, -64, 196]], 
 ![[0, 0, 0, 1, 0], [6, 89, -106, -134, 444], [84, -38, 85, -16, 0], [-51, -672, 882, 1224, -3774], [3, -212, 286, 367, -1143]], 
 ![[0, 0, 0, 0, 1], [2, 27, -32, -40, 134], [28, 28, -21, -64, 196], [3, -212, 286, 367, -1143], [7, -58, 82, 97, -303]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp37: Fact $ Nat.Prime 37 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [34, -11, 36, -1, 1]
 g :=  [2, 1]
 h :=  [1, 2, 4, 3, 1]
 a :=  [4]
 b :=  [0, 2, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 37] where
 n := 4
 p := ![2, 3, 5, 37]
 exp := ![14, 8, 6, 2]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp37.out
 a := [-14410288800000, 1494255600000, -23522400000, 206161200000]
 b := [-2025570240000, 7115973120000, -546244560000, 4704480000, -41232240000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1], [1, 0, 0, 1, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 0, 1]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 0, 1, 1, 1],![1, 1, 0, 0, 1],![1, 1, 1, 0, 1],![0, 1, 1, 0, 0],![0, 0, 0, 1, 1]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![1861, 1668],![246, 229],![-164, 66],![-622, -332],![2270, 1830]]
 c := ![![2068, -1394, -2874],![258, -176, -350],![-101, 4, 290],![-604, 339, 996],![2426, -1574, -3515]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 1, 0], [2, 0, 1, 2, 2]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 2, 0], [0, 1, 1, 2, 0], [1, 1, 0, 2, 1]], 
![[0, 0, 0, 1, 0], [0, 2, 2, 1, 0], [0, 1, 1, 2, 0], [0, 0, 0, 0, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [2, 0, 1, 2, 2], [1, 1, 0, 2, 1], [0, 1, 1, 1, 0], [1, 2, 1, 1, 0]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 2, 0, 1],![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 1],![0, 1, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 0, 1, 1, 0],![1, 0, 2, 2, 2],![0, 2, 2, 1, 1],![0, 1, 1, 0, 0],![0, 1, 1, 2, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![-281, 993, 132],![-1203, 3625, 489],![3414, -7056, -968],![3438, -7578, -1044],![-2844, 6984, 972]]
 c := ![![219, -369],![720, -1335],![-924, 2544],![-1094, 2742],![1152, -2540]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by native_decide 

noncomputable def M37 : MaximalOrderCertificateOfUnramifiedLists 37 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [6, 15, 5, 14, 0], [2, 27, 5, 34, 23]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [12, 30, 11, 28, 0], [10, 36, 11, 21, 0], [28, 28, 16, 10, 11]], 
![[0, 0, 0, 1, 0], [6, 15, 5, 14, 0], [10, 36, 11, 21, 0], [23, 31, 31, 3, 0], [3, 10, 27, 34, 4]], 
![[0, 0, 0, 0, 1], [2, 27, 5, 34, 23], [28, 28, 16, 10, 11], [3, 10, 27, 34, 4], [7, 16, 8, 23, 30]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![22, 14, 11, 19, 0],![36, 34, 36, 23, 0],![2, 28, 17, 24, 0],![0, 28, 30, 34, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 37]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 37 O Om hm M37
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 37] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
