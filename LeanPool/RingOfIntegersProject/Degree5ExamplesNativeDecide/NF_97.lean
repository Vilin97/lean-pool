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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible97

-- Number field with label 5.1.1687500000.3 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 250*X^2 - 750*X - 680 
lemma T_def : T = X^5 - 25*X^3 - 250*X^2 - 750*X - 680 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-680, -750, -250, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/194*a^4 - 23/97*a^3 - 43/194*a^2 - 9/97*a + 39/97] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  194
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![194, 0, 0, 0, 0], ![0, 194, 0, 0, 0], ![0, 0, 194, 0, 0], ![0, 0, -97, 97, 0], ![78, -18, -43, -46, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![-39, 9, 44, 45, 97],![22, 0, -20, -22, -46]], 
![![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![-78, 18, 89, 92, 194],![379, 366, 93, -21, -97],![-154, -176, -68, -18, -18]], 
![![0, 0, 0, 1, 0],![-39, 9, 44, 45, 97],![379, 366, 93, -21, -97],![-847, -88, 691, 698, 1261],![230, -70, -304, -266, -450]], 
![![0, 0, 0, 0, 1],![22, 0, -20, -22, -46],![-154, -176, -68, -18, -18],![230, -70, -304, -266, -450],![-34, 90, 142, 106, 169]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-194]],![[], [], [], [-18818], [8924, -194]],![[], [], [-18818], [18818, -9409], [-2716, 4559, -97]],![[], [-194], [8924, -194], [-2716, 4559, -97], [-1870, -2055, 92, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [-39, 9, 44, 45, 97], [22, 0, -20, -22, -46]], 
 ![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [-78, 18, 89, 92, 194], [379, 366, 93, -21, -97], [-154, -176, -68, -18, -18]], 
 ![[0, 0, 0, 1, 0], [-39, 9, 44, 45, 97], [379, 366, 93, -21, -97], [-847, -88, 691, 698, 1261], [230, -70, -304, -266, -450]], 
 ![[0, 0, 0, 0, 1], [22, 0, -20, -22, -46], [-154, -176, -68, -18, -18], [230, -70, -304, -266, -450], [-34, 90, 142, 106, 169]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp97: Fact $ Nat.Prime 97 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  4
 a' := [2]
 b' :=  [0, 2]
 k := [1, 0, 0, 1]
 f := [228, 250, 84, 9]
 g :=  [2, 0, 1]
 h :=  [2, 0, 0, 1]
 a :=  [0, 1]
 b :=  [2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [136, 150, 50, 5]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [97, 2] where
 n := 4
 p := ![2, 3, 5, 97]
 exp := ![9, 3, 9, 2]
 pdgood := [3, 5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp97.out
 a := [-26241975000000, -3848625000000, -654187500000, 338512500000]
 b := [23454000000000, 14095395000000, 1446750000000, 130837500000, -67702500000]
 hab := by native_decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M97 : MaximalOrderCertificateOfUnramifiedLists 97 O Om hm where
 n := 5
 t :=  1
 hpos := by native_decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [58, 9, 44, 45, 0], [22, 0, 77, 75, 51]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [19, 18, 89, 92, 0], [88, 75, 93, 76, 0], [40, 18, 29, 79, 79]], 
![[0, 0, 0, 1, 0], [58, 9, 44, 45, 0], [88, 75, 93, 76, 0], [26, 9, 12, 19, 0], [36, 27, 84, 25, 35]], 
![[0, 0, 0, 0, 1], [22, 0, 77, 75, 51], [40, 18, 29, 79, 79], [36, 27, 84, 25, 35], [63, 90, 45, 9, 72]]]
 hTMod := by native_decide
 hle := by native_decide
 w := ![![1, 0, 0, 0, 0],![40, 67, 46, 76, 0],![81, 90, 2, 86, 0],![76, 9, 68, 29, 0],![74, 93, 56, 63, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by native_decide
 hwFrobComp := by native_decide 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 1], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 1], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [1, 1, 0, 1, 1], [1, 0, 1, 1, 1], [1, 0, 1, 0, 1], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 1, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 1, 0]]
 v := ![![1, 0, 1, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 4]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 0, 0, 0],![0, 1, 1, 1, 0],![1, 1, 0, 1, 0],![1, 0, 1, 1, 1],![0, 0, 0, 0, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![245, -126],![3948, -1257],![3870, -1574],![2260, -692],![-1444, 438]]
 c := ![![-106, 142, -64],![-1630, 2196, -852],![-1987, 1894, -868],![-876, 1297, -484],![648, -758, 303]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [97, 2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 97 O Om hm M97
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [97, 2] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
