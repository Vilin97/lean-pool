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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible132

-- Number field with label 5.1.15187500000.9 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 100*X^2 + 300*X - 360 
lemma T_def : T = X^5 - 100*X^2 + 300*X - 360 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-360, 300, -100, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/12*a^4 - 1/3*a] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  12
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![12, 0, 0, 0, 0], ![0, 12, 0, 0, 0], ![0, 0, 6, 0, 0], ![0, -6, 0, 3, 0], ![0, -4, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 2, 0],![0, 1, -1, 0, 3],![30, -25, 16, 0, 0]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![0, 1, 0, 0, 3],![45, -38, 25, -1, 0],![0, 23, -25, 16, 0]], 
![![0, 0, 0, 1, 0],![0, 1, -1, 0, 3],![45, -38, 25, -1, 0],![0, 34, -37, 25, -3],![-15, 8, 7, -25, 24]], 
![![0, 0, 0, 0, 1],![30, -25, 16, 0, 0],![0, 23, -25, 16, 0],![-15, 8, 7, -25, 24],![230, -195, 128, 10, -25]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-12]],![[], [], [], [-18], [0, -6]],![[], [], [-18], [0, -9], [6, 0, -3]],![[], [-12], [0, -6], [6, 0, -3], [-92, 0, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 1, -1, 0, 3], [30, -25, 16, 0, 0]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 0, 0, 3], [45, -38, 25, -1, 0], [0, 23, -25, 16, 0]], 
 ![[0, 0, 0, 1, 0], [0, 1, -1, 0, 3], [45, -38, 25, -1, 0], [0, 34, -37, 25, -3], [-15, 8, 7, -25, 24]], 
 ![[0, 0, 0, 0, 1], [30, -25, 16, 0, 0], [0, 23, -25, 16, 0], [-15, 8, 7, -25, 24], [230, -195, 128, 10, -25]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [72, -60, 20]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [3]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![15, 7, 9]
 pdgood := [5]
 hsub := by native_decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-1036800000000, -97200000000, 0, 16200000000]
 b := [-777600000000, 401760000000, 19440000000, 0, -3240000000]
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
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 1, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 0, 1], [1, 0, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [1, 0, 1, 1, 0], [0, 1, 0, 0, 1]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![1, 1, 1, 0, 1],![1, 0, 0, 1, 0],![1, 0, 0, 0, 1],![0, 1, 0, 0, 0],![1, 0, 1, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 1, 1]
 a := ![![-29, 62],![-6, -3],![38, 50],![6, 6],![-72, 6]]
 c := ![![46, -14, -6],![46, -10, 26],![1, -34, -8],![0, -3, 2],![46, 24, 1]]
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
![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 1, 2, 0, 0], [0, 2, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 0, 0, 0], [0, 1, 1, 2, 0], [0, 2, 2, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 2, 0, 0], [0, 1, 1, 2, 0], [0, 1, 2, 1, 0], [0, 2, 1, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 2, 1, 0, 0], [0, 2, 2, 1, 0], [0, 2, 1, 2, 0], [2, 0, 2, 1, 2]]]
 hTMod := by native_decide
 hle := by native_decide
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 0, 1, 0],![0, 0, 1, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 0, 1, 0],![0, 0, 1, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![0, 1, 2]
 w_ind := ![0, 1]
 hmod1 := by native_decide
 hmod2 := by native_decide
 hindv := by native_decide
 hindw := by native_decide
 hvFrobKer := by native_decide
 hwFrobComp := by native_decide 
 g := ![![0, 1, 1, 0, 1],![1, 0, 2, 2, 2],![1, 2, 2, 0, 2],![2, 2, 2, 0, 4],![0, 0, 2, 1, 0]]
 w1 := ![1, 0, 1]
 w2 := ![0, 0]
 a := ![![4, -534, 276],![45, -812, 423],![9, -1068, 553],![9, -2076, 1044],![24, 126, -33]]
 c := ![![192, 18],![342, 24],![384, 36],![671, 87],![57, -23]]
 hmulw := by native_decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by native_decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
