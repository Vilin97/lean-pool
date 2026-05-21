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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible32

-- Number field with label 5.1.72900000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 20*X^2 - 30*X - 24 
lemma T_def : T = X^5 + 15*X^3 - 20*X^2 - 30*X - 24 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-24, -30, -20, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/58*a^4 + 3/29*a^3 - 7/58*a^2 - 2/29*a + 2/29] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  58
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![58, 0, 0, 0, 0], ![0, 58, 0, 0, 0], ![0, 0, 58, 0, 0], ![0, 0, 0, 58, 0], ![4, -4, -7, 6, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-4, 4, 7, -6, 58],![0, 1, 1, -1, 6]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-4, 4, 7, -6, 58],![24, 30, 20, -15, 0],![4, 2, 0, 1, -22]], 
![![0, 0, 0, 1, 0],![-4, 4, 7, -6, 58],![24, 30, 20, -15, 0],![60, -36, -75, 110, -870],![-4, -14, -13, 16, -74]], 
![![0, 0, 0, 0, 1],![0, 1, 1, -1, 6],![4, 2, 0, 1, -22],![-4, -14, -13, 16, -74],![-2, -2, -1, 1, 3]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-58]],![[], [], [], [-3364], [-348, -58]],![[], [], [-3364], [0, -3364], [1276, -348, -58]],![[], [-58], [-348, -58], [1276, -348, -58], [252, -7, -12, -1]]]
 h := Adj
 honed := by decide!
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide! 

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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-4, 4, 7, -6, 58], [0, 1, 1, -1, 6]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-4, 4, 7, -6, 58], [24, 30, 20, -15, 0], [4, 2, 0, 1, -22]], 
 ![[0, 0, 0, 1, 0], [-4, 4, 7, -6, 58], [24, 30, 20, -15, 0], [60, -36, -75, 110, -870], [-4, -14, -13, 16, -74]], 
 ![[0, 0, 0, 0, 1], [0, 1, 1, -1, 6], [4, 2, 0, 1, -22], [-4, -14, -13, 16, -74], [-2, -2, -1, 1, 3]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp29: Fact $ Nat.Prime 29 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  3
 a' := [2]
 b' :=  [1, 2]
 k := [0, 1]
 f := [8, 10, 7, -4, 1]
 g :=  [0, 1, 1]
 h :=  [0, 1, 2, 1]
 a :=  [2, 1]
 b :=  [2, 1, 0, 2]
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
 f := [5, 7, 5, -2, 1]
 g :=  [1, 1]
 h :=  [1, 4, 1, 4, 1]
 a :=  [1]
 b :=  [1, 2, 3, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 29] where
 n := 4
 p := ![2, 3, 5, 29]
 exp := ![7, 6, 5, 2]
 pdgood := [3, 5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp29.out
 a := [-12101400000, 6394950000, -729000000, 700650000]
 b := [1506600000, 4976640000, -2119770000, 145800000, -140130000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![0, 1, 0, 0, 1],![0, 1, 0, 0, 0],![1, 1, 0, 1, 1],![0, 0, 1, 1, 0],![0, 1, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![25, -6],![-32, 19],![382, -140],![276, -86],![324, -116]]
 c := ![![-8, -12, -8],![-4, -42, 64],![55, 638, -864],![88, 717, -850],![58, 608, -793]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M29 : MaximalOrderCertificateOfUnramifiedLists 29 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [25, 4, 7, 23, 0], [0, 1, 1, 28, 6]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [25, 4, 7, 23, 0], [24, 1, 20, 14, 0], [4, 2, 0, 1, 7]], 
![[0, 0, 0, 1, 0], [25, 4, 7, 23, 0], [24, 1, 20, 14, 0], [2, 22, 12, 23, 0], [25, 15, 16, 16, 13]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 28, 6], [4, 2, 0, 1, 7], [25, 15, 16, 16, 13], [27, 27, 28, 1, 3]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![18, 9, 3, 0, 0],![27, 12, 20, 0, 0],![14, 3, 12, 1, 0],![28, 6, 24, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide! 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 29]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 29 O Om hm M29
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 29] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
