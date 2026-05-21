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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible83

-- Number field with label 5.1.1012500000.2 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 80*X^2 - 90*X - 936 
lemma T_def : T = X^5 + 15*X^3 - 80*X^2 - 90*X - 936 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-936, -90, -80, 15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/258*a^4 + 4/43*a^3 + 25/86*a^2 - 1/3*a - 15/43] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  258
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![258, 0, 0, 0, 0], ![0, 258, 0, 0, 0], ![0, 0, 258, 0, 0], ![0, 0, 0, 258, 0], ![-90, -86, 75, 24, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![90, 86, -75, -24, 258],![12, 8, -7, -2, 24]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![90, 86, -75, -24, 258],![936, 90, 80, -15, 0],![108, 32, -10, -7, 60]], 
![![0, 0, 0, 1, 0],![90, 86, -75, -24, 258],![936, 90, 80, -15, 0],![-1350, -354, 1215, 440, -3870],![90, -14, 137, 38, -366]], 
![![0, 0, 0, 0, 1],![12, 8, -7, -2, 24],![108, 32, -10, -7, 60],![90, -14, 137, 38, -366],![32, 7, 11, 2, -21]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-258]],![[], [], [], [-66564], [-6192, -258]],![[], [], [-66564], [0, -66564], [-15480, -6192, -258]],![[], [-258], [-6192, -258], [-15480, -6192, -258], [-2788, -711, -48, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [90, 86, -75, -24, 258], [12, 8, -7, -2, 24]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [90, 86, -75, -24, 258], [936, 90, 80, -15, 0], [108, 32, -10, -7, 60]], 
 ![[0, 0, 0, 1, 0], [90, 86, -75, -24, 258], [936, 90, 80, -15, 0], [-1350, -354, 1215, 440, -3870], [90, -14, 137, 38, -366]], 
 ![[0, 0, 0, 0, 1], [12, 8, -7, -2, 24], [108, 32, -10, -7, 60], [90, -14, 137, 38, -366], [32, 7, 11, 2, -21]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp43: Fact $ Nat.Prime 43 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [188, 19, 17, -2, 1]
 g :=  [4, 1]
 h :=  [1, 1, 1, 1, 1]
 a :=  [2]
 b :=  [0, 3, 2, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 2, 43] where
 n := 4
 p := ![2, 3, 5, 43]
 exp := ![7, 6, 8, 2]
 pdgood := [5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp43.out
 a := [-41512500000, 60041250000, -13567500000, -4556250000]
 b := [-317115000000, -19156500000, -6540750000, 2713500000, 911250000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 2, 0, 0, 0], [0, 2, 2, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 2, 0, 0, 0], [0, 0, 2, 0, 0], [0, 2, 2, 2, 0]], 
![[0, 0, 0, 1, 0], [0, 2, 0, 0, 0], [0, 0, 2, 0, 0], [0, 0, 0, 2, 0], [0, 1, 2, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 2, 2, 1, 0], [0, 2, 2, 2, 0], [0, 1, 2, 2, 0], [2, 1, 2, 2, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 2, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 2, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 2, 0, 1],![0, 0, 0, 1, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![2, 2, 0, 2, 1],![0, 4, 4, 2, 0],![2, 1, 2, 2, 2],![1, 0, 0, 0, 2],![0, 2, 4, 2, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-2198, 6783],![-2379, 6638],![-2643, 7713],![-273, 747],![-2529, 7080]]
 c := ![![-1512, -6849, 14196],![2388, -5676, 12549],![472, -7248, 15300],![285, -626, 1359],![2208, -6192, 13457]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![1, 1, 1, 0, 1],![0, 1, 1, 1, 0],![0, 0, 1, 0, 1],![0, 1, 0, 0, 1],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-217, 184],![-1528, 2225],![-318, 330],![-80, 96],![-1628, 2372]]
 c := ![![1234, 88, 256],![324, -3096, 3900],![1143, -170, 476],![252, -41, 182],![234, -3354, 4121]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M43 : MaximalOrderCertificateOfUnramifiedLists 43 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [4, 0, 11, 19, 0], [12, 8, 36, 41, 24]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [4, 0, 11, 19, 0], [33, 4, 37, 28, 0], [22, 32, 33, 36, 17]], 
![[0, 0, 0, 1, 0], [4, 0, 11, 19, 0], [33, 4, 37, 28, 0], [26, 33, 11, 10, 0], [4, 29, 8, 38, 21]], 
![[0, 0, 0, 0, 1], [12, 8, 36, 41, 24], [22, 32, 33, 36, 17], [4, 29, 8, 38, 21], [32, 7, 11, 2, 22]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![24, 7, 41, 10, 0],![24, 36, 39, 15, 0],![16, 26, 28, 40, 0],![10, 31, 34, 40, 42]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide! 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3, 2, 43]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 43 O Om hm M43
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 2, 43] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
