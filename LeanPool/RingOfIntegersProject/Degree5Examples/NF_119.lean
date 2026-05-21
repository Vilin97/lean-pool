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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible119

-- Number field with label 5.1.9112500000.1 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 - 75*X^3 - 150*X^2 - 3600 
lemma T_def : T = X^5 - 75*X^3 - 150*X^2 - 3600 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-3600, 0, -150, -75, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/60*a^3 - 1/4*a^2 - 1/2*a, 1/60*a^4 - 1/4*a^2 - 1/2*a] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  60
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![60, 0, 0, 0, 0], ![0, 60, 0, 0, 0], ![0, -30, 30, 0, 0], ![0, -30, -15, 1, 0], ![0, -30, -15, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![0, 22, 14, 30, 0],![0, -11, -8, -15, 1],![60, 47, 34, 60, 0]], 
![![0, 0, 1, 0, 0],![0, 22, 14, 30, 0],![0, -11, -7, -30, 15],![30, 18, 14, 30, -8],![-30, 74, 28, 30, 30]], 
![![0, 0, 0, 1, 0],![0, -11, -8, -15, 1],![30, 18, 14, 30, -8],![-30, -12, -10, -20, 4],![30, -11, 6, 15, -13]], 
![![0, 0, 0, 0, 1],![60, 47, 34, 60, 0],![-30, 74, 28, 30, 30],![30, -11, 6, 15, -13],![90, 319, 188, 300, 60]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-60]],![[], [], [], [-30], [30, -30]],![[], [], [-30], [30, -1], [-30, 15, -1]],![[], [-60], [30, -30], [-30, 15, -1], [-90, -45, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 22, 14, 30, 0], [0, -11, -8, -15, 1], [60, 47, 34, 60, 0]], 
 ![[0, 0, 1, 0, 0], [0, 22, 14, 30, 0], [0, -11, -7, -30, 15], [30, 18, 14, 30, -8], [-30, 74, 28, 30, 30]], 
 ![[0, 0, 0, 1, 0], [0, -11, -8, -15, 1], [30, 18, 14, 30, -8], [-30, -12, -10, -20, 4], [30, -11, 6, 15, -13]], 
 ![[0, 0, 0, 0, 1], [60, 47, 34, 60, 0], [-30, 74, 28, 30, 30], [30, -11, 6, 15, -13], [90, 319, 188, 300, 60]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![15, 10, 12]
 pdgood := []
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-131220000000000, -21870000000000, -10935000000000, 2187000000000]
 b := [262440000000000, 0, 17496000000000, 2187000000000, -437400000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 

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
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 1, 1]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 1]]
 v_ind := ![1, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![1, 1, 1, 0, 0],![1, 0, 1, 0, 0],![0, 1, 1, 1, 1],![0, 1, 0, 1, 1],![0, 0, 1, 1, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![-7, 76],![-8, 91],![-12, 162],![-4, 72],![-2, 42]]
 c := ![![16, 12, 20],![16, 14, 22],![75, 14, 44],![60, 1, 22],![0, 6, 9]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 1, 2, 0, 0], [0, 1, 1, 0, 1], [0, 2, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 2, 0, 0], [0, 1, 2, 0, 0], [0, 0, 2, 0, 1], [0, 2, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 0, 1], [0, 0, 2, 0, 1], [0, 0, 2, 1, 1], [0, 1, 0, 0, 2]], 
![[0, 0, 0, 0, 1], [0, 2, 1, 0, 0], [0, 2, 1, 0, 0], [0, 1, 0, 0, 2], [0, 1, 2, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 2]]
 v_ind := ![1, 2, 4]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![1, 0, 1, 1, 1],![1, 1, 0, 1, 0],![1, 2, 1, 0, 0],![0, 2, 0, 0, 2],![0, 1, 2, 0, 0]]
 w1 := ![0, 0, 1]
 w2 := ![0, 1]
 a := ![![367, 252, 27],![-33, -14, 3],![156, 90, 13],![600, 432, 48],![270, 150, 15]]
 c := ![![60, 141],![0, -9],![60, 51],![160, 240],![60, 85]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 

noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 2, 4, 0, 0], [0, 4, 2, 0, 1], [0, 2, 4, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 2, 4, 0, 0], [0, 4, 3, 0, 0], [0, 3, 4, 0, 2], [0, 4, 3, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 4, 2, 0, 1], [0, 3, 4, 0, 2], [0, 3, 0, 0, 4], [0, 4, 1, 0, 2]], 
![[0, 0, 0, 0, 1], [0, 2, 4, 0, 0], [0, 4, 3, 0, 0], [0, 4, 1, 0, 2], [0, 4, 3, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![1, 2, 3, 4]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![0, 3, 0, 1, 0],![0, 2, 4, 2, 3],![1, 2, 0, 2, 2],![0, 4, 3, 2, 1],![0, 3, 1, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![46, 20, 45, 0],![470, 316, 465, 90],![245, 145, 241, 40],![255, 170, 255, 41],![80, 50, 75, 10]]
 c := ![![0],![60],![25],![30],![6]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide 


 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 5]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 5] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
