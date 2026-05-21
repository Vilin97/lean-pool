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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible125

-- Number field with label 5.1.10125000000.12 in the LMFDB

open Polynomial

noncomputable def T : ℤ[X] := X^5 + 75*X^3 - 150*X^2 + 150*X - 780 
lemma T_def : T = X^5 + 75*X^3 - 150*X^2 + 150*X - 780 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-780, 150, -150, 75, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/1904*a^4 - 375/1904*a^3 - 7/68*a^2 - 453/952*a - 229/476] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1904
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1904, 0, 0, 0, 0], ![0, 1904, 0, 0, 0], ![0, 0, 1904, 0, 0], ![0, 0, -952, 952, 0], ![-916, -906, -196, -375, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![458, 453, 285, 374, 952],![-180, -179, -113, -148, -375]], 
![![0, 0, 1, 0, 0],![0, 0, 1, 2, 0],![916, 906, 571, 750, 1904],![-68, -528, -248, -450, -952],![-284, -99, -97, -78, -271]], 
![![0, 0, 0, 1, 0],![458, 453, 285, 374, 952],![-68, -528, -248, -450, -952],![-17336, -16491, -10601, -13725, -35224],![6670, 6495, 4147, 5410, 13820]], 
![![0, 0, 0, 0, 1],![-180, -179, -113, -148, -375],![-284, -99, -97, -78, -271],![6670, 6495, 4147, 5410, 13820],![-2460, -2454, -1556, -2046, -5204]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-1904]],![[], [], [], [-1812608], [714000, -1904]],![[], [], [-1812608], [1812608, -906304], [-99008, 357952, -952]],![[], [-1904], [714000, -1904], [-99008, 357952, -952], [-201588, -140158, 750, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [458, 453, 285, 374, 952], [-180, -179, -113, -148, -375]], 
 ![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [916, 906, 571, 750, 1904], [-68, -528, -248, -450, -952], [-284, -99, -97, -78, -271]], 
 ![[0, 0, 0, 1, 0], [458, 453, 285, 374, 952], [-68, -528, -248, -450, -952], [-17336, -16491, -10601, -13725, -35224], [6670, 6495, 4147, 5410, 13820]], 
 ![[0, 0, 0, 0, 1], [-180, -179, -113, -148, -375], [-284, -99, -97, -78, -271], [6670, 6495, 4147, 5410, 13820], [-2460, -2454, -1556, -2046, -5204]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide!

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide!)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp17: Fact $ Nat.Prime 17 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [260, -50, 50, -25]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  [1, 2, 2]
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
 f := [156, -30, 30, -15]
 g :=  [0, 1]
 h :=  [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [17, 2, 7] where
 n := 5
 p := ![2, 3, 5, 7, 17]
 exp := ![16, 4, 9, 2, 2]
 pdgood := [3, 5]
 hsub := by decide!
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
  exact hp17.out
 a := [-199153350000000, -3508650000000, -4536675000000, 15525000000]
 b := [-56789100000000, 67330170000000, 608580000000, 907335000000, -3105000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M17 : MaximalOrderCertificateOfUnramifiedLists 17 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [16, 11, 13, 0, 0], [7, 8, 6, 5, 16]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [15, 5, 10, 2, 0], [0, 16, 7, 9, 0], [5, 3, 5, 7, 1]], 
![[0, 0, 0, 1, 0], [16, 11, 13, 0, 0], [0, 16, 7, 9, 0], [4, 16, 7, 11, 0], [6, 1, 16, 4, 16]], 
![[0, 0, 0, 0, 1], [7, 8, 6, 5, 16], [5, 3, 5, 7, 1], [6, 1, 16, 4, 16], [5, 11, 8, 11, 15]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 12, 5, 11, 0],![0, 10, 4, 10, 0],![0, 1, 2, 2, 0],![0, 2, 4, 2, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide! 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 1, 0, 0]]
 v_ind := ![1, 4]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide!
 hwFrobComp := by decide! 
 g := ![![1, 1, 0, 0, 1],![1, 0, 0, 0, 1],![1, 1, 0, 1, 1],![0, 0, 0, 0, 1],![0, 1, 1, 0, 1]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![6971, 23216],![6512, 21687],![-9514, -31508],![6512, 21686],![6380, 21040]]
 c := ![![5628, 4540, -2572],![5260, 4240, -2406],![-7915, -6106, 3526],![5260, 4239, -2406],![5418, 4052, -2367]]
 hmulw := by decide! 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [3, 5, 5, 3, 0], [2, 3, 6, 6, 3]], 
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [6, 3, 4, 1, 0], [2, 4, 4, 5, 0], [3, 6, 1, 6, 2]], 
![[0, 0, 0, 1, 0], [3, 5, 5, 3, 0], [2, 4, 4, 5, 0], [3, 1, 4, 2, 0], [6, 6, 3, 6, 2]], 
![[0, 0, 0, 0, 1], [2, 3, 6, 6, 3], [3, 6, 1, 6, 2], [6, 6, 3, 6, 2], [4, 3, 5, 5, 4]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![3, 3, 1, 5, 0],![4, 5, 0, 2, 0],![1, 3, 5, 5, 0],![6, 4, 2, 3, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide! 

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible 

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [17, 2, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 17 O Om hm M17
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [17, 2, 7] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']


theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
    
