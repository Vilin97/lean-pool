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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible17

-- Number field with label 5.1.25000000.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 + 10*X^3 - 40*X^2 - 15*X + 88
lemma T_def : T = X^5 + 10*X^3 - 40*X^2 - 15*X + 88 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [88, -15, -40, 10, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/28*a^4 + 3/28*a^3 + 5/28*a^2 + 3/28*a + 2/7]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  28
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![28, 0, 0, 0, 0], ![0, 28, 0, 0, 0], ![0, 0, 28, 0, 0], ![0, -7, -14, 7, 0], ![8, 3, 5, 3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![-2, -2, -4, -5, 7],![-4, 0, 0, -2, 3]],
![![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![-8, -6, -11, -12, 28],![-18, 4, 10, -5, -14],![-8, 0, 8, 4, -5]],
![![0, 0, 0, 1, 0],![-2, -2, -4, -5, 7],![-18, 4, 10, -5, -14],![26, -1, 7, 27, -14],![8, -2, -4, 4, 5]],
![![0, 0, 0, 0, 1],![-4, 0, 0, -2, 3],![-8, 0, 8, 4, -5],![8, -2, -4, 4, 5],![-4, -2, -2, -2, 8]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-28]],![[], [], [], [-196], [-84, -28]],![[], [], [-196], [196, -49], [84, -7, -7]],![[], [-28], [-84, -28], [84, -7, -7], [-16, -9, -6, -1]]]
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
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [-2, -2, -4, -5, 7], [-4, 0, 0, -2, 3]],
 ![[0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [-8, -6, -11, -12, 28], [-18, 4, 10, -5, -14], [-8, 0, 8, 4, -5]],
 ![[0, 0, 0, 1, 0], [-2, -2, -4, -5, 7], [-18, 4, 10, -5, -14], [26, -1, 7, 27, -14], [8, -2, -4, 4, 5]],
 ![[0, 0, 0, 0, 1], [-4, 0, 0, -2, 3], [-8, 0, 8, 4, -5], [8, -2, -4, 4, 5], [-4, -2, -2, -2, 8]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-17, 5, 11, 0, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a :=  [2]
 b :=  [0, 0, 1, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 7] where
 n := 3
 p := ![2, 5, 7]
 exp := ![14, 8, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  exact hp2.out
  exact hp5.out
  exact hp7.out
 a := [5200000000, 9960000000, 2160000000, 1000000000]
 b := [9600000000, 2032000000, -2792000000, -432000000, -200000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 1, 0, 0]]
 v_ind := ![1, 4]
 w_ind := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 0, 0, 0],![0, 0, 0, 1, 0],![1, 1, 0, 0, 0],![0, 1, 1, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![3, 0],![6, -7],![4, 0],![4, 28],![-4, 28]]
 c := ![![0, 2, -2],![-10, -4, 2],![1, 2, -2],![-10, -1, -2],![-4, -2, 3]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [5, 5, 3, 2, 0], [3, 0, 0, 5, 3]],
![[0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [6, 1, 3, 2, 0], [3, 4, 3, 2, 0], [6, 0, 1, 4, 2]],
![[0, 0, 0, 1, 0], [5, 5, 3, 2, 0], [3, 4, 3, 2, 0], [5, 6, 0, 6, 0], [1, 5, 3, 4, 5]],
![[0, 0, 0, 0, 1], [3, 0, 0, 5, 3], [6, 0, 1, 4, 2], [1, 5, 3, 4, 5], [3, 5, 5, 5, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],![0, 5, 2, 1, 0],![0, 5, 0, 3, 0],![0, 1, 4, 3, 0],![4, 0, 5, 3, 6]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

