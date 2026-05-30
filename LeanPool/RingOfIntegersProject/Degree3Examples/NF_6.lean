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
import LeanPool.RingOfIntegersProject.Degree3Examples.Irreducible6
import LeanPool.RingOfIntegersProject.DiscriminantSubalgebraBuilder

-- Number field with label 3.1.16200.2 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - 30*X - 80
lemma T_def : T = X^3 - 30*X - 80 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-80, -30, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2]

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d :=  2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0], ![0, 2, 0], ![0, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]],
![![0, 1, 0],![0, 0, 2],![40, 15, 0]],
![![0, 0, 1],![40, 15, 0],![0, 20, 15]]]
 s := ![![[], [], []],![[], [], [-2]],![[], [-2], [0, -1]]]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide +kernel

lemma T_degree : T.natDegree = 3 := (SubalgebraBuilderOfList T l BQ).hdeg

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

noncomputable def B : Basis (Fin 3) ℤ O := basisOfBuilderLists T l BQ
noncomputable def B' : Basis (Fin 3) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 3) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
def Table : Fin 3 → Fin 3 → List ℤ :=
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
 ![[0, 1, 0], [0, 0, 2], [40, 15, 0]],
 ![[0, 0, 1], [40, 15, 0], [0, 20, 15]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [27, 11, 1]
 g := [1, 1]
 h := [1, 2, 1]
 a :=  [2]
 b :=  [1, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [16, 6]
 g := [0, 1]
 h := [0, 0, 1]
 a :=  [1]
 b :=  [4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![5, 4, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-2160, 540]
 b := [3600, 720, -180]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
 m := 1
 n := 2
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
![[0, 1, 0], [0, 0, 0], [0, 1, 0]],
![[0, 0, 1], [0, 1, 0], [0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0]]
 b2 := ![![1, 0, 0],![0, 0, 1]]
 v := ![![0, 1, 0]]
 w := ![![1, 0, 0],![0, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 0, 1]]
 v_ind := ![1]
 w_ind := ![0, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by intro i; fin_cases i; decide +kernel
 hwFrobComp := by intro i; fin_cases i <;> decide +kernel
 g := ![![0, 0, 1],![1, 0, 1],![0, 1, 0]]
 a := ![![![15]],![![16]],![![0]]]
 c := ![![![20, 0]],![![20, 0]],![![0, 1]]]
 d := ![![![0],![40]],![![0],![40]],![![2],![30]]]
 e := ![![![0, 1],![0, 15]],![![1, 1],![0, 16]],![![0, 0],![40, 0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inr 0, Sum.inr 0),(Sum.inl 0, Sum.inr 1)]
 hindab := by decide
 hmul1 := by decide +kernel
 hmul2 := by decide +kernel


 theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateLists 2 O Om hm M2
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl

theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl


lemma T_discr : T.discriminant = -64800 := by
  rw [T_monic.discriminant_def, T_degree, ← T_ofList]
  have : [-80, -30, 0, 1].derivative = [-30, 0, 3, 0] := rfl
  rw [← ofList_derivative_eq_derivative , this]
  decide +kernel

theorem K_discr : NumberField.discr K = -16200 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder
  T_irreducible BQ O_ringOfIntegers]
  rw [T_discr]
  rfl
