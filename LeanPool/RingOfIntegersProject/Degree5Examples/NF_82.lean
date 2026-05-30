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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible82

-- Number field with label 5.1.1012500000.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 90*X^2 - 90*X - 1992
lemma T_def : T = X^5 - 15*X^3 - 90*X^2 - 90*X - 1992 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-1992, -90, -90, -15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/9254*a^4 + 1580/4627*a^3 + 519/9254*a^2 + 996/4627*a + 955/4627]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  9254
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![9254, 0, 0, 0, 0], ![0, 9254, 0, 0, 0], ![0, 0, 9254, 0, 0], ![0, 0, 0, 9254, 0], ![1910, 1992, 519, 3160, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-1910, -1992, -519, -3160, 9254],![-652, -680, -177, -1079, 3160]],
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-1910, -1992, -519, -3160, 9254],![1992, 90, 90, 15, 0],![570, -84, 1, -177, 534]],
![![0, 0, 0, 1, 0],![-1910, -1992, -519, -3160, 9254],![1992, 90, 90, 15, 0],![-28650, -27888, -7695, -47310, 138810],![-10098, -9966, -2739, -16865, 49482]],
![![0, 0, 0, 0, 1],![-652, -680, -177, -1079, 3160],![570, -84, 1, -177, 534],![-10098, -9966, -2739, -16865, 49482],![-3562, -3561, -975, -6012, 17639]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-9254]],![[], [], [], [-85636516], [-29242640, -9254]],![[], [], [-85636516], [0, -85636516], [-4941636, -29242640, -9254]],![[], [-9254], [-29242640, -9254], [-4941636, -29242640, -9254], [-3378954, -9986653, -6320, -1]]]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-1910, -1992, -519, -3160, 9254], [-652, -680, -177, -1079, 3160]],
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-1910, -1992, -519, -3160, 9254], [1992, 90, 90, 15, 0], [570, -84, 1, -177, 534]],
 ![[0, 0, 0, 1, 0], [-1910, -1992, -519, -3160, 9254], [1992, 90, 90, 15, 0], [-28650, -27888, -7695, -47310, 138810], [-10098, -9966, -2739, -16865, 49482]],
 ![[0, 0, 0, 0, 1], [-652, -680, -177, -1079, 3160], [570, -84, 1, -177, 534], [-10098, -9966, -2739, -16865, 49482], [-3562, -3561, -975, -6012, 17639]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp661 : Fact (Nat.Prime 661) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [664, 30, 30, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  [0, 0, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [399, 20, 21, 5, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a :=  [4]
 b :=  [0, 0, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 661, 7] where
 n := 5
 p := ![2, 3, 5, 7, 661]
 exp := ![7, 4, 8, 2, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
  exact hp661.out
 a := [-44003587500000, 571252500000, 797040000000, 49275000000]
 b := [10535265000000, 10289335500000, -55120500000, -159408000000, -9855000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1]]]
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
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 0, 0, 1],![0, 1, 1, 1, 0],![0, 0, 0, 0, 1],![0, 1, 0, 1, 1],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-36419, -7042],![-95300, -18229],![-31136, -6008],![-123646, -23900],![-90016, -17194]]
 c := ![![-12700, 63744, -58552],![-31392, 166572, -152650],![-10791, 54490, -49950],![-43220, 216435, -198462],![-29482, 157318, -144047]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

noncomputable def M661 : MaximalOrderCertificateOfUnramifiedLists 661 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [73, 652, 142, 145, 0], [9, 642, 484, 243, 516]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [73, 652, 142, 145, 0], [9, 90, 90, 15, 0], [570, 577, 1, 484, 534]],
![[0, 0, 0, 1, 0], [73, 652, 142, 145, 0], [9, 90, 90, 15, 0], [434, 535, 237, 282, 0], [478, 610, 566, 321, 568]],
![[0, 0, 0, 0, 1], [9, 642, 484, 243, 516], [570, 577, 1, 484, 534], [478, 610, 566, 321, 568], [404, 405, 347, 598, 453]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![401, 381, 510, 144, 0],![228, 582, 469, 311, 0],![176, 658, 570, 473, 0],![592, 50, 415, 506, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel
noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 3, 6, 4, 0], [6, 6, 5, 6, 3]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 3, 6, 4, 0], [4, 6, 6, 1, 0], [3, 0, 1, 5, 2]],
![[0, 0, 0, 1, 0], [1, 3, 6, 4, 0], [4, 6, 6, 1, 0], [1, 0, 5, 3, 0], [3, 2, 5, 5, 6]],
![[0, 0, 0, 0, 1], [6, 6, 5, 6, 3], [3, 0, 1, 5, 2], [3, 2, 5, 5, 6], [1, 2, 5, 1, 6]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![2, 0, 5, 2, 0],![1, 6, 2, 0, 0],![5, 4, 4, 5, 0],![3, 6, 2, 4, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel

 instance : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 661, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 661 O Om hm M661
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 661, 7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

