/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertificateDedekind
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible31

namespace RoiDegree5ExamplesNativeDecideNF31
open RoiDegree5ExamplesNativeDecideIrreducible31

-- Number field with label 5.1.67500000.3 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 10*X^2 + 15*X + 54
lemma T_def : T = X^5 - 10*X^2 + 15*X + 54 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [54, 15, -10, 0, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 - 1/4*a^3 +
-- 1/4*a^2 + 5/12*a - 1/2]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  12
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![12, 0, 0, 0, 0],
   ![0, 12, 0, 0, 0],
   ![0, 0, 12, 0, 0],
   ![0, -6, 0, 6, 0],
   ![-6, 5, 3, -3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![3, -1, -2, 3, 6],![-6, -1, 2, -1, -3]],
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![6, -2, -3, 6, 12],![-27, -8, 5, -1, 0],![15, 0, -5, 4, 3]],
![![0, 0, 0, 1, 0],![3, -1, -2, 3, 6],![-27, -8, 5, -1, 0],![-3, -10, -2, 2, -6],![0, 2, -2, 0, 9]],
![![0, 0, 0, 0, 1],![-6, -1, 2, -1, -3],![15, 0, -5, 4, 3],![0, 2, -2, 0, 9],![-5, -3, 3, -1, -9]]]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-12]],
   ![[], [], [], [-72], [36, -12]],
   ![[], [], [-72], [0, -36], [-12, 18, -6]],
   ![[], [-12], [36, -12], [-12, 18, -6], [-2, -15, 6, -1]]]
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

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| Irreducible (map (algebraMap ℤ ℚ) T) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible

/-- Auxiliary declaration for the worked example. -/
instance : IsDomain K := by
  have hmap : Irreducible (map (algebraMap ℤ ℚ) T) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1 T_irreducible
  exact AdjoinRoot.isDomain_of_prime (Irreducible.prime hmap)

/-- Auxiliary declaration for the worked example. -/
instance : NoZeroSMulDivisors ℤ K := by
  haveI : IsAddTorsionFree K := IsDomain.instIsAddTorsionFreeOfCharZero K
  infer_instance

/-- Auxiliary declaration for the worked example. -/
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

/-- Auxiliary declaration for the worked example. -/
noncomputable def O := subalgebraOfBuilderLists T l BQ

lemma hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

/-- Auxiliary declaration for the worked example. -/
noncomputable def B : Basis (Fin 5) ℤ O := basisOfBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

/-- Auxiliary declaration for the worked example. -/
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
/-- Auxiliary declaration for the worked example. -/
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

/-- Auxiliary declaration for the worked example. -/
noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
def Table : Fin 5 → Fin 5 → List ℤ :=
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [3, -1, -2, 3, 6], [-6, -1, 2, -1, -3]],
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [6, -2, -3, 6, 12], [-27, -8, 5, -1, 0], [15, 0, -5, 4, 3]],
 ![[0, 0, 0, 1, 0], [3, -1, -2, 3, 6], [-27, -8, 5, -1, 0], [-3, -10, -2, 2, -6], [0, 2, -2, 0, 9]],
 ![[0, 0, 0, 0, 1], [-6, -1, 2, -1, -3], [15, 0, -5, 4, 3], [0, 2, -2, 0, 9], [-5, -3, 3, -1, -9]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-10, -2, 3, 1, 1]
 g := [4, 1]
 h := [1, 1, 1, 1, 1]
 a :=  [2]
 b :=  [4, 0, 1, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![11, 5, 7]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [675000000, -81000000, 81000000, -27000000]
 b := [162000000, -167400000, 16200000, -16200000, 5400000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 1, 0], [0, 1, 0, 1, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 0, 1]],
![[0, 0, 0, 1, 0], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [1, 0, 1, 0, 1], [0, 0, 0, 0, 1], [1, 1, 1, 1, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 vInd := ![0, 1]
 wInd := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 1, 0, 1],![0, 1, 1, 1, 0],![1, 1, 0, 0, 0],![1, 1, 1, 1, 0],![0, 1, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![19, -4],![30, -9],![0, 8],![30, -8],![20, -4]]
 c := ![![4, -2, 0],![-36, 24, -22],![-3, -2, 0],![-36, 25, -22],![-4, 6, -3]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 1, 0, 0], [0, 2, 2, 2, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 0, 0, 0], [0, 1, 2, 2, 0], [0, 0, 1, 1, 0]],
![[0, 0, 0, 1, 0], [0, 2, 1, 0, 0], [0, 1, 2, 2, 0], [0, 2, 1, 2, 0], [0, 2, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 2, 2, 2, 0], [0, 0, 1, 1, 0], [0, 2, 1, 0, 0], [1, 0, 0, 2, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 2]]
 v := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0],![0, 0, 1, 2, 2]]
 vInd := ![1, 3]
 wInd := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 2, 2, 2, 4],![0, 0, 0, 2, 2],![0, 2, 0, 0, 4],![2, 4, 4, 4, 2],![0, 2, 4, 2, 0]]
 a := ![![![-13, 66],![-3, 8]],
   ![![0, 16],![-4, 4]],
   ![![-15, 36],![-6, 6]],
   ![![0, 90],![0, 18]],
   ![![-3, 66],![6, 6]]]
 c := ![![![6, -21, 12],![-18, -15, 6]],
   ![![-18, -15, 3],![-2, -5, 1]],
   ![![32, 3, 2],![2, -4, 8]],
   ![![-36, -45, 21],![-36, -27, 3]],
   ![![-18, -31, 18],![-36, -20, 0]]]
 d := ![![![3, 6],![9, 18],![15, 30]],
   ![![0, 6],![0, 12],![6, 0]],
   ![![0, 0],![15, -12],![63, -48]],
   ![![6, 12],![0, 54],![-42, 114]],
   ![![6, 6],![-3, 42],![-63, 126]]]
 e := ![![![0, -1, 2],![-18, -7, 0],![-22, -11, -18]],
   ![![0, -1, 1],![-6, -7, 3],![-26, -13, 3]],
   ![![0, 0, 2],![-24, -3, -6],![-88, -5, -48]],
   ![![2, 1, 1],![0, -9, 9],![52, -19, 29]],
   ![![0, 0, 0],![6, -3, 6],![102, -3, 30]]]
 abInd := ![(Sum.inl 0, Sum.inl 0),
   (Sum.inl 1, Sum.inl 0),
   (Sum.inl 0, Sum.inr 0),
   (Sum.inr 0, Sum.inr 0),
   (Sum.inl 0, Sum.inr 1)]
 hindab := by decide +kernel
 hmul1 := by decide +kernel
 hmul2 := by decide +kernel


/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateLists 3 O Om hm M3
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF31
