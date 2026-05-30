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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible64

namespace RoiDegree5ExamplesNF64
open RoiDegree5ExamplesIrreducible64

-- Number field with label 5.3.480000000.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 20*X^3 - 20*X - 96
lemma T_def : T = X^5 - 20*X^3 - 20*X - 96 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-96, -20, 0, -20, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/12*a^4 + 1/12*a^3
-- + 1/6*a^2 + 1/6*a]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  12
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![12, 0, 0, 0, 0], ![0, 12, 0, 0, 0], ![0, 0, 6, 0, 0], ![0, -6, 0, 3, 0], ![0, 2, 2, 1, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 2, 0],![0, -1, -2, -1, 3],![8, 5, 0, 7, 1]],
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![0, -1, -1, -1, 3],![12, 7, 0, 9, 0],![4, 3, -2, 0, 11]],
![![0, 0, 0, 1, 0],![0, -1, -2, -1, 3],![12, 7, 0, 9, 0],![0, 2, -1, -4, 12],![40, 26, 3, 33, 5]],
![![0, 0, 0, 0, 1],![8, 5, 0, 7, 1],![4, 3, -2, 0, 11],![40, 26, 3, 33, 5],![32, 24, -5, 16, 44]]]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-12]],
   ![[], [], [], [-18], [-6, -6]],
   ![[], [], [-18], [0, -9], [-60, -3, -3]],
   ![[], [-12], [-6, -6], [-60, -3, -3], [-48, -25, -2, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, -1, -2, -1, 3], [8, 5, 0, 7, 1]],
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, -1, -1, -1, 3], [12, 7, 0, 9, 0], [4, 3, -2, 0, 11]],
 ![[0, 0, 0, 1, 0], [0, -1, -2, -1, 3], [12, 7, 0, 9, 0], [0, 2, -1, -4, 12], [40, 26, 3, 33, 5]],
 ![[0, 0, 0, 0, 1], [8, 5, 0, 7, 1], [4, 3, -2, 0, 11], [40, 26, 3, 33, 5], [32, 24, -5, 16, 44]]]

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
 f := [20, 5, 1, 5, 1]
 g := [4, 1]
 h := [1, 1, 1, 1, 1]
 a :=  [3]
 b :=  [4, 4, 2, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![21, 3, 7]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-44544000000, 6144000000, 3840000000, -768000000]
 b := [-7372800000, 15052800000, -2457600000, -768000000, 153600000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 3
 n := 2
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1]],
![[0, 0, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]],
![[0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 0, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 0, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 1, 1]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 1, 0, 1],![0, 1, 0, 0, 1],![0, 1, 0, 1, 1],![1, 1, 1, 0, 0],![0, 0, 0, 1, 1]]
 w1 := ![1, 1, 0]
 w2 := ![1, 0]
 a := ![![35, 48, 24],![40, 27, 32],![72, -8, 75],![12, 6, 10],![64, 0, 66]]
 c := ![![24, -28],![26, -16],![52, 2],![7, -2],![48, -3]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 1
 n := 4
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 2, 1, 2, 0], [2, 2, 0, 1, 1]],
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 2, 2, 0], [0, 1, 0, 0, 0], [1, 0, 1, 0, 2]],
![[0, 0, 0, 1, 0], [0, 2, 1, 2, 0], [0, 1, 0, 0, 0], [0, 2, 2, 2, 0], [1, 2, 0, 0, 2]],
![[0, 0, 0, 0, 1], [2, 2, 0, 1, 1], [1, 0, 1, 0, 2], [1, 2, 0, 0, 2], [2, 0, 1, 1, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 2, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 2, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 0, 0, 1, 1]]
 v_ind := ![1]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 2, 1, 2],![2, 0, 0, 1, 0],![1, 0, 1, 2, 1],![2, 2, 2, 0, 2],![1, 1, 2, 1, 1]]
 w1 := ![1]
 w2 := ![0, 1, 0, 0]
 a := ![![343],![93],![309],![294],![255]]
 c := ![![168, 303, -12, -150],
   ![40, 33, 0, -18],
   ![144, 199, -6, -102],
   ![144, 270, -8, -132],
   ![120, 195, -6, -98]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
 hacindw := by decide


/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF64
