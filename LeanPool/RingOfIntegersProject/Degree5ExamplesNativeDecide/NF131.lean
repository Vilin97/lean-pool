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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible131

/-!
Support declarations and worked examples for `RingOfIntegersProject`.
-/

namespace RoiDegree5ExamplesNativeDecideNF131
open RoiDegree5ExamplesNativeDecideIrreducible131

-- Number field with label 5.3.15187500000.8 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 50*X^2 - 150*X + 920
lemma T_def : T = X^5 - 25*X^3 - 50*X^2 - 150*X + 920 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [920, -150, -50, -25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/14*a^3 - 1/14*a^2 - 3/7*a - 3/7,
-- 1/42*a^4 - 1/42*a^3 - 1/7*a^2 - 10/21*a + 1/3]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  42
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![42, 0, 0, 0, 0],
   ![0, 42, 0, 0, 0],
   ![0, 0, 42, 0, 0],
   ![-18, -18, -3, 3, 0],
   ![14, -20, -6, -1, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![6, 6, 1, 14, 0],![-1, 1, 0, 0, 3],![-19, 6, 1, 6, -1]],
     ![
       ![0, 0, 1, 0, 0],
       ![6, 6, 1, 14, 0],
       ![-8, 26, 7, 14, 42],
       ![-57, 17, 4, 18, -3],
       ![19, -13, 6, 8, 19]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-1, 1, 0, 0, 3],
       ![-57, 17, 4, 18, -3],
       ![9, -4, 1, 1, 3],
       ![-17, 11, 0, 11, -1]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-19, 6, 1, 6, -1],
       ![19, -13, 6, 8, 19],
       ![-17, 11, 0, 11, -1],
       ![9, -6, 3, -4, 12]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-42]],
   ![[], [], [], [-126], [42, -42]],
   ![[], [], [-126], [18, -9], [-42, 6, -3]],
   ![[], [-42], [42, -42], [-42, 6, -3], [28, -14, 2, -1]]]
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
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [6, 6, 1, 14, 0], [-1, 1, 0, 0, 3], [-19, 6, 1, 6, -1]],
   ![
     [0, 0, 1, 0, 0],
     [6, 6, 1, 14, 0],
     [-8, 26, 7, 14, 42],
     [-57, 17, 4, 18, -3],
     [19, -13, 6, 8, 19]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-1, 1, 0, 0, 3],
     [-57, 17, 4, 18, -3],
     [9, -4, 1, 1, 3],
     [-17, 11, 0, 11, -1]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-19, 6, 1, 6, -1],
     [19, -13, 6, 8, 19],
     [-17, 11, 0, 11, -1],
     [9, -6, 3, -4, 12]
   ]
 ]

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
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-184, 30, 10, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![9, 7, 9, 4]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp7.out
 a := [5060475000000, 99225000000, -248062500000, -49612500000]
 b := [-3969000000000, -1805895000000, -119070000000, 49612500000, 9922500000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 1]],
![[0, 0, 0, 1, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 1, 1], [1, 1, 0, 1, 1]],
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 0, 1, 0, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 1, 0, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 1, 0]]
 v := ![![1, 0, 1, 0, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 1, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 vInd := ![0, 1]
 wInd := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 0, 1, 0],![1, 1, 0, 1, 0],![0, 0, 0, 1, 0],![1, 1, 0, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![-3, 8],![-4, 11],![-4, 8],![34, -22],![60, -42]]
 c := ![![-50, -6, 16],![-66, -10, 26],![-51, -6, 16],![-20, -3, 12],![-52, 14, 21]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [2, 1, 0, 0, 0], [2, 0, 1, 0, 2]],
![[0, 0, 1, 0, 0], [0, 0, 1, 2, 0], [1, 2, 1, 2, 0], [0, 2, 1, 0, 0], [1, 2, 0, 2, 1]],
![[0, 0, 0, 1, 0], [2, 1, 0, 0, 0], [0, 2, 1, 0, 0], [0, 2, 1, 1, 0], [1, 2, 0, 2, 2]],
![[0, 0, 0, 0, 1], [2, 0, 1, 0, 2], [1, 2, 0, 2, 1], [1, 2, 0, 2, 2], [0, 0, 0, 2, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 2, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 2, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 2, 0]]
 vInd := ![0, 1]
 wInd := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 2, 2, 0],![2, 2, 1, 0, 0],![0, 0, 2, 0, 1],![2, 1, 2, 0, 0],![4, 0, 0, 2, 4]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![-308, 360],![-150, 178],![-138, 189],![-171, 216],![-177, 234]]
 c := ![![-114, 90, -42],![-30, 48, -24],![-68, 117, -48],![-57, 94, -36],![-105, 102, -70]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [6, 6, 1, 0, 0], [6, 1, 0, 0, 3], [2, 6, 1, 6, 6]],
![[0, 0, 1, 0, 0], [6, 6, 1, 0, 0], [6, 5, 0, 0, 0], [6, 3, 4, 4, 4], [5, 1, 6, 1, 5]],
![[0, 0, 0, 1, 0], [6, 1, 0, 0, 3], [6, 3, 4, 4, 4], [2, 3, 1, 1, 3], [4, 4, 0, 4, 6]],
![[0, 0, 0, 0, 1], [2, 6, 1, 6, 6], [5, 1, 6, 1, 5], [4, 4, 0, 4, 6], [2, 1, 3, 3, 5]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],![3, 5, 6, 0, 0],![4, 3, 2, 0, 0],![2, 6, 6, 2, 1],![6, 3, 2, 2, 5]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 wInd := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 7]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF131
