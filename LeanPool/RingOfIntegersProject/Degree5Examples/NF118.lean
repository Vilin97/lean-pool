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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible118

/-!
Support declarations and worked examples for `RingOfIntegersProject`.
-/

namespace RoiDegree5ExamplesNF118
open RoiDegree5ExamplesIrreducible118

-- Number field with label 5.1.6075000000.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 + 15*X^3 - 30*X^2 + 360*X + 144
lemma T_def : T = X^5 + 15*X^3 - 30*X^2 + 360*X + 144 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [144, 360, -30, 15, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/6*a^3 - 1/2*a, 1/84*a^4 - 1/14*a^3 -
-- 11/28*a^2 + 2/7]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  84
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![84, 0, 0, 0, 0],
   ![0, 84, 0, 0, 0],
   ![0, 0, 84, 0, 0],
   ![0, -42, 0, 14, 0],
   ![24, 0, -33, -6, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 3, 0, 6, 0],![-4, 3, 5, 6, 14],![0, -7, -2, -6, -6]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 3, 0, 6, 0],
       ![-24, 18, 33, 36, 84],
       ![-24, -69, 5, -18, 0],
       ![24, 18, -25, -12, -48]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-4, 3, 5, 6, 14],
       ![-24, -69, 5, -18, 0],
       ![14, -12, -29, -16, -49],
       ![8, 45, 10, 14, 23]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![0, -7, -2, -6, -6],
       ![24, 18, -25, -12, -48],
       ![8, 45, 10, 14, 23],
       ![-16, -30, 10, 0, 13]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-84]],
   ![[], [], [], [-1176], [504, -84]],
   ![[], [], [-1176], [0, -196], [714, 84, -14]],
   ![[], [-84], [504, -84], [714, 84, -14], [-606, 45, 12, -1]]]
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
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 3, 0, 6, 0], [-4, 3, 5, 6, 14], [0, -7, -2, -6, -6]],
   ![
     [0, 0, 1, 0, 0],
     [0, 3, 0, 6, 0],
     [-24, 18, 33, 36, 84],
     [-24, -69, 5, -18, 0],
     [24, 18, -25, -12, -48]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-4, 3, 5, 6, 14],
     [-24, -69, 5, -18, 0],
     [14, -12, -29, -16, -49],
     [8, 45, 10, 14, 23]
   ],
   ![
     [0, 0, 0, 0, 1],
     [0, -7, -2, -6, -6],
     [24, 18, -25, -12, -48],
     [8, 45, 10, 14, 23],
     [-16, -30, 10, 0, 13]
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
 f := [-28, -71, 7, -2, 1]
 g := [4, 1]
 h := [1, 1, 1, 1, 1]
 a :=  [3]
 b :=  [0, 2, 3, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![12, 9, 8, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp7.out
 a := [1399680000000, -645165000000, 14580000000, -61965000000]
 b := [3726648000000, -520506000000, 203391000000, -2916000000, 12393000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 1]],
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 1, 0]]
 v := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 vInd := ![1, 2]
 wInd := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 1, 1, 1],![1, 1, 1, 1, 0],![0, 0, 0, 1, 0],![0, 1, 1, 0, 0],![0, 1, 0, 0, 1]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![17, 8],![30, 17],![6, -4],![24, 20],![-10, -4]]
 c := ![![-10, -18, -8],![-18, -28, -14],![-5, -14, -4],![-14, -15, -10],![6, 10, 5]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [2, 0, 2, 0, 2], [0, 2, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 2, 0, 0], [0, 0, 2, 0, 0]],
![[0, 0, 0, 1, 0], [2, 0, 2, 0, 2], [0, 0, 2, 0, 0], [2, 0, 1, 2, 2], [2, 0, 1, 2, 2]],
![[0, 0, 0, 0, 1], [0, 2, 1, 0, 0], [0, 0, 2, 0, 0], [2, 0, 1, 2, 2], [2, 0, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 0, 0, 1, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 0, 1, 2]]
 vInd := ![0, 1, 2]
 wInd := ![0, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 2, 2, 1, 0],![1, 2, 0, 2, 0],![1, 1, 0, 0, 1],![2, 1, 0, 0, 2],![2, 1, 1, 0, 2]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![34, -375, 15],![-147, -95, -105],![69, 126, 28],![102, 243, 42],![138, 75, 69]]
 c := ![![-42, -18],![72, -15],![-30, 15],![-38, 24],![-66, 16]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 3, 0, 6, 0], [3, 3, 5, 6, 0], [0, 0, 5, 1, 1]],
![[0, 0, 1, 0, 0], [0, 3, 0, 6, 0], [4, 4, 5, 1, 0], [4, 1, 5, 3, 0], [3, 4, 3, 2, 1]],
![[0, 0, 0, 1, 0], [3, 3, 5, 6, 0], [4, 1, 5, 3, 0], [0, 2, 6, 5, 0], [1, 3, 3, 0, 2]],
![[0, 0, 0, 0, 1], [0, 0, 5, 1, 1], [3, 4, 3, 2, 1], [1, 3, 3, 0, 2], [5, 5, 3, 0, 6]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![5, 5, 4, 4, 0],![1, 5, 6, 5, 0],![2, 3, 3, 4, 0],![5, 4, 4, 4, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 wInd := ![0, 1, 2, 3, 4]
 hindw := by decide
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

end RoiDegree5ExamplesNF118
