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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible96

namespace RoiDegree5ExamplesNF96
open RoiDegree5ExamplesIrreducible96

-- Number field with label 5.1.1687500000.2 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 250*X^2 - 750*X - 1100
lemma T_def : T = X^5 - 25*X^3 - 250*X^2 - 750*X - 1100 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-1100, -750, -250, -25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/10*a^3 - 1/2*a^2, 1/120*a^4 - 1/24*a^3
-- - 1/2*a^2 - 1/12*a + 1/6]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  120
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![120, 0, 0, 0, 0],
   ![0, 120, 0, 0, 0],
   ![0, 0, 120, 0, 0],
   ![0, 0, -60, 12, 0],
   ![20, -10, -60, -5, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 5, 10, 0],![-2, 1, 6, 0, 12],![10, 6, -3, -5, -5]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 5, 10, 0],
       ![-20, 10, 85, 50, 120],
       ![120, 70, -5, 0, -60],
       ![-40, -25, -24, -5, -35]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-2, 1, 6, 0, 12],
       ![120, 70, -5, 0, -60],
       ![-120, -59, 25, 25, 60],
       ![-14, -13, 5, -4, 29]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![10, 6, -3, -5, -5],
       ![-40, -25, -24, -5, -35],
       ![-14, -13, 5, -4, 29],
       ![44, 25, 4, -5, 2]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-120]],
   ![[], [], [], [-1440], [600, -120]],
   ![[], [], [-1440], [1440, -144], [120, 120, -12]],
   ![[], [-120], [600, -120], [120, 120, -12], [-580, 70, 10, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 5, 10, 0], [-2, 1, 6, 0, 12], [10, 6, -3, -5, -5]],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 5, 10, 0],
     [-20, 10, 85, 50, 120],
     [120, 70, -5, 0, -60],
     [-40, -25, -24, -5, -35]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-2, 1, 6, 0, 12],
     [120, 70, -5, 0, -60],
     [-120, -59, 25, 25, 60],
     [-14, -13, 5, -4, 29]
   ],
   ![
     [0, 0, 0, 0, 1],
     [10, 6, -3, -5, -5],
     [-40, -25, -24, -5, -35],
     [-14, -13, 5, -4, 29],
     [44, 25, 4, -5, 2]
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
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 5, 13]
 pdgood := []
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-6581250000000, -1856250000000, -421875000000, 151875000000]
 b := [6412500000000, 5028750000000, 675000000000, 84375000000, -30375000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 1, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 1, 1]],
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 0],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 1, 1, 1],![1, 1, 1, 0, 0],![1, 1, 0, 0, 1],![0, 1, 1, 0, 0],![0, 1, 0, 1, 1]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![-1, 154],![-142, 79],![64, 12],![-142, 78],![150, 98]]
 c := ![![14, -22, 52],![152, 68, 106],![-7, -50, 10],![152, 67, 106],![-136, -102, -41]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 2, 1, 0], [1, 1, 0, 0, 0], [1, 0, 0, 1, 1]],
![[0, 0, 1, 0, 0], [0, 0, 2, 1, 0], [1, 1, 1, 2, 0], [0, 1, 1, 0, 0], [2, 2, 0, 1, 1]],
![[0, 0, 0, 1, 0], [1, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [1, 2, 2, 2, 2]],
![[0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [2, 2, 0, 1, 1], [1, 2, 2, 2, 2], [2, 1, 1, 1, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 1, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![1, 1, 0, 0, 1]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 1, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![1, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 0, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![2, 1, 0, 0, 1],![1, 2, 1, 1, 1],![4, 8, 8, 4, 4],![4, 0, 8, 8, 4],![0, 4, 4, 4, 4]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![-8, -12],![69, 88],![495, 642],![519, 666],![249, 318]]
 c := ![![21, -15, 6],![-12, 21, 30],![-221, 234, 150],![-225, 262, 150],![-63, 90, 98]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [3, 1, 1, 0, 2], [0, 1, 2, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [3, 1, 1, 0, 2], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 2, 0, 1, 4]],
![[0, 0, 0, 0, 1], [0, 1, 2, 0, 0], [0, 0, 1, 0, 0], [1, 2, 0, 1, 4], [4, 0, 4, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 4],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 4],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![0, 1, 2, 3]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 2, 4, 3, 4],![8, 0, 16, 4, 12],![6, 2, 4, 0, 4],![12, 12, 8, 4, 12],![0, 0, 3, 0, 0]]
 w1 := ![1, 1, 0, 1]
 w2 := ![0]
 a := ![![-29, -25, -165, -165],
   ![-505, 204, -1100, -460],
   ![-165, 310, -318, -190],
   ![-125, 760, -400, -616],
   ![-150, -90, -285, -30]]
 c := ![![20],![245],![155],![325],![6]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide


/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3, 5]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 5] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF96
