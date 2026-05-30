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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible65

namespace RoiDegree5ExamplesNF65
open RoiDegree5ExamplesIrreducible65

-- Number field with label 5.1.480000000.2 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 + 10*X^3 - 60*X^2 - 65*X - 228
lemma T_def : T = X^5 + 10*X^3 - 60*X^2 - 65*X - 228 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-228, -65, -60, 10, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/15*a^3 + 2/5*a^2 + 2/15*a + 1/5,
-- 1/15*a^4 - 4/15*a^2 + 2/5*a - 1/5]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  15
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![15, 0, 0, 0, 0],
   ![0, 15, 0, 0, 0],
   ![0, 0, 15, 0, 0],
   ![3, 2, 6, 1, 0],
   ![-3, 6, -4, 0, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![-3, -2, -6, 15, 0],
       ![-1, -1, -2, 6, 1],
       ![18, 6, 10, -14, 0]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![-3, -2, -6, 15, 0],
       ![3, -6, 4, 0, 15],
       ![18, 3, 9, -8, 6],
       ![-16, 12, -26, 66, -14]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-1, -1, -2, 6, 1],
       ![18, 3, 9, -8, 6],
       ![13, 4, 5, -2, 2],
       ![-20, -2, -16, 38, -1]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![18, 6, 10, -14, 0],
       ![-16, 12, -26, 66, -14],
       ![-20, -2, -16, 38, -1],
       ![98, 10, 62, -108, 17]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-15]],
   ![[], [], [], [-15], [0, -15]],
   ![[], [], [-15], [-12, -1], [12, -6, -1]],
   ![[], [-15], [0, -15], [12, -6, -1], [-72, 18, 0, -1]]]
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
   ![
     [0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0],
     [-3, -2, -6, 15, 0],
     [-1, -1, -2, 6, 1],
     [18, 6, 10, -14, 0]
   ],
   ![
     [0, 0, 1, 0, 0],
     [-3, -2, -6, 15, 0],
     [3, -6, 4, 0, 15],
     [18, 3, 9, -8, 6],
     [-16, 12, -26, 66, -14]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-1, -1, -2, 6, 1],
     [18, 3, 9, -8, 6],
     [13, 4, 5, -2, 2],
     [-20, -2, -16, 38, -1]
   ],
   ![
     [0, 0, 0, 0, 1],
     [18, 6, 10, -14, 0],
     [-16, 12, -26, 66, -14],
     [-20, -2, -16, 38, -1],
     [98, 10, 62, -108, 17]
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
def CD2 : CertificateDedekindCriterionLists l 2 where
 n := 4
 a' := []
 b' := [1]
 k := [0, 0, 0, 1]
 f := [114, 33, 31, -4, 1]
 g := [0, 1, 1]
 h := [1, 1, 1, 1]
 a :=  [1, 1, 1]
 b :=  [0, 1, 0, 0, 1]
 c :=  [1]
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![11, 5, 11]
 pdgood := [2]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-103500000000, 18000000000, -9000000000, 4500000000]
 b := [-10800000000, 60300000000, -7200000000, 1800000000, -900000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [2, 2, 1, 0, 1], [0, 0, 1, 1, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [2, 0, 1, 0, 1]],
![[0, 0, 0, 1, 0], [2, 2, 1, 0, 1], [0, 0, 0, 1, 0], [1, 1, 2, 1, 2], [1, 1, 2, 2, 2]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [2, 0, 1, 0, 1], [1, 1, 2, 2, 2], [2, 1, 2, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 2, 2, 2]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![2, 2, 1, 2, 0]]
 v := ![![1, 1, 2, 2, 2]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![2, 2, 1, 2, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 2]]
 v_ind := ![0]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![4, 0, 2, 4, 2],![0, 2, 2, 2, 2],![1, 0, 0, 2, 2],![2, 4, 2, 4, 4],![2, 2, 2, 4, 0]]
 w1 := ![1]
 w2 := ![0, 0, 1, 1]
 a := ![![203],![138],![-9],![138],![288]]
 c := ![![-87, -309, -318, 198],
   ![-302, -426, -402, 246],
   ![-222, -254, -234, 192],
   ![-612, -774, -709, 483],
   ![174, -126, -153, 41]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [2, 3, 4, 0, 0], [4, 4, 3, 1, 1], [3, 1, 0, 1, 0]],
![[0, 0, 1, 0, 0], [2, 3, 4, 0, 0], [3, 4, 4, 0, 0], [3, 3, 4, 2, 1], [4, 2, 4, 1, 1]],
![[0, 0, 0, 1, 0], [4, 4, 3, 1, 1], [3, 3, 4, 2, 1], [3, 4, 0, 3, 2], [0, 3, 4, 3, 4]],
![[0, 0, 0, 0, 1], [3, 1, 0, 1, 0], [4, 2, 4, 1, 1], [0, 3, 4, 3, 4], [3, 0, 2, 2, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 3],![0, 0, 1, 0, 4],![0, 0, 0, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 3],![0, 0, 1, 0, 4],![0, 0, 0, 1, 1]]
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
 g := ![![0, 4, 3, 3, 0],![2, 1, 3, 0, 1],![0, 1, 3, 2, 4],![2, 0, 2, 4, 1],![4, 4, 1, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![-1049, 430, -675, 2165],
   ![-1895, 416, -55, 720],
   ![-5285, 680, 1141, -1100],
   ![-580, 220, -410, 1506],
   ![-1520, 300, 100, 155]]
 c := ![![160],![490],![1580],![110],![396]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide


/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3, 5]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 5] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF65
