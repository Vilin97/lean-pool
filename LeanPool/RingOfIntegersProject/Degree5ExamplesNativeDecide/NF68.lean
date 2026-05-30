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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible68

namespace RoiDegree5ExamplesNativeDecideNF68
open RoiDegree5ExamplesNativeDecideIrreducible68

-- Number field with label 5.1.632812500.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 1200
lemma T_def : T = X^5 - 25*X^3 - 1200 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-1200, 0, 0, -25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/10*a^3 - 1/2*a, 1/140*a^4 +
-- 3/70*a^3 + 5/28*a^2 - 3/7*a + 3/7]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  140
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![140, 0, 0, 0, 0],
   ![0, 140, 0, 0, 0],
   ![0, -70, 70, 0, 0],
   ![0, -70, 0, 14, 0],
   ![60, -60, 25, 6, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![0, 2, -1, 5, 0],![-6, 0, -6, -6, 14],![6, 2, -3, 1, 6]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 2, -1, 5, 0],
       ![-15, -1, -12, -20, 35],
       ![63, 5, 3, 13, -7],
       ![12, 6, -7, -8, 22]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-6, 0, -6, -6, 14],
       ![63, 5, 3, 13, -7],
       ![-9, 13, -7, -9, 21],
       ![36, 10, 0, 5, 6]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![6, 2, -3, 1, 6],
       ![12, 6, -7, -8, 22],
       ![36, 10, 0, 5, 6],
       ![21, 11, -5, -3, 20]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-140]],
   ![[], [], [], [-980], [-350, -70]],
   ![[], [], [-980], [0, -196], [-630, -84, -14]],
   ![[], [-140], [-350, -70], [-630, -84, -14], [-480, -111, -12, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 2, -1, 5, 0], [-6, 0, -6, -6, 14], [6, 2, -3, 1, 6]],
   ![
     [0, 0, 1, 0, 0],
     [0, 2, -1, 5, 0],
     [-15, -1, -12, -20, 35],
     [63, 5, 3, 13, -7],
     [12, 6, -7, -8, 22]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-6, 0, -6, -6, 14],
     [63, 5, 3, 13, -7],
     [-9, 13, -7, -9, 21],
     [36, 10, 0, 5, 6]
   ],
   ![
     [0, 0, 0, 0, 1],
     [6, 2, -3, 1, 6],
     [12, 6, -7, -8, 22],
     [36, 10, 0, 5, 6],
     [21, 11, -5, -3, 20]
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
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := []
 b' := [2]
 k := [1, 0, 1, 0, 1]
 f := [400, 0, 0, 9]
 g := [0, 2, 0, 1]
 h := [0, 0, 1]
 a :=  [1]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 5, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![10, 4, 13, 2]
 pdgood := [3]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp7.out
 a := [-4134375000000, 0, -84375000000, 45000000000]
 b := [1350000000000, 658125000000, 90000000000, 16875000000, -9000000000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3

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
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 0], [0, 0, 1, 1, 0]],
![[0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 1, 1], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [0, 0, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 1, 1, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 1, 1, 0, 1],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![1, 1, 1, 0, 1],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 1, 0]]
 v_ind := ![0, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 0, 1, 0],![0, 1, 1, 1, 1],![1, 0, 1, 1, 1],![0, 1, 0, 0, 0],![0, 0, 1, 1, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![63, -24],![76, 5],![62, 12],![14, -6],![42, 4]]
 c := ![![-44, -22, -42],![4, -18, -50],![15, -12, -42],![-10, -5, -8],![0, -10, -29]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 2, 4, 0, 0], [4, 0, 4, 4, 4], [1, 2, 2, 1, 1]],
![[0, 0, 1, 0, 0], [0, 2, 4, 0, 0], [0, 4, 3, 0, 0], [3, 0, 3, 3, 3], [2, 1, 3, 2, 2]],
![[0, 0, 0, 1, 0], [4, 0, 4, 4, 4], [3, 0, 3, 3, 3], [1, 3, 3, 1, 1], [1, 0, 0, 0, 1]],
![[0, 0, 0, 0, 1], [1, 2, 2, 1, 1], [2, 1, 3, 2, 2], [1, 0, 0, 0, 1], [1, 1, 0, 2, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![0, 1, 2, 3]
 w_ind := ![0]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![4, 2, 1, 2, 3],![1, 0, 3, 3, 1],![1, 2, 4, 0, 1],![2, 3, 4, 0, 3],![0, 1, 2, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![261, 120, -65, -5],
   ![265, 86, -65, -25],
   ![295, 70, -74, -90],
   ![410, 120, -105, -104],
   ![120, 25, -30, -40]]
 c := ![![15],![10],![-50],![-55],![-24]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
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
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 2, 6, 5, 0], [1, 0, 1, 1, 0], [6, 2, 4, 1, 6]],
![[0, 0, 1, 0, 0], [0, 2, 6, 5, 0], [6, 6, 2, 1, 0], [0, 5, 3, 6, 0], [5, 6, 0, 6, 1]],
![[0, 0, 0, 1, 0], [1, 0, 1, 1, 0], [0, 5, 3, 6, 0], [5, 6, 0, 5, 0], [1, 3, 0, 5, 6]],
![[0, 0, 0, 0, 1], [6, 2, 4, 1, 6], [5, 6, 0, 6, 1], [1, 3, 0, 5, 6], [0, 4, 2, 4, 6]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],![1, 2, 4, 4, 0],![5, 6, 0, 5, 0],![6, 5, 3, 5, 0],![6, 2, 6, 4, 6]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 5, 7]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 5, 7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF68
