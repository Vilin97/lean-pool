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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible5

namespace RoiDegree5ExamplesNativeDecideNF5
open RoiDegree5ExamplesNativeDecideIrreducible5

-- Number field with label 5.1.3515625.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 + 10*X^3 - 15*X^2 + 10*X - 12
lemma T_def : T = X^5 + 10*X^3 - 15*X^2 + 10*X - 12 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-12, 10, -15, 10, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/22*a^4 + 2/11*a^3 + 2/11*a^2 +
-- 1/22*a - 4/11]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  22
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![22, 0, 0, 0, 0],
   ![0, 22, 0, 0, 0],
   ![0, 0, 22, 0, 0],
   ![0, 0, 0, 22, 0],
   ![-8, 1, 4, 4, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![8, -1, -4, -4, 22],![2, -1, 0, -1, 4]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 0, 1, 0],
       ![8, -1, -4, -4, 22],
       ![12, -10, 15, -10, 0],
       ![0, -1, 3, 0, -6]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![8, -1, -4, -4, 22],
       ![12, -10, 15, -10, 0],
       ![-80, 22, 30, 55, -220],
       ![-12, 6, -1, 9, -24]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![2, -1, 0, -1, 4],
       ![0, -1, 3, 0, -6],
       ![-12, 6, -1, 9, -24],
       ![-1, 1, -1, 1, -1]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-22]],
   ![[], [], [], [-484], [-88, -22]],
   ![[], [], [-484], [0, -484], [132, -88, -22]],
   ![[], [-22], [-88, -22], [132, -88, -22], [31, -14, -8, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide

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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [8, -1, -4, -4, 22], [2, -1, 0, -1, 4]],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 0, 1, 0],
     [8, -1, -4, -4, 22],
     [12, -10, 15, -10, 0],
     [0, -1, 3, 0, -6]
   ],
   ![
     [0, 0, 0, 1, 0],
     [8, -1, -4, -4, 22],
     [12, -10, 15, -10, 0],
     [-80, 22, 30, 55, -220],
     [-12, 6, -1, 9, -24]
   ],
   ![
     [0, 0, 0, 0, 1],
     [2, -1, 0, -1, 4],
     [0, -1, 3, 0, -6],
     [-12, 6, -1, 9, -24],
     [-1, 1, -1, 1, -1]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

/-- Auxiliary declaration for the worked example. -/
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := []
 b' := [2]
 k := [0, 1]
 f := [4, -2, 5, -2]
 g := [0, 2, 0, 1]
 h := [2, 0, 1]
 a :=  [1, 2, 2]
 b :=  [0, 0, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [3, 0, 6, 0, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a :=  [2]
 b :=  [0, 0, 1, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 11] where
 n := 4
 p := ![2, 3, 5, 11]
 exp := ![2, 2, 8, 2]
 pdgood := [3, 5]
 hsub := by decide
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp11.out
 a := [-168750000, -10312500, -26718750, 2343750]
 b := [-32343750, 59343750, 187500, 5343750, -468750]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
 n := 5
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0]],
![[0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [1, 1, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0],![1, 1, 1, 1, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by
  intro i
  fin_cases i <;>
    norm_num [nPow_sq_table, table_mul_list, List.mulPointwise, List.addPointwise,
      List.replicate,
      instAddListOfAddMonoid_leanPool, CharP.cast_eq_mod]
  decide +kernel
/-- Auxiliary declaration for the worked example. -/
noncomputable def M11 : MaximalOrderCertificateOfUnramifiedLists 11 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [8, 10, 7, 7, 0], [2, 10, 0, 10, 4]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [8, 10, 7, 7, 0], [1, 1, 4, 1, 0], [0, 10, 3, 0, 5]],
![[0, 0, 0, 1, 0], [8, 10, 7, 7, 0], [1, 1, 4, 1, 0], [8, 0, 8, 0, 0], [10, 6, 10, 9, 9]],
![[0, 0, 0, 0, 1], [2, 10, 0, 10, 4], [0, 10, 3, 0, 5], [10, 6, 10, 9, 9], [10, 1, 10, 1, 10]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![8, 6, 10, 6, 0],![0, 0, 1, 0, 0],![9, 7, 3, 5, 0],![5, 7, 0, 6, 10]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by
  intro i
  fin_cases i <;>
    norm_num [nPow_sq_table, table_mul_list, List.mulPointwise, List.addPointwise,
      List.replicate,
      instAddListOfAddMonoid_leanPool, CharP.cast_eq_mod] <;>
    decide +kernel

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 11]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 11 O Om hm M11
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 11] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF5
