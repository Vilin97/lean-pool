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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible1

namespace RoiDegree5ExamplesNativeDecideNF1
open RoiDegree5ExamplesNativeDecideIrreducible1

-- Number field with label 5.5.390625.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 10*X^3 - 5*X^2 + 10*X - 1
lemma T_def : T = X^5 - 10*X^3 - 5*X^2 + 10*X - 1 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-1, 10, -5, -10, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/7*a^4 - 3/7*a^3 - 1/7*a^2 - 2/7*a
-- + 2/7]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  7
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, -2, -1, -3, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-2, 2, 1, 3, 7],![1, -2, 0, 0, -3]],
     ![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-2, 2, 1, 3, 7],![1, -10, 5, 10, 0],![-3, 7, -2, 0, 9]],
     ![
       ![0, 0, 0, 1, 0],
       ![-2, 2, 1, 3, 7],
       ![1, -10, 5, 10, 0],
       ![-20, 21, 0, 35, 70],
       ![9, -21, 7, -2, -27]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![1, -2, 0, 0, -3],
       ![-3, 7, -2, 0, 9],
       ![9, -21, 7, -2, -27],
       ![-7, 17, -6, 1, 21]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-7]],
   ![[], [], [], [-49], [21, -7]],
   ![[], [], [-49], [0, -49], [-63, 21, -7]],
   ![[], [-7], [21, -7], [-63, 21, -7], [53, -17, 6, -1]]]
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
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-2, 2, 1, 3, 7], [1, -2, 0, 0, -3]],
   ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-2, 2, 1, 3, 7], [1, -10, 5, 10, 0], [-3, 7, -2, 0, 9]],
   ![
     [0, 0, 0, 1, 0],
     [-2, 2, 1, 3, 7],
     [1, -10, 5, 10, 0],
     [-20, 21, 0, 35, 70],
     [9, -21, 7, -2, -27]
   ],
   ![
     [0, 0, 0, 0, 1],
     [1, -2, 0, 0, -3],
     [-3, 7, -2, 0, 9],
     [9, -21, 7, -2, -27],
     [-7, 17, -6, 1, 21]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [1, -1, 2, 3, 1]
 g := [4, 1]
 h := [1, 1, 1, 1, 1]
 a :=  [1]
 b :=  [0, 4, 1, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
 n := 2
 p := ![5, 7]
 exp := ![8, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp5.out
  · exact hp7.out
 a := [6640625, 12656250, -78125, -2343750]
 b := [2578125, -2796875, -4406250, 15625, 468750]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [5, 2, 1, 3, 0], [1, 5, 0, 0, 4]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [5, 2, 1, 3, 0], [1, 4, 5, 3, 0], [4, 0, 5, 0, 2]],
![[0, 0, 0, 1, 0], [5, 2, 1, 3, 0], [1, 4, 5, 3, 0], [1, 0, 0, 0, 0], [2, 0, 0, 5, 1]],
![[0, 0, 0, 0, 1], [1, 5, 0, 0, 4], [4, 0, 5, 0, 2], [2, 0, 0, 5, 1], [0, 3, 1, 1, 0]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF1
