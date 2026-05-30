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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible92

-- Number field with label 5.1.1423828125.3 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 25*X^2 - 300*X - 960
lemma T_def : T = X^5 - 25*X^2 - 300*X - 960 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-960, -300, -25, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/7*a^3 - 2/7*a^2 + 3/7*a - 1/7,
-- 1/196*a^4 - 2/49*a^3 + 16/49*a^2 + 51/196*a + 19/49]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  196
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![196, 0, 0, 0, 0],
   ![0, 196, 0, 0, 0],
   ![0, 0, 196, 0, 0],
   ![-28, 84, -56, 28, 0],
   ![76, 51, 64, -8, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![1, -3, 2, 7, 0],
       ![-10, -10, -7, 6, 28],
       ![8, 4, 3, 0, -8]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![1, -3, 2, 7, 0],
       ![-68, -75, -48, 56, 196],
       ![157, 63, 18, -13, -56],
       ![-61, -33, -14, 21, 64]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-10, -10, -7, 6, 28],
       ![157, 63, 18, -13, -56],
       ![-92, -21, -5, 13, 40],
       ![62, 15, 3, -2, -11]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![8, 4, 3, 0, -8],
       ![-61, -33, -14, 21, 64],
       ![62, 15, 3, -2, -11],
       ![-28, -9, -3, 6, 17]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-196]],
   ![[], [], [], [-5488], [1568, -196]],
   ![[], [], [-5488], [3136, -784], [-2324, 280, -28]],
   ![[], [-196], [1568, -196], [-2324, 280, -28], [897, -192, 16, -1]]]
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
 ![
   ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, -3, 2, 7, 0], [-10, -10, -7, 6, 28], [8, 4, 3, 0, -8]],
   ![
     [0, 0, 1, 0, 0],
     [1, -3, 2, 7, 0],
     [-68, -75, -48, 56, 196],
     [157, 63, 18, -13, -56],
     [-61, -33, -14, 21, 64]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-10, -10, -7, 6, 28],
     [157, 63, 18, -13, -56],
     [-92, -21, -5, 13, 40],
     [62, 15, 3, -2, -11]
   ],
   ![
     [0, 0, 0, 0, 1],
     [8, 4, 3, 0, -8],
     [-61, -33, -14, 21, 64],
     [62, 15, 3, -2, -11],
     [-28, -9, -3, 6, 17]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := [2]
 b' := [2, 2]
 k := [0, 1]
 f := [320, 100, 9, 1, 1]
 g := [0, 2, 1]
 h := [0, 1, 1, 1]
 a :=  [2]
 b :=  [2, 2, 1]
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
 f := [192, 60, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [3]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![4, 6, 9, 6]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp7.out
 a := [-2995354687500, 694575000000, -130232812500, 21705468750]
 b := [651164062500, 664187343750, -138915000000, 26046562500, -4341093750]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
 n := 5
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 1, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1]],
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 0, 0],![0, 1, 1, 1, 0],![0, 1, 1, 0, 1]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 4, 2, 0, 0], [4, 4, 0, 6, 0], [1, 4, 3, 0, 6]],
![[0, 0, 1, 0, 0], [1, 4, 2, 0, 0], [2, 2, 1, 0, 0], [3, 0, 4, 1, 0], [2, 2, 0, 0, 1]],
![[0, 0, 0, 1, 0], [4, 4, 0, 6, 0], [3, 0, 4, 1, 0], [6, 0, 2, 6, 5], [6, 1, 3, 5, 3]],
![[0, 0, 0, 0, 1], [1, 4, 3, 0, 6], [2, 2, 0, 0, 1], [6, 1, 3, 5, 3], [0, 5, 4, 6, 3]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 4, 3, 0, 0],![0, 2, 3, 0, 0],![1, 4, 1, 4, 0],![6, 6, 2, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel

instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 7]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 7] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

