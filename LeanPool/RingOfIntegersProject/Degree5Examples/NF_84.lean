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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible84

-- Number field with label 5.1.1012500000.3 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 210*X^2 - 540*X - 648
lemma T_def : T = X^5 - 15*X^3 - 210*X^2 - 540*X - 648 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-648, -540, -210, -15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/12*a^3 - 1/4*a^2, 1/72*a^4
-- + 1/24*a^2 + 1/3*a - 1/2]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  72
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![72, 0, 0, 0, 0],
   ![0, 72, 0, 0, 0],
   ![0, -36, 36, 0, 0],
   ![0, 0, -18, 6, 0],
   ![-36, 24, 3, 0, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![0, 1, 2, 6, 0],![3, -3, -2, -3, 6],![9, 11, 8, 3, 0]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 1, 2, 6, 0],
       ![9, -8, -4, -6, 18],
       ![21, 38, 23, 9, -12],
       ![0, 4, 12, 18, 9]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![3, -3, -2, -3, 6],
       ![21, 38, 23, 9, -12],
       ![-21, -25, -6, 10, 12],
       ![21, 7, 6, 1, 15]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![9, 11, 8, 3, 0],
       ![0, 4, 12, 18, 9],
       ![21, 7, 6, 1, 15],
       ![38, 43, 35, 21, 11]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-72]],
   ![[], [], [], [-216], [36, -36]],
   ![[], [], [-216], [216, -36], [-108, 18, -6]],
   ![[], [-72], [36, -36], [-108, 18, -6], [-258, -21, 0, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 1, 2, 6, 0], [3, -3, -2, -3, 6], [9, 11, 8, 3, 0]],
   ![
     [0, 0, 1, 0, 0],
     [0, 1, 2, 6, 0],
     [9, -8, -4, -6, 18],
     [21, 38, 23, 9, -12],
     [0, 4, 12, 18, 9]
   ],
   ![
     [0, 0, 0, 1, 0],
     [3, -3, -2, -3, 6],
     [21, 38, 23, 9, -12],
     [-21, -25, -6, 10, 12],
     [21, 7, 6, 1, 15]
   ],
   ![[0, 0, 0, 0, 1], [9, 11, 8, 3, 0], [0, 4, 12, 18, 9], [21, 7, 6, 1, 15], [38, 43, 35, 21, 11]]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [130, 109, 44, 5, 1]
 g := [2, 1]
 h := [1, 2, 4, 3, 1]
 a :=  [4]
 b :=  [3, 3, 3, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![17, 10, 8]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [-12713760000000, -1924560000000, -349920000000, 213840000000]
 b := [9657792000000, 7511616000000, 641520000000, 69984000000, -42768000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 0, 1, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]],
![[0, 0, 0, 1, 0], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 1]],
![[0, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 0, 0, 0, 1], [1, 1, 0, 1, 1], [0, 1, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 0, 0],![0, 1, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![1, 0, 1, 0, 0],![0, 1, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 1, 1, 1],![0, 1, 0, 1, 0],![0, 0, 0, 0, 1],![1, 1, 0, 1, 0],![1, 0, 1, 0, 1]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![19, 60],![4, 13],![14, 28],![4, 14],![18, 50]]
 c := ![![34, -12, 24],![4, -16, 12],![17, -4, 12],![4, -15, 12],![30, 0, 15]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

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
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [0, 1, 2, 0, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 2, 0, 0], [0, 1, 2, 0, 0], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 2, 0, 1, 0], [0, 1, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [2, 1, 2, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 2, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 2, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 2, 0]]
 v_ind := ![0, 1, 2]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![2, 4, 4, 2, 0],![0, 2, 4, 2, 0],![0, 2, 2, 2, 0],![1, 0, 1, 0, 2],![0, 2, 1, 0, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![98, 744, 672],![60, 728, 654],![96, 270, 332],![105, 516, 414],![18, 243, 177]]
 c := ![![156, 81],![144, 81],![42, 51],![151, 39],![63, 13]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide


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

