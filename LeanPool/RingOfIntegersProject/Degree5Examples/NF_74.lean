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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible74

-- Number field with label 5.3.675000000.2 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 50*X^2 + 800
lemma T_def : T = X^5 - 25*X^3 - 50*X^2 + 800 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [800, 0, -50, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/10*a^3 - 1/2*a, 1/120*a^4 - 1/30*a^3 +
-- 1/8*a^2 + 1/12*a - 1/3]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  120
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![120, 0, 0, 0, 0],
   ![0, 120, 0, 0, 0],
   ![0, 0, 120, 0, 0],
   ![0, -60, 0, 12, 0],
   ![-40, 10, 15, -4, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 5, 0, 10, 0],![4, 1, -2, 4, 12],![-8, 1, 1, 2, -4]],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 5, 0, 10, 0],
       ![40, 10, -15, 40, 120],
       ![-80, 10, 5, 20, 0],
       ![40, -5, -7, 10, 40]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![4, 1, -2, 4, 12],
       ![-80, 10, 5, 20, 0],
       ![6, -4, -2, 11, 18],
       ![-24, 5, 1, 4, -2]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-8, 1, 1, 2, -4],
       ![40, -5, -7, 10, 40],
       ![-24, 5, 1, 4, -2],
       ![18, -4, -2, 2, 12]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-120]],
   ![[], [], [], [-1440], [480, -120]],
   ![[], [], [-1440], [0, -144], [-420, 48, -12]],
   ![[], [-120], [480, -120], [-420, 48, -12], [250, -71, 8, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 5, 0, 10, 0], [4, 1, -2, 4, 12], [-8, 1, 1, 2, -4]],
   ![
     [0, 0, 1, 0, 0],
     [0, 5, 0, 10, 0],
     [40, 10, -15, 40, 120],
     [-80, 10, 5, 20, 0],
     [40, -5, -7, 10, 40]
   ],
   ![
     [0, 0, 0, 1, 0],
     [4, 1, -2, 4, 12],
     [-80, 10, 5, 20, 0],
     [6, -4, -2, 11, 18],
     [-24, 5, 1, 4, -2]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-8, 1, 1, 2, -4],
     [40, -5, -7, 10, 40],
     [-24, 5, 1, 4, -2],
     [18, -4, -2, 2, 12]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 5, 12]
 pdgood := []
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [1215000000000, -118125000000, -67500000000, -10125000000]
 b := [-945000000000, -438750000000, 3375000000, 13500000000, 2025000000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 1, 0, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 4]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 1, 1, 0],![1, 1, 1, 0, 0],![0, 0, 1, 1, 1],![0, 1, 1, 0, 0],![0, 1, 0, 1, 0]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![-7, 58],![-4, 37],![-10, 66],![-4, 36],![0, 18]]
 c := ![![8, 10, 22],![16, 6, 16],![13, 10, 24],![16, 5, 16],![-12, 4, 7]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 1, 2, 2]],
![[0, 0, 1, 0, 0], [0, 2, 0, 1, 0], [1, 1, 0, 1, 0], [1, 1, 2, 2, 0], [1, 1, 2, 1, 1]],
![[0, 0, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 2, 2, 0], [0, 2, 1, 2, 0], [0, 2, 1, 1, 1]],
![[0, 0, 0, 0, 1], [1, 1, 1, 2, 2], [1, 1, 2, 1, 1], [0, 2, 1, 1, 1], [0, 2, 1, 2, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 2, 0, 0, 2]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 2, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 0, 0, 1, 2]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 2, 2, 1, 2],![0, 1, 1, 2, 2],![2, 4, 2, 4, 2],![0, 0, 1, 2, 0],![0, 0, 0, 1, 2]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![-35, 375],![-24, 292],![-33, 570],![-21, 228],![-9, 102]]
 c := ![![84, 327, -222],![0, 234, -159],![-67, 402, -273],![-21, 172, -114],![-3, 90, -62]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [4, 1, 3, 4, 2], [2, 1, 1, 2, 1]],
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 3, 0, 0]],
![[0, 0, 0, 1, 0], [4, 1, 3, 4, 2], [0, 0, 0, 0, 0], [1, 1, 3, 1, 3], [1, 0, 1, 4, 3]],
![[0, 0, 0, 0, 1], [2, 1, 1, 2, 1], [0, 0, 3, 0, 0], [1, 0, 1, 4, 3], [3, 1, 3, 2, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 3],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 3],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
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
 g := ![![1, 4, 0, 3, 0],![2, 4, 2, 4, 1],![3, 2, 2, 3, 4],![4, 3, 3, 4, 0],![0, 0, 1, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![-9, 135, 35, 190],
   ![180, 146, -30, 410],
   ![265, 45, -79, 390],
   ![240, 150, -50, 456],
   ![80, 0, -30, 80]]
 c := ![![-105],![-90],![-15],![-80],![16]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide


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

