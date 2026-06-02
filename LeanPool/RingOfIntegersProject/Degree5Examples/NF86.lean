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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible86

namespace RoiDegree5ExamplesNF86
open RoiDegree5ExamplesIrreducible86

-- Number field with label 5.3.1125000000.3 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 150*X^2 + 100*X + 120
lemma T_def : T = X^5 - 25*X^3 - 150*X^2 + 100*X + 120 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [120, 100, -150, -25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/12*a^3 - 5/12*a - 1/2, 1/96*a^4 -
-- 1/48*a^3 + 43/96*a^2 - 11/24*a - 3/8]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  96
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![96, 0, 0, 0, 0],
   ![0, 96, 0, 0, 0],
   ![0, 0, 96, 0, 0],
   ![-48, -40, 0, 8, 0],
   ![-36, -44, 43, -2, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![6, 5, 0, 12, 0],![4, 4, -4, 2, 8],![2, 1, 2, 8, -2]],
     ![
       ![0, 0, 1, 0, 0],
       ![6, 5, 0, 12, 0],
       ![48, 54, -43, 24, 96],
       ![0, 0, 12, 20, 0],
       ![40, 42, -35, 24, 68]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![4, 4, -4, 2, 8],
       ![0, 0, 12, 20, 0],
       ![11, 10, -5, 14, 10],
       ![1, 2, 6, 11, 5]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![2, 1, 2, 8, -2],
       ![40, 42, -35, 24, 68],
       ![1, 2, 6, 11, 5],
       ![30, 30, -24, 22, 43]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-96]],
   ![[], [], [], [-768], [192, -96]],
   ![[], [], [-768], [0, -64], [-504, 16, -8]],
   ![[], [-96], [192, -96], [-504, 16, -8], [210, -115, 4, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [6, 5, 0, 12, 0], [4, 4, -4, 2, 8], [2, 1, 2, 8, -2]],
   ![
     [0, 0, 1, 0, 0],
     [6, 5, 0, 12, 0],
     [48, 54, -43, 24, 96],
     [0, 0, 12, 20, 0],
     [40, 42, -35, 24, 68]
   ],
   ![[0, 0, 0, 1, 0], [4, 4, -4, 2, 8], [0, 0, 12, 20, 0], [11, 10, -5, 14, 10], [1, 2, 6, 11, 5]],
   ![
     [0, 0, 0, 0, 1],
     [2, 1, 2, 8, -2],
     [40, 42, -35, 24, 68],
     [1, 2, 6, 11, 5],
     [30, 30, -24, 22, 43]
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
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-24, -20, 30, 5]
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
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![20, 6, 9]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [10227600000000, 2478600000000, 10800000000, -178200000000]
 b := [2656800000000, -5231520000000, -852120000000, -2160000000, 35640000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 1, 0, 0], [1, 0, 0, 1, 1]],
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 v := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 0, 1]]
 vInd := ![0, 1]
 wInd := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 0, 1, 0],![0, 0, 0, 1, 1],![0, 1, 0, 1, 1],![0, 1, 1, 0, 0],![1, 1, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![81, -54],![192, -275],![234, -316],![170, -310],![124, -94]]
 c := ![![-32, 36, 14],![-16, 220, 128],![-27, 250, 130],![16, 263, 166],![-42, 66, 17]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 0, 0, 0], [1, 1, 2, 2, 2], [2, 1, 2, 2, 1]],
![[0, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 2, 0, 0], [0, 0, 0, 2, 0], [1, 0, 1, 0, 2]],
![[0, 0, 0, 1, 0], [1, 1, 2, 2, 2], [0, 0, 0, 2, 0], [2, 1, 1, 2, 1], [1, 2, 0, 2, 2]],
![[0, 0, 0, 0, 1], [2, 1, 2, 2, 1], [1, 0, 1, 0, 2], [1, 2, 0, 2, 2], [0, 0, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 1, 2],![0, 1, 1, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![1, 0, 2, 1, 2],![0, 1, 1, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0]]
 vInd := ![0, 1]
 wInd := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 0, 1, 0],![2, 0, 2, 2, 0],![4, 2, 2, 0, 4],![2, 0, 4, 2, 4],![8, 8, 0, 0, 4]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![25, 84],![762, 76],![1758, -57],![2496, -69],![1110, 291]]
 c := ![![6, -15, -21],![24, 276, -678],![110, 753, -1659],![102, 1025, -2295],![186, 459, -1157]]
 hmulw := by decide +kernel
 acIndw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide


/-- Auxiliary declaration for the worked example. -/
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

end RoiDegree5ExamplesNF86
