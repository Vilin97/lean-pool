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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible94

namespace RoiDegree5ExamplesNF94
open RoiDegree5ExamplesIrreducible94

-- Number field with label 5.3.1687500000.3 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 + 25*X^3 - 200*X^2 + 300*X - 80
lemma T_def : T = X^5 + 25*X^3 - 200*X^2 + 300*X - 80 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-80, 300, -200, 25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/172*a^4 + 10/43*a^3 +
-- 77/172*a^2 - 11/43*a - 21/43]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  172
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![172, 0, 0, 0, 0],
   ![0, 172, 0, 0, 0],
   ![0, 0, 172, 0, 0],
   ![0, -86, 0, 86, 0],
   ![-84, -44, 77, 40, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![42, 2, -39, -40, 86],
       ![20, -1, -17, -18, 40]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 1, 0, 2, 0],
       ![84, 4, -77, -80, 172],
       ![40, -163, 100, -26, 0],
       ![44, -73, 21, -34, 52]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![42, 2, -39, -40, 86],
       ![40, -163, 100, -26, 0],
       ![-567, 43, 445, 640, -1161],
       ![-204, -27, 193, 242, -442]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![20, -1, -17, -18, 40],
       ![44, -73, 21, -34, 52],
       ![-204, -27, 193, 242, -442],
       ![-60, -35, 77, 82, -147]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-172]],
   ![[], [], [], [-14792], [-6880, -172]],
   ![[], [], [-14792], [0, -7396], [-4386, -3440, -86]],
   ![[], [-172], [-6880, -172], [-4386, -3440, -86], [-4272, -1729, -80, -1]]]
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
     [0, 1, 0, 2, 0],
     [42, 2, -39, -40, 86],
     [20, -1, -17, -18, 40]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 1, 0, 2, 0],
     [84, 4, -77, -80, 172],
     [40, -163, 100, -26, 0],
     [44, -73, 21, -34, 52]
   ],
   ![
     [0, 0, 0, 1, 0],
     [42, 2, -39, -40, 86],
     [40, -163, 100, -26, 0],
     [-567, 43, 445, 640, -1161],
     [-204, -27, 193, 242, -442]
   ],
   ![
     [0, 0, 0, 0, 1],
     [20, -1, -17, -18, 40],
     [44, -73, 21, -34, 52],
     [-204, -27, 193, 242, -442],
     [-60, -35, 77, 82, -147]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := [1]
 b' := [0, 2, 1]
 k := [1, 0, 2, 0, 1]
 f := [27, -99, 68, -7, 1]
 g := [1, 1, 1, 1]
 h := [1, 2, 1]
 a :=  [0, 1, 2]
 b :=  [1, 2, 0, 1]
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
 f := [16, -60, 40, -5]
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
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 43] where
 n := 4
 p := ![2, 3, 5, 43]
 exp := ![11, 3, 9, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp43.out
 a := [6349725000000, -2035012500000, -158625000000, -116437500000]
 b := [2358900000000, -3747195000000, 639877500000, 31725000000, 23287500000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 1, 1, 0, 1], [0, 1, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 0, 1, 0, 1],![1, 1, 0, 1, 1],![1, 0, 0, 1, 0],![0, 0, 0, 0, 1],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-189, 288],![-1632, 809],![-1344, 622],![-414, 240],![350, -6]]
 c := ![![-46, 146, -472],
   ![-810, 1276, -1816],
   ![-671, 1042, -1422],
   ![-198, 325, -514],
   ![210, -270, 161]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M43 : MaximalOrderCertificateOfUnramifiedLists 43 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
     ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [42, 2, 4, 3, 0], [20, 42, 26, 25, 40]],
     ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [41, 4, 9, 6, 0], [40, 9, 14, 17, 0], [1, 13, 21, 9, 9]],
     ![
       [0, 0, 0, 1, 0],
       [42, 2, 4, 3, 0],
       [40, 9, 14, 17, 0],
       [35, 0, 15, 38, 0],
       [11, 16, 21, 27, 31]
     ],
     ![
       [0, 0, 0, 0, 1],
       [20, 42, 26, 25, 40],
       [1, 13, 21, 9, 9],
       [11, 16, 21, 27, 31],
       [26, 8, 34, 39, 25]
     ]
   ]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],
   ![15, 7, 0, 32, 0],
   ![13, 31, 1, 22, 0],
   ![7, 20, 0, 36, 0],
   ![35, 18, 41, 2, 42]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 43]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 43 O Om hm M43
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 43] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF94
