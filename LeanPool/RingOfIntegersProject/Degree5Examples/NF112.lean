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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible112

namespace RoiDegree5ExamplesNF112
open RoiDegree5ExamplesIrreducible112

-- Number field with label 5.1.3037500000.7 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 100*X^2 + 750*X + 2200
lemma T_def : T = X^5 - 25*X^3 - 100*X^2 + 750*X + 2200 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [2200, 750, -100, -25, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/5*a^3, 1/1110*a^4 - 34/555*a^3 -
-- 19/74*a^2 + 41/111*a - 49/111]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1110
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1110, 0, 0, 0, 0],
   ![0, 1110, 0, 0, 0],
   ![0, 0, 1110, 0, 0],
   ![0, 0, 0, 222, 0],
   ![-490, 410, -285, -68, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 0, 0, 5, 0],
       ![98, -82, 57, 68, 222],
       ![-32, 24, -17, -22, -68]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 0, 5, 0],
       ![490, -410, 285, 340, 1110],
       ![-440, -150, 20, 25, 0],
       ![20, 140, -74, -85, -260]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![98, -82, 57, 68, 222],
       ![-440, -150, 20, 25, 0],
       ![490, -498, 255, 360, 1110],
       ![-2, 150, -57, -86, -238]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-32, 24, -17, -22, -68],
       ![20, 140, -74, -85, -260],
       ![-2, 150, -57, -86, -238],
       ![-20, -67, 27, 36, 101]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-1110]],
   ![[], [], [], [-246420], [75480, -1110]],
   ![[], [], [-246420], [0, -49284], [57720, 15096, -222]],
   ![[], [-1110], [75480, -1110], [57720, 15096, -222], [-36280, -4079, 136, -1]]]
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
     [0, 0, 0, 5, 0],
     [98, -82, 57, 68, 222],
     [-32, 24, -17, -22, -68]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 0, 5, 0],
     [490, -410, 285, 340, 1110],
     [-440, -150, 20, 25, 0],
     [20, 140, -74, -85, -260]
   ],
   ![
     [0, 0, 0, 1, 0],
     [98, -82, 57, 68, 222],
     [-440, -150, 20, 25, 0],
     [490, -498, 255, 360, 1110],
     [-2, 150, -57, -86, -238]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-32, 24, -17, -22, -68],
     [20, 140, -74, -85, -260],
     [-2, 150, -57, -86, -238],
     [-20, -67, 27, 36, 101]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [37, 2, 3, 5] where
 n := 4
 p := ![2, 3, 5, 37]
 exp := ![7, 7, 12, 2]
 pdgood := []
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp37.out
 a := [13516875000000, 4923281250000, 2075625000000, -559406250000]
 b := [85100625000000, -5265000000000, -2103468750000, -415125000000, 111881250000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp

/-- Auxiliary declaration for the worked example. -/
noncomputable def M37 : MaximalOrderCertificateOfUnramifiedLists 37 O Om hm where
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
     ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 5, 0], [24, 29, 20, 31, 0], [5, 24, 20, 15, 6]],
     ![
       [0, 0, 1, 0, 0],
       [0, 0, 0, 5, 0],
       [9, 34, 26, 7, 0],
       [4, 35, 20, 25, 0],
       [20, 29, 0, 26, 36]
     ],
     ![
       [0, 0, 0, 1, 0],
       [24, 29, 20, 31, 0],
       [4, 35, 20, 25, 0],
       [9, 20, 33, 27, 0],
       [35, 2, 17, 25, 21]
     ],
     ![
       [0, 0, 0, 0, 1],
       [5, 24, 20, 15, 6],
       [20, 29, 0, 26, 36],
       [35, 2, 17, 25, 21],
       [17, 7, 27, 36, 27]
     ]
   ]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],
   ![18, 31, 22, 11, 0],
   ![23, 26, 25, 12, 0],
   ![16, 2, 36, 19, 0],
   ![13, 34, 20, 10, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 1, 0, 1],![0, 1, 1, 1, 0],![0, 0, 1, 0, 1],![0, 1, 0, 0, 1],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![19, 206],![352, 1145],![-6, 88],![-60, -122],![328, 1028]]
 c := ![![-136, 308, -496],
   ![320, 2220, -3528],
   ![-235, 86, -182],
   ![58, -247, 452],
   ![222, 1998, -3213]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 2, 0], [2, 2, 0, 2, 0], [1, 0, 1, 2, 1]],
![[0, 0, 1, 0, 0], [0, 0, 0, 2, 0], [1, 1, 0, 1, 0], [1, 0, 2, 1, 0], [2, 2, 1, 2, 1]],
![[0, 0, 0, 1, 0], [2, 2, 0, 2, 0], [1, 0, 2, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 1, 2]],
![[0, 0, 0, 0, 1], [1, 0, 1, 2, 1], [2, 2, 1, 2, 1], [1, 0, 0, 1, 2], [1, 2, 0, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 2, 0, 1],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![2, 1, 2, 0, 0],![0, 2, 1, 1, 0],![0, 0, 1, 0, 1],![1, 1, 1, 0, 0],![2, 0, 2, 2, 2]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![628, 1560],![708, 1786],![135, 330],![330, 819],![966, 2442]]
 c := ![![-2922, 1554, -1371],
   ![-3444, 1776, -1602],
   ![-587, 330, -282],
   ![-1524, 814, -717],
   ![-4758, 2436, -2204]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [3, 3, 2, 3, 2], [3, 4, 3, 3, 2]],
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [3, 3, 2, 3, 2], [0, 0, 0, 0, 0], [0, 2, 0, 0, 0], [3, 0, 3, 4, 2]],
![[0, 0, 0, 0, 1], [3, 4, 3, 3, 2], [0, 0, 1, 0, 0], [3, 0, 3, 4, 2], [0, 3, 2, 1, 1]]]
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
 g := ![![6, 4, 4, 0, 6],![4, 4, 4, 8, 6],![2, 2, 8, 2, 8],![2, 0, 4, 4, 6],![0, 0, 2, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![-73, 390, -180, -90],
   ![-1535, 3332, -1390, -2050],
   ![-195, 1310, -338, -320],
   ![-535, 1450, -520, -738],
   ![35, 300, -10, 10]]
 c := ![![265],![-5],![615],![175],![221]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
 hacindw := by decide


/-- Auxiliary declaration for the worked example. -/
instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [37, 2, 3, 5]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 37 O Om hm M37
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateWLists 5 O Om hm M5
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [37, 2, 3, 5] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF112
