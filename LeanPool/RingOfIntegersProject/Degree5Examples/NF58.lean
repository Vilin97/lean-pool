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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible58

namespace RoiDegree5ExamplesNF58
open RoiDegree5ExamplesIrreducible58

-- Number field with label 5.3.379687500.2 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 10*X^2 - 240*X + 492
lemma T_def : T = X^5 - 15*X^3 - 10*X^2 - 240*X + 492 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [492, -240, -10, -15, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/796*a^4 - 67/796*a^3
-- + 24/199*a^2 + 81/199*a + 85/199]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  796
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![796, 0, 0, 0, 0],
   ![0, 796, 0, 0, 0],
   ![0, 0, 796, 0, 0],
   ![0, 0, -398, 398, 0],
   ![340, 324, 96, -67, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![-170, -162, -15, 66, 398],
       ![28, 28, 3, -11, -67]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![-340, -324, -29, 134, 796],
       ![-76, 282, 27, -52, -398],
       ![-6, -66, -5, 17, 111]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-170, -162, -15, 66, 398],
       ![-76, 282, 27, -52, -398],
       ![-1114, -1539, -66, 526, 3184],
       ![112, 207, 6, -63, -391]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![28, 28, 3, -11, -67],
       ![-6, -66, -5, 17, 111],
       ![112, 207, 6, -63, -391],
       ![-8, -27, 0, 7, 45]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-796]],
   ![[], [], [], [-316808], [53332, -796]],
   ![[], [], [-316808], [316808, -158404], [-70844, 27064, -398]],
   ![[], [-796], [53332, -796], [-70844, 27064, -398], [14216, -4696, 134, -1]]]
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
     [0, 0, 1, 2, 0],
     [-170, -162, -15, 66, 398],
     [28, 28, 3, -11, -67]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 1, 2, 0],
     [-340, -324, -29, 134, 796],
     [-76, 282, 27, -52, -398],
     [-6, -66, -5, 17, 111]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-170, -162, -15, 66, 398],
     [-76, 282, 27, -52, -398],
     [-1114, -1539, -66, 526, 3184],
     [112, 207, 6, -63, -391]
   ],
   ![
     [0, 0, 0, 0, 1],
     [28, 28, 3, -11, -67],
     [-6, -66, -5, 17, 111],
     [112, 207, 6, -63, -391],
     [-8, -27, 0, 7, 45]
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
instance hp199 : Fact (Nat.Prime 199) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := [2]
 b' := [2, 2]
 k := [0, 1]
 f := [-164, 80, 4, 6, 1]
 g := [0, 2, 1]
 h := [0, 1, 1, 1]
 a :=  [1, 1]
 b :=  [0, 0, 1, 2]
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
 f := [-98, 49, 4, 5, 1]
 g := [2, 1]
 h := [1, 2, 4, 3, 1]
 a :=  [1]
 b :=  [2, 2, 2, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 199] where
 n := 4
 p := ![2, 3, 5, 199]
 exp := ![8, 5, 8, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp199.out
 a := [1022625000000, 237060000000, -101722500000, -42187500000]
 b := [-1913220000000, -377217000000, -98037000000, 20344500000, 8437500000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 1]],
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 1, 1, 1],![1, 1, 1, 0, 1],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 w1 := ![1, 0]
 w2 := ![1, 1, 1]
 a := ![![753, -88],![-108, 41],![48, -4],![-32, 24],![736, -108]]
 c := ![![-852, -3096, 1924],
   ![18, 498, -272],
   ![-57, -208, 132],
   ![-44, 179, -88],
   ![-752, -3068, 1879]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def M199 : MaximalOrderCertificateOfUnramifiedLists 199 O Om hm where
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
     ![
       [0, 1, 0, 0, 0],
       [0, 0, 1, 0, 0],
       [0, 0, 1, 2, 0],
       [29, 37, 184, 66, 0],
       [28, 28, 3, 188, 132]
     ],
     ![
       [0, 0, 1, 0, 0],
       [0, 0, 1, 2, 0],
       [58, 74, 170, 134, 0],
       [123, 83, 27, 147, 0],
       [193, 133, 194, 17, 111]
     ],
     ![
       [0, 0, 0, 1, 0],
       [29, 37, 184, 66, 0],
       [123, 83, 27, 147, 0],
       [80, 53, 133, 128, 0],
       [112, 8, 6, 136, 7]
     ],
     ![
       [0, 0, 0, 0, 1],
       [28, 28, 3, 188, 132],
       [193, 133, 194, 17, 111],
       [112, 8, 6, 136, 7],
       [191, 172, 0, 7, 45]
     ]
   ]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],
   ![192, 144, 167, 143, 0],
   ![65, 6, 156, 92, 0],
   ![162, 149, 172, 98, 0],
   ![88, 148, 118, 73, 1]]
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
  by_cases hc : p ∈ [2, 199]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 199 O Om hm M199
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 199] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF58
