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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible110

namespace RoiDegree5ExamplesNativeDecideNF110
open RoiDegree5ExamplesNativeDecideIrreducible110

-- Number field with label 5.1.3037500000.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 10*X^2 - 390*X - 2088
lemma T_def : T = X^5 - 15*X^3 - 10*X^2 - 390*X - 2088 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-2088, -390, -10, -15, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/1182*a^4 -
-- 91/591*a^3 + 13/1182*a^2 - 2/197*a - 95/197]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  1182
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1182, 0, 0, 0, 0],
   ![0, 1182, 0, 0, 0],
   ![0, 0, 1182, 0, 0],
   ![0, 394, 394, 394, 0],
   ![-570, -12, 13, -182, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, -1, -1, 3, 0],
       ![190, -57, -65, 183, 394],
       ![-86, 26, 30, -84, -182]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, -1, -1, 3, 0],
       ![570, -170, -195, 546, 1182],
       ![886, 68, -67, 198, 394],
       ![-308, -60, -4, 6, 28]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![190, -57, -65, 183, 394],
       ![886, 68, -67, 198, 394],
       ![1604, -26, -349, 1106, 2364],
       ![-554, 16, 140, -448, -962]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-86, 26, 30, -84, -182],
       ![-308, -60, -4, 6, 28],
       ![-554, 16, 140, -448, -962],
       ![188, -14, -61, 195, 421]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-1182]],
   ![[], [], [], [-465708], [215124, -1182]],
   ![[], [], [-465708], [-310472, -155236], [60282, 71314, -394]],
   ![[], [-1182], [215124, -1182], [60282, 71314, -394], [10206, -33165, 364, -1]]]
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
   ![
     [0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0],
     [0, -1, -1, 3, 0],
     [190, -57, -65, 183, 394],
     [-86, 26, 30, -84, -182]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, -1, -1, 3, 0],
     [570, -170, -195, 546, 1182],
     [886, 68, -67, 198, 394],
     [-308, -60, -4, 6, 28]
   ],
   ![
     [0, 0, 0, 1, 0],
     [190, -57, -65, 183, 394],
     [886, 68, -67, 198, 394],
     [1604, -26, -349, 1106, 2364],
     [-554, 16, 140, -448, -962]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-86, 26, 30, -84, -182],
     [-308, -60, -4, 6, 28],
     [-554, 16, 140, -448, -962],
     [188, -14, -61, 195, 421]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp197 : Fact (Nat.Prime 197) := fact_iff.2 (by norm_num)
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
 f := [418, 79, 4, 5, 1]
 g := [2, 1]
 h := [1, 2, 4, 3, 1]
 a :=  [3]
 b :=  [1, 1, 1, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 197] where
 n := 4
 p := ![2, 3, 5, 197]
 exp := ![7, 9, 8, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp197.out
 a := [-21365167500000, 3172972500000, -801900000000, 185895000000]
 b := [16452801000000, 3533827500000, -411520500000, 160380000000, -37179000000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 0, 0, 1, 0],![1, 0, 1, 0, 1],![0, 1, 0, 1, 1],![0, 1, 0, 1, 0],![0, 1, 1, 0, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![3239, -810],![88, -37],![2282, -572],![3506, -876],![354, -104]]
 c := ![![1968, -4322, 2584],
   ![128, -116, 32],
   ![1337, -3068, 1814],
   ![2072, -4699, 2796],
   ![232, -494, 243]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [1, 0, 1, 0, 1], [1, 2, 0, 0, 1]],
![[0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0], [1, 2, 2, 0, 1], [1, 0, 2, 0, 1]],
![[0, 0, 0, 1, 0], [1, 0, 1, 0, 1], [1, 2, 2, 0, 1], [2, 1, 2, 2, 0], [1, 1, 2, 2, 1]],
![[0, 0, 0, 0, 1], [1, 2, 0, 0, 1], [1, 0, 2, 0, 1], [1, 1, 2, 2, 1], [2, 1, 2, 0, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 1],![0, 1, 2, 0, 0],![0, 0, 0, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 1],![0, 1, 2, 0, 0],![0, 0, 0, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 0, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![8, 0, 8, 4, 0],![2, 0, 0, 4, 0],![4, 8, 4, 0, 0],![2, 1, 2, 2, 1],![0, 4, 8, 0, 0]]
 w1 := ![0, 0, 1]
 w2 := ![0, 1]
 a := ![![9640, -1506, 8808],
   ![8040, -1198, 7026],
   ![1704, -270, 1684],
   ![3657, -561, 3300],
   ![2052, -366, 2172]]
 c := ![![1248, 27],![240, -33],![480, 9],![367, 0],![996, 43]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M197 : MaximalOrderCertificateOfUnramifiedLists 197 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
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
       [0, 196, 196, 3, 0],
       [190, 140, 132, 183, 0],
       [111, 26, 30, 113, 15]
     ],
     ![
       [0, 0, 1, 0, 0],
       [0, 196, 196, 3, 0],
       [176, 27, 2, 152, 0],
       [98, 68, 130, 1, 0],
       [86, 137, 193, 6, 28]
     ],
     ![
       [0, 0, 0, 1, 0],
       [190, 140, 132, 183, 0],
       [98, 68, 130, 1, 0],
       [28, 171, 45, 121, 0],
       [37, 16, 140, 143, 23]
     ],
     ![
       [0, 0, 0, 0, 1],
       [111, 26, 30, 113, 15],
       [86, 137, 193, 6, 28],
       [37, 16, 140, 143, 23],
       [188, 183, 136, 195, 27]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],
   ![106, 7, 194, 175, 0],
   ![94, 154, 121, 92, 0],
   ![169, 17, 90, 70, 0],
   ![193, 116, 98, 149, 196]]
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
  by_cases hc : p ∈ [2, 3, 197]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 197 O Om hm M197
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3, 197] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF110
