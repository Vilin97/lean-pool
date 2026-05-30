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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible33

namespace RoiDegree5ExamplesNativeDecideNF33
open RoiDegree5ExamplesNativeDecideIrreducible33

-- Number field with label 5.1.75000000.1 in the LMFDB

open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 40*X^2 + 135*X + 198
lemma T_def : T = X^5 - 15*X^3 - 40*X^2 + 135*X + 198 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [198, 135, -40, -15, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/69*a^4 -
-- 3/23*a^3 - 1/23*a^2 - 13/69*a - 8/23]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  69
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![69, 0, 0, 0, 0],
   ![0, 69, 0, 0, 0],
   ![0, 0, 69, 0, 0],
   ![0, 23, 23, 23, 0],
   ![-24, -13, -3, -9, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, -1, -1, 3, 0],
       ![8, 1, -2, 10, 23],
       ![-6, -3, 1, -3, -9]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, -1, -1, 3, 0],
       ![24, 4, -6, 27, 69],
       ![-58, -49, 6, 25, 23],
       ![30, 17, -7, 0, 12]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![8, 1, -2, 10, 23],
       ![-58, -49, 6, 25, 23],
       ![4, -52, -26, 78, 138],
       ![-16, 5, 10, -20, -35]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-6, -3, 1, -3, -9],
       ![30, 17, -7, 0, 12],
       ![-16, 5, 10, -20, -35],
       ![12, 2, -5, 6, 10]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-69]],
   ![[], [], [], [-1587], [621, -69]],
   ![[], [], [-1587], [-1058, -529], [-92, 184, -23]],
   ![[], [-69], [621, -69], [-92, 184, -23], [202, -90, 18, -1]]]
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
   ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, -1, -1, 3, 0], [8, 1, -2, 10, 23], [-6, -3, 1, -3, -9]],
   ![
     [0, 0, 1, 0, 0],
     [0, -1, -1, 3, 0],
     [24, 4, -6, 27, 69],
     [-58, -49, 6, 25, 23],
     [30, 17, -7, 0, 12]
   ],
   ![
     [0, 0, 0, 1, 0],
     [8, 1, -2, 10, 23],
     [-58, -49, 6, 25, 23],
     [4, -52, -26, 78, 138],
     [-16, 5, 10, -20, -35]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-6, -3, 1, -3, -9],
     [30, 17, -7, 0, 12],
     [-16, 5, 10, -20, -35],
     [12, 2, -5, 6, 10]
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
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD2 : CertificateDedekindCriterionLists l 2 where
 n := 2
 a' := [1]
 b' := [1, 1]
 k := [0, 1]
 f := [-99, -67, 21, 9, 1]
 g := [0, 1, 1, 1]
 h := [1, 1, 1]
 a :=  [1, 0, 1]
 b :=  [1, 1, 0, 1]
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
 f := [-39, -25, 11, 5, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a :=  [1]
 b :=  [0, 0, 3, 4]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 23] where
 n := 4
 p := ![2, 3, 5, 23]
 exp := ![6, 5, 8, 2]
 pdgood := [2, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp23.out
 a := [573750000, 6783750000, 2936250000, -67500000]
 b := [22963500000, 3084750000, -1437750000, -587250000, 13500000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 1
 n := 4
 t := 2
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [2, 1, 1, 1, 2], [0, 0, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [0, 1, 0, 0, 0], [2, 2, 0, 1, 2], [0, 2, 2, 0, 0]],
![[0, 0, 0, 1, 0], [2, 1, 1, 1, 2], [2, 2, 0, 1, 2], [1, 2, 1, 0, 0], [2, 2, 1, 1, 1]],
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 2, 2, 0, 0], [2, 2, 1, 1, 1], [0, 2, 1, 0, 1]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![0, 1, 2, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 1, 0, 0, 1],![0, 0, 0, 1, 2]]
 v := ![![0, 1, 2, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 1, 0, 0, 1],![0, 0, 0, 1, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 2],![0, 0, 1, 0, 1],![0, 0, 0, 1, 2]]
 v_ind := ![1]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 2, 1, 2],![0, 1, 0, 1, 0],![0, 2, 0, 0, 1],![1, 0, 1, 2, 0],![1, 1, 0, 0, 1]]
 w1 := ![1]
 w2 := ![0, 1, 1, 0]
 a := ![![-83],![51],![-12],![48],![-18]]
 c := ![![210, -81, 207, 45],
   ![-86, 33, -75, -27],
   ![6, -26, 21, -3],
   ![-30, 36, -29, -15],
   ![24, -24, 33, 4]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
 hacindw := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def M23 : MaximalOrderCertificateOfUnramifiedLists 23 O Om hm where
 n := 5
 t := 1
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 22, 22, 3, 0], [8, 1, 21, 10, 0], [17, 20, 1, 20, 14]],
![[0, 0, 1, 0, 0], [0, 22, 22, 3, 0], [1, 4, 17, 4, 0], [11, 20, 6, 2, 0], [7, 17, 16, 0, 12]],
![[0, 0, 0, 1, 0], [8, 1, 21, 10, 0], [11, 20, 6, 2, 0], [4, 17, 20, 9, 0], [7, 5, 10, 3, 11]],
![[0, 0, 0, 0, 1], [17, 20, 1, 20, 14], [7, 17, 16, 0, 12], [7, 5, 10, 3, 11], [12, 2, 18, 6, 10]]]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],![10, 6, 0, 22, 0],![8, 10, 11, 7, 0],![7, 7, 2, 6, 0],![13, 12, 13, 7, 1]]
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
  by_cases hc : p ∈ [3, 23]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 23 O Om hm M23
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 23] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNativeDecideNF33
