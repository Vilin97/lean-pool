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
import LeanPool.RingOfIntegersProject.Degree5Examples.Irreducible114

namespace RoiDegree5ExamplesNF114
open RoiDegree5ExamplesIrreducible114

-- Number field with label 5.3.5695312500.2 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 75*X^3 - 200*X^2 + 150*X - 60
lemma T_def : T = X^5 - 75*X^3 - 200*X^2 + 150*X - 60 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-60, 150, -200, -75, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/166*a^4 + 27/166*a^3
-- - 5/83*a^2 + 14/83*a + 38/83]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  166
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![166, 0, 0, 0, 0],
   ![0, 166, 0, 0, 0],
   ![0, 0, 166, 0, 0],
   ![0, 0, -83, 83, 0],
   ![76, 28, -10, 27, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![-38, -14, -9, -28, 83],
       ![-12, -5, -1, -8, 27]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 1, 2, 0],
       ![-76, -28, -17, -54, 166],
       ![68, -61, 146, 102, -83],
       ![-20, -35, 39, 6, 65]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-38, -14, -9, -28, 83],
       ![68, -61, 146, 102, -83],
       ![-1474, -442, -448, -1001, 3154],
       ![-494, -197, -77, -308, 1094]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-12, -5, -1, -8, 27],
       ![-20, -35, 39, 6, 65],
       ![-494, -197, -77, -308, 1094],
       ![-188, -91, -5, -108, 429]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-166]],
   ![[], [], [], [-13778], [-4482, -166]],
   ![[], [], [-13778], [13778, -6889], [-3154, -2158, -83]],
   ![[], [-166], [-4482, -166], [-3154, -2158, -83], [-3766, -784, -54, -1]]]
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
   ![
     [0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0],
     [0, 0, 1, 2, 0],
     [-38, -14, -9, -28, 83],
     [-12, -5, -1, -8, 27]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 1, 2, 0],
     [-76, -28, -17, -54, 166],
     [68, -61, 146, 102, -83],
     [-20, -35, 39, 6, 65]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-38, -14, -9, -28, 83],
     [68, -61, 146, 102, -83],
     [-1474, -442, -448, -1001, 3154],
     [-494, -197, -77, -308, 1094]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-12, -5, -1, -8, 27],
     [-20, -35, 39, 6, 65],
     [-494, -197, -77, -308, 1094],
     [-188, -91, -5, -108, 429]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp83 : Fact (Nat.Prime 83) := fact_iff.2 (by norm_num)
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := [2]
 b' := [1, 2]
 k := [0, 1]
 f := [20, -50, 67, 26, 1]
 g := [0, 1, 1]
 h := [0, 1, 2, 1]
 a :=  [2, 1]
 b :=  [2, 1, 0, 2]
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
 f := [12, -30, 40, 15]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [3]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 83] where
 n := 4
 p := ![2, 3, 5, 83]
 exp := ![6, 6, 9, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp83.out
 a := [-15808668750000, -6843993750000, 111881250000, 147318750000]
 b := [-2138400000000, 7368671250000, 2252711250000, -22376250000, -29463750000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 1
 n := 4
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 0, 1]],
![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 0, 1]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 1], [0, 0, 0, 1, 0], [0, 1, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![1, 1, 0, 0, 1],![1, 0, 1, 1, 1],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0],![0, 0, 1, 0, 1]]
 w1 := ![1]
 w2 := ![0, 1, 0, 0]
 a := ![![29],![56],![28],![64],![90]]
 c := ![![-228, 530, -664, -124],
   ![-791, 1828, -2268, -434],
   ![-228, 529, -664, -124],
   ![-58, 148, -229, -18],
   ![-274, 650, -860, -135]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
 hacindw := by decide

noncomputable def M83 : MaximalOrderCertificateOfUnramifiedLists 83 O Om hm where
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
       [45, 69, 74, 55, 0],
       [71, 78, 82, 75, 27]
     ],
     ![
       [0, 0, 1, 0, 0],
       [0, 0, 1, 2, 0],
       [7, 55, 66, 29, 0],
       [68, 22, 63, 19, 0],
       [63, 48, 39, 6, 65]
     ],
     ![
       [0, 0, 0, 1, 0],
       [45, 69, 74, 55, 0],
       [68, 22, 63, 19, 0],
       [20, 56, 50, 78, 0],
       [4, 52, 6, 24, 15]
     ],
     ![
       [0, 0, 0, 0, 1],
       [71, 78, 82, 75, 27],
       [63, 48, 39, 6, 65],
       [4, 52, 6, 24, 15],
       [61, 75, 78, 58, 14]
     ]
   ]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],
   ![78, 0, 75, 70, 0],
   ![69, 47, 45, 30, 0],
   ![21, 54, 17, 39, 0],
   ![24, 41, 69, 36, 82]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide +kernel

instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 83]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 83 O Om hm M83
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 83] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree5ExamplesNF114
