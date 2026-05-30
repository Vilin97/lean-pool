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
import LeanPool.RingOfIntegersProject.Degree5ExamplesNativeDecide.Irreducible134

-- Number field with label 5.1.15187500000.11 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^5 + 25*X^3 - 150*X^2 + 450*X - 240
lemma T_def : T = X^5 + 25*X^3 - 150*X^2 + 450*X - 240 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [-240, 450, -150, 25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/334*a^4 + 45/167*a^3 + 109/334*a^2
-- - 13/167*a + 57/167]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  334
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![334, 0, 0, 0, 0],
   ![0, 334, 0, 0, 0],
   ![0, 0, 334, 0, 0],
   ![0, 0, 0, 334, 0],
   ![114, -26, 109, 90, 1]]
 a :=
   ![
     ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
     ![
       ![0, 1, 0, 0, 0],
       ![0, 0, 1, 0, 0],
       ![0, 0, 0, 1, 0],
       ![-114, 26, -109, -90, 334],
       ![-30, 6, -29, -24, 90]
     ],
     ![
       ![0, 0, 1, 0, 0],
       ![0, 0, 0, 1, 0],
       ![-114, 26, -109, -90, 334],
       ![240, -450, 150, -25, 0],
       ![36, -114, 12, -29, 84]
     ],
     ![
       ![0, 0, 0, 1, 0],
       ![-114, 26, -109, -90, 334],
       ![240, -450, 150, -25, 0],
       ![2850, -410, 2275, 2400, -8350],
       ![786, -214, 611, 606, -2126]
     ],
     ![
       ![0, 0, 0, 0, 1],
       ![-30, 6, -29, -24, 90],
       ![36, -114, 12, -29, 84],
       ![786, -214, 611, 606, -2126],
       ![210, -84, 157, 147, -519]
     ]
   ]
 s := ![![[], [], [], [], []],
   ![[], [], [], [], [-334]],
   ![[], [], [], [-111556], [-30060, -334]],
   ![[], [], [-111556], [0, -111556], [-28056, -30060, -334]],
   ![[], [-334], [-30060, -334], [-28056, -30060, -334], [-15218, -8293, -180, -1]]]
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
     [0, 0, 0, 1, 0],
     [-114, 26, -109, -90, 334],
     [-30, 6, -29, -24, 90]
   ],
   ![
     [0, 0, 1, 0, 0],
     [0, 0, 0, 1, 0],
     [-114, 26, -109, -90, 334],
     [240, -450, 150, -25, 0],
     [36, -114, 12, -29, 84]
   ],
   ![
     [0, 0, 0, 1, 0],
     [-114, 26, -109, -90, 334],
     [240, -450, 150, -25, 0],
     [2850, -410, 2275, 2400, -8350],
     [786, -214, 611, 606, -2126]
   ],
   ![
     [0, 0, 0, 0, 1],
     [-30, 6, -29, -24, 90],
     [36, -114, 12, -29, 84],
     [786, -214, 611, 606, -2126],
     [210, -84, 157, 147, -519]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide +kernel)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp167 : Fact (Nat.Prime 167) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 3
 a' := []
 b' := [1]
 k := [1, 0, 2, 0, 1]
 f := [80, -150, 50, -8]
 g := [0, 1, 0, 1]
 h := [0, 0, 1]
 a :=  [2, 1, 2]
 b :=  [1, 1, 1]
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
 f := [48, -90, 30, -5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 167] where
 n := 4
 p := ![2, 3, 5, 167]
 exp := ![7, 5, 9, 2]
 pdgood := [3, 5]
 hsub := by decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
  · exact hp167.out
 a := [8655862500000, -2023987500000, -97875000000, -145125000000]
 b := [8381475000000, -4147672500000, 695047500000, 19575000000, 29025000000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 1]]]
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
 g := ![![1, 1, 1, 0, 1],![0, 1, 0, 0, 0],![0, 1, 1, 1, 1],![0, 0, 1, 1, 0],![0, 0, 0, 1, 1]]
 w1 := ![1, 1]
 w2 := ![0, 1, 1]
 a := ![![-409, 1348],![44, -271],![-250, 6724],![-248, 5592],![114, 6780]]
 c := ![![1014, 1050, -1702],
   ![-144, -414, 424],
   ![4485, 9826, -11344],
   ![3690, 8179, -9390],
   ![4410, 10838, -12019]]
 hmulw := by decide +kernel
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide +kernel

noncomputable def M167 : MaximalOrderCertificateOfUnramifiedLists 167 O Om hm where
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
       [0, 0, 0, 1, 0],
       [53, 26, 58, 77, 0],
       [137, 6, 138, 143, 90]
     ],
     ![
       [0, 0, 1, 0, 0],
       [0, 0, 0, 1, 0],
       [53, 26, 58, 77, 0],
       [73, 51, 150, 142, 0],
       [36, 53, 12, 138, 84]
     ],
     ![
       [0, 0, 0, 1, 0],
       [53, 26, 58, 77, 0],
       [73, 51, 150, 142, 0],
       [11, 91, 104, 62, 0],
       [118, 120, 110, 105, 45]
     ],
     ![
       [0, 0, 0, 0, 1],
       [137, 6, 138, 143, 90],
       [36, 53, 12, 138, 84],
       [118, 120, 110, 105, 45],
       [43, 83, 157, 147, 149]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 w := ![![1, 0, 0, 0, 0],
   ![106, 31, 46, 93, 0],
   ![83, 55, 141, 87, 0],
   ![120, 160, 134, 163, 0],
   ![108, 144, 154, 79, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide +kernel
 hwFrobComp := by decide +kernel

instance : Fact <| (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 167]
  · fin_cases hc
    · exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    · exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 167 O Om hm M167
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 167] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

