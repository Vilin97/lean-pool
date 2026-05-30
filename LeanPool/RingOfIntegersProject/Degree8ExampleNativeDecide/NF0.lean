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
import LeanPool.RingOfIntegersProject.Degree8ExampleNativeDecide.Irreducible0

namespace RoiDegree8ExampleNativeDecideNF0
open RoiDegree8ExampleNativeDecideIrreducible0


open Polynomial Module

/-- Auxiliary declaration for the worked example. -/
noncomputable def T : ℤ[X] := X^8 - X^6 + 2*X^4 + X^2 + 1
lemma T_def : T = X^8 - X^6 + 2*X^4 + X^2 + 1 := rfl

local notation "K" => AdjoinRoot (map (algebraMap ℤ ℚ) T)
local notation "l" => [1, 0, 1, 0, 2, 0, -1, 0, 1]

/-- Auxiliary declaration for the worked example. -/
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def]; norm_num; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, a^4, a^5, 1/2*a^6 - 1/2, 1/2*a^7 -
-- 1/2*a]

/-- Auxiliary declaration for the worked example. -/
noncomputable def BQ : SubalgebraBuilderLists 8 ℤ  ℚ K T l where
 d :=  2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0, 0, 0, 0, 0, 0],
   ![0, 2, 0, 0, 0, 0, 0, 0],
   ![0, 0, 2, 0, 0, 0, 0, 0],
   ![0, 0, 0, 2, 0, 0, 0, 0],
   ![0, 0, 0, 0, 2, 0, 0, 0],
   ![0, 0, 0, 0, 0, 2, 0, 0],
   ![-1, 0, 0, 0, 0, 0, 1, 0],
   ![0, -1, 0, 0, 0, 0, 0, 1]]
 a :=
   ![
     ![
       ![1, 0, 0, 0, 0, 0, 0, 0],
       ![0, 1, 0, 0, 0, 0, 0, 0],
       ![0, 0, 1, 0, 0, 0, 0, 0],
       ![0, 0, 0, 1, 0, 0, 0, 0],
       ![0, 0, 0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![0, 0, 0, 0, 0, 0, 1, 0],
       ![0, 0, 0, 0, 0, 0, 0, 1]
     ],
     ![
       ![0, 1, 0, 0, 0, 0, 0, 0],
       ![0, 0, 1, 0, 0, 0, 0, 0],
       ![0, 0, 0, 1, 0, 0, 0, 0],
       ![0, 0, 0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![1, 0, 0, 0, 0, 0, 2, 0],
       ![0, 0, 0, 0, 0, 0, 0, 1],
       ![0, 0, -1, 0, -1, 0, 1, 0]
     ],
     ![
       ![0, 0, 1, 0, 0, 0, 0, 0],
       ![0, 0, 0, 1, 0, 0, 0, 0],
       ![0, 0, 0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![1, 0, 0, 0, 0, 0, 2, 0],
       ![0, 1, 0, 0, 0, 0, 0, 2],
       ![0, 0, -1, 0, -1, 0, 1, 0],
       ![0, 0, 0, -1, 0, -1, 0, 1]
     ],
     ![
       ![0, 0, 0, 1, 0, 0, 0, 0],
       ![0, 0, 0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![1, 0, 0, 0, 0, 0, 2, 0],
       ![0, 1, 0, 0, 0, 0, 0, 2],
       ![0, 0, -1, 0, -2, 0, 2, 0],
       ![0, 0, 0, -1, 0, -1, 0, 1],
       ![-1, 0, -1, 0, -2, 0, -1, 0]
     ],
     ![
       ![0, 0, 0, 0, 1, 0, 0, 0],
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![1, 0, 0, 0, 0, 0, 2, 0],
       ![0, 1, 0, 0, 0, 0, 0, 2],
       ![0, 0, -1, 0, -2, 0, 2, 0],
       ![0, 0, 0, -1, 0, -2, 0, 2],
       ![-1, 0, -1, 0, -2, 0, -1, 0],
       ![0, -1, 0, -1, 0, -2, 0, -1]
     ],
     ![
       ![0, 0, 0, 0, 0, 1, 0, 0],
       ![1, 0, 0, 0, 0, 0, 2, 0],
       ![0, 1, 0, 0, 0, 0, 0, 2],
       ![0, 0, -1, 0, -2, 0, 2, 0],
       ![0, 0, 0, -1, 0, -2, 0, 2],
       ![-2, 0, -2, 0, -3, 0, -2, 0],
       ![0, -1, 0, -1, 0, -2, 0, -1],
       ![-2, 0, 0, 0, 0, 0, -5, 0]
     ],
     ![
       ![0, 0, 0, 0, 0, 0, 1, 0],
       ![0, 0, 0, 0, 0, 0, 0, 1],
       ![0, 0, -1, 0, -1, 0, 1, 0],
       ![0, 0, 0, -1, 0, -1, 0, 1],
       ![-1, 0, -1, 0, -2, 0, -1, 0],
       ![0, -1, 0, -1, 0, -2, 0, -1],
       ![-1, 0, 0, 0, 0, 0, -3, 0],
       ![0, -1, 0, 0, 0, 0, 0, -3]
     ],
     ![
       ![0, 0, 0, 0, 0, 0, 0, 1],
       ![0, 0, -1, 0, -1, 0, 1, 0],
       ![0, 0, 0, -1, 0, -1, 0, 1],
       ![-1, 0, -1, 0, -2, 0, -1, 0],
       ![0, -1, 0, -1, 0, -2, 0, -1],
       ![-2, 0, 0, 0, 0, 0, -5, 0],
       ![0, -1, 0, 0, 0, 0, 0, -3],
       ![0, 0, 2, 0, 3, 0, -3, 0]
     ]
   ]
 s :=
   ![
     ![[], [], [], [], [], [], [], []],
     ![[], [], [], [], [], [], [], [-2]],
     ![[], [], [], [], [], [], [-2], [0, -2]],
     ![[], [], [], [], [], [-4], [0, -2], [-2, 0, -2]],
     ![[], [], [], [], [-4], [0, -4], [-2, 0, -2], [0, -2, 0, -2]],
     ![[], [], [], [-4], [0, -4], [-4, 0, -4], [0, -2, 0, -2], [2, 0, -2, 0, -2]],
     ![[], [], [-2], [0, -2], [-2, 0, -2], [0, -2, 0, -2], [1, 0, -1, 0, -1], [0, 1, 0, -1, 0, -1]],
     ![
       [],
       [-2],
       [0, -2],
       [-2, 0, -2],
       [0, -2, 0, -2],
       [2, 0, -2, 0, -2],
       [0, 1, 0, -1, 0, -1],
       [6, 0, 1, 0, -1, 0, -1]
     ]
   ]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide +kernel
 hin := by decide +kernel
 hsymma := by decide +kernel
 hc_le := by decide +kernel

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

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
noncomputable def B : Basis (Fin 8) ℤ O := basisOfBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

/-- Auxiliary declaration for the worked example. -/
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
/-- Auxiliary declaration for the worked example. -/
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

/-- Auxiliary declaration for the worked example. -/
noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
/-- Auxiliary declaration for the worked example. -/
def Table : Fin 8 → Fin 8 → List ℤ :=
 ![
   ![
     [1, 0, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0],
     [0, 0, 0, 0, 0, 0, 1, 0],
     [0, 0, 0, 0, 0, 0, 0, 1]
   ],
   ![
     [0, 1, 0, 0, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0],
     [1, 0, 0, 0, 0, 0, 2, 0],
     [0, 0, 0, 0, 0, 0, 0, 1],
     [0, 0, -1, 0, -1, 0, 1, 0]
   ],
   ![
     [0, 0, 1, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0],
     [1, 0, 0, 0, 0, 0, 2, 0],
     [0, 1, 0, 0, 0, 0, 0, 2],
     [0, 0, -1, 0, -1, 0, 1, 0],
     [0, 0, 0, -1, 0, -1, 0, 1]
   ],
   ![
     [0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0],
     [1, 0, 0, 0, 0, 0, 2, 0],
     [0, 1, 0, 0, 0, 0, 0, 2],
     [0, 0, -1, 0, -2, 0, 2, 0],
     [0, 0, 0, -1, 0, -1, 0, 1],
     [-1, 0, -1, 0, -2, 0, -1, 0]
   ],
   ![
     [0, 0, 0, 0, 1, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0],
     [1, 0, 0, 0, 0, 0, 2, 0],
     [0, 1, 0, 0, 0, 0, 0, 2],
     [0, 0, -1, 0, -2, 0, 2, 0],
     [0, 0, 0, -1, 0, -2, 0, 2],
     [-1, 0, -1, 0, -2, 0, -1, 0],
     [0, -1, 0, -1, 0, -2, 0, -1]
   ],
   ![
     [0, 0, 0, 0, 0, 1, 0, 0],
     [1, 0, 0, 0, 0, 0, 2, 0],
     [0, 1, 0, 0, 0, 0, 0, 2],
     [0, 0, -1, 0, -2, 0, 2, 0],
     [0, 0, 0, -1, 0, -2, 0, 2],
     [-2, 0, -2, 0, -3, 0, -2, 0],
     [0, -1, 0, -1, 0, -2, 0, -1],
     [-2, 0, 0, 0, 0, 0, -5, 0]
   ],
   ![
     [0, 0, 0, 0, 0, 0, 1, 0],
     [0, 0, 0, 0, 0, 0, 0, 1],
     [0, 0, -1, 0, -1, 0, 1, 0],
     [0, 0, 0, -1, 0, -1, 0, 1],
     [-1, 0, -1, 0, -2, 0, -1, 0],
     [0, -1, 0, -1, 0, -2, 0, -1],
     [-1, 0, 0, 0, 0, 0, -3, 0],
     [0, -1, 0, 0, 0, 0, 0, -3]
   ],
   ![
     [0, 0, 0, 0, 0, 0, 0, 1],
     [0, 0, -1, 0, -1, 0, 1, 0],
     [0, 0, 0, -1, 0, -1, 0, 1],
     [-1, 0, -1, 0, -2, 0, -1, 0],
     [0, -1, 0, -1, 0, -2, 0, -1],
     [-2, 0, 0, 0, 0, 0, -5, 0],
     [0, -1, 0, 0, 0, 0, 0, -3],
     [0, 0, 2, 0, 3, 0, -3, 0]
   ]
 ]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) :=
  by decide +kernel

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide +kernel)

/-- Auxiliary declaration for the worked example. -/
instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def CD3 : CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2, 0, 2]
 b' := [0, 0, 0, 1]
 k := [1]
 f := [1, 0, 1, 0, 1, 0, 1]
 g := [2, 0, 1, 0, 1]
 h := [2, 0, 1, 0, 1]
 a :=  [2, 0, 1]
 b :=  [1, 0, 1, 0, 2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
def CD5 : CertificateDedekindCriterionLists l 5 where
 n := 2
 a' := [4, 0, 2]
 b' := [0, 1, 0, 2]
 k := [1]
 f := [3, 0, 3, 0, 2, 0, 1]
 g := [4, 0, 2, 0, 1]
 h := [4, 0, 2, 0, 1]
 a :=  [0, 0, 4]
 b :=  [4, 0, 0, 0, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

/-- Auxiliary declaration for the worked example. -/
noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 3
 p := ![2, 3, 5]
 exp := ![12, 4, 4]
 pdgood := [3, 5]
 hsub := by  decide +kernel
 hp := by
  intro i; fin_cases i
  · exact hp2.out
  · exact hp3.out
  · exact hp5.out
 a := [207360000, 0, -117504000, 0, 41472000, 0, 55296000]
 b := [0, -44928000, 0, 10368000, 0, -3456000, 0, -6912000]
 hab := by decide +kernel
 hd := by
  intro p hp
  fin_cases hp
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  · exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

/-- Auxiliary declaration for the worked example. -/
noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 4
 n := 4
 t := 3
 hpos := by decide +kernel
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod :=
   ![
     ![
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 0, 0, 0, 1]
     ],
     ![
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 0, 0, 1],
       [0, 0, 1, 0, 1, 0, 1, 0]
     ],
     ![
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 1, 0, 1, 0],
       [0, 0, 0, 1, 0, 1, 0, 1]
     ],
     ![
       [0, 0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 1, 0, 1],
       [1, 0, 1, 0, 0, 0, 1, 0]
     ],
     ![
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 0, 0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0],
       [1, 0, 1, 0, 0, 0, 1, 0],
       [0, 1, 0, 1, 0, 0, 0, 1]
     ],
     ![
       [0, 0, 0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0, 0, 0],
       [0, 1, 0, 1, 0, 0, 0, 1],
       [0, 0, 0, 0, 0, 0, 1, 0]
     ],
     ![
       [0, 0, 0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 0, 0, 0, 1],
       [0, 0, 1, 0, 1, 0, 1, 0],
       [0, 0, 0, 1, 0, 1, 0, 1],
       [1, 0, 1, 0, 0, 0, 1, 0],
       [0, 1, 0, 1, 0, 0, 0, 1],
       [1, 0, 0, 0, 0, 0, 1, 0],
       [0, 1, 0, 0, 0, 0, 0, 1]
     ],
     ![
       [0, 0, 0, 0, 0, 0, 0, 1],
       [0, 0, 1, 0, 1, 0, 1, 0],
       [0, 0, 0, 1, 0, 1, 0, 1],
       [1, 0, 1, 0, 0, 0, 1, 0],
       [0, 1, 0, 1, 0, 0, 0, 1],
       [0, 0, 0, 0, 0, 0, 1, 0],
       [0, 1, 0, 0, 0, 0, 0, 1],
       [0, 0, 0, 0, 1, 0, 1, 0]
     ]
   ]
 hTMod := by decide +kernel
 hle := by decide +kernel
 b1 := ![![1, 0, 0, 0, 0, 1, 1, 1],
   ![0, 1, 0, 0, 1, 0, 0, 0],
   ![0, 0, 1, 0, 0, 1, 0, 0],
   ![0, 0, 0, 1, 0, 1, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0, 0, 0],
   ![1, 0, 0, 0, 0, 0, 1, 0]]
 v := ![![1, 0, 0, 0, 0, 1, 1, 1],
   ![0, 1, 0, 0, 1, 0, 0, 0],
   ![0, 0, 1, 0, 0, 1, 0, 0],
   ![0, 0, 0, 1, 0, 1, 1, 1]]
 w := ![![1, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0, 0, 0],
   ![1, 0, 0, 0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 1, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 1, 0]]
 v_ind := ![0, 1, 2, 3]
 w_ind := ![0, 2, 4, 6]
 hmod1 := by decide +kernel
 hmod2 := by decide +kernel
 hindv := by decide +kernel
 hindw := by decide +kernel
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel
 g := ![![0, 1, 0, 0, 0, 0, 1, 0],
   ![0, 1, 0, 0, 1, 1, 1, 1],
   ![1, 0, 0, 0, 1, 1, 1, 1],
   ![1, 1, 0, 1, 0, 1, 1, 0],
   ![0, 1, 0, 1, 1, 1, 1, 1],
   ![1, 0, 0, 0, 0, 1, 1, 1],
   ![1, 1, 1, 0, 1, 0, 1, 1],
   ![0, 1, 1, 1, 1, 0, 1, 1]]
 w1 := ![0, 3, 2, 2]
 w2 := ![1, 0, 3, 3]
 a := ![![1, -14, -10, 2],
   ![42, -45, -60, -26],
   ![42, -42, -53, -32],
   ![40, -36, -50, -7],
   ![56, -54, -74, -26],
   ![26, -28, -34, -26],
   ![26, -26, -40, -12],
   ![40, -38, -56, -14]]
 c := ![![-2, 8, 0, -2],
   ![-16, 18, 14, -18],
   ![-16, 14, 14, -16],
   ![-12, 22, 16, -12],
   ![-21, 24, 18, -20],
   ![-6, 7, 10, -18],
   ![-14, 12, 13, -2],
   ![-20, 18, 14, -7]]
 hmulw := by  decide +kernel
 ac_indw := ![Sum.inl 0,
   Sum.inl 1,
   Sum.inl 2,
   Sum.inl 3,
   Sum.inr 0,
   Sum.inr 1,
   Sum.inr 2,
   Sum.inr 3]
 hacindw := by decide +kernel


theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
  · haveI : Fact (Nat.Prime p) := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D p hp hc)
    rw [T_degree, ← rank_subalgebra_eq_card_basis Om B']
    rfl


theorem O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers]; rfl

end RoiDegree8ExampleNativeDecideNF0
