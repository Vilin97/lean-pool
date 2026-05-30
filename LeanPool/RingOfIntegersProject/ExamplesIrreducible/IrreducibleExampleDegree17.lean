/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiExamplesIrreducibleIrreducibleExampleDegree17

open Polynomial

local notation "T" => (X^17
  - 2*X^16
  - X^15
  + 5*X^14
  - X^13
  - 8*X^12
  + 6*X^11
  + 8*X^10
  - 11*X^9
  - 3*X^8
  + 12*X^7
  - 3*X^6
  - 7*X^5
  + 5*X^4
  + 3*X^3
  - 3*X^2
  + 1 : ℤ[X])

local notation "l" => [1, 0, -3, 3, 5, -7, -3, 12, -3, -11, 8, 6, -8, -1, 5, -1, -2, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]],![[2, 2]]]
 h' := ![![[1, 2], [0, 1]],![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

/-- Auxiliary declaration for the worked example. -/
def P3P1 : CertificateIrreducibleZModOfList' 3 13 2 1
    [1, 1, 2, 2, 1, 2, 2, 1, 0, 1, 0, 0, 0, 1] where
 m := 1
 P := ![13]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1],
   [0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 0, 2],
   [0, 1, 1, 1, 0, 0, 0, 1, 0, 2, 2, 0, 2],
   [1, 1, 0, 2, 0, 2, 2, 1, 2, 2, 1, 0, 1],
   [1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 1, 1],
   [1, 0, 2, 0, 2, 2, 0, 0, 1, 2, 0, 1, 2],
   [0, 1, 2, 0, 1, 2, 1, 2, 2, 0, 1, 1],
   [2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1],
   [2, 0, 0, 1, 2, 2, 1, 0, 0, 2, 2, 0, 1],
   [2, 1, 0, 1, 0, 2, 2, 2, 1, 2, 2, 1, 2],
   [0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 1, 1, 2],
   [0, 1]]
 g := ![![[]],
   ![[]],
   ![[0, 2, 0, 2, 0, 2, 2, 1, 2, 0, 2, 0, 0, 0, 1]],
   ![[0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0, 2, 1, 2, 1, 0, 1, 0, 0, 0, 2]],
   ![[2, 0, 2, 2, 1, 0, 2, 2, 1, 1, 1, 1, 1, 1, 0, 1, 2, 0, 0, 1, 0, 0, 0, 2]],
   ![[0, 2, 2, 1, 2, 2, 0, 0, 0, 2, 1, 1, 2, 2, 1, 2, 1, 0, 0, 2, 0, 0, 0, 1]],
   ![[0, 0, 1, 0, 2, 0, 0, 0, 1, 1, 2, 2, 2, 0, 1, 0, 2, 1, 0, 0, 1]],
   ![[1, 1, 1, 1, 2, 1, 1, 0, 2, 2, 2, 0, 0, 1, 2, 1, 1, 1, 0, 1, 1, 0, 0, 2]],
   ![[1, 0, 1, 1, 2, 1, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 0, 0, 1]],
   ![[0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 1]],
   ![[0, 2, 1, 0, 0, 0, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 0, 2, 0, 0, 0, 1]],
   ![[2, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 1, 1, 0, 0, 1, 1, 0, 0, 2]],
   ![[0, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 1, 2, 0, 1, 1, 0, 0, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]],
   ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1]],
   ![[0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
   ![[0, 1, 1, 1, 0, 0, 0, 1, 0, 2, 2, 0, 2], [0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 0, 2]],
   ![[1, 1, 0, 2, 0, 2, 2, 1, 2, 2, 1, 0, 1], [0, 1, 1, 1, 0, 0, 0, 1, 0, 2, 2, 0, 2]],
   ![[1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 1, 1], [1, 1, 0, 2, 0, 2, 2, 1, 2, 2, 1, 0, 1]],
   ![[1, 0, 2, 0, 2, 2, 0, 0, 1, 2, 0, 1, 2], [1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 1, 1]],
   ![[0, 1, 2, 0, 1, 2, 1, 2, 2, 0, 1, 1], [1, 0, 2, 0, 2, 2, 0, 0, 1, 2, 0, 1, 2]],
   ![[2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1], [0, 1, 2, 0, 1, 2, 1, 2, 2, 0, 1, 1]],
   ![[2, 0, 0, 1, 2, 2, 1, 0, 0, 2, 2, 0, 1], [2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1]],
   ![[2, 1, 0, 1, 0, 2, 2, 2, 1, 2, 2, 1, 2], [2, 0, 0, 1, 2, 2, 1, 0, 0, 2, 2, 0, 1]],
   ![[0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 1, 1, 2], [2, 1, 0, 1, 0, 2, 2, 2, 1, 2, 2, 1, 2]],
   ![[0, 1], [0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 1, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2, 2], [], [], [], [], [], [], [], [], [], [], []]
 b := ![[], [0, 0, 2, 0, 1, 2, 1, 2, 1, 1, 0, 1, 1], [], [], [], [], [], [], [], [], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

/-- Auxiliary declaration for the worked example. -/
def P7P1 : CertificateIrreducibleZModOfList' 7 6 2 2 [6, 0, 4, 5, 5, 3, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1],
   [4, 1, 5, 4, 3, 4],
   [4, 6, 1, 4, 1, 2],
   [2, 0, 2, 2, 0, 3],
   [2, 4, 3, 3, 5, 3],
   [6, 2, 3, 1, 5, 2],
   [0, 1]]
 g := ![![[4, 1], []],
   ![[0, 1, 4, 1, 0, 5, 2, 5, 0, 4], [5, 4, 2, 1, 0, 1, 5, 5, 1, 1]],
   ![[2, 0, 6, 5, 0, 4, 4, 1, 5, 4], [6, 5, 5, 6, 6, 2, 1, 1, 2, 1]],
   ![[5, 5, 6, 3, 6, 5, 6, 5, 6, 6], [3, 3, 3, 4, 3, 2, 6, 1, 3, 6]],
   ![[5, 1, 5, 5, 4, 0, 2, 3, 4, 6], [4, 2, 4, 3, 5, 3, 2, 2, 5, 6]],
   ![[4, 4, 2, 3, 0, 3, 3, 0, 0, 1], [3, 2, 4, 5, 4, 0, 1, 0, 1, 1]]]
 h' := ![![[4, 1, 5, 4, 3, 4], [0, 0, 0, 1], [0, 1]],
   ![[4, 6, 1, 4, 1, 2], [6, 3, 3, 0, 5, 6], [4, 1, 5, 4, 3, 4]],
   ![[2, 0, 2, 2, 0, 3], [0, 6, 6, 4, 3, 3], [4, 6, 1, 4, 1, 2]],
   ![[2, 4, 3, 3, 5, 3], [4, 3, 1, 1, 6, 3], [2, 0, 2, 2, 0, 3]],
   ![[6, 2, 3, 1, 5, 2], [5, 1, 1, 2, 4, 4], [2, 4, 3, 3, 5, 3]],
   ![[0, 1], [2, 1, 3, 6, 3, 5], [6, 2, 3, 1, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 5, 1, 6, 3], [3, 6, 5, 0, 6], [], []]
 b := ![[], [], [1, 0, 4, 6, 2, 2], [2, 4, 0, 6, 1, 5], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

/-- Auxiliary declaration for the worked example. -/
def P7P2 : CertificateIrreducibleZModOfList' 7 10 2 2 [4, 2, 5, 3, 5, 5, 3, 4, 3, 4, 1] where
 m := 2
 P := ![2, 5]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1],
   [0, 0, 0, 0, 0, 0, 0, 1],
   [4, 5, 1, 3, 2, 3, 4, 0, 1],
   [1, 6, 2, 5, 3, 0, 5, 4, 3],
   [1, 1, 5, 3, 4, 2, 6, 5, 4],
   [2, 1, 1, 6, 4, 3, 0, 4, 4, 1],
   [5, 6, 4, 3, 0, 1, 2, 4, 2, 5],
   [3, 0, 0, 0, 1, 6, 0, 0, 3, 4],
   [5, 2, 2, 4, 5, 6, 6, 5, 4, 5],
   [3, 6, 6, 4, 2, 0, 5, 5, 0, 6],
   [0, 1]]
 g :=
   ![
     ![[], []],
     ![[6, 1, 4, 2, 1, 2, 2, 0, 3, 2, 4, 5, 2, 3, 6, 2], [4, 2, 6, 6, 6, 4, 5, 3, 5, 6, 3, 1]],
     ![
       [6, 1, 1, 3, 6, 3, 0, 4, 0, 4, 0, 3, 0, 2, 4, 3, 4],
       [0, 5, 6, 2, 6, 6, 0, 2, 3, 5, 2, 1, 4, 3, 1]
     ],
     ![
       [0, 4, 5, 0, 1, 1, 5, 3, 5, 2, 1, 6, 1, 6, 0, 0, 3],
       [0, 4, 6, 3, 0, 6, 3, 0, 1, 2, 4, 0, 2, 0, 6]
     ],
     ![
       [5, 5, 5, 0, 4, 6, 2, 2, 0, 5, 2, 2, 2, 0, 5, 0, 4],
       [4, 6, 6, 2, 5, 6, 3, 1, 0, 1, 6, 6, 5, 5, 1]
     ],
     ![
       [1, 4, 6, 3, 0, 0, 2, 2, 0, 1, 6, 2, 0, 0, 0, 5, 0, 1],
       [4, 2, 2, 2, 3, 0, 3, 6, 6, 0, 5, 1, 0, 4, 4, 4, 1, 1]
     ],
     ![
       [1, 3, 2, 1, 5, 3, 5, 4, 2, 6, 1, 4, 0, 6, 6, 4, 5, 6],
       [5, 3, 4, 2, 2, 5, 3, 1, 4, 1, 0, 4, 6, 6, 0, 6, 0, 6]
     ],
     ![
       [4, 1, 6, 2, 2, 3, 4, 1, 5, 1, 0, 5, 1, 4, 4, 4, 4, 4],
       [5, 2, 2, 4, 3, 6, 2, 0, 4, 3, 1, 0, 5, 4, 2, 0, 0, 1]
     ],
     ![
       [6, 4, 2, 4, 2, 1, 6, 2, 5, 2, 6, 3, 4, 6, 5, 1, 1, 3],
       [1, 5, 0, 4, 5, 3, 6, 6, 2, 1, 2, 1, 0, 3, 1, 4, 3, 6]
     ],
     ![
       [3, 1, 6, 4, 3, 4, 1, 5, 5, 4, 0, 5, 6, 1, 0, 5, 2, 6],
       [1, 6, 2, 6, 6, 5, 5, 3, 0, 5, 3, 3, 1, 1, 6, 2, 4, 6]
     ]
   ]
 h' :=
   ![
     ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 1]],
     ![[4, 5, 1, 3, 2, 3, 4, 0, 1], [5, 5, 1, 5, 6, 6, 5, 5, 0, 4], [0, 0, 0, 0, 0, 0, 0, 1]],
     ![[1, 6, 2, 5, 3, 0, 5, 4, 3], [1, 3, 6, 1, 1, 5, 6, 6, 3, 2], [4, 5, 1, 3, 2, 3, 4, 0, 1]],
     ![[1, 1, 5, 3, 4, 2, 6, 5, 4], [1, 2, 5, 0, 5, 3, 0, 5, 6, 1], [1, 6, 2, 5, 3, 0, 5, 4, 3]],
     ![[2, 1, 1, 6, 4, 3, 0, 4, 4, 1], [6, 6, 4, 6, 0, 1, 4, 5, 4, 1], [1, 1, 5, 3, 4, 2, 6, 5, 4]],
     ![
       [5, 6, 4, 3, 0, 1, 2, 4, 2, 5],
       [6, 3, 0, 2, 0, 6, 4, 2, 0, 1],
       [2, 1, 1, 6, 4, 3, 0, 4, 4, 1]
     ],
     ![
       [3, 0, 0, 0, 1, 6, 0, 0, 3, 4],
       [0, 1, 2, 2, 5, 2, 5, 2, 0, 2],
       [5, 6, 4, 3, 0, 1, 2, 4, 2, 5]
     ],
     ![
       [5, 2, 2, 4, 5, 6, 6, 5, 4, 5],
       [0, 3, 5, 4, 1, 1, 2, 6, 3, 1],
       [3, 0, 0, 0, 1, 6, 0, 0, 3, 4]
     ],
     ![
       [3, 6, 6, 4, 2, 0, 5, 5, 0, 6],
       [2, 2, 6, 6, 0, 3, 5, 1, 6, 3],
       [5, 2, 2, 4, 5, 6, 6, 5, 4, 5]
     ],
     ![[0, 1], [2, 3, 6, 1, 3, 1, 4, 3, 6, 6], [3, 6, 6, 4, 2, 0, 5, 5, 0, 6]]
   ]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 6, 5, 4, 6, 2, 1, 6], [], [], [3, 2, 2, 5, 3, 6, 3, 0, 4], [], [], [], []]
 b := ![[],
   [],
   [2, 6, 3, 1, 2, 3, 0, 0, 3, 1],
   [],
   [],
   [5, 0, 5, 2, 3, 0, 4, 1, 0, 3],
   [],
   [],
   [],
   []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 17
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![3, 7]
 hp := by
  intro i
  fin_cases i
  · exact hp3.out
  · exact hp7.out
 hlc := by decide
 m := ![3, 3]
 F := fun i =>
  match i with
  | 0 => ![[2, 2, 1], [2, 2, 1], [1, 1, 2, 2, 1, 2, 2, 1, 0, 1, 0, 0, 0, 1]]
  | 1 => ![[5, 1], [6, 0, 4, 5, 5, 3, 1], [4, 2, 5, 3, 5, 5, 3, 4, 3, 4, 1]]
 D := fun i =>
  match i with
  | 0 => ![2, 2, 13]
  | 1 => ![1, 6, 10]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P1
  · dsimp; exact irreducible_ofList_of_linear (R := ZMod 7) _ (by decide) (by decide)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P2
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiExamplesIrreducibleIrreducibleExampleDegree17
