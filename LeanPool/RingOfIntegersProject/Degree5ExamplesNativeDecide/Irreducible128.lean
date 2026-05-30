/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesNativeDecideIrreducible128

open Polynomial

local notation "T" => (X^5 - 200*X^2 - 450*X + 480 : ℤ[X])

local notation "l" => [480, -450, -200, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp17' : Fact <| Nat.Prime 17 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 9, 4, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1],
   [10, 12, 12, 4, 1],
   [10, 14, 8, 14, 9],
   [8, 8, 11, 10, 11],
   [6, 16, 3, 6, 13],
   [0, 1]]
 g := ![![[6, 5, 0, 4, 13], [13, 0, 0, 1], [], []],
   ![[1, 14, 15, 9, 10, 10, 2, 9], [7, 15, 14, 2], [0, 0, 16, 4], [14, 6, 8, 1]],
   ![[3, 11, 8, 5, 14, 13, 11, 2], [11, 3, 13, 1], [9, 10, 7, 16], [16, 0, 14, 13]],
   ![[6, 10, 8, 14, 14, 7, 16, 10], [13, 15, 1, 2], [1, 2, 12, 1], [14, 2, 16, 2]],
   ![[12, 16, 3, 1, 7, 1, 13, 9], [6, 3, 13, 9], [5, 9, 13, 9], [14, 12, 3, 16]]]
 h' :=
   ![
     ![[10, 12, 12, 4, 1], [16, 2, 16, 13, 8], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],
     ![
       [10, 14, 8, 14, 9],
       [10, 4, 12, 0, 3],
       [15, 15, 7, 4, 6],
       [10, 5, 4, 13, 15],
       [10, 12, 12, 4, 1]
     ],
     ![
       [8, 8, 11, 10, 11],
       [11, 0, 15, 14, 15],
       [2, 15, 8, 15, 1],
       [2, 0, 15, 3, 4],
       [10, 14, 8, 14, 9]
     ],
     ![
       [6, 16, 3, 6, 13],
       [12, 16, 15, 1, 2],
       [9, 6, 0, 10, 6],
       [8, 11, 0, 6, 1],
       [8, 8, 11, 10, 11]
     ],
     ![[0, 1], [12, 12, 10, 6, 6], [6, 15, 2, 5, 3], [14, 1, 14, 12, 14], [6, 16, 3, 6, 13]]
   ]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [13, 0, 2, 5], [], [], []]
 b := ![[], [0, 7, 5, 1, 12], [], [], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by decide +kernel
 hdeg := by decide +kernel
 hnn := by decide +kernel
 hdn := by decide +kernel
 p := ![17]
 hp := by
  intro i
  fin_cases i
  exact hp17'.out
 hlc := by decide +kernel
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[4, 9, 4, 0, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesNativeDecideIrreducible128
