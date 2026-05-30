/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 75*X^3 - 100*X^2 + 1500*X + 3840 : ℤ[X])

local notation "l" => [3840, 1500, -100, -75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp19' : Fact <| Nat.Prime 19 := fact_iff.2 (by norm_num)

def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [2, 18, 14, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 9, 8, 1, 8], [7, 9, 4, 5, 2], [12, 5, 9, 11, 13], [17, 14, 17, 2, 15], [0, 1]]
 g := ![![[18, 3, 8, 4, 11], [2, 5, 18, 0, 1], [], []],
   ![[7, 12, 4, 2, 18, 16, 12, 15], [1, 10, 9, 16, 10, 8, 0, 3], [2, 12, 9, 9], [8, 8, 16, 7]],
   ![[6, 8, 6, 14, 17, 13, 3, 10], [10, 6, 10, 7, 3, 12, 4, 8], [4, 5, 10, 7], [0, 18, 1, 4]],
   ![[17, 13, 2, 7, 3, 5, 14, 12], [9, 5, 4, 0, 5, 0, 16, 15], [10, 5, 1, 9], [13, 15, 1, 17]],
   ![[12, 6, 16, 2, 4, 12, 4, 10], [18, 2, 17, 6, 17, 12, 13, 10], [1, 1, 14, 7], [14, 4, 3, 16]]]
 h' :=
   ![
     ![[2, 9, 8, 1, 8], [15, 11, 17, 3, 7], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],
     ![[7, 9, 4, 5, 2], [1, 9, 8, 13, 16], [7, 9, 10, 17, 13], [7, 9, 15, 11, 3], [2, 9, 8, 1, 8]],
     ![
       [12, 5, 9, 11, 13],
       [6, 16, 3, 8, 10],
       [18, 17, 14, 17, 2],
       [11, 14, 1, 16, 11],
       [7, 9, 4, 5, 2]
     ],
     ![
       [17, 14, 17, 2, 15],
       [3, 15, 10, 10, 13],
       [15, 7, 9, 15, 11],
       [4, 8, 15, 3, 16],
       [12, 5, 9, 11, 13]
     ],
     ![[0, 1], [8, 6, 0, 4, 11], [4, 5, 5, 8, 11], [14, 7, 6, 8, 8], [17, 14, 17, 2, 15]]
   ]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 8, 13, 7], [], [], []]
 b := ![[], [13, 5, 16, 16, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![19]
 hp := by
  intro i
  fin_cases i
  exact hp19'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[2, 18, 14, 1, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
