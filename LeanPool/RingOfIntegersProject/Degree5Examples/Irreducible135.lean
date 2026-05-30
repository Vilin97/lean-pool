/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesIrreducible135

open Polynomial

local notation "T" => (X^5 - 50*X^3 - 50*X^2 + 1125*X + 910 : ℤ[X])

local notation "l" => [910, 1125, -50, -50, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp17' : Fact <| Nat.Prime 17 := fact_iff.2 (by norm_num)

def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [9, 3, 1, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 8, 15, 8], [3, 3, 16, 13, 8], [2, 10, 10, 8], [11, 1, 0, 15, 1], [0, 1]]
 g := ![![[15, 0, 12, 11, 4], [16, 16, 0, 1], [], []],
   ![[15, 5, 1, 10, 11, 11, 9, 2], [14, 13, 5, 1], [16, 16, 4, 9], [2, 0, 2, 13]],
   ![[16, 6, 12, 9, 0, 11, 5, 16], [13, 15, 14, 1], [6, 3, 14, 8], [5, 4, 4, 13]],
   ![[4, 16, 12, 14, 14, 5, 8], [6, 9, 12, 16], [8, 9, 8, 13], [7, 13]],
   ![[5, 3, 16, 3, 7, 11, 8, 1], [1, 10, 1, 1], [16, 8, 13, 1], [5, 3, 13, 1]]]
 h' := ![![[1, 2, 8, 15, 8], [9, 12, 4, 10, 15], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],
   ![[3, 3, 16, 13, 8], [6, 6, 1, 2, 8], [9, 12, 6, 11, 1], [0, 15, 0, 5, 14], [1, 2, 8, 15, 8]],
   ![[2, 10, 10, 8], [3, 0, 8, 5, 11], [1, 2, 9, 7, 1], [15, 1, 1, 2, 12], [3, 3, 16, 13, 8]],
   ![[11, 1, 0, 15, 1], [10, 4, 16, 5, 1], [9, 1, 3, 7, 13], [9, 4, 9, 8, 9], [2, 10, 10, 8]],
   ![[0, 1], [16, 12, 5, 12, 16], [5, 2, 16, 9, 1], [8, 14, 6, 2, 16], [11, 1, 0, 15, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 12, 7, 15], [], [], []]
 b := ![[], [13, 2, 6, 13, 13], [], [], []]
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
 p := ![17]
 hp := by
  intro i
  fin_cases i
  exact hp17'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[9, 3, 1, 1, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesIrreducible135
