/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesIrreducible95

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 50*X^2 + 80 : ℤ[X])

local notation "l" => [80, 0, -50, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp11' : Fact <| Nat.Prime 11 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [3, 0, 5, 8, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 0, 10, 6, 1], [9, 1, 5, 6, 10], [5, 9, 0, 3, 6], [10, 0, 7, 7, 5], [0, 1]]
 g := ![![[8, 3, 9], [1], []],
   ![[0, 3, 8, 10, 3, 5, 9, 1], [8, 9, 1, 3, 2, 3, 0, 5], [8, 4, 1, 1]],
   ![[5, 0, 2, 0, 9, 1, 8, 2], [1, 10, 3, 3, 4, 4, 8, 10], [6, 7, 10, 1]],
   ![[9, 2, 5, 7, 3, 1, 10, 10], [7, 7, 10, 8, 9, 9, 8, 6], [3, 7, 3, 3]],
   ![[10, 6, 6, 1, 10, 1, 8, 5], [8, 7, 7, 10, 1, 5, 8, 3], [7, 7, 4, 3]]]
 h' := ![![[9, 0, 10, 6, 1], [8, 0, 6, 3], [0, 0, 1], [0, 1]],
   ![[9, 1, 5, 6, 10], [1, 3, 10, 4, 10], [2, 10, 5, 10, 4], [9, 0, 10, 6, 1]],
   ![[5, 9, 0, 3, 6], [1, 9, 7, 7, 8], [8, 8, 9, 10, 1], [9, 1, 5, 6, 10]],
   ![[10, 0, 7, 7, 5], [5, 2, 9, 9, 3], [5, 3, 2, 6, 10], [5, 9, 0, 3, 6]],
   ![[0, 1], [5, 8, 1, 10, 1], [2, 1, 5, 7, 7], [10, 0, 7, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3, 3, 1], [], [], []]
 b := ![[], [9, 0, 3, 3, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![11]
 hp := by
  intro i
  fin_cases i
  exact hp11'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[3, 0, 5, 8, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesIrreducible95
