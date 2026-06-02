/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

/-!
Support declarations and worked examples for `RingOfIntegersProject`.
-/

namespace RoiDegree5ExamplesIrreducible124

open Polynomial

local notation "T" => (X^5 - 75*X^3 - 250*X^2 + 480 : ℤ[X])

local notation "l" => [480, 0, -250, -75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp11' : Fact <| Nat.Prime 11 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [7, 0, 3, 2, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 2, 4, 3], [4, 4, 0, 4, 2], [6, 10, 10, 2, 9], [8, 9, 10, 1, 8], [0, 1]]
 g := ![![[1, 1, 4], [1], []],
   ![[8, 9, 9, 0, 10, 1], [0, 1, 1, 6, 7, 5, 9, 5], [6, 10, 2, 9]],
   ![[4, 5, 0, 5, 0, 8, 10, 6], [9, 3, 7, 0, 7, 5, 7, 6], [5, 8, 5, 4]],
   ![[2, 5, 8, 3, 4, 7, 4, 1], [3, 4, 5, 0, 3, 2, 8, 4], [4, 0, 3, 4]],
   ![[3, 1, 5, 0, 1, 3, 2, 8], [5, 4, 6, 8], [6, 0, 5, 9]]]
 h' := ![![[4, 9, 2, 4, 3], [4, 0, 8, 9], [0, 0, 1], [0, 1]],
   ![[4, 4, 0, 4, 2], [9, 7, 6, 9], [7, 2, 10, 7, 8], [4, 9, 2, 4, 3]],
   ![[6, 10, 10, 2, 9], [6, 0, 0, 1, 5], [3, 9, 10, 3, 6], [4, 4, 0, 4, 2]],
   ![[8, 9, 10, 1, 8], [0, 10, 2, 1, 7], [8, 10, 0, 1, 8], [6, 10, 10, 2, 9]],
   ![[0, 1], [9, 5, 6, 2, 10], [0, 1, 1], [8, 9, 10, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 10, 3, 1], [], [], []]
 b := ![[], [1, 8, 10, 8, 7], [], [], []]
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
  | 0 => ![[7, 0, 3, 2, 0, 1]]
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

end RoiDegree5ExamplesIrreducible124
