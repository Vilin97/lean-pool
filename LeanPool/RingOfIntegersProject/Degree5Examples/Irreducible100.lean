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

namespace RoiDegree5ExamplesIrreducible100

open Polynomial

local notation "T" => (X^5 - 45*X^3 - 10*X^2 + 150*X + 228 : ℤ[X])

local notation "l" => [228, 150, -10, -45, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp13' : Fact <| Nat.Prime 13 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [7, 7, 3, 7, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1, 2, 9, 1], [10, 6, 4, 12, 2], [7, 9, 1, 2, 2], [9, 9, 6, 3, 8], [0, 1]]
 g := ![![[0, 11, 11, 3, 10], [0, 1], []],
   ![[6, 1, 12, 3, 11, 9, 8, 10], [12, 12, 2, 1], [1, 1, 1, 5, 11, 8, 1, 1]],
   ![[10, 2, 8, 6, 8, 1, 12, 7], [0, 11, 8, 12], [10, 4, 7, 7, 5, 11, 1, 8]],
   ![[12, 0, 0, 0, 3, 0, 8, 7], [7, 0, 10, 3], [0, 11, 5, 5, 0, 6, 11, 8]],
   ![[2, 2, 5, 12, 6, 5, 10, 8], [10, 8, 3, 9], [4, 7, 2, 2, 2, 7, 4, 5]]]
 h' := ![![[0, 1, 2, 9, 1], [0, 6, 6, 10, 6], [0, 0, 0, 1], [0, 1]],
   ![[10, 6, 4, 12, 2], [4, 2, 1, 9, 7], [6, 12, 9, 1, 1], [0, 1, 2, 9, 1]],
   ![[7, 9, 1, 2, 2], [10, 0, 0, 11, 7], [7, 12, 2, 6, 5], [10, 6, 4, 12, 2]],
   ![[9, 9, 6, 3, 8], [2, 9, 9, 7, 7], [5, 11, 7, 11, 4], [7, 9, 1, 2, 2]],
   ![[0, 1], [9, 9, 10, 2, 12], [12, 4, 8, 7, 3], [9, 9, 6, 3, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 11, 0, 7], [], [], []]
 b := ![[], [4, 12, 11, 11, 6], [], [], []]
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
 p := ![13]
 hp := by
  intro i
  fin_cases i
  exact hp13'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[7, 7, 3, 7, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesIrreducible100
