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

namespace RoiDegree5ExamplesIrreducible85

open Polynomial

local notation "T" => (X^5 - 50*X^3 + 200*X - 160 : ℤ[X])

local notation "l" => [-160, 200, 0, -50, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp7' : Fact <| Nat.Prime 7 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [1, 4, 0, 6, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3, 6, 4], [4, 4, 4, 0, 3], [1, 3, 1, 4, 4], [3, 3, 3, 6], [0, 1]]
 g := ![![[1, 0, 1], []],
   ![[2, 4, 6, 3, 3, 6, 1], [0, 6, 3, 1, 1]],
   ![[3, 5, 2, 1, 3, 0, 3, 3], [2, 4, 5, 6, 3, 2, 0, 6]],
   ![[1, 3, 0, 0, 0, 4, 0, 4], [6, 3, 2, 3, 6, 3, 3, 1]],
   ![[0, 6, 3, 1, 3, 2, 6], [6, 5, 2, 2, 6]]]
 h' := ![![[6, 3, 6, 4], [0, 0, 0, 1], [0, 1]],
   ![[4, 4, 4, 0, 3], [6, 3, 6, 2, 4], [6, 3, 6, 4]],
   ![[1, 3, 1, 4, 4], [6, 5, 6, 4, 1], [4, 4, 4, 0, 3]],
   ![[3, 3, 3, 6], [2, 3, 2, 3, 1], [1, 3, 1, 4, 4]],
   ![[0, 1], [0, 3, 0, 4, 1], [3, 3, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 6, 6], [], [], []]
 b := ![[], [1, 2, 5, 6, 2], [], [], []]
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
 p := ![7]
 hp := by
  intro i
  fin_cases i
  exact hp7'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[1, 4, 0, 6, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesIrreducible85
