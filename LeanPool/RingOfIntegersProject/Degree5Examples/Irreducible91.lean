/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesIrreducible91

open Polynomial

local notation "T" => (X^5 + 35*X^3 - 90*X^2 + 270*X - 396 : ℤ[X])

local notation "l" => [-396, 270, -90, 35, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp7' : Fact <| Nat.Prime 7 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 4, 1, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 4, 3, 6], [1, 3, 0, 3, 5], [5, 2, 6, 3, 1], [1, 1, 4, 5, 2], [0, 1]]
 g := ![![[0, 0, 1], []],
   ![[2, 1, 4, 2, 4, 3, 1, 5], [5, 1, 0, 6, 5, 6, 2, 6]],
   ![[2, 4, 1, 1, 3, 3, 5, 3], [2, 3, 0, 5, 1, 2, 1, 6]],
   ![[3, 1, 0, 1, 2, 2, 4, 4], [3, 6, 1, 0, 0, 3, 2, 1]],
   ![[5, 6, 4, 5, 2, 4, 4, 1], [3, 1, 3, 5, 5, 2, 4, 1]]]
 h' := ![![[0, 0, 4, 3, 6], [0, 0, 0, 1], [0, 1]],
   ![[1, 3, 0, 3, 5], [6, 5, 5, 2, 3], [0, 0, 4, 3, 6]],
   ![[5, 2, 6, 3, 1], [2, 6, 6, 4, 4], [1, 3, 0, 3, 5]],
   ![[1, 1, 4, 5, 2], [4, 1, 4, 2, 5], [5, 2, 6, 3, 1]],
   ![[0, 1], [6, 2, 6, 5, 2], [1, 1, 4, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 0, 4, 6], [], [], []]
 b := ![[], [6, 6, 6, 1, 6], [], [], []]
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
  | 0 => ![[3, 4, 1, 0, 0, 1]]
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

end RoiDegree5ExamplesIrreducible91
