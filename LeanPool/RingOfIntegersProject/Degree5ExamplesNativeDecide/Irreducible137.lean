/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesNativeDecideIrreducible137

open Polynomial

local notation "T" => (X^5 - 90*X^3 - 240*X^2 + 2160*X + 10368 : ℤ[X])

local notation "l" => [10368, 2160, -240, -90, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp13' : Fact <| Nat.Prime 13 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [7, 2, 7, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [12, 5, 9, 10, 11], [2, 1, 5, 6, 5], [1, 3, 1, 2], [11, 3, 11, 8, 10], [0, 1]]
 g := ![![[2, 8, 0, 1, 1], [0, 1], []],
   ![[11, 7, 11, 5, 0, 5], [2, 4, 1, 4], [4, 6, 12, 1, 7, 10, 3, 5]],
   ![[8, 3, 2, 10, 5, 8], [1, 12, 9, 4], [12, 2, 7, 6, 9, 10, 8, 8]],
   ![[6, 11, 5, 5, 10, 1, 7], [6, 4, 0, 1], [6, 7, 8, 12, 8]],
   ![[4, 9, 4, 10, 2, 9, 1, 3], [8, 8, 6, 1], [7, 0, 6, 7, 9, 8, 8, 12]]]
 h' := ![![[12, 5, 9, 10, 11], [0, 6, 11, 6, 12], [0, 0, 0, 1], [0, 1]],
   ![[2, 1, 5, 6, 5], [8, 9, 5, 2], [10, 4, 10, 3, 11], [12, 5, 9, 10, 11]],
   ![[1, 3, 1, 2], [10, 5, 12, 8], [2, 0, 7, 12, 2], [2, 1, 5, 6, 5]],
   ![[11, 3, 11, 8, 10], [1, 12, 5, 11, 6], [11, 0, 9, 0, 1], [1, 3, 1, 2]],
   ![[0, 1], [8, 7, 6, 12, 8], [8, 9, 0, 10, 12], [11, 3, 11, 8, 10]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [4, 3, 2, 6], [], [], []]
 b := ![[], [1, 7, 7, 3, 3], [], [], []]
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
 p := ![13]
 hp := by
  intro i
  fin_cases i
  exact hp13'.out
 hlc := by decide +kernel
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[7, 2, 7, 1, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesNativeDecideIrreducible137
