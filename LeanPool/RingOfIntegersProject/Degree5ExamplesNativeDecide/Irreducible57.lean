/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesNativeDecideIrreducible57

open Polynomial

local notation "T" => (X^5 - 40*X^3 - 10*X^2 - 15*X - 8 : ℤ[X])

local notation "l" => [-8, -15, -10, -40, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp13' : Fact <| Nat.Prime 13 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [5, 11, 3, 12, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [11, 5, 2, 10, 7], [5, 2, 8, 7, 10], [8, 1, 1, 4, 2], [2, 4, 2, 5, 7], [0, 1]]
 g := ![![[3, 8, 1, 7, 1], [0, 1], []],
   ![[3, 1, 8, 11, 12, 1, 7, 6], [1, 11, 5, 4], [12, 5, 12, 8, 0, 7, 1, 5]],
   ![[0, 8, 1, 7, 10, 11, 8, 1], [1, 12, 0, 9], [8, 9, 10, 0, 10, 8, 7, 12]],
   ![[9, 0, 7, 2, 8, 3, 11, 6], [6, 12, 5, 1], [7, 11, 0, 4, 5, 12, 9, 8]],
   ![[4, 4, 4, 7, 2, 5, 1, 11], [7, 5, 7, 10], [6, 8, 5, 10, 7, 5, 7, 5]]]
 h' := ![![[11, 5, 2, 10, 7], [0, 8, 2, 10, 1], [0, 0, 0, 1], [0, 1]],
   ![[5, 2, 8, 7, 10], [4, 9, 2, 7, 8], [10, 7, 9, 2, 11], [11, 5, 2, 10, 7]],
   ![[8, 1, 1, 4, 2], [5, 11, 4, 7, 11], [7, 4, 6, 0, 10], [5, 2, 8, 7, 10]],
   ![[2, 4, 2, 5, 7], [12, 5, 12, 9, 9], [9, 8, 9, 4, 12], [8, 1, 1, 4, 2]],
   ![[0, 1], [7, 6, 6, 6, 10], [4, 7, 2, 6, 6], [2, 4, 2, 5, 7]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [3, 9, 0, 1], [], [], []]
 b := ![[], [7, 1, 11, 1, 11], [], [], []]
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
  | 0 => ![[5, 11, 3, 12, 0, 1]]
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

end RoiDegree5ExamplesNativeDecideIrreducible57
