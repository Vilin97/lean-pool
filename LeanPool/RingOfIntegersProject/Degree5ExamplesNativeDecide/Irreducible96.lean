/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesNativeDecideIrreducible96

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 250*X^2 - 750*X - 1100 : ℤ[X])

local notation "l" => [-1100, -750, -250, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp7' : Fact <| Nat.Prime 7 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 6, 2, 3, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [4, 4, 0, 3, 5], [5, 0, 2, 1], [5, 2, 1, 0, 2], [0, 0, 4, 3], [0, 1]]
 g := ![![[4, 0, 1], []],
   ![[5, 2, 2, 4, 5, 1, 6, 3], [6, 2, 5, 5, 4, 5, 1, 6]],
   ![[5, 4, 4, 3, 4, 6, 4], [1, 3, 2, 6, 1]],
   ![[2, 2, 1, 2, 1, 2], [2, 0, 4, 5, 1, 2, 0, 1]],
   ![[0, 1, 6, 3, 1, 5, 3], [0, 1, 0, 3, 6]]]
 h' := ![![[4, 4, 0, 3, 5], [0, 0, 0, 1], [0, 1]],
   ![[5, 0, 2, 1], [0, 4, 5, 0, 3], [4, 4, 0, 3, 5]],
   ![[5, 2, 1, 0, 2], [0, 4, 6, 4, 5], [5, 0, 2, 1]],
   ![[0, 0, 4, 3], [1, 5, 2, 1], [5, 2, 1, 0, 2]],
   ![[0, 1], [0, 1, 1, 1, 6], [0, 0, 4, 3]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [2, 4, 4, 6], [], [], []]
 b := ![[], [6, 4, 5, 3, 3], [], [], []]
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
 p := ![7]
 hp := by
  intro i
  fin_cases i
  exact hp7'.out
 hlc := by decide +kernel
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[6, 6, 2, 3, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i
  fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesNativeDecideIrreducible96
