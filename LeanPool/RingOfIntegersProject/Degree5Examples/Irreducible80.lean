/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 + 15*X^3 - 170*X^2 + 60*X - 168 : ℤ[X])

local notation "l" => [-168, 60, -170, 15, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp11' : Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [8, 5, 6, 4, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 5, 3, 2, 1], [8, 6, 5, 7, 5], [6, 3, 7, 1], [5, 7, 7, 1, 5], [0, 1]]
 g := ![![[1, 4, 5], [1], []],![[7, 9, 7, 10, 4, 0, 1, 4], [9, 1, 3, 5, 2, 8, 10, 5], [0, 6, 4, 1]],![[5, 1, 4, 8, 0, 3, 7, 9], [2, 5, 6, 10, 6, 1], [8, 10, 4, 3]],![[1, 3, 6, 4, 9, 10, 5], [6, 5, 6, 6, 2, 0, 5], [3, 1]],![[7, 10, 4, 4, 8, 8, 1, 3], [9, 10, 8, 1, 6, 4], [4, 4, 10, 3]]]
 h' := ![![[3, 5, 3, 2, 1], [3, 6, 5, 7], [0, 0, 1], [0, 1]],![[8, 6, 5, 7, 5], [6, 7, 4, 10, 9], [9, 4, 3, 0, 4], [3, 5, 3, 2, 1]],![[6, 3, 7, 1], [6, 5, 2, 5, 2], [0, 9, 8, 3], [8, 6, 5, 7, 5]],![[5, 7, 7, 1, 5], [2, 1, 4, 10, 7], [1, 2, 4, 3, 7], [6, 3, 7, 1]],![[0, 1], [8, 3, 7, 1, 4], [4, 7, 6, 5], [5, 7, 7, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 0, 8, 3], [], [], []]
 b := ![[], [0, 3, 1, 9, 8], [], [], []]
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
 p := ![11]
 hp := by
  intro i
  fin_cases i
  exact hp11'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[8, 5, 6, 4, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i; intro j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
