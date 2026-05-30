/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 5*X^3 - 10*X^2 - 16 : ℤ[X])

local notation "l" => [-16, 0, -10, -5, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp7' : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [5, 0, 4, 2, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [3, 0, 3, 4, 3], [5, 2, 3, 3, 2], [1, 2, 5, 0, 1], [5, 2, 3, 0, 1], [0, 1]]
 g := ![![[5, 0, 1], []],![[0, 4, 6, 4, 4, 3, 2, 6], [3, 2, 6, 1, 5, 3, 3, 6]],![[6, 5, 6, 3, 3, 4, 3, 4], [6, 5, 4, 3, 6, 4, 1, 1]],![[6, 1, 2, 3, 0, 5, 4, 1], [3, 6, 6, 3, 2, 6, 0, 1]],![[0, 4, 0, 1, 5, 2, 5, 4], [4, 2, 6, 0, 2, 0, 0, 1]]]
 h' := ![![[3, 0, 3, 4, 3], [0, 0, 0, 1], [0, 1]],![[5, 2, 3, 3, 2], [5, 4, 4, 5, 4], [3, 0, 3, 4, 3]],![[1, 2, 5, 0, 1], [4, 6, 3, 2, 4], [5, 2, 3, 3, 2]],![[5, 2, 3, 0, 1], [0, 4, 6, 2, 1], [1, 2, 5, 0, 1]],![[0, 1], [0, 0, 1, 4, 5], [5, 2, 3, 0, 1]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [4, 1, 2], [], [], []]
 b := ![[], [3, 4, 6, 4], [], [], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

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
  | 0 => ![[5, 0, 4, 2, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![5]
 hl := by decide +kernel
 hirr := by
  intro i; intro j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
