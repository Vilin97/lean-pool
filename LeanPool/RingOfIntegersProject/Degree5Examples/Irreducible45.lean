/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 600 : ℤ[X])

local notation "l" => [-600, 0, 0, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp11' : Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [5, 0, 0, 8, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 10, 4, 3], [7, 7, 6, 1, 4], [6, 6, 5, 5, 4], [1, 5, 1, 1], [0, 1]]
 g := ![![[5, 0, 9], [1], []],![[2, 8, 0, 7, 2, 0, 10, 5], [1, 8, 7, 9, 9, 1, 5, 5], [5, 4, 2, 9]],![[1, 1, 9, 5, 5, 3, 5, 4], [7, 10, 4, 7, 5, 0, 10, 4], [4, 9, 8, 5]],![[10, 9, 5, 1, 2, 8, 0, 4], [6, 3, 5, 1, 8, 7, 8, 4], [9, 3, 7, 5]],![[0, 2, 5, 6, 0, 4, 9], [3, 7, 2, 1, 6, 7, 9], [2, 1]]]
 h' := ![![[8, 3, 10, 4, 3], [6, 0, 0, 3], [0, 0, 1], [0, 1]],![[7, 7, 6, 1, 4], [8, 6, 0, 10, 8], [6, 6, 5, 6, 8], [8, 3, 10, 4, 3]],![[6, 6, 5, 5, 4], [0, 9, 2, 6, 1], [7, 9, 5, 8, 1], [7, 7, 6, 1, 4]],![[1, 5, 1, 1], [5, 2, 2, 2, 10], [2, 2, 6, 1, 10], [6, 6, 5, 5, 4]],![[0, 1], [0, 5, 7, 1, 3], [2, 5, 5, 7, 3], [1, 5, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3, 0, 7], [], [], []]
 b := ![[], [9, 0, 8, 8, 5], [], [], []]
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
  | 0 => ![[5, 0, 0, 8, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
 hm := by decide
 hprod := by decide!
 hinter := by decide!

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
