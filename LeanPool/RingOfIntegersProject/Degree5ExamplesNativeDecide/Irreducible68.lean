/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 25*X^3 - 1200 : ℤ[X])

local notation "l" => [-1200, 0, 0, -25, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp11' : Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [10, 0, 0, 8, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 1, 0, 1]
 hbits := by native_decide
 h := ![[0, 1], [5, 1, 9, 4, 6], [10, 6, 4, 9, 2], [10, 7, 0, 3, 7], [8, 7, 9, 6, 7], [0, 1]]
 g := ![![[5, 0, 9], [1], []],![[6, 0, 9, 0, 10, 6], [6, 5, 5, 3, 4, 9, 0, 2], [8, 1, 4, 3]],![[10, 7, 5, 2, 5, 3, 8, 8], [5, 4, 8, 6, 4, 8, 5, 10], [6, 10, 3, 4]],![[2, 3, 2, 10, 1, 6, 4, 6], [10, 5, 3, 7, 9, 8, 3, 7], [4, 2, 9, 5]],![[1, 2, 3, 0, 6, 8, 3, 2], [0, 10, 4, 6, 4, 6, 9, 10], [7, 1, 7, 5]]]
 h' := ![![[5, 1, 9, 4, 6], [1, 0, 0, 3], [0, 0, 1], [0, 1]],![[10, 6, 4, 9, 2], [6, 5, 5, 10], [0, 0, 7, 8, 9], [5, 1, 9, 4, 6]],![[10, 7, 0, 3, 7], [0, 7, 5, 9, 9], [7, 9, 9, 8, 7], [10, 6, 4, 9, 2]],![[8, 7, 9, 6, 7], [7, 3, 1, 5, 9], [5, 10, 3, 0, 1], [10, 7, 0, 3, 7]],![[0, 1], [2, 7, 0, 6, 4], [5, 3, 2, 6, 5], [8, 7, 9, 6, 7]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [0, 5, 5, 8], [], [], []]
 b := ![[], [9, 1, 9, 8, 6], [], [], []]
 hhz := by native_decide
 hhn := by native_decide
 hgcd := by native_decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by native_decide
 hdeg := by native_decide
 hnn := by native_decide
 hdn := by native_decide
 p := ![11]
 hp := by 
  intro i
  fin_cases i
  exact hp11'.out
 hlc := by native_decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[10, 0, 0, 8, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by native_decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
 hm := by native_decide
 hprod := by native_decide
 hinter := by native_decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
