/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 + 75*X^3 - 150*X^2 + 1350*X - 4860 : ℤ[X])

local notation "l" => [-4860, 1350, -150, 75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp11' : Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [2, 8, 4, 9, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by native_decide
 hP := by native_decide
 hlen := by native_decide
 htr := by native_decide
 bit := ![1, 1, 0, 1]
 hbits := by native_decide
 h := ![[0, 1], [5, 1, 8, 8, 8], [1, 8, 5, 4, 5], [9, 3, 8, 7, 2], [7, 9, 1, 3, 7], [0, 1]]
 g := ![![[3, 6, 4], [1], []],![[1, 6, 7, 7, 2, 8, 8, 10], [6, 0, 7, 6, 0, 5, 3, 7], [1, 1, 7, 9]],![[7, 4, 7, 8, 0, 8, 5, 9], [1, 5, 9, 7, 5, 9, 4, 3], [1, 6, 7, 3]],![[9, 9, 2, 8, 1, 7, 7, 7], [9, 0, 2, 3, 2, 8], [10, 1, 6, 4]],![[5, 8, 3, 2, 3, 6, 6, 7], [0, 0, 5, 2, 7, 2], [9, 0, 9, 5]]]
 h' := ![![[5, 1, 8, 8, 8], [9, 3, 7, 2], [0, 0, 1], [0, 1]],![[1, 8, 5, 4, 5], [4, 8, 3, 9, 9], [1, 0, 0, 9, 7], [5, 1, 8, 8, 8]],![[9, 3, 8, 7, 2], [10, 9, 7, 0, 9], [10, 7, 8, 4, 4], [1, 8, 5, 4, 5]],![[7, 9, 1, 3, 7], [9, 4, 5, 10, 3], [6, 5, 5, 2], [9, 3, 8, 7, 2]],![[0, 1], [6, 9, 0, 1, 1], [9, 10, 8, 7], [7, 9, 1, 3, 7]]]
 hs := by native_decide
 hz := by native_decide
 hmul := by native_decide
 a := ![[], [7, 8, 3, 3], [], [], []]
 b := ![[], [4, 1, 7, 0, 1], [], [], []]
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
  | 0 => ![[2, 8, 4, 9, 0, 1]]
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
