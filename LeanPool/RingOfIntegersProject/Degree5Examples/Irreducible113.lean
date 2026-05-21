/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 220*X^2 + 915*X - 888 : ℤ[X])

local notation "l" => [-888, 915, -220, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp7' : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]],![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]],![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 2, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 2], [6, 6, 5], [0, 1]]
 g := ![![[1, 0, 4], [1]],![[2, 1, 0, 2], [5, 3, 2, 1]],![[6, 5, 5, 3], [1, 5, 0, 6]]]
 h' := ![![[3, 0, 2], [3, 5, 2], [0, 1]],![[6, 6, 5], [0, 6, 1], [3, 0, 2]],![[0, 1], [2, 3, 4], [6, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 5], []]
 b := ![[], [5, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P13P1 : CertificateIrreducibleZModOfList' 13 4 2 3 [8, 6, 10, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6, 9, 2], [12, 3, 10, 8], [1, 3, 7, 3], [0, 1]]
 g := ![![[9, 12, 3, 1], [0, 6, 1], []],![[1, 8, 12, 4, 2, 11], [3, 4, 10], [7, 4, 5, 10, 0, 8]],![[10, 10, 1, 2, 6, 11], [4, 3, 3], [8, 7, 1, 1, 0, 5]],![[8, 0, 7, 11, 9, 12], [6, 9, 4], [0, 9, 5, 5, 0, 1]]]
 h' := ![![[6, 6, 9, 2], [0, 4, 8, 12], [0, 0, 0, 1], [0, 1]],![[12, 3, 10, 8], [5, 5, 6, 8], [4, 2, 4, 6], [6, 6, 9, 2]],![[1, 3, 7, 3], [7, 4, 12, 4], [0, 9, 3, 4], [12, 3, 10, 8]],![[0, 1], [5, 0, 0, 2], [1, 2, 6, 2], [1, 3, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 4, 1], []]
 b := ![[], [], [4, 8, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![7, 13]
 hp := by 
  intro i
  fin_cases i
  exact hp7'.out
  exact hp13'.out
 hlc := by decide
 m := ![2, 2]
 F := fun i =>
  match i with 
  | 0 => ![[2, 2, 1], [4, 2, 5, 1]]
  | 1 => ![[6, 1], [8, 6, 10, 7, 1]]
 D := fun i =>
  match i with 
  | 0 => ![2, 3]
  | 1 => ![1, 4]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  · exact irreducible_ofList_of_linear (R := ZMod 13) _ (by decide) (by decide)
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
 hm := by decide
 hprod := by decide!
 hinter := by decide!

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
