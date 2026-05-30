/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 60*X^3 - 330*X^2 - 765*X - 666 : ℤ[X])

local notation "l" => [-666, -765, -330, -60, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp19' : Fact $ Nat.Prime 19 := fact_iff.2 (by norm_num)

def P13P1 : CertificateIrreducibleZModOfList' 13 4 2 3 [3, 1, 6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 6, 2], [1, 12, 3, 1], [3, 5, 4, 10], [0, 1]]
 g := ![![[6, 1, 5, 9], [8, 12, 1], []],![[4, 12, 2, 2, 10, 7], [4, 9, 10], [12, 6, 10, 5, 12, 8]],![[2, 2, 1, 8, 1, 4], [1, 11, 9], [9, 9, 5, 10, 8, 1]],![[4, 10, 9, 9, 3, 9], [7, 2, 4], [7, 3, 11, 5, 5, 12]]]
 h' := ![![[8, 8, 6, 2], [2, 8, 2, 10], [0, 0, 0, 1], [0, 1]],![[1, 12, 3, 1], [0, 2, 11, 7], [8, 11, 6, 7], [8, 8, 6, 2]],![[3, 5, 4, 10], [10, 5, 8, 2], [0, 0, 12, 3], [1, 12, 3, 1]],![[0, 1], [2, 11, 5, 7], [6, 2, 8, 2], [3, 5, 4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 10, 9], []]
 b := ![[], [], [1, 11, 8, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18], [0, 1]]
 g := ![![[5, 11], [7, 5], [17], [1]],![[14, 8], [18, 14], [17], [1]]]
 h' := ![![[6, 18], [16, 7], [15, 10], [5, 6], [0, 1]],![[0, 1], [1, 12], [18, 9], [3, 13], [6, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [13, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 3 2 4 [4, 0, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 13, 5], [11, 5, 14], [0, 1]]
 g := ![![[9, 3, 9], [6, 11, 4], [13, 1], []],![[2, 13, 16, 4], [0, 17, 0, 16], [16, 6], [18, 6]],![[1, 12, 1, 14], [4, 2, 0, 10], [6, 17], [9, 6]]]
 h' := ![![[2, 13, 5], [14, 0, 3], [5, 15, 17], [0, 0, 1], [0, 1]],![[11, 5, 14], [0, 8, 15], [0, 6, 8], [8, 9, 5], [2, 13, 5]],![[0, 1], [3, 11, 1], [0, 17, 13], [9, 10, 13], [11, 5, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 6], []]
 b := ![[], [8, 16, 14], []]
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
 p := ![13, 19]
 hp := by
  intro i
  fin_cases i
  exact hp13'.out
  exact hp19'.out
 hlc := by decide
 m := ![2, 2]
 F := fun i =>
  match i with
  | 0 => ![[12, 1], [3, 1, 6, 1, 1]]
  | 1 => ![[14, 13, 1], [4, 0, 6, 1]]
 D := fun i =>
  match i with
  | 0 => ![1, 4]
  | 1 => ![2, 3]
 hl := by decide
 hirr := by
  intro i; intro j
  fin_cases i <;> fin_cases j
  · exact irreducible_ofList_of_linear (R := ZMod 13) _ (by decide) (by decide)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
