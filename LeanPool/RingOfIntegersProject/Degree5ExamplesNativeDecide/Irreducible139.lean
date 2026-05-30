/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 100*X^2 - 525*X - 15720 : ℤ[X])

local notation "l" => [-15720, -525, -100, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp7' : Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp23' : Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)

def P7P1 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 6, 2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [1, 2, 1, 6], [2, 1, 0, 4], [0, 3, 6, 4], [0, 1]]
 g := ![![[2, 0, 3, 1], []],![[2, 0, 5, 2, 6, 5], [0, 6, 6, 5, 0, 6]],![[3, 5, 0, 1, 5, 4], [3, 5, 4, 6, 3, 1]],![[0, 6, 4, 2, 3, 1], [3, 4, 5, 5, 4, 1]]]
 h' := ![![[1, 2, 1, 6], [0, 0, 0, 1], [0, 1]],![[2, 1, 0, 4], [1, 2, 3, 3], [1, 2, 1, 6]],![[0, 3, 6, 4], [6, 0, 0, 6], [2, 1, 0, 4]],![[0, 1], [5, 5, 4, 4], [0, 3, 6, 4]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [], [2, 2, 6], []]
 b := ![[], [], [1, 5, 4, 2], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [11, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[6, 13], [6, 9], [7, 9], [1]],![[22, 10], [10, 14], [11, 14], [1]]]
 h' := ![![[3, 22], [3, 6], [15, 20], [12, 3], [0, 1]],![[0, 1], [21, 17], [6, 3], [21, 20], [3, 22]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [8]]
 b := ![[], [17, 4]]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

def P23P1 : CertificateIrreducibleZModOfList' 23 3 2 4 [22, 21, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [15, 18, 4], [5, 4, 19], [0, 1]]
 g := ![![[15, 8, 2], [7, 20, 18], [11, 20, 1], []],![[9, 19, 4, 16], [16, 22, 8, 12], [20, 4, 20, 18], [4, 16]],![[18, 22, 16, 10], [15, 20, 17, 19], [20, 8, 12, 15], [12, 16]]]
 h' := ![![[15, 18, 4], [7, 17, 18], [11, 19, 8], [0, 0, 1], [0, 1]],![[5, 4, 19], [14, 16, 2], [12, 1, 16], [22, 12, 4], [15, 18, 4]],![[0, 1], [22, 13, 3], [11, 3, 22], [14, 11, 18], [5, 4, 19]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [18, 9], []]
 b := ![[], [12, 17, 15], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 5
 hprim := by decide +kernel
 hdeg := by decide +kernel
 hnn := by decide +kernel
 hdn := by decide +kernel
 p := ![7, 23]
 hp := by
  intro i
  fin_cases i
  exact hp7'.out
  exact hp23'.out
 hlc := by decide +kernel
 m := ![2, 2]
 F := fun i =>
  match i with
  | 0 => ![[3, 1], [3, 6, 2, 4, 1]]
  | 1 => ![[11, 20, 1], [22, 21, 3, 1]]
 D := fun i =>
  match i with
  | 0 => ![1, 4]
  | 1 => ![2, 3]
 hl := by decide +kernel
 hirr := by
  intro i; intro j
  fin_cases i <;> fin_cases j
  · exact irreducible_ofList_of_linear (R := ZMod 7) _ (by decide +kernel) (by decide +kernel)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
