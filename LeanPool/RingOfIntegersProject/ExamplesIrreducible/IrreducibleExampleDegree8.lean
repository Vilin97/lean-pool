/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^8 - 2*X^7 + 2*X^6 + 4*X^5 - 8*X^4 + 2*X^3 + 5*X^2 - 4*X + 1 : ℤ[X])

local notation "l" => [1, -4, 5, 2, -8, 4, 2, -2, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)

def P2P0 : CertificateIrreducibleZModOfList' 2 4 2 1 [1, 1, 0, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 1], [1, 0, 1], [0, 1]]
 g := ![![[]],![[1]],![[]],![[1]]]
 h' := ![![[0, 0, 1], [0, 1]],![[1, 1], [0, 0, 1]],![[1, 0, 1], [1, 1]],![[0, 1], [1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [], []]
 b := ![[], [], [1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 n := 1
 d := 4
 s := 1789
 P := 283093
 M := -12
 r := 7/4
 ρ := 15/4
 hPPrime := by norm_num
 hrpos := by norm_num
 hnn := by decide
 hdn := by decide
 p := ![2]
 hp := by
  intro i
  fin_cases i
  exact hp2.out
 hlc := by decide
 m := ![2]
 F := fun i =>
  match i with
  | 0 => ![[1, 1, 0, 0, 1], [1, 1, 0, 0, 1]]
 D := fun i =>
  match i with
  | 0 => ![4, 4]
 hl := by decide
 hirr := by
  intro i; intro j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P0
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C
