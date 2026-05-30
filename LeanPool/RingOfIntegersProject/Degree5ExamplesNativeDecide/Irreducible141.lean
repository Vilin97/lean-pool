/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 150*X^3 - 100*X^2 + 8025*X + 28260 : ℤ[X])

local notation "l" => [28260, 8025, -100, -150, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp13' : Fact <| Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp23' : Fact <| Nat.Prime 23 := fact_iff.2 (by norm_num)

def P13P1 : CertificateIrreducibleZModOfList' 13 4 2 3 [2, 11, 7, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [8, 7, 11, 1], [6, 12, 3, 10], [11, 6, 12, 2], [0, 1]]
 g := ![![[9, 6, 5, 4], [7, 12, 1], []],
   ![[7, 1, 3, 5, 2, 9], [10, 8, 12], [6, 3, 2, 7, 6, 1]],
   ![[10, 5, 10, 1, 12, 12], [11, 6, 12], [4, 2, 6, 12, 4, 12]],
   ![[0, 6, 9, 12, 9, 6], [5, 9, 1], [12, 8, 4, 3, 6, 8]]]
 h' := ![![[8, 7, 11, 1], [12, 3, 12, 2], [0, 0, 0, 1], [0, 1]],
   ![[6, 12, 3, 10], [3, 6, 6, 10], [6, 11, 11, 8], [8, 7, 11, 1]],
   ![[11, 6, 12, 2], [4, 10, 2, 10], [0, 0, 7, 5], [6, 12, 3, 10]],
   ![[0, 1], [0, 7, 6, 4], [7, 2, 8, 12], [11, 6, 12, 2]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [], [6, 11, 7], []]
 b := ![[], [], [9, 10, 4, 11], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [10, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [4, 22], [0, 1]]
 g := ![![[18, 3], [20, 12], [7, 16], [1]],![[7, 20], [22, 11], [2, 7], [1]]]
 h' := ![![[4, 22], [7, 7], [22, 14], [13, 4], [0, 1]],
   ![[0, 1], [12, 16], [9, 9], [6, 19], [4, 22]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [4]]
 b := ![[], [19, 2]]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

def P23P1 : CertificateIrreducibleZModOfList' 23 3 2 4 [20, 17, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [21, 10, 13], [21, 12, 10], [0, 1]]
 g := ![![[7, 2, 12], [12, 8, 13], [22, 19, 1], []],
   ![[19, 19, 6, 13], [0, 0, 13, 13], [2, 18, 5, 9], [21, 8]],
   ![[3, 21, 10, 11], [10, 2, 6, 20], [4, 3, 17, 11], [1, 8]]]
 h' := ![![[21, 10, 13], [13, 13, 9], [20, 5, 6], [0, 0, 1], [0, 1]],
   ![[21, 12, 10], [15, 16, 1], [21, 20, 22], [21, 18, 12], [21, 10, 13]],
   ![[0, 1], [4, 17, 13], [6, 21, 18], [7, 5, 10], [21, 12, 10]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [17, 11], []]
 b := ![[], [20, 11, 8], []]
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
 p := ![13, 23]
 hp := by
  intro i
  fin_cases i
  · exact hp13'.out
  · exact hp23'.out
 hlc := by decide +kernel
 m := ![2, 2]
 F := fun i =>
  match i with
  | 0 => ![[12, 1], [2, 11, 7, 1, 1]]
  | 1 => ![[10, 19, 1], [20, 17, 4, 1]]
 D := fun i =>
  match i with
  | 0 => ![1, 4]
  | 1 => ![2, 3]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i <;> fin_cases j
  · dsimp
    exact irreducible_ofList_of_linear (R := ZMod 13) _ (by decide +kernel) (by decide +kernel)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
