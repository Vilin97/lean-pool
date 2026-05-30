/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesIrreducible117

open Polynomial

local notation "T" => (X^5 - 60*X^3 - 80*X^2 + 735*X + 1764 : ℤ[X])

local notation "l" => [1764, 735, -80, -60, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

instance hp11' : Fact <| Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp29' : Fact <| Nat.Prime 29 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[7, 9], [4, 1], [1]],![[9, 2], [3, 10], [1]]]
 h' := ![![[10, 10], [1, 8], [3, 10], [0, 1]],![[0, 1], [4, 3], [4, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [5, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 3 2 3 [6, 10, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10, 7], [0, 0, 4], [0, 1]]
 g := ![![[9, 0, 9], [2, 1, 1], []],
   ![[6, 7, 9, 10], [10, 8], [2, 5]],
   ![[0, 9, 4, 5], [9, 0, 6, 4], [5, 5]]]
 h' := ![![[1, 10, 7], [10, 7, 8], [0, 0, 1], [0, 1]],
   ![[0, 0, 4], [6, 6, 5], [0, 3], [1, 10, 7]],
   ![[0, 1], [1, 9, 9], [3, 8, 10], [0, 0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8], []]
 b := ![[], [8, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 4 2 4 [28, 8, 23, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 22, 19, 24], [22, 15, 11, 6], [26, 20, 28, 28], [0, 1]]
 g := ![![[15, 1, 28, 23], [25, 1, 28], [3, 2, 5, 1], []],
   ![[20, 16, 27, 20, 5, 7], [1, 11, 23], [7, 5, 17, 28, 4, 13], [8, 11, 3, 7, 17, 20]],
   ![[2, 9, 4, 5, 22, 23], [3, 16, 13], [15, 7, 21, 20, 24, 25], [2, 16, 22, 20, 6, 13]],
   ![[21, 13, 11, 1, 22, 1], [15, 10, 4], [4, 4, 13, 26, 19, 9], [18, 2, 9, 11, 21, 28]]]
 h' := ![![[15, 22, 19, 24], [5, 17, 0, 20], [3, 7, 7, 17], [0, 0, 0, 1], [0, 1]],
   ![[22, 15, 11, 6], [2, 21, 4, 4], [28, 20, 9, 20], [19, 7, 0, 3], [15, 22, 19, 24]],
   ![[26, 20, 28, 28], [26, 14, 5, 17], [20, 2, 1, 19], [7, 1, 17, 3], [22, 15, 11, 6]],
   ![[0, 1], [6, 6, 20, 17], [22, 0, 12, 2], [20, 21, 12, 22], [26, 20, 28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 14, 3], []]
 b := ![[], [], [16, 21, 18, 14], []]
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
 p := ![11, 29]
 hp := by
  intro i
  fin_cases i
  · exact hp11'.out
  · exact hp29'.out
 hlc := by decide
 m := ![2, 2]
 F := fun i =>
  match i with
  | 0 => ![[8, 1, 1], [6, 10, 10, 1]]
  | 1 => ![[5, 1], [28, 8, 23, 24, 1]]
 D := fun i =>
  match i with
  | 0 => ![2, 3]
  | 1 => ![1, 4]
 hl := by decide
 hirr := by
  intro i j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  · dsimp; exact irreducible_ofList_of_linear (R := ZMod 29) _ (by decide) (by decide)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P1
 hm := by decide
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesIrreducible117
