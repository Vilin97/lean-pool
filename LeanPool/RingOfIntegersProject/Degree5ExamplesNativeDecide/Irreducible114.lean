/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree5ExamplesNativeDecideIrreducible114

open Polynomial

local notation "T" => (X^5 - 75*X^3 - 200*X^2 + 150*X - 60 : ℤ[X])

local notation "l" => [-60, 150, -200, -75, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp13' : Fact <| Nat.Prime 13 := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp19' : Fact <| Nat.Prime 19 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[7, 4], [4], [8, 1]],![[0, 9], [4], [3, 12]]]
 h' := ![![[8, 12], [3, 11], [11, 2], [0, 1]],![[0, 1], [0, 2], [1, 11], [8, 12]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
def P13P1 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 5, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 0, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [11, 5, 6], [7, 7, 7], [0, 1]]
 g := ![![[4, 0, 9], [10, 12], [1]],
   ![[12, 9, 12, 11], [11, 12], [7, 0, 8, 8]],
   ![[3, 0, 0, 6], [3, 9], [6, 10, 1, 5]]]
 h' := ![![[11, 5, 6], [5, 1, 10], [6, 8, 5], [0, 1]],
   ![[7, 7, 7], [0, 1, 11], [8, 12, 5], [11, 5, 6]],
   ![[0, 1], [9, 11, 5], [2, 6, 3], [7, 7, 7]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [0, 10], []]
 b := ![[], [6, 8, 7], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
def P19P1 : CertificateIrreducibleZModOfList' 19 4 2 4 [1, 1, 10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [15, 4, 10, 7], [1, 13, 1, 8], [0, 1, 8, 4], [0, 1]]
 g := ![![[4, 3, 5, 17], [12, 12, 14, 9], [1], []],
   ![[11, 8, 13, 13, 3, 1], [10, 14, 13, 4], [3, 4, 16], [10, 12, 11]],
   ![[0, 18, 12, 13, 10, 8], [1, 5, 17, 8, 16, 10], [0, 12, 9], [2, 14, 7]],
   ![[0, 0, 2, 8, 2, 16], [1, 1, 8, 17, 14, 9], [18, 14, 1], [16, 16, 16]]]
 h' := ![![[15, 4, 10, 7], [7, 15, 8, 13], [18, 18, 9, 16], [0, 0, 1], [0, 1]],
   ![[1, 13, 1, 8], [4, 1, 16, 7], [14, 10, 14], [6, 3, 3, 15], [15, 4, 10, 7]],
   ![[0, 1, 8, 4], [0, 0, 8, 1], [1, 6, 9, 14], [18, 10, 16, 3], [1, 13, 1, 8]],
   ![[0, 1], [18, 3, 6, 17], [10, 4, 6, 8], [3, 6, 18, 1], [0, 1, 8, 4]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [], [16, 14, 1], []]
 b := ![[], [], [4, 17, 16, 7], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 5
 hprim := by decide +kernel
 hdeg := by decide +kernel
 hnn := by decide +kernel
 hdn := by decide +kernel
 p := ![13, 19]
 hp := by
  intro i
  fin_cases i
  · exact hp13'.out
  · exact hp19'.out
 hlc := by decide +kernel
 m := ![2, 2]
 F := fun i =>
  match i with
  | 0 => ![[10, 5, 1], [7, 5, 8, 1]]
  | 1 => ![[16, 1], [1, 1, 10, 3, 1]]
 D := fun i =>
  match i with
  | 0 => ![2, 3]
  | 1 => ![1, 4]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i <;> fin_cases j
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  · dsimp
    exact irreducible_ofList_of_linear (R := ZMod 19) _ (by decide +kernel) (by decide +kernel)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree5ExamplesNativeDecideIrreducible114
