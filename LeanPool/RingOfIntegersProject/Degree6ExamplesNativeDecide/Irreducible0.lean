/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

namespace RoiDegree6ExamplesNativeDecideIrreducible0

open Polynomial

local notation "T" => (X^6 - 15*X^4 - 140*X^3 - 270*X^2 + 96*X + 3220 : ℤ[X])

local notation "l" => [3220, 96, -270, -140, -15, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
instance hp7' : Fact <| Nat.Prime 7 := fact_iff.2 (by norm_num)
/-- Auxiliary declaration for the worked example. -/
instance hp19' : Fact <| Nat.Prime 19 := fact_iff.2 (by norm_num)

/-- Auxiliary declaration for the worked example. -/
def P7P2 : CertificateIrreducibleZModOfList' 7 4 2 2 [1, 6, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [2, 4, 2, 5], [2, 4, 4, 1], [1, 5, 1, 1], [0, 1]]
 g := ![![[5, 1, 5, 1], []],
   ![[5, 1, 0, 0, 1, 5], [1, 3, 5, 3, 5, 6]],
   ![[3, 6, 4, 4, 2, 1], [5, 4, 0, 2, 3, 1]],
   ![[2, 1, 1, 1, 5, 1], [5, 3, 6, 6, 1, 1]]]
 h' := ![![[2, 4, 2, 5], [0, 0, 0, 1], [0, 1]],
   ![[2, 4, 4, 1], [0, 4, 3, 1], [2, 4, 2, 5]],
   ![[1, 5, 1, 1], [3, 0, 0, 6], [2, 4, 4, 1]],
   ![[0, 1], [3, 3, 4, 6], [1, 5, 1, 1]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [], [4, 5, 6], []]
 b := ![[], [], [2, 0, 0, 1], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [8, 16, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [16, 16, 1], [16, 2, 18], [0, 1]]
 g := ![![[17, 15, 7], [2, 18, 1], [13, 1], []],
   ![[1, 5, 8, 9], [10, 2, 15, 6], [5, 4], [7, 1]],
   ![[3, 8, 0, 13], [4, 16, 13, 3], [18, 9], [9, 1]]]
 h' := ![![[16, 16, 1], [3, 0, 8], [10, 12, 1], [0, 0, 1], [0, 1]],
   ![[16, 2, 18], [7, 1, 16], [3, 14, 14], [10, 12, 2], [16, 16, 1]],
   ![[0, 1], [12, 18, 14], [6, 12, 4], [13, 7, 16], [16, 2, 18]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [12, 16], []]
 b := ![[], [0, 18, 3], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
def P19P1 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 5, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide +kernel
 hP := by decide +kernel
 hlen := by decide +kernel
 htr := by decide +kernel
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide +kernel
 h := ![[0, 1], [11, 11, 3], [14, 7, 16], [0, 1]]
 g := ![![[5, 9, 16], [16, 3, 11], [6, 1], []],
   ![[18, 3, 9, 14], [7, 13, 7, 14], [9, 11], [6, 9]],
   ![[16, 10, 3, 11], [7, 9, 5, 1], [4, 7], [12, 9]]]
 h' := ![![[11, 11, 3], [1, 18, 15], [17, 14, 12], [0, 0, 1], [0, 1]],
   ![[14, 7, 16], [8, 8, 7], [3, 2, 12], [5, 0, 7], [11, 11, 3]],
   ![[0, 1], [17, 12, 16], [9, 3, 14], [2, 0, 11], [14, 7, 16]]]
 hs := by decide +kernel
 hz := by decide +kernel
 hmul := by decide +kernel
 a := ![[], [12, 16], []]
 b := ![[], [17, 12, 1], []]
 hhz := by decide +kernel
 hhn := by decide +kernel
 hgcd := by decide +kernel

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 2
 d := 6
 hprim := by decide +kernel
 hdeg := by decide +kernel
 hnn := by decide +kernel
 hdn := by decide +kernel
 p := ![7, 19]
 hp := by
  intro i
  fin_cases i
  · exact hp7'.out
  · exact hp19'.out
 hlc := by decide +kernel
 m := ![3, 2]
 F := fun i =>
  match i with
  | 0 => ![[0, 1], [5, 1], [1, 6, 3, 2, 1]]
  | 1 => ![[8, 16, 6, 1], [13, 5, 13, 1]]
 D := fun i =>
  match i with
  | 0 => ![1, 1, 4]
  | 1 => ![3, 3]
 hl := by decide +kernel
 hirr := by
  intro i j
  fin_cases i <;> fin_cases j
  · dsimp
    exact irreducible_ofList_of_linear (R := ZMod 7) _ (by decide +kernel) (by decide +kernel)
  · dsimp
    exact irreducible_ofList_of_linear (R := ZMod 7) _ (by decide +kernel) (by decide +kernel)
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P2
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  · dsimp; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
 hm := by decide +kernel
 hprod := by decide +kernel
 hinter := by decide +kernel

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C

end RoiDegree6ExamplesNativeDecideIrreducible0
