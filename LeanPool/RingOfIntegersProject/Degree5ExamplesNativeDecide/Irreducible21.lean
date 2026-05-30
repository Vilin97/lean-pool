/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

namespace RoiDegree5ExamplesNativeDecideIrreducible21

open Polynomial

local notation "T" => (X^5 - 20*X^3 - 40*X^2 + 135*X + 284 : ℤ[X])

local notation "l" => [284, 135, -40, -20, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide +kernel
 hprim := by decide +kernel
 hlz := by decide +kernel
 s := 2
 P := 238639
 M := 14
 r := 17/4
 ρ := 609/68
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

end RoiDegree5ExamplesNativeDecideIrreducible21
