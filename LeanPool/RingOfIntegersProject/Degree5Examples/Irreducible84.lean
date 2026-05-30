/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

namespace RoiDegree5ExamplesIrreducible84

open Polynomial

local notation "T" => (X^5 - 15*X^3 - 210*X^2 - 540*X - 648 : ℤ[X])

local notation "l" => [-648, -540, -210, -15, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 4
 P := 318911
 M := 17
 r := 29/4
 ρ := 37829/3364
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

end RoiDegree5ExamplesIrreducible84
