/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

/-!
Support declarations and worked examples for `RingOfIntegersProject`.
-/

namespace RoiDegree3ExamplesNativeDecideIrreducible5

open Polynomial

local notation "T" => (X^3 + 18*X - 24 : ℤ[X])

local notation "l" => [-24, 18, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num; ring

/-- Auxiliary declaration for the worked example. -/
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide +kernel
 hprim := by decide +kernel
 hlz := by decide +kernel
 s := 4
 P := 743
 M := 14
 r := 4
 ρ := 17/2
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

end RoiDegree3ExamplesNativeDecideIrreducible5
