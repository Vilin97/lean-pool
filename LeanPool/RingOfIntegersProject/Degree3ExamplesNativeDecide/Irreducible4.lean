/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^3 - 18*X - 48 : ℤ[X])

local notation "l" => [-48, -18, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring

noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by native_decide
 hprim := by native_decide
 hlz := by native_decide
 s := 3
 P := 1019
 M := 15
 r := 17/4
 ρ := 577/68
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by native_decide
 hrho := by native_decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C
