/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanPool.RingOfIntegersProject.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 10*X^3 - 15*X^2 + 10*X - 12 : ℤ[X])

local notation "l" => [-12, 10, -15, 10, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by native_decide
 hprim := by native_decide
 hlz := by native_decide
 s := 6
 P := 65141
 M := 13
 r := 3
 ρ := 19/3
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by native_decide
 hrho := by native_decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
