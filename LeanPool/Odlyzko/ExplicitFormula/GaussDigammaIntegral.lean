/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gauss Digamma Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma integrand used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-x) - Complex.exp (-s * x)) /
    (1 - Complex.exp (-x))

theorem integral_cexp_neg_mul_Ioi {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-s * x)) = 1 / s := by
  have hneg : (-s).re < 0 := by simpa using hs
  rw [integral_exp_mul_complex_Ioi hneg 0]
  simp

end NumberField.Odlyzko
