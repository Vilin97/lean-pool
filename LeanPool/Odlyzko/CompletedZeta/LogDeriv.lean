/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.Defs
public import Mathlib.Analysis.Calculus.LogDeriv

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_dedekindDiscriminantFactor (s : ℂ) :
    logDeriv (CompletedZeta.discriminantFactor K) s =
      Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 := by
  change logDeriv (fun z : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (z / 2)) s = _
  rw [logDeriv_apply]
  have hderiv :
      deriv (fun z : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (z / 2)) s =
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) *
          deriv (fun z : ℂ ↦ z / 2) s *
            ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) :=
    Complex.deriv_const_cpow (f := fun z : ℂ ↦ z / 2) (x := s) (by simp) _
  rw [hderiv]
  have hdiv : deriv (fun z : ℂ ↦ z / 2) s = 1 / 2 :=
    ((hasDerivAt_id s).div_const 2).deriv
  rw [hdiv]
  have hne : (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)) ≠ 0 :=
    dedekindDiscriminantFactor_ne_zero K s
  grind

end NumberField.Odlyzko
