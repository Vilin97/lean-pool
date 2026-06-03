/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! # ForMathlibFunctionsBoundedAtInfty -/


@[expose] public section

open UpperHalfPlane

theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, Pi.neg_apply, norm_neg]

alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff
