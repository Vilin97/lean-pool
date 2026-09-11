/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Lean.LabelAttribute

/-!
# LeanPool.Rupert.Attr

Imported Lean Pool material for `LeanPool.Rupert.Attr`.
-/

@[expose] public section

/-- Simp set for evaluating concrete matrices in Rupert certificates. -/
register_simp_attr matrix_simps
