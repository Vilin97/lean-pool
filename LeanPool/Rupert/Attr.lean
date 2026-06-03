/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

/-!
# LeanPool.Rupert.Attr

Imported Lean Pool material for `LeanPool.Rupert.Attr`.
-/

/-- Simp set for evaluating concrete matrices in Rupert certificates. -/
register_simp_attr matrix_simps
