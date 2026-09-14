/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- only here we register simp attributes
-- details: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Attr/Core.html
module

public meta import Lean.Meta.Tactic.Simp.Simproc
meta import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Register

Imported Lean Pool material for `LeanPool.FormalizationOfBoundedArithmetic.Register`.
-/

@[expose] public section
/-- Simp set used by the bounded-arithmetic import for formula normalization. -/
register_simp_attr delta0_simps
