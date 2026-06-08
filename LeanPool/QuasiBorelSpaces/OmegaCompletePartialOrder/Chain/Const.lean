/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Order.OmegaCompletePartialOrder

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const`.
-/


namespace OmegaCompletePartialOrder.Chain

variable {A : Type*} [Preorder A]

/-- The chain that always returns the same value. -/
def const (x : A) : Chain A where
  toOrderHom := OrderHom.const ℕ x

@[simp]
lemma const_apply (x : A) (n : ℕ) : const x n = x := by
  rfl

end OmegaCompletePartialOrder.Chain
