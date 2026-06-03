/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Data.Option.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# LeanPool.QuasiBorelSpaces.Option.Instances

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Option.Instances`.
-/


variable {A : Type*}

namespace Option

instance instPreorderLeanPool [Preorder A] : Preorder (Option A) where
  le_refl x := by cases x <;> simp only [Option.le_none, Option.some_le_some, le_refl]
  le_trans x y z h₁ h₂ := by
    cases x <;> cases y <;> cases z <;>
    · simp only [Option.none_le, Option.le_none, reduceCtorEq, Option.some_le_some] at h₁ h₂
      try simp only [Option.some_le_some, Option.none_le, Option.le_none]
      try apply le_trans h₁ h₂
  lt_iff_le_not_ge x y := by
    cases x <;> cases y <;>
    · try simp only [
        Option.none_lt, Option.isSome_some, Option.none_le,
        Option.le_none, reduceCtorEq, not_false_eq_true, and_self,
        Option.not_lt_none, Option.le_none, not_true_eq_false, and_false,
        Option.some_lt_some, Option.some_le_some, lt_iff_le_not_ge]

/-- Bottom-order on options: `none` is bottom, `some` is ordered pointwise. -/
instance instPartialOrderLeanPool [PartialOrder A] : PartialOrder (Option A) where
  le_antisymm x y h₁ h₂ := by cases x <;> cases y <;> grind

instance instOrderBotLeanPool [LE A] : OrderBot (Option A) where
  bot := none
  bot_le _ := Option.none_le

end Option
