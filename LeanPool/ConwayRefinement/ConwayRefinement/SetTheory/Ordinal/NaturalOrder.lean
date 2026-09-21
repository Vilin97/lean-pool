/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# The ordered multiplicative monoid of natural ordinals

Natural ordinal multiplication is commutative and strictly order-preserving away from zero.
This supplies the bundled ordered monoid with zero used by Mathlib valuations, retaining the
existing natural operations and order.
-/

public noncomputable section
namespace NatOrdinal

instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero NatOrdinal where
  bot := 0
  bot_le := fun _ ↦ zero_le
  isBot_zero := fun _ ↦ zero_le

end NatOrdinal
