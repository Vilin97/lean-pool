/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

/-!
# Clearing a binary work tape — definitions

This module names the concrete time bound used by the public framed contract
for `TM.clearWorkTM`.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Concrete running-time bound for clearing and rewinding a Boolean work tape
whose represented string has `length` bits. -/
def clearWorkTimeBound (length : ℕ) : ℕ :=
  2 * length + 5

end TM

end Complexity
