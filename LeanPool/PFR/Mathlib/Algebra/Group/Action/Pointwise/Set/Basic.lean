/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Pointwise set operations
-/

open scoped Pointwise

namespace Set
variable {α : Type*}

section Mul
variable [Mul α]

@[to_additive]
public
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul



end Mul
end Set
