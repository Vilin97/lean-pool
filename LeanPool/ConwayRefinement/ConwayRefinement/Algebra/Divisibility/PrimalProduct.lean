/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite products of primal elements

Mathlib records that a unit is primal and that the product of two primal elements of a
cancellative commutative monoid with zero is primal. This file iterates the binary statement to
finite products indexed by a list.
-/

universe u

public section

/-- A product of primal elements over a list is primal. -/
theorem isPrimal_list_prod {M : Type u} [CommMonoidWithZero M] [IsCancelMulZero M]
    {l : List M} (hl : ∀ c ∈ l, IsPrimal c) : IsPrimal l.prod := by
  induction l with
  | nil => simpa using isUnit_one.isPrimal
  | cons c cs ih =>
      rw [List.prod_cons]
      exact (hl c List.mem_cons_self).mul (ih fun d hd ↦ hl d (List.mem_cons_of_mem c hd))

end
