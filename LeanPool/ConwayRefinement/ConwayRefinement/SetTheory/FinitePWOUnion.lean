/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Finite unions of partially well-ordered sets

A union indexed by a finite type is partially well ordered when every member is. This is the
finite-family form of closure of partially well-ordered subsets of a linear order under union.
-/

universe u v

namespace Set.IsPWO

variable {α : Type u} {ι : Type v} [LinearOrder α]

public section

/-- A finite union of partially well-ordered sets is partially well ordered. -/
theorem iUnion_of_finite [Finite ι] (S : ι → Set α) (hS : ∀ i, (S i).IsPWO) :
    (⋃ i, S i).IsPWO := by
  classical
  cases nonempty_fintype ι
  have hfin : ∀ t : Finset ι, (⋃ i ∈ t, S i).IsPWO := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ht =>
      rw [Finset.set_biUnion_insert]
      exact (hS i).union ht
  simpa using hfin Finset.univ

end

end Set.IsPWO
