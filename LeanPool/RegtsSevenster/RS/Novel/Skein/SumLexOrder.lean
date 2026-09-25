/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSplit

/-!
# The lexicographic order on disjoint-union labels

Plain `α ⊕ β` carries no linear order in mathlib (only the `⊕ₗ`
synonym does); the corrected constrained value of a `disjUnion`
needs one for its through-product orientation.  This file
transports the lexicographic order to the plain sum (left before
right) and pins the disjoint-union factorization interface — the
multiplicativity of the corrected value, first target of the
factorization chain.
-/

namespace RS

-- Deliberately semireducible: supplied explicitly via `letI` in
-- the gluing chain, never by instance search.
/-- The lexicographic linear order on a plain sum type: left
before right. -/
@[instance_reducible]
def sumLexLinearOrder (α β : Type) [LinearOrder α]
    [LinearOrder β] : LinearOrder (α ⊕ β) :=
  LinearOrder.lift' (toLex : α ⊕ β → α ⊕ₗ β) (fun _ _ h => h)

section Lemmas

variable {α β : Type}

/-- Within the left block the order is the left order. -/
theorem sumLex_inl_lt_inl_iff [LinearOrder α] [LinearOrder β]
    {a a' : α} :
    (sumLexLinearOrder α β).lt (Sum.inl a) (Sum.inl a') ↔
      a < a' := by
  change toLex (Sum.inl a) < toLex (Sum.inl a') ↔ _
  exact Sum.Lex.inl_lt_inl_iff

/-- Within the right block, the right order. -/
theorem sumLex_inr_lt_inr_iff [LinearOrder α] [LinearOrder β]
    {b b' : β} :
    (sumLexLinearOrder α β).lt (Sum.inr b) (Sum.inr b') ↔
      b < b' := by
  change toLex (Sum.inr b) < toLex (Sum.inr b') ↔ _
  exact Sum.Lex.inr_lt_inr_iff

/-- Every left label precedes every right one. -/
theorem sumLex_inl_lt_inr [LinearOrder α] [LinearOrder β]
    (a : α) (b : β) :
    (sumLexLinearOrder α β).lt (Sum.inl a) (Sum.inr b) := by
  change toLex (Sum.inl a) < toLex (Sum.inr b)
  exact Sum.Lex.inl_lt_inr a b

/-- And no right label precedes a left one. -/
theorem sumLex_not_inr_lt_inl [LinearOrder α] [LinearOrder β]
    (a : α) (b : β) :
    ¬ (sumLexLinearOrder α β).lt (Sum.inr b) (Sum.inl a) := by
  change ¬ toLex (Sum.inr b) < toLex (Sum.inl a)
  exact fun h => absurd (lt_trans (Sum.Lex.inl_lt_inr a b) h)
    (lt_irrefl _)

end Lemmas

end RS
