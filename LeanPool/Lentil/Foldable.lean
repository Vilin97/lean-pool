/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean

/-! ## A `Foldable` typeclass for big operators

A small typeclass abstracting collections that can be folded with a
commutative-associative operation, used to give big-conjunction and
big-disjunction TLA operators a uniform definition. -/

namespace TLA

-- HMM this is kind of awkward: we need `Std.Commutative` and `Std.Associative` to be able
-- to work on finset.
-- FIXME: how about removing this, and instead using `∀ ..., ... ∈ ... → ...`? do we really need this generic `fold`?
/-- A customized typeclass to express structures that can be folded upon. -/
class Foldable (c : Type u → Type v) where
  /-- Fold a finite collection with a commutative-associative operation. -/
  fold {α : Type u} {β : Type w} (op : β → β → β) [Std.Commutative op] [Std.Associative op]
    (b : β) (f : α → β) (s : c α) : β

instance : Foldable List where
  fold op _ _ b f s := List.foldr (op <| f ·) b s

/-- Folding over a list equals folding over its positional re-indexing
    through `List.finRange`. -/
theorem Foldable.list_index_form_change {α : Type u} {β : Type w} (op : β → β → β)
    [inst1 : Std.Commutative op] [inst2 : Std.Associative op]
    (b : β) (f : α → β) (l : List α) :
  Foldable.fold op b f l = Foldable.fold op b (f <| l[·]) (List.finRange l.length) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [Foldable.fold, List.finRange_succ] at *
    rw [ih]; apply congrArg
    rw [List.foldr_map]; simp

end TLA
