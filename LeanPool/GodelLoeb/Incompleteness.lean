/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Loeb

/-!
# Modal second incompleteness

This file derives the modal-axiomatic second incompleteness corollary
from Loeb's theorem. A consistent modal substrate cannot prove its own
modal consistency sentence `[]⊥ -> ⊥`.
-/

namespace ModalLogic.GoedelLoeb

open ModalFormula

universe u

/-- Consistency of the polymorphic modal substrate. -/
class Consistent (α : Type u) where
  not_bot : ¬ Provable (⊥ₛ : ModalFormula α)

/-- The modal consistency sentence. -/
def modalConsistencySentence {α : Type u} : ModalFormula α :=
  □ₛ⊥ₛ ⟶ ⊥ₛ

/-- Modal Goedel second incompleteness as a corollary of Loeb's theorem. -/
theorem secondIncompleteness {α : Type u} [DecidableEq α] [Diagonalisable α]
    [Consistent α] : ¬ Provable (modalConsistencySentence : ModalFormula α) := by
  intro h
  exact Consistent.not_bot (loeb h)

/-- The canonical proof predicate is consistent in the empty-frame witness. -/
instance canonicalConsistent (α : Type u) : Consistent α where
  not_bot := Provable.not_bot

end ModalLogic.GoedelLoeb
