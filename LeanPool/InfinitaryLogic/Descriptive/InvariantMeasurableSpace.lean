/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.LogicAction
/-!
# Complement closure for isomorphism-invariant classes

The complement of an isomorphism-invariant class of coded structures is again invariant. This
elementary lemma is the only closure property needed by the retained López–Escobar branch.
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

variable [L.IsRelational]

/-- Isomorphism invariance is closed under complement. -/
theorem IsomorphismInvariant.compl {B : Set (StructureSpace L)} (h : IsomorphismInvariant B) :
    IsomorphismInvariant Bᶜ := fun c d hcd => by
  simp only [Set.mem_compl_iff]; rw [h c d hcd]

end FirstOrder.Language
