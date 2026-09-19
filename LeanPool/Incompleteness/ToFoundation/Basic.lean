/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
import Mathlib.Algebra.Order.Ring.Nat

/-! # Basic -/

@[expose] public section


namespace Fin

/-- Imported declaration from the Incompleteness formalization. -/
@[inline] def addCast (m) : Fin n → Fin (m + n) := castLE <| Nat.le_add_left n m

@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl

end Fin

namespace Matrix

variable {α : Type*}

@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]

@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]

end Matrix
