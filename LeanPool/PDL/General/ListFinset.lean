/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic
import Mathlib.Data.Vector.Basic

/-! # General helper lemmas

Nothing in this file is about PDL. These are helper definitions and lemmas that are
used in several places and might also be in (newer versions of) Mathlib.
-/

namespace PDL

/-! ## Helpers about `List`s and `Finset`s -/

/-- Convert a list of formula-like lists into a finset of finsets. -/
@[simp]
def _root_.List.pdlToFinFin [DecidableEq α] : List (List α) → Finset (Finset α )
  | LS => (LS.map (fun L => L.toFinset)).toFinset

/-- Turning a mapped list into a `Finset` is the image of the `Finset`. -/
lemma List.toFinset_map_eq_image {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

/-! ## Helpers about `List.Vector` -/

lemma List.Vector.tail_last_eq_last {k : Nat} (l : List.Vector α k.succ.succ) :
    l.tail.last = l.last := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

end PDL
