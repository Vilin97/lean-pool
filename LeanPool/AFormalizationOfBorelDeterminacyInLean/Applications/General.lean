/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.TautoSet
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Notation
import Mathlib.Order.Filter.Basic

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.General

Auxiliary declarations for the Borel determinacy formalization.
-/


lemma diff_subset_union {I} {A B C : Set I} : A \ C ⊆ (A \ B) ∪ (B \ C) := by tauto_set
lemma projection_formula {α β} (f : α → β) (X : Set α) (Y : Set β) :
  Disjoint X (f⁻¹' Y) ↔ Disjoint (f '' X) Y := by --exists?
  constructor <;> intro h
  · rw [Set.disjoint_iff] at *; rintro _ ⟨⟨x, hx, rfl⟩, hy⟩; exact h ⟨hx, hy⟩
  · exact Set.disjoint_of_subset_left (Set.subset_preimage_image f X) (h.preimage f)

namespace Filter
variable {α β γ : Type*} {s t : Set α} {l : Filter α}
lemma mem_congr (h : s =ᶠ[l] t) : s ∈ l ↔ t ∈ l := by
  apply congr_sets
  rwa [eventuallyEq_set, eventually_iff] at h
lemma eventuallyEq_set' {α} {s t : Set α} {l : Filter α} :
  l.EventuallyEq s t ↔ (s \ t)ᶜ ∈ l ∧ (t \ s)ᶜ ∈ l := by
  constructor <;> intro h
  · simp [Filter.mem_congr (h.diff (Filter.EventuallyEq.refl _ t)).compl,
      Filter.mem_congr ((Filter.EventuallyEq.refl _ t).diff h).compl]
  · rw [Filter.eventuallyEq_set]; filter_upwards [h.1, h.2]; tauto_set
end Filter
