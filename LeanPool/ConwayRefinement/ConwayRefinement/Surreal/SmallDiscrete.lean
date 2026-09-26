/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Basic
public import Mathlib.Logic.Small.Set

/-!
# Small sets of surreals are discrete

No small family of positive surreals reaches down to zero: the surreal born between zero and the
family is positive and below all of it (`exists_pos_lt_of_small`). Every small set of surreals is
therefore discrete — around any point sits an interval meeting the set only there
(`exists_Ioo_inter_subset_singleton_of_small`).

This is why an analysis by limit points of a support has to be carried out over a small group of
exponents rather than over the surreals themselves. A surreal has a small support, so its support
has no limit points at all inside the surreals, and every rank computed there collapses. Over a
small exponent group the positive elements do have a small coinitial family, limit points exist,
and the analysis has content; the factorisations it produces are equations, and equations transfer
back along the embedding of exponents whatever the ranks do.
-/

universe u

public noncomputable section

namespace Surreal

/-- **No small family of positive surreals is coinitial.** The surreal born from zero on the left
and the family on the right is positive and lies below every member. -/
theorem exists_pos_lt_of_small {P : Set Surreal.{u}} [Small.{u} P] (hP : ∀ p ∈ P, 0 < p) :
    ∃ q : Surreal.{u}, 0 < q ∧ ∀ p ∈ P, q < p := by
  have hsep : ∀ x ∈ ({0} : Set Surreal.{u}), ∀ y ∈ P, x < y := by
    rintro _ rfl y hy
    exact hP y hy
  refine ⟨!{({0} : Set Surreal.{u}) | P}, ?_, fun p hp ↦ ?_⟩
  · exact lt_ofSets_of_mem_left (H := hsep) rfl
  · exact ofSets_lt_of_mem_right (H := hsep) hp

/-- **A small set of surreals is discrete.** Around any surreal there is an interval meeting a
given small set only at that surreal, obtained from a positive surreal below all the distances
from it to the other members. -/
theorem exists_Ioo_inter_subset_singleton_of_small {S : Set Surreal.{u}} [Small.{u} S]
    (p : Surreal.{u}) :
    ∃ a b : Surreal.{u}, a < p ∧ p < b ∧ Set.Ioo a b ∩ S ⊆ {p} := by
  classical
  set d : Surreal.{u} → Surreal.{u} := fun s ↦ max (s - p) (p - s) with hd
  have hsub : (S \ {p} : Set Surreal.{u}) ⊆ S := Set.sdiff_subset
  have : Small.{u} (S \ {p} : Set Surreal.{u}) := small_subset hsub
  obtain ⟨q, hq, hlt⟩ := exists_pos_lt_of_small (P := d '' (S \ {p})) (by
    rintro _ ⟨s, hs, rfl⟩
    rw [hd, lt_max_iff]
    rcases lt_trichotomy s p with h | h | h
    · exact Or.inr (sub_pos.mpr h)
    · exact absurd h fun h' ↦ hs.2 (by simp [h'])
    · exact Or.inl (sub_pos.mpr h))
  refine ⟨p - q, p + q, sub_lt_self p hq, lt_add_of_pos_right p hq, fun s hs ↦ ?_⟩
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hs.1
  have hclose : d s < q := by
    rw [hd, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [sub_lt_iff_lt_add, add_comm]
      exact h₂
    · rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
      exact h₁
  exact absurd hclose (not_lt.mpr (hlt _ ⟨s, ⟨hs.2, hne⟩, rfl⟩).le)

end Surreal
