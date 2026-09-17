/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Plane

/-!
# One positive bound for finitely many

Every "choose `ε` small enough for all of them" step in the development is this lemma: a
finite family of positive bounds has a single positive bound below all of them. The
polygonal-redrawing argument alone uses it three times, and the two-sided strip lemma chooses
its vertex disks and edge blocks the same way.

It is stated for a *predicate that is monotone downward in the bound* rather than as a `min`
fold, because no consumer wants the value — only that some positive value works for every
member at once.

## Blueprint

* `exists_pos_le_of_finite` — the numerical form.
* `exists_pos_forall_of_finite` — the form consumers use: a downward-monotone predicate
  holding at some positive bound for each member holds at one common positive bound.
-/

open Set

namespace Schoenflies

variable {ι : Type*}

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

/-- The form the geometry uses: if a property that only gets easier as the bound shrinks holds
at *some* positive bound for each member of a finite family, then it holds at *one* positive
bound for all of them at once. -/
theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  -- Pick a witness for each member, then take a positive bound below all the witnesses.
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies
