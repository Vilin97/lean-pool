/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Data.Set.Functor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

namespace LeanPool.Sard

/-!
# Coercions between sets and subtypes

Auxiliary API for viewing an intersection `s ∩ t` as a subset of the subtype `t`.
-/
-- Coercion of sets and subsets.
-- Based on a Zulip discussion about casting sets to subsets.

namespace Set
variable {X : Type*} (s t : Set X)

-- first variant uses a proof of inclusion: is not as nice to work with
/-- If two subsets `s` and `t` satisfy `s ⊆ t` and `h` is a proof of this inclusion,
`toSubset' s t h` is the set `s` as a subset of `t`. -/
def toSubset' (h : s ≤ t) : Set t := Set.range (Set.inclusion h)

@[simp]
lemma mem_toSubset' (h : s ≤ t)
    (x : t) : x ∈ toSubset' s t h ↔ ↑x ∈ s := by
  rw [toSubset', Set.range_inclusion, Set.mem_setOf_eq]

/-- Given sets `s t : Set X`, `Set.toSubset s t` is `s ∩ t` realized as a term of `Set t`. -/
def toSubset : Set t := (Subtype.val · ∈ s)

@[simp]
lemma mem_toSubset (x : t) : x ∈ toSubset s t ↔ ↑x ∈ s := Iff.rfl

@[simp]
lemma coe_toSubset : (Set.toSubset s t : Set X) = s ∩ t := by
  ext
  simp
end Set

open Set

/-- The image of `s ∩ w` agrees with the image of `s` viewed inside the subtype `w`. -/
lemma toSubset_aux1 {X Y : Type*} (f : X → Y) {s w : Set X} (hsw : s ⊆ w) :
    f '' (s ∩ w) = (w.restrict f) '' (Set.toSubset s w) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsw hx.1⟩, by simpa using hx.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨by simpa using hx, x.2⟩, rfl⟩

/-- `toSubset` commutes with countable unions. -/
lemma toSubset_iUnion {X : Type*} {t : Set X} (S : ℕ → Set X) :
    Set.toSubset (⋃ n, S n) t = ⋃ n, Set.toSubset (S n) t := by
  ext
  simp

/-- If `s` is compact and `s ⊆ t`, then `s` is compact as a subset of the subtype `t`. -/
lemma toSubset_compact {X : Type*} [TopologicalSpace X] {s t : Set X} (hsw : s ⊆ t)
    (hs : IsCompact s) : IsCompact (Set.toSubset s t) := by
  have h_univ : IsCompact (Set.univ : Set s) := isCompact_iff_isCompact_univ.mp hs
  have h_image : IsCompact (Set.inclusion hsw '' (Set.univ : Set s)) :=
    h_univ.image (continuous_inclusion hsw)
  convert h_image
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, hx⟩, trivial, ?_⟩
    ext
    rfl
  · rintro ⟨a, _, ha⟩
    have h_value : (a : X) = x := congrArg Subtype.val ha
    simp [← h_value, a.property]

end LeanPool.Sard
