/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Exercise 1.25 (Scott 1981, PRG-19, §1) — final segments of an ordinal

Scott: let `Δ` be a well-ordered set (ordinal) and let `𝒟` be the family of
non-empty *final*
segments of `Δ`. Describe `|𝒟|`; are all elements finite; is every approximation
to a finite
element finite?

For a linear order, the *final segments* are exactly the non-empty **upper sets**
(`IsUpperSet`).
Any two upper sets of a linear order are nested (`upperSet_subset_or`), so the
family is a
neighbourhood system by Scott's nested-or-disjoint criterion
(`finalSegmentSystem`).

**Classification of `|𝒟|`.** For a *well-order* every non-empty upper set is
`Set.Ici a` with `a`
its minimum (`exists_Ici_of_mem`). Hence a filter `x` is completely described by
its trace
`lowerSetOf x = {a ∣ Ici a ∈ x}`, which is a **non-empty lower set** of `Δ`, and
`x ↦ lowerSetOf x`
is an order isomorphism

`|𝒟| ≃o {S : Set Δ ∣ S non-empty lower set}` (ordered by `⊆`)   —
`finalSegmentClassify`.

So `|𝒟|` is the lattice of non-empty initial segments of `Δ` (the "cuts" of `Δ`).

**Total / finite.** The greatest element is the filter of *all* neighbourhoods
(`topElement`),
which is the unique total element (`topElement_isTotal`,
`eq_topElement_of_isTotal`). The finite
elements are the principal filters `↑(Ici a)`. When `Δ` has no greatest element
(e.g. `ℕ = ω`) the
total element is **not** finite (`topElement_not_principal_of_noMax`): not all
elements are finite.

The system and `Ici` lemmas are `[propext, Quot.sound]`; the classification's
surjectivity uses
the well-ordering (`WellFounded.has_min`), so it is classical. -/

namespace Domain.Neighborhood

namespace FinalSegment

open NeighborhoodSystem

/-- In a linear order, any two upper sets are nested. (Hence final segments are
*nested-or-disjoint* — in fact always nested.) -/
theorem upperSet_subset_or {Δ : Type*} [LinearOrder Δ] {X Y : Set Δ}
    (hX : IsUpperSet X) (hY : IsUpperSet Y) : X ⊆ Y ∨ Y ⊆ X := by
  by_cases h : X ⊆ Y
  · exact Or.inl h
  · right
    rw [Set.not_subset] at h
    obtain ⟨a, haX, haY⟩ := h
    intro b hbY
    rcases le_total a b with hab | hba
    · exact hX hab haX
    · exact absurd (hY hba hbY) haY

/-- **Exercise 1.25 — the final-segment neighbourhood system.** Over a (non-empty)
linear order
`Δ`, the non-empty upper sets (final segments) form a neighbourhood system. Built
via
`ofNestedOrDisjoint` since any two upper sets are nested (`upperSet_subset_or`). -/
def finalSegmentSystem (Δ : Type*) [LinearOrder Δ] [Nonempty Δ] : NeighborhoodSystem Δ :=
  NeighborhoodSystem.ofNestedOrDisjoint
    (fun X => X.Nonempty ∧ IsUpperSet X)
    Set.univ
    ⟨Set.univ_nonempty, isUpperSet_univ⟩
    (fun _ _ hX hY => (upperSet_subset_or hX.2 hY.2).imp_right Or.inl)
    (fun _ => Set.subset_univ _)

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

@[simp] theorem mem_def {X : Set Δ} :
    (finalSegmentSystem Δ).mem X ↔ X.Nonempty ∧ IsUpperSet X := Iff.rfl

@[simp] theorem master_eq : (finalSegmentSystem Δ).master = Set.univ := rfl

/-- Each `Set.Ici a` is a (non-empty, upper) neighbourhood. -/
theorem Ici_mem (a : Δ) : (finalSegmentSystem Δ).mem (Set.Ici a) :=
  ⟨⟨a, le_refl a⟩, isUpperSet_Ici a⟩

/-- The principal finite elements `↑(Ici a)`; the correspondence `a ↦ ↑(Ici a)` is
order-*reversing* (`Ici a ⊆ Ici b ↔ b ≤ a`), one of Scott's "finite elements". -/
theorem principal_Ici_le_iff (a b : Δ) :
    (finalSegmentSystem Δ).principal (Ici_mem a) ≤ (finalSegmentSystem Δ).principal (Ici_mem b)
      ↔ a ≤ b := by
  rw [NeighborhoodSystem.principal_le_iff, Set.Ici_subset_Ici]

/-! ### Well-order: every neighbourhood is `Ici (its minimum)`. -/

variable [WellFoundedLT Δ]

/-- **Well-order key lemma.** In a well-order, every non-empty upper set is
`Set.Ici a`, where `a`
is its least element. -/
theorem exists_Ici_of_mem {X : Set Δ} (hX : (finalSegmentSystem Δ).mem X) :
    ∃ a, X = Set.Ici a := by
  obtain ⟨a, haX, hmin⟩ := (IsWellFounded.wf (r := (· < · : Δ → Δ → Prop))).has_min X hX.1
  refine ⟨a, Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rcases lt_or_ge b a with hlt | hge
    · exact absurd hlt (hmin b hb)
    · exact hge
  · exact hX.2 (Set.mem_Ici.mp hb) haX

/-! ### The classification of `|𝒟|` as the non-empty lower sets (initial
segments). -/

/-- The trace `lowerSetOf x = {a ∣ Ici a ∈ x}` of a filter `x`. -/
def lowerSetOf (x : (finalSegmentSystem Δ).Element) : Set Δ :=
  {a : Δ | x.mem (Set.Ici a)}

theorem lowerSetOf_nonempty (x : (finalSegmentSystem Δ).Element) : (lowerSetOf x).Nonempty := by
  obtain ⟨a, ha⟩ := exists_Ici_of_mem (X := (Set.univ : Set Δ)) ⟨Set.univ_nonempty, isUpperSet_univ⟩
  refine ⟨a, ?_⟩
  have hu : x.mem (Set.univ) := x.master_mem
  rw [ha] at hu
  exact hu

omit [WellFoundedLT Δ] in
theorem lowerSetOf_isLowerSet (x : (finalSegmentSystem Δ).Element) :
    IsLowerSet (lowerSetOf x) := by
  intro a b hba ha
  exact x.up_mem ha (Ici_mem b) (Set.Ici_subset_Ici.mpr hba)

/-- The filter built from a non-empty lower set `S`: the neighbourhoods that
contain some
`Ici a` with `a ∈ S`. -/
def ofLowerSet (S : Set Δ) (hSne : S.Nonempty) :
    (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X ∧ ∃ a ∈ S, Set.Ici a ⊆ X
  sub h := h.1
  master_mem := by
    obtain ⟨a, ha⟩ := hSne
    exact ⟨⟨Set.univ_nonempty, isUpperSet_univ⟩, a, ha, Set.subset_univ _⟩
  inter_mem := by
    rintro X Y ⟨hX, a, haS, haX⟩ ⟨hY, b, hbS, hbY⟩
    have hsub : Set.Ici (max a b) ⊆ X ∩ Y :=
      Set.subset_inter
        ((Set.Ici_subset_Ici.mpr (le_max_left a b)).trans haX)
        ((Set.Ici_subset_Ici.mpr (le_max_right a b)).trans hbY)
    refine ⟨(finalSegmentSystem Δ).inter_mem hX hY (Ici_mem (max a b)) hsub, max a b, ?_, hsub⟩
    rcases max_choice a b with h | h
    · rw [h]; exact haS
    · rw [h]; exact hbS
  up_mem := by
    rintro X Y ⟨_, a, haS, haX⟩ hY hXY
    exact ⟨hY, a, haS, haX.trans hXY⟩

omit [WellFoundedLT Δ] in
theorem lowerSetOf_ofLowerSet (S : Set Δ) (hSne : S.Nonempty) (hS : IsLowerSet S) :
    lowerSetOf (ofLowerSet S hSne) = S := by
  ext a
  constructor
  · rintro ⟨_, b, hbS, hba⟩
    exact hS (Set.Ici_subset_Ici.mp hba) hbS
  · intro ha
    exact ⟨Ici_mem a, a, ha, subset_rfl⟩

theorem ofLowerSet_lowerSetOf (x : (finalSegmentSystem Δ).Element) :
    ofLowerSet (lowerSetOf x) (lowerSetOf_nonempty x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, a, haS, haX⟩
    exact x.up_mem haS hX haX
  · intro hX
    obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
    exact ⟨x.sub hX, a, hX, subset_rfl⟩

/-- **Exercise 1.25 — classification of `|𝒟|`.** For a well-order `Δ`, the domain
of non-empty
final segments is order-isomorphic to the poset of **non-empty initial segments**
(lower sets) of
`Δ` under inclusion: `x ↦ {a ∣ Ici a ∈ x}`. (So `|𝒟|` is the lattice of cuts of
`Δ`.) -/
def finalSegmentClassify :
    (finalSegmentSystem Δ).Element ≃o {S : Set Δ // S.Nonempty ∧ IsLowerSet S} where
  toFun x := ⟨lowerSetOf x, lowerSetOf_nonempty x, lowerSetOf_isLowerSet x⟩
  invFun S := ofLowerSet S.1 S.2.1
  left_inv x := ofLowerSet_lowerSetOf x
  right_inv S := Subtype.ext (lowerSetOf_ofLowerSet S.1 S.2.1 S.2.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
      exact h hX
    · intro h a ha
      exact h _ ha

/-! ### Total elements and finiteness (Scott's prose questions). -/

omit [WellFoundedLT Δ]

/-- The greatest element: the filter of **all** neighbourhoods. -/
def topElement : (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X
  sub h := h
  master_mem := ⟨Set.univ_nonempty, isUpperSet_univ⟩
  inter_mem := by
    rintro X Y hX hY
    rcases upperSet_subset_or hX.2 hY.2 with h | h
    · rw [Set.inter_eq_left.mpr h]; exact hX
    · rw [Set.inter_eq_right.mpr h]; exact hY
  up_mem := fun _ hY _ => hY

theorem le_topElement (x : (finalSegmentSystem Δ).Element) : x ≤ topElement :=
  fun _ hX => x.sub hX

/-- **Exercise 1.25 — the unique total element.** The filter of all neighbourhoods
is total
(`⊑`-maximal). -/
theorem topElement_isTotal : (finalSegmentSystem Δ).IsTotal (topElement (Δ := Δ)) :=
  fun y _ => le_topElement y

/-- It is the *unique* total element: any total `x` equals `topElement`. -/
theorem eq_topElement_of_isTotal {x : (finalSegmentSystem Δ).Element}
    (hx : (finalSegmentSystem Δ).IsTotal x) : x = topElement :=
  le_antisymm (le_topElement x) (hx topElement (le_topElement x))

/-- **Exercise 1.25 — not all elements are finite.** If `Δ` has *no greatest
element* (e.g.
`Δ = ℕ = ω`), the total element `topElement` is not a principal filter `↑(Ici a)`:
pick `b > a`,
then `Ici b ∈ topElement` but `Ici a ⊄ Ici b`. So `|𝒟|` has a non-finite (limit)
element. -/
theorem topElement_not_principal_of_noMax (hnomax : ∀ a : Δ, ∃ b, a < b) (a : Δ) :
    topElement ≠ (finalSegmentSystem Δ).principal (Ici_mem a) := by
  intro h
  obtain ⟨b, hab⟩ := hnomax a
  have hmem : ((finalSegmentSystem Δ).principal (Ici_mem a)).mem (Set.Ici b) := by
    rw [← h]; exact Ici_mem b
  have hsub : Set.Ici a ⊆ Set.Ici b := hmem.2
  exact absurd (Set.Ici_subset_Ici.mp hsub) (not_le.mpr hab)

end FinalSegment

end Domain.Neighborhood
