/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.PairDisjoint
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels

/-!
# The label chord diagram of a transition system

The boundary pairing of a relative transition system, recorded as
a finite set of label chords (each low-to-high): the combinatorial
index over which the pairing-resolved open-sector values live.
`SamePairing` is exactly equality of chord diagrams.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

open Classical in
/-- The chord diagram of a system: for each participating boundary
flag, the sorted pair of its label and its path match's label. -/
noncomputable def labelChords
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) : Finset (α × α) :=
  F.boundaryFlags.attach.image (fun b =>
    (min (F.boundaryLabel b.prop)
        (F.boundaryLabel (κ.pathMatch_mem b.prop)),
      max (F.boundaryLabel b.prop)
        (F.boundaryLabel (κ.pathMatch_mem b.prop))))

/-- Membership: a pair is a chord exactly when it is the sorted
label pair of some participating boundary flag. -/
theorem mem_labelChords [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {p : α × α} :
    p ∈ labelChords κ ↔
      ∃ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        p = (min (F.boundaryLabel hδ)
              (F.boundaryLabel (κ.pathMatch_mem hδ)),
            max (F.boundaryLabel hδ)
              (F.boundaryLabel (κ.pathMatch_mem hδ))) := by
  unfold labelChords
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨δ, hδ⟩, -, h⟩
    exact ⟨δ, hδ, h.symm⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨⟨δ, hδ⟩, Finset.mem_attach _ _, h.symm⟩

/-- The converse: equal chord diagrams force the same pairing.  The
chord of `δ` in `κ'` is the chord of `δ` in `κ` (the only `κ'`
chord containing `δ`'s label, by label injectivity), and the
partner's label determines the partner. -/
theorem samePairing_of_labelChords
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (h : labelChords κ = labelChords κ') : SamePairing κ κ' := by
  intro δ hδ
  -- the κ'-chord of δ appears in the κ-diagram
  have hmem : (min (F.boundaryLabel hδ)
        (F.boundaryLabel (κ'.pathMatch_mem hδ)),
      max (F.boundaryLabel hδ)
        (F.boundaryLabel (κ'.pathMatch_mem hδ))) ∈
      labelChords κ := by
    rw [h]
    exact mem_labelChords.mpr ⟨δ, hδ, rfl⟩
  obtain ⟨γ, hγ, hp⟩ := mem_labelChords.mp hmem
  -- the two sorted pairs share the label of δ, so δ ∈ {γ, π γ};
  -- in either case the partners' labels agree
  have hpair := Prod.ext_iff.mp hp
  rcases le_total (F.boundaryLabel hδ)
      (F.boundaryLabel (κ'.pathMatch_mem hδ)) with hle | hle <;>
    rcases le_total (F.boundaryLabel hγ)
        (F.boundaryLabel (κ.pathMatch_mem hγ)) with hle' | hle'
  · -- δ low in κ', γ low in κ: labels of δ, γ agree ⟹ δ = γ
    rw [min_eq_left hle, max_eq_right hle,
      min_eq_left hle', max_eq_right hle'] at hpair
    have hδγ : δ = γ := boundaryLabel_inj hδ hγ hpair.1
    subst hδγ
    exact (boundaryLabel_inj (κ'.pathMatch_mem hδ)
      (κ.pathMatch_mem hδ) hpair.2).symm
  · -- δ low in κ', γ high in κ: δ = π γ, partner label = label γ
    rw [min_eq_left hle, max_eq_right hle,
      min_eq_right hle', max_eq_left hle'] at hpair
    have hδπγ : δ = κ.pathMatch γ hγ :=
      boundaryLabel_inj hδ (κ.pathMatch_mem hγ) hpair.1
    have h2 : κ.pathMatch δ hδ = γ := by
      have := κ.pathMatch_congr hδπγ hδ (κ.pathMatch_mem hγ)
      exact this.trans (κ.pathMatch_invol hγ)
    have h3 : κ'.pathMatch δ hδ = γ :=
      boundaryLabel_inj (κ'.pathMatch_mem hδ) hγ hpair.2
    exact h2.trans h3.symm
  · -- δ high in κ', γ low in κ: symmetric
    rw [min_eq_right hle, max_eq_left hle,
      min_eq_left hle', max_eq_right hle'] at hpair
    have hπδγ : κ'.pathMatch δ hδ = γ :=
      boundaryLabel_inj (κ'.pathMatch_mem hδ) hγ hpair.1
    have hδπγ : δ = κ.pathMatch γ hγ :=
      boundaryLabel_inj hδ (κ.pathMatch_mem hγ) hpair.2
    have h2 : κ.pathMatch δ hδ = γ := by
      have := κ.pathMatch_congr hδπγ hδ (κ.pathMatch_mem hγ)
      exact this.trans (κ.pathMatch_invol hγ)
    exact h2.trans hπδγ.symm
  · -- both high: δ = π γ in both readings ⟹ partners agree
    rw [min_eq_right hle, max_eq_left hle,
      min_eq_right hle', max_eq_left hle'] at hpair
    have hδγ : δ = γ := boundaryLabel_inj hδ hγ hpair.2
    subst hδγ
    exact (boundaryLabel_inj (κ'.pathMatch_mem hδ)
      (κ.pathMatch_mem hδ) hpair.1).symm

end EdgeSubset

/-- A well-formed chord diagram. -/
structure IsChordDiagram
    [LinearOrder α]
    (P : Finset (α × α)) : Prop where
  /-- Every chord is recorded low end first. -/
  ordered : ∀ p ∈ P, p.1 < p.2
  /-- Distinct chords share no end. -/
  disjoint : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → PairDisjoint p q

namespace EdgeSubset

/-- On an all-internal subset the chord diagram is empty: there are
no participating boundary flags. -/
theorem labelChords_of_allInternal
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (hall : F.allInternal)
    (κ : F.RelTransitionSystem) : labelChords κ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun p hp => by
    obtain ⟨δ, hδ, -⟩ := mem_labelChords.mp hp
    rw [show F.boundaryFlags = ∅ from hall] at hδ
    exact Finset.notMem_empty δ hδ

end EdgeSubset

end RS
