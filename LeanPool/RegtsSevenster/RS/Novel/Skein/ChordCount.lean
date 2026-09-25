/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCrossDelta

/-!
# The chord diagram has half as many chords as the subset has boundary flags

Each chord is the sorted pair of a boundary flag's label and its chain
partner's, so the two ends of a chord give the same chord and nothing
else does.  The map from boundary flags to chords is therefore two to
one, and the diagram's cardinality is half the boundary's.

This is what makes "the number of chords" a single notion: it is
`oddLabelCount / 2` read off the state, and `labelChords.card` read off
the diagram, and they agree.
-/

@[expose] public section

namespace RS



namespace EdgeSubset

variable {α : Type}

end EdgeSubset

/-! ### Degenerate chords never cross

A label outside the subset contributes a chord with both ends at
itself.  Crossing asks for a strict interleaving, so such a chord
crosses nothing and counts for nothing — which is why an involution
extended by the identity off a subset has the crossing count of its
genuine chords alone.
-/

namespace EdgeSubset

variable {α : Type}

/-! ### The involution a subset induces on the interface labels

Chords pair up the labels a subset uses.  Extending by the identity off
those labels gives an involution of the whole interface, whose genuine
chords are the subset's and whose fixed points are the unused labels.
This is the object the restriction transports are applied to.
-/

/-- A boundary flag's label is its own index. -/
theorem boundaryLabel_boundaryFlag {W : Fragment α}
    (F : EdgeSubset W) {i : α}
    (h : W.boundaryFlag i ∈ F.boundaryFlags) : F.boundaryLabel h = i :=
  boundaryLabel_eq_of_attach h (W.attach_boundaryFlag i)

/-- The label a subset's chain carries a used label to; the identity on
unused ones. -/
noncomputable def chordInv {W : Fragment α}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (i : α) : α :=
  if h : W.boundaryFlag i ∈ F.boundaryFlags then
    F.boundaryLabel (κ.pathMatch_mem h) else i

/-- A used label's image is used. -/
theorem boundaryFlag_chordInv {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) {i : α}
    (h : W.boundaryFlag i ∈ F.boundaryFlags) :
    W.boundaryFlag (chordInv F κ i) = κ.pathMatch (W.boundaryFlag i) h := by
  unfold chordInv
  rw [dite_eq_left h]
  exact (W.eq_boundaryFlag _ _ (attach_boundaryLabel (κ.pathMatch_mem h))).symm

/-- The chord partner of a participating boundary label is itself
participating. -/
theorem chordInv_mem {W : Fragment α}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    {i : α} (h : W.boundaryFlag i ∈ F.boundaryFlags) :
    W.boundaryFlag (chordInv F κ i) ∈ F.boundaryFlags := by
  rw [boundaryFlag_chordInv F κ h]
  exact κ.pathMatch_mem h

/-- **The induced map is an involution.** -/
theorem chordInv_invol {W : Fragment α}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (i : α) : chordInv F κ (chordInv F κ i) = i := by
  by_cases h : W.boundaryFlag i ∈ F.boundaryFlags
  · have h2 := chordInv_mem F κ h
    refine W.boundaryFlag_injective ?_
    rw [boundaryFlag_chordInv F κ h2,
      κ.pathMatch_congr (boundaryFlag_chordInv F κ h) h2
        (κ.pathMatch_mem h)]
    exact κ.pathMatch_invol h
  · unfold chordInv
    rw [dite_eq_right h, dite_eq_right h]

/-- **The induced map is fixed-point-free on the used labels.** -/
theorem chordInv_ne {W : Fragment α}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    {i : α} (h : W.boundaryFlag i ∈ F.boundaryFlags) :
    chordInv F κ i ≠ i := by
  intro hx
  refine κ.pathMatch_ne_self h ?_
  rw [← boundaryFlag_chordInv F κ h, hx]

end EdgeSubset

end RS
