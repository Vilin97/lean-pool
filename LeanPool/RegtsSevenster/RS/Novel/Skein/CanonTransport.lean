/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionProduct

/-!
# Canonical data across a relabel and a glue

Canonical data — a transition system with a path-canonical
orientation — transport along a relabel, down across either branch
of a single-pair glue, and back up from a closed lift.
-/

@[expose] public section

namespace RS



/-! ## Transport along a relabel -/

/-- Canonical-data existence transports along a relabel. -/
theorem EdgeSubset.nonempty_canonData_relabelUp {α β : Type}
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) :
    Nonempty (F.relabelUp e.toEquiv).CanonData ↔
      Nonempty F.CanonData := by
  constructor
  · rintro ⟨⟨κ, o, -⟩⟩
    obtain ⟨o', hc'⟩ := EdgeSubset.exists_pathCanonical
      (relabelTransDown e.toEquiv F κ)
      (relabelOrientDown e.toEquiv F o)
    exact ⟨⟨_, o', hc'⟩⟩
  · rintro ⟨⟨κ, o, hc⟩⟩
    exact ⟨⟨relabelTransUp e.toEquiv F κ,
      relabelOrientUp e.toEquiv F o,
      pathCanonical_relabelUp e F hc⟩⟩

/-! ## Descent and the glued tower family (open cut)

The support data transfer across the open glue: Eulerian-ness on
the nose, canonical data downward by unglue-and-repair, and the
glued pinned family built bottom-up from a lifted family. -/

section TowerFamilyOpen

open EdgeSubset Fragment

variable {α : Type}

/-- Canonical data descend across the open unglue. -/
theorem nonempty_canonData_unglueOpen
    [LinearOrder α] {W : Fragment α} {i : α} {j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetOpen hopen s', W.pairing f ∈ liftSubsetOpen hopen
      s')
    (hne : Nonempty (EdgeSubset.mk s' hc' :
      EdgeSubset (W.gluePairOpen i j hij hopen)).CanonData) :
    Nonempty (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
      EdgeSubset W).CanonData := by
  obtain ⟨⟨κ'', o'', -⟩⟩ := hne
  obtain ⟨o₂, hc₂⟩ := EdgeSubset.exists_pathCanonical
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ'')
    (unglueOrientationOpen hij hopen s' hc' hc κ'' o'')
  exact ⟨⟨_, o₂, hc₂⟩⟩

end TowerFamilyOpen

/-! ## The closed-cut step at the pinned sum

The mechanical mirror of for the circle-closing cut: support
transfer across either lift, the true-lift tower family, and the
`(k − 2ℓ)`-weighted per-subset split — the extra factor is the
glued fragment's extra circle, absorbed against the prefactor in
the tower. -/

section ClosedStep

open EdgeSubset Fragment

variable {α : Type}

/-- Canonical data descend across either closed unglue. -/
theorem nonempty_canonData_unglueClosed
    [LinearOrder α] {W : Fragment α} {i : α} {j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
    (b : Bool)
    (hc : ∀ f ∈ liftSubsetClosed s' b,
      W.pairing f ∈ liftSubsetClosed s' b)
    (hne : Nonempty (EdgeSubset.mk s' hc' :
      EdgeSubset (W.gluePairClosed i j hclosed)).CanonData) :
    Nonempty (EdgeSubset.mk (liftSubsetClosed s' b) hc :
      EdgeSubset W).CanonData := by
  obtain ⟨⟨κ'', o'', -⟩⟩ := hne
  obtain ⟨o₂, hc₂⟩ := EdgeSubset.exists_pathCanonical
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ'')
    (unglueOrientationClosed hclosed b s' hc' hc κ'' o'')
  exact ⟨⟨_, o₂, hc₂⟩⟩

end ClosedStep

/-! ## Fibrewise absorption and the per-term relabel

The generic state-fibre regrouping (the `𝒲`-form absorber), and
the relabel transport at the level of a single pinned term. -/

section ClosedConverse

open EdgeSubset Fragment

variable {α : Type}

/-- Canonical data ascend from either closed lift to the glued
subset. -/
theorem nonempty_canonData_glueClosed
    [LinearOrder α] {W : Fragment α} {i : α} {j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
    (b : Bool)
    (hc : ∀ f ∈ liftSubsetClosed s' b,
      W.pairing f ∈ liftSubsetClosed s' b)
    (hne : Nonempty (EdgeSubset.mk (liftSubsetClosed s' b) hc :
      EdgeSubset W).CanonData) :
    Nonempty (EdgeSubset.mk s' hc' :
      EdgeSubset (W.gluePairClosed i j hclosed)).CanonData := by
  obtain ⟨⟨κ, o, -⟩⟩ := hne
  obtain ⟨o₂, hc₂⟩ := EdgeSubset.exists_pathCanonical
    (RelTransitionSystem.glueClosed hclosed b s' hc' hc κ)
    (glueOrientationClosed hclosed b s' hc' hc κ o)
  exact ⟨⟨_, o₂, hc₂⟩⟩

end ClosedConverse

end RS
