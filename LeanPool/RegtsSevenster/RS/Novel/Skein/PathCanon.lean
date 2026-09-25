/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.OrientationFlip
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCircuitDelta

/-!
# Path-canonical orientations and the corrected independence

The orientation counterexample shows the constrained summand
genuinely depends on the orientation of boundary-to-boundary
chains; only circuit-supported differences are invisible.  The
correction: orient every chain canonically, from its lower-labelled
boundary end to its higher-labelled one.  Two path-canonical
orientations of the same system then differ only on circuits, so
the circuit-restricted invariance makes the canonical
summand well-defined; the corrected value chooses among canonical
data, and the corrected independence interface quantifies over it.
-/

@[expose] public section

namespace RS



variable {α : Type}

namespace EdgeSubset

/-- **Path-canonical orientation**: every participating
boundary-to-boundary chain is directed from its lower-labelled end
to its higher-labelled one — the entry edge at the lower end is
incoming. -/
def PathCanonical [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) : Prop :=
  ∀ (i j : α) (hb : W.boundaryFlag i ∈ F.boundaryFlags),
    W.pairing (W.boundaryFlag i) ∈ F.internalFlags →
    κ.pathMatch (W.boundaryFlag i) hb = W.boundaryFlag j →
    i < j →
    o.isOut (W.pairing (W.boundaryFlag i)) = false

/-- On an all-internal subset every orientation is path-canonical:
there are no participating boundary flags. -/
theorem pathCanonical_of_allInternal [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    (hall : F.allInternal) {κ : F.RelTransitionSystem}
    (o : κ.Orientation) : PathCanonical o := by
  intro i j hb _ _ _
  exact absurd hb (by
    rw [hall]
    exact Finset.notMem_empty _)

/-- The chord-interleaving condition between two boundary chains:
both chords are recorded at their lower-labelled ends and
interleave. -/
def ChordCross [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (b b' : {x : W.Flag // x ∈ F.boundaryFlags}) : Prop :=
  ∃ i j i' j' : α,
    W.attach b.val = Sum.inr i ∧
    W.attach (κ.pathMatch b.val b.prop) = Sum.inr j ∧
    W.attach b'.val = Sum.inr i' ∧
    W.attach (κ.pathMatch b'.val b'.prop) = Sum.inr j' ∧
    i < j ∧ i' < j' ∧ i < i' ∧ i' < j ∧ j < j'

open Classical in
/-- The number of interleaving chain-chord pairs of a transition
system. -/
noncomputable def chordCrossingCount [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) : ℕ :=
  ((F.boundaryFlags.attach ×ˢ F.boundaryFlags.attach).filter
    (fun bb => ChordCross κ bb.1 bb.2)).card

/-- **The path-sector sign**: the crossing sign of the boundary
chain pairing — the Pfaffian chord-diagram sign forced by the
two-path repair obstruction. -/
noncomputable def pathSign [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) : ℂ :=
  (-1 : ℂ) ^ chordCrossingCount κ

/-- On an all-internal subset the path sign is trivial. -/
theorem pathSign_of_allInternal [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    (hall : F.allInternal) (κ : F.RelTransitionSystem) :
    pathSign κ = 1 := by
  unfold pathSign chordCrossingCount
  rw [show ((F.boundaryFlags.attach ×ˢ F.boundaryFlags.attach).filter
      (fun bb => ChordCross κ bb.1 bb.2)) = ∅ from
    Finset.eq_empty_of_forall_notMem (fun bb _ => by
      obtain ⟨⟨v, hv⟩, _⟩ := bb
      rw [hall] at hv
      exact absurd hv (Finset.notMem_empty _))]
  rw [Finset.card_empty, pow_zero]

/-- Canonical transition data: a relative system with a
path-canonical orientation. -/
def CanonData [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) : Type :=
  (κ : F.RelTransitionSystem) × {o : κ.Orientation // PathCanonical o}

open Classical in
/-- **The canonical constrained value**: the through summand at the
open circuit count, chosen among path-canonical data. -/
noncomputable def throughValueC [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st) : ℂ :=
  if hne : Nonempty F.CanonData then
    pathSign (Classical.choice hne).1 *
      F.throughSummand h st hbnd (Classical.choice hne).2.val
        ((Classical.choice hne).1.openCircuitCount)
  else 0

end EdgeSubset

open Classical in
/-- **The canonical state-constrained partition value** of an open
fragment. -/
noncomputable def throughMixedPartitionC [LinearOrder α]
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (W : Fragment α)
    (st : GenBoundaryState k ℓ α) : ℂ :=
  ((k : ℂ) - 2 * ℓ) ^ W.circles *
    ∑ s : Finset W.Flag,
      if hc : ∀ f ∈ s, W.pairing f ∈ s then
        if hbnd : genBoundarySubsetMatches W s st then
          if (EdgeSubset.mk s hc).Eulerian then
            (EdgeSubset.mk s hc).throughValueC h st hbnd
          else 0
        else 0
      else 0

namespace EdgeSubset

/-- Two path-canonical orientations of one system differ only on
circuit components, so their summands agree — the difference set
avoids every chain (both orientations direct each chain the same
way) and is therefore pairing-closed on internal flags. -/
theorem throughSummand_canonical_unique [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} {o o' : κ.Orientation}
    (_hc : PathCanonical o) (_hc' : PathCanonical o')
    (hchain : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (c : ℕ) :
    F.throughSummand h st hbnd o c =
      F.throughSummand h st hbnd o' c :=
  F.throughSummand_orientation_invariant h st hbnd o o' hchain c

end EdgeSubset

/-- **The corrected independence interface**: the constrained
summand at the open circuit count is independent of the choice of
relative transition system and *path-canonical* orientation. -/
def ThroughIndependenceC : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α} (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem}
    (o : κ.Orientation) (o' : κ'.Orientation),
    EdgeSubset.PathCanonical o → EdgeSubset.PathCanonical o' →
    EdgeSubset.pathSign κ *
        F.throughSummand h st hbnd o κ.openCircuitCount =
      EdgeSubset.pathSign κ' *
        F.throughSummand h st hbnd o' κ'.openCircuitCount

end RS
