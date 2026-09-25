/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelTransition
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GenBoundaryStates

/-!
# The boundary-relative constrained summand

The Definition 5 summand re-founded on boundary-relative
transition systems: vertex-local odd lists and signs over a
relative orientation (in-flags at a vertex are automatically
internal), and the state-constrained summand with an abstract
circuit exponent — specialized to the open circuit count when
that lands.  For subsets arising from a standard transition
system, the relative data agrees with the original.
-/

@[expose] public section

namespace RS

variable {α : Type} {W : Fragment α}

/-! ## Vertex-local data over a relative orientation -/

/-- In-flags at a vertex for a boundary-relative orientation: the
participating flags attached to the vertex and marked incoming, in
the fixed enumeration order. -/
noncomputable def EdgeSubset.relInFlagsAt (F : EdgeSubset W)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (v : W.Vertex) : List W.Flag :=
  letI := W.flagOrder
  letI := Classical.dec
  (F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).sort
    (· ≤ ·)

/-- An in-flag at a vertex is an internal flag. -/
theorem EdgeSubset.mem_internal_of_mem_relInFlagsAt
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {v : W.Vertex} {f : W.Flag}
    (hf : f ∈ F.relInFlagsAt o v) : f ∈ F.internalFlags := by
  let := W.flagOrder
  let := Classical.dec
  unfold EdgeSubset.relInFlagsAt at hf
  have hmem := (Finset.mem_sort (α := W.Flag) (· ≤ ·)).mp hf
  have h := Finset.mem_filter.mp hmem
  exact mem_internalFlags_of h.1 ⟨v, h.2.1⟩

/-! ## Agreement with the standard data -/

/-- Transport of an orientation to the relative system. -/
def EdgeSubset.TransitionSystem.Orientation.toRel
    {F : EdgeSubset W} {κ : F.TransitionSystem}
    (o : κ.Orientation) : κ.toRelTransitionSystem.Orientation where
  isOut := o.isOut
  match_flip := fun f hf =>
    o.match_flip f (mem_flags_of_internalFlags F hf)
  pairing_flip := fun f hf _ =>
    o.pairing_flip f (mem_flags_of_internalFlags F hf)

/-- Membership in the in-flag list, unfolded. -/
theorem mem_relInFlagsAt_iff {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {vv : W.Vertex} {f : W.Flag} :
    f ∈ F.relInFlagsAt o vv ↔
      f ∈ F.flags ∧ W.attach f = Sum.inl vv ∧
        o.isOut f = false := by
  let := W.flagOrder
  let := Classical.dec
  unfold EdgeSubset.relInFlagsAt
  rw [Finset.mem_sort, Finset.mem_filter]

/-- The in-flag list is `Nodup`. -/
theorem relInFlagsAt_nodup {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (vv : W.Vertex) :
    (F.relInFlagsAt o vv).Nodup := by
  let := W.flagOrder
  let := Classical.dec
  unfold EdgeSubset.relInFlagsAt
  exact Finset.sort_nodup _ _

end RS
