/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij

/-!
# Representative flags

Each edge's representative flag is the one enumerated on the low
slot half.  The set of participating flags whose edge
representative is outgoing (under an orientation) is closed under
the pairing — it is the flip set aligning the data colouring with
the Definition 5 odd lists.
-/

@[expose] public section

namespace RS

open Finset

/-- The representative flag of a flag's edge: the one on the low
slot half. -/
noncomputable def repFlag (W : ClosedFragment) (g : W.Flag) :
    W.Flag :=
  if (starFlagEnum W g).val < edgeCount W then g
  else W.pairing g

/-- A flag on the low half represents its own edge. -/
theorem repFlag_low (W : ClosedFragment) (g : W.Flag)
    (h : (starFlagEnum W g).val < edgeCount W) :
    repFlag W g = g := ite_eq_left h

/-- A flag on the high half is represented by its partner. -/
theorem repFlag_high (W : ClosedFragment) (g : W.Flag)
    (h : ¬ (starFlagEnum W g).val < edgeCount W) :
    repFlag W g = W.pairing g := ite_eq_right h

/-- The representative flag is pairing-invariant. -/
theorem repFlag_pairing (W : ClosedFragment) (g : W.Flag) :
    repFlag W (W.pairing g) = repFlag W g := by
  by_cases h : (starFlagEnum W g).val < edgeCount W
  · have hp := starFlagEnum_pairing_low W g h
    have hhigh : ¬ (starFlagEnum W (W.pairing g)).val <
        edgeCount W := by
      rw [hp]
      change ¬ edgeCount W + _ < edgeCount W
      omega
    rw [repFlag, ite_eq_right hhigh, W.pairing_invol,
      repFlag_low W g h]
  · have hp := starFlagEnum_pairing_high W g h
    have hisLt := (starFlagEnum W g).isLt
    have hlow : (starFlagEnum W (W.pairing g)).val <
        edgeCount W := by
      rw [hp]
      change (starFlagEnum W g).val - edgeCount W < edgeCount W
      omega
    rw [repFlag, ite_eq_left hlow, repFlag_high W g h]

open Classical in
/-- The flip set of an orientation: participating flags whose
edge representative is outgoing. -/
noncomputable def outRepSet (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) : Finset W.Flag :=
  F.flags.filter (fun g => o.isOut (repFlag W g) = true)

/-- The flip set is closed under the pairing. -/
theorem outRepSet_pairing_mem (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    ∀ g ∈ outRepSet W F o, W.pairing g ∈ outRepSet W F o := by
  intro g hg
  rw [outRepSet, Finset.mem_filter] at hg ⊢
  refine ⟨F.pairing_mem _ hg.1, ?_⟩
  rw [repFlag_pairing]
  exact hg.2

/-- Membership in the flip set depends only on the edge. -/
theorem mem_outRepSet_iff (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (g : W.Flag) (hg : g ∈ F.flags) :
    g ∈ outRepSet W F o ↔ o.isOut (repFlag W g) = true := by
  rw [outRepSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

end RS
