/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockRestrict
import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists

/-!
# Transitions on closed fragments

Closed fragments have no boundary labels, so every flag attaches
internally, and every Eulerian edge subset admits an oriented
transition system: the choice in the Definition 5 value is
always inhabited.
-/

namespace RS

/-- Every flag of a closed fragment attaches to a vertex. -/
theorem ClosedFragment.attach_internal (W : ClosedFragment)
    (f : W.Flag) : ∃ v : W.Vertex, W.attach f = Sum.inl v := by
  rcases h : W.attach f with v | ℓ0
  · exact ⟨v, rfl⟩
  · exact ℓ0.elim0

/-- Eulerian subsets of closed fragments admit oriented
transition systems. -/
theorem ClosedFragment.eulerian_transition_nonempty
    (W : ClosedFragment) (F : EdgeSubset W)
    (hE : F.Eulerian) :
    Nonempty ((κ : F.TransitionSystem) × κ.Orientation) :=
  F.exists_transition_orientation hE
    (fun f _ => W.attach_internal f)

end RS
