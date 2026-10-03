/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Equitable

/-!
# Equitable Vizing colourings on a prescribed palette

A finite simple graph has an equitable proper edge colouring on any palette
of at least `maxDegree + 1` colours. Unused colours are included in the
balancing, and every class has at most the ceiling of the average size.
-/

public section

namespace LeanPool.Vizing

open ColourClasses EquitableDefinitions

/-- Every palette of at least `maxDegree + 1` colours admits an equitable
proper edge colouring, with each class bounded by the ceiling average. -/
theorem exists_equitable_edge_colouring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (hc : G.maxDegree + 1 ≤ c) :
    ∃ colour : Sym2 V → Fin c,
      ProperOn G.edgeFinset colour ∧ IsEquitable G.edgeFinset colour ∧
      ∀ a, (colourClass G.edgeFinset colour a).card ≤
        classCeiling G.edgeFinset.card c := by
  classical
  let initial : Sym2 V → Fin c := fun e =>
    Fin.castLE hc (LineGraphColouring.vizingEdgeColour G e)
  have hproper : ProperOn G.edgeFinset initial := by
    intro e he f hf hef hsame
    apply LineGraphColouring.properOn_vizingEdgeColour G e he f hf hef
    exact Fin.castLE_injective hc hsame
  have hcpos : 0 < c := lt_of_lt_of_le (Nat.zero_lt_succ G.maxDegree) hc
  let : Nonempty (Fin c) := Fin.pos_iff_nonempty.mp hcpos
  obtain ⟨colour, hp, heq⟩ := Equitable.exists_equitable_colouring initial hproper
  refine ⟨colour, hp, heq, ?_⟩
  intro a
  simpa using class_card_le_ceiling_of_equitable G.edgeFinset colour heq a

end LeanPool.Vizing
