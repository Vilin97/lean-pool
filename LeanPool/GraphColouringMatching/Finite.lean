/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.GraphColouringMatching.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Exact edge accounting for finite matching decompositions

The equivalence on individual edges yields an exact count, including palettes
with unused colours. Only the edge set must be finite: infinitely many isolated
vertices are allowed. Empty matching classes contribute zero.
-/

public section

namespace SimpleGraph.MatchingDecomposition

variable {V C : Type*} {G : SimpleGraph V}

/-- The total number of edges is the sum of the matching-class sizes. -/
theorem card_edges_eq_sum [Finite G.edgeSet] [Fintype C] (D : MatchingDecomposition G C) :
    Nat.card G.edgeSet = ∑ c, Nat.card (D.matching c).edgeSet := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : ∀ c, Finite (D.matching c).edgeSet := fun c =>
    Finite.of_injective (fun e => (⟨e.1, (D.matching c).edgeSet_subset e.2⟩ : G.edgeSet))
      (fun x y h => Subtype.ext (congrArg (fun e : G.edgeSet => e.1) h))
  let : ∀ c, Fintype (D.matching c).edgeSet := fun c => Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using
    Fintype.card_congr D.edgeEquivSigma

end SimpleGraph.MatchingDecomposition
