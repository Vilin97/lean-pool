/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
Misere combinatorial games.
-/

namespace MisereGames

-- TODO: Upstream to mathlib

public section

variable {V : Type}

namespace SimpleGraph

/--
If the support of a simple graph is finite, then so is its edge set.
-/
theorem edgeSet_finite_of_support_finite {graph : SimpleGraph V}
    (hfin : graph.support.Finite) : graph.edgeSet.Finite := by
  apply Set.Finite.subset (Set.Finite.image2 (fun a b => s(a, b)) hfin hfin)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u w =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact Set.mem_image2_of_mem
      (graph.mem_support.mpr ⟨w, he⟩)
      (graph.mem_support.mpr ⟨u, he.symm⟩)

/--
If a non-empty walk ends with a vertex `u`, then there exists some edge
incident to `u`.
-/
theorem exist_edge_end_walk {graph : SimpleGraph V} {v u : V} (h1 : v ≠ u)
    (walk : graph.Walk v u) : ∃ e ∈ graph.edgeSet, u ∈ e := by
  induction walk with
  | nil => absurd h1; rfl
  | @cons v w u h rest ih =>
    by_cases h2 : w = u
    · subst h2
      use Sym2.mk v w
      constructor
      · exact (SimpleGraph.mem_edgeSet graph).mpr h
      · simp only [Sym2.mem_iff, or_true]
    · exact ih h2

end SimpleGraph

end

end MisereGames
