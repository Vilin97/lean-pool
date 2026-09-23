/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransferTarget
public import LeanPool.Schoenflies.InitialPairFixed

/-!
# The initial distinguished outer graph is a simple cycle

Reverse finite transfer ultimately needs only the local fact that at most two distinguished
outer edges meet at a vertex. `Schoenflies.GeneratedStructure.outerEdgesFormCycle` propagates
the stronger and more natural invariant that the complete outer edge set is one simple cycle.
This module supplies its base case for the concrete initial hexagon.

## Blueprint

* `Schoenflies.outerEdgesFormCycle_initialStructure` — the distinguished outer graph of the
  initial matched cellulation is its six-edge simple cycle.
-/

@[expose] public section

open Set
open scoped Graph

namespace Schoenflies

open Graph

/-- One oriented side of the initial hexagonal outer graph. -/
theorem initOuter_isLink_edge (i : Fin 6) :
    initOuter.IsLink (.edge i) (.vert i) (.vert (i + 1)) :=
  ⟨⟨i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Incidence in the initial outer graph is membership among an outer edge's two ends. -/
theorem initOuter_inc_iff {e x : InitialCell} :
    initOuter.Inc e x ↔
      e ∈ InitialCell.outerEdges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, he, hxy⟩
    rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨he, Or.inr rfl⟩
  · rintro ⟨⟨i, rfl⟩, rfl | rfl⟩
    · exact (initOuter_isLink_edge i).inc_left
    · exact (initOuter_isLink_edge i).inc_right

/-- The five-edge complementary path to outer edge zero. -/
theorem isPath_initOuter_complement :
    initOuter.IsPath (.vert 0)
      [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1] (.vert 1) := by
  refine .cons (initOuter_isLink_edge 5).symm
    (.cons (initOuter_isLink_edge 4).symm
      (.cons (initOuter_isLink_edge 3).symm
        (.cons (initOuter_isLink_edge 2).symm
          (Graph.IsPath.single (initOuter_isLink_edge 1).symm (by simp)) ?_) ?_) ?_) ?_
  all_goals
    simp [Graph.walkVertices, Graph.coveredVertices,
      initOuter_inc_iff, InitialCell.outerEdges, InitialCell.ends]

/-- The initial distinguished outer edge set is exactly the six-edge hexagonal cycle. -/
theorem outerEdgesFormCycle_initialStructure : initialStructure.OuterEdgesFormCycle := by
  refine ⟨.edge 0, .vert 0, .vert 1,
    [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1], ?_, ?_⟩
  · exact ⟨initOuter_isLink_edge 0, isPath_initOuter_complement, by simp⟩
  · ext c
    change c ∈ InitialCell.outerEdges ↔
      c ∈ [InitialCell.edge 0, .edge 5, .edge 4, .edge 3, .edge 2, .edge 1]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, rfl⟩

end Schoenflies
