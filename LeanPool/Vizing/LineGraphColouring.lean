/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.ColourClasses
public import LeanPool.Vizing.Main

/-!
# Line-graph colourings as literal proper edge colourings

Any colouring of the line graph induces a proper colour assignment on
`G.edgeFinset`. This connects the fan proof of Vizing's theorem to
equitable recolouring on a fixed finite palette.
-/

public section

namespace LeanPool.Vizing.LineGraphColouring

open LeanPool.Vizing.ColourClasses

variable {V Color : Type*} [Fintype V] [DecidableEq V] [Inhabited Color]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extend a line-graph colouring to all unordered pairs; values off the
literal edge finset are irrelevant to `ProperOn`. -/
noncomputable def edgeColourOfLineGraph
    (C : (G.lineGraph).Coloring Color) : Sym2 V → Color := fun e =>
  if he : e ∈ SimpleGraph.edgeFinset G then C ⟨e, (SimpleGraph.mem_edgeFinset).mp he⟩ else default

/-- A line-graph colouring is a proper colour assignment on literal graph
edges in the exact `ColourClasses.ProperOn` sense. -/
theorem properOn_of_lineGraph_colouring
    (C : (G.lineGraph).Coloring Color) :
    ProperOn (SimpleGraph.edgeFinset G) (edgeColourOfLineGraph C) := by
  intro e he f hf hne hsame
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hsame' : C ⟨e, (SimpleGraph.mem_edgeFinset).mp he⟩ =
      C ⟨f, (SimpleGraph.mem_edgeFinset).mp hf⟩ := by
    simpa [edgeColourOfLineGraph, he, hf] using hsame
  have hadj : (G.lineGraph).Adj ⟨e, (SimpleGraph.mem_edgeFinset).mp he⟩
      ⟨f, (SimpleGraph.mem_edgeFinset).mp hf⟩ := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hne (congrArg Subtype.val h), v, ?_, ?_⟩
    · exact Sym2.mem_toFinset.mp hve
    · exact Sym2.mem_toFinset.mp hvf
  exact (C.valid hadj) hsame'

/-- The colour assignment supplied by Vizing's theorem, extended to unordered pairs. -/
noncomputable def vizingEdgeColour (G : SimpleGraph V) [DecidableRel G.Adj] :
    Sym2 V → Fin (G.maxDegree + 1) :=
  edgeColourOfLineGraph (Classical.choice (LeanPool.Vizing.lineGraph_colorable G))

theorem properOn_vizingEdgeColour (G : SimpleGraph V) [DecidableRel G.Adj] :
    ProperOn (SimpleGraph.edgeFinset G) (vizingEdgeColour G) :=
  properOn_of_lineGraph_colouring (Classical.choice (LeanPool.Vizing.lineGraph_colorable G))

end LeanPool.Vizing.LineGraphColouring
