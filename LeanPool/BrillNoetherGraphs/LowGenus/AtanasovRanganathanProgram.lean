/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence
import LeanPool.BrillNoetherGraphs.Utilities.Iso.FossilTopology
import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocorePresentation
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoVertexPencilCore

/-!
# A formal interface for the Atanasov--Ranganathan low-genus program

The paper's finite configuration analysis is naturally stated uniformly over
all positive integral subdivisions of a fixed loopless core.  This file gives
that obligation a name and connects it to the public low-genus existence
reduction.

It also closes one infinite genus-five family: a loopless two-vertex core with
six edge slots.  Every such subdivision is a genus-five banana graph, and its
two endpoint chips already have rank one.  Padding that pencil by two effective
chips supplies the critical degree-four divisor.

The remaining work is geometric, not arithmetic: prove the corresponding
`PositiveSubdivisionPencil` assertions for the finitely many loopless cubic
cores, and connect the loop, bridge, and contraction reductions to those core
statements.
-/

namespace AtanasovRanganathan

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.SubdivisionGraph

/-- A fixed ordered loopless core carries a degree-`degree` rank-one pencil on
every assignment of positive integral edge lengths.  This is the exact target
proved by each uniform configuration calculation in the paper. -/
def PositiveSubdivisionPencil {n p : ℕ} (core : Core n p)
    (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (degree : ℤ) : Prop :=
  ∀ (length : Fin p → ℕ) (length_pos : ∀ edge, 0 < length edge),
    BNExists
      (Spec.ofCore core core_nonempty core_loopless length length_pos).graph
      1 degree

/-- The finite geometric genus-five boundary produced by the public
pseudocore normal form.  Each input is a valid loop-aware pseudocore with at
most eight base vertices; the obligation is uniform over every positive
subdivision of its checked loopless split.

This formulation deliberately does not mention the historical numbering of
the sixteen cubic pictures.  A finite catalog theorem may discharge these
quantifiers later, while structural proofs can already handle looped,
separated, and small-core families directly. -/
def GenusFivePseudocorePencils : Prop :=
  ∀ (vertexCount : ℕ)
    (core : Certificate.GenusFourPseudocore.Pseudocore vertexCount)
    (split : core.SplitMetadata),
    vertexCount ≤ 8 →
    core.ValidAt 5 →
    Certificate.PseudocoreSplitGlue.Compatible split →
    ∀ spec : Spec (vertexCount + core.loopCount) core.splitEdgeCount,
      spec.core = split.splitCore → BNExists spec.graph 1 4

/-- The fossil and public pseudocore presentation reduce the whole genus-five
critical-pencil theorem to `GenusFivePseudocorePencils`.

Passing to the fossil contracts every pendant tree and every separating
bridge at once.  Its rank and genus agree with the source, and its two-edge
cut condition supplies the leafless hypothesis needed by the pseudocore
presentation.  This replaces the former recursive, one-leaf-at-a-time
load-bearing reduction. -/
theorem genusFiveRankOneExistence_of_pseudocorePencils
    (pencils : GenusFivePseudocorePencils) :
    GenusFiveRankOneExistence := by
  intro G hConnected hGenus
  let F := fossil G
  have hFConnected : graphConnected F := graph_connected_fossil G hConnected
  have hFGenus : genus F = 5 := (genus_fossil G hConnected).trans hGenus
  have hFLeafless : ∀ vertex : F.V, vertexDegree F vertex ≠ 1 :=
    fossil_vertex_degree_ne_one G hConnected
  obtain ⟨vertexCount, core, split, hSmall, hValid, hCompatible,
      spec, hCore, ⟨equivalence⟩⟩ :=
    Certificate.PseudocorePresentation.pseudocorePresentation_genusFive
      F hFConnected hFGenus hFLeafless
  have hSpec : BNExists spec.graph 1 4 :=
    pencils vertexCount core split hSmall hValid hCompatible spec hCore
  have hFossil : BNExists F 1 4 :=
    (equivalence.bnExists_iff 1 4).mpr hSpec
  exact (BNExists_fossil_iff G hConnected 1 4).mpr hFossil

/-- Exact high-level inputs for the direct proof: the already-isolated
genus-four pencil theorem and the finite genus-five pseudocore family. -/
structure GeometricInputs : Prop where
  genusFour : GenusFourRankOneExistence
  genusFivePseudocores : GenusFivePseudocorePencils

/-- The geometric inputs assemble into the two critical pencils consumed by
the low-genus arithmetic reduction. -/
theorem GeometricInputs.toCriticalPencils
    (inputs : GeometricInputs) : LowGenusCriticalPencils where
  genusFour := inputs.genusFour
  genusFive := genusFiveRankOneExistence_of_pseudocorePencils
    inputs.genusFivePseudocores

/-- Once the two geometric inputs are proved, the full
Atanasov--Ranganathan existence theorem follows with no further mathematics. -/
theorem brillNoetherExistenceThroughFive_of_geometricInputs
    (inputs : GeometricInputs) : BrillNoetherExistenceThroughFive :=
  criticalPencils_imply_brillNoetherExistenceThroughFive
    inputs.toCriticalPencils

/-- The endpoint pencil proves the degree-four subdivision obligation for
every loopless two-vertex core, independently of its number of edge slots. -/
theorem positiveSubdivisionPencil_twoVertex_degreeFour {p : ℕ}
    (core : Core 2 p)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    PositiveSubdivisionPencil core (by norm_num) core_loopless 4 := by
  intro length length_pos
  let spec := Spec.ofCore core (by norm_num) core_loopless length length_pos
  exact spec.bnExists_one_four_of_two_core_vertices

/-- The two-vertex endpoint pencil directly retires every pseudocore whose
loopless split has two vertices.  This is phrased at the exact finite boundary
used by `GenusFivePseudocorePencils`. -/
theorem genusFivePseudocorePencil_of_splitVertexCount_eq_two
    {vertexCount : ℕ}
    {core : Certificate.GenusFourPseudocore.Pseudocore vertexCount}
    {split : core.SplitMetadata}
    (hCount : vertexCount + core.loopCount = 2)
    (spec : Spec (vertexCount + core.loopCount) core.splitEdgeCount)
    (_hCore : spec.core = split.splitCore) :
    BNExists spec.graph 1 4 := by
  apply BNExists_mono_degree (by norm_num : (2 : ℤ) ≤ 4)
  exact spec.bnExists_one_two_of_coreVertexCount_eq_two hCount

/-- A positive subdivision of a two-vertex, six-edge core has genus five. -/
theorem genus_twoVertex_sixEdges
    (spec : Spec 2 6) : genus spec.graph = 5 := by
  rw [spec.genus_graph]
  norm_num

/-- The first completed genus-five structural family in the direct
Atanasov--Ranganathan track. -/
theorem genusFivePencil_twoVertex_sixEdges
    (spec : Spec 2 6) : BNExists spec.graph 1 4 :=
  spec.bnExists_one_four_of_two_core_vertices

/-- Any loopless two-vertex core with at least one named edge slot is
connected.  Stating the elementary finite argument here lets the completed
banana family feed the semantic Brill--Noether theorem, not merely the
subdivision-level pencil interface. -/
theorem twoVertexCore_connected_of_edge {p : ℕ}
    (spec : Spec 2 p) (edge : Fin p) : spec.core.Connected := by
  intro side hSplit
  refine ⟨edge, ?_⟩
  have fin_two_cases (vertex : Fin 2) : vertex = 0 ∨ vertex = 1 := by
    omega
  have hSide :
      ((0 : Fin 2) ∈ side ∧ (1 : Fin 2) ∉ side) ∨
        ((1 : Fin 2) ∈ side ∧ (0 : Fin 2) ∉ side) := by
    obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
    rcases fin_two_cases inside with hInsideZero | hInsideOne <;>
      rcases fin_two_cases outside with hOutsideZero | hOutsideOne
    · subst inside
      subst outside
      exact False.elim (hOutside hInside)
    · left
      simpa [hInsideZero, hOutsideOne] using And.intro hInside hOutside
    · right
      simpa [hInsideOne, hOutsideZero] using And.intro hInside hOutside
    · subst inside
      subst outside
      exact False.elim (hOutside hInside)
  have hEnds :
      (spec.core.tail edge = 0 ∧ spec.core.head edge = 1) ∨
        (spec.core.tail edge = 1 ∧ spec.core.head edge = 0) := by
    rcases fin_two_cases (spec.core.tail edge) with hTailZero | hTailOne <;>
      rcases fin_two_cases (spec.core.head edge) with hHeadZero | hHeadOne
    · exact False.elim (spec.core_loopless edge (hTailZero.trans hHeadZero.symm))
    · exact Or.inl ⟨hTailZero, hHeadOne⟩
    · exact Or.inr ⟨hTailOne, hHeadZero⟩
    · exact False.elim (spec.core_loopless edge (hTailOne.trans hHeadOne.symm))
  rcases hEnds with hEnds | hEnds <;> rcases hSide with hSide | hSide
  · exact Or.inl ⟨by simpa [hEnds.1] using hSide.1,
        by simpa [hEnds.2] using hSide.2⟩
  · exact Or.inr ⟨by simpa [hEnds.2] using hSide.1,
        by simpa [hEnds.1] using hSide.2⟩
  · exact Or.inr ⟨by simpa [hEnds.2] using hSide.1,
        by simpa [hEnds.1] using hSide.2⟩
  · exact Or.inl ⟨by simpa [hEnds.1] using hSide.1,
        by simpa [hEnds.2] using hSide.2⟩

/-- Every positive subdivision of a loopless two-vertex, six-edge core is
connected. -/
theorem graph_connected_twoVertex_sixEdges (spec : Spec 2 6) :
    graphConnected spec.graph :=
  spec.graph_connected_of_coreConnected
    (twoVertexCore_connected_of_edge spec (0 : Fin 6))

/-- The full Brill--Noether existence conjecture, at every admissible `(r,d)`,
for the completed genus-five banana family. -/
theorem brillNoetherConjecture_twoVertex_sixEdges
    (spec : Spec 2 6) (r d : ℤ) :
    brillNoetherConjecture
      (graph_connected_twoVertex_sixEdges spec) r d := by
  show 0 ≤ genus spec.graph - (r + 1) * (genus spec.graph - d + r) →
    ∃ D : CFDiv spec.graph, rank spec.graph D ≥ r ∧ deg D = d
  intro hRho
  by_cases hR : 0 ≤ r
  · obtain ⟨D, hDegree, hRank⟩ :=
      bnExists_genus_five_of_rankOneDegreeFour
        (graph_connected_twoVertex_sixEdges spec)
        (genus_twoVertex_sixEdges spec)
        (genusFivePencil_twoVertex_sixEdges spec) hR
        (by simpa [bnNumber, rectangleWidth] using hRho)
    exact ⟨D, hRank, hDegree⟩
  · let vertex : spec.graph.V := Classical.arbitrary spec.graph.V
    refine ⟨d • oneChip vertex, ?_, ?_⟩
    · have hLower := rank_geq_neg_one spec.graph (d • oneChip vertex)
      omega
    · rw [map_zsmul, deg_one_chip]
      ring

end AtanasovRanganathan
