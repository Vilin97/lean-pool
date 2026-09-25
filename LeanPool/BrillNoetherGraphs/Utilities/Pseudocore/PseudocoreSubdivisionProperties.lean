/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreMarkerCut

/-!
# Graph properties of compatible pseudocore subdivisions

The lightweight `PseudocoreSplitGlue.Compatible` predicate omits displayed
core connectedness on purpose.  Together with validity of the underlying
pseudocore, however, it determines all graph-theoretic properties needed by
the low-genus normalizers: connectedness, genus, and leaflessness of every
positive subdivision.
-/
namespace Utilities.Certificate.PseudocoreSubdivisionProperties

open Utilities
open ExplicitPotential SubdivisionGraph
open GenusFourPseudocore
open GenusFourPseudocore.Pseudocore
open PseudocorePresentation

/-- Original base vertices retain their loop-aware pseudocore valence after
semantic loops are displayed as two-edge marker cycles. -/
theorem slotValence_baseVertex {n : ℕ} {core : Pseudocore n}
    (split : core.SplitMetadata)
    (hCompatible : PseudocoreSplitGlue.Compatible split) (vertex : Fin n) :
    slotValence split.splitCore (core.baseVertex vertex) = core.valence vertex := by
  rw [slotValence_eq_natSum]
  exact PseudocoreMarkerCut.splitCore_incidenceDegree_baseVertex split vertex
    hCompatible

/-- Every displayed semantic-loop marker has the two incident slot ends of
its marker cycle. -/
theorem slotValence_markerVertex {n : ℕ} {core : Pseudocore n}
    (split : core.SplitMetadata)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (marker : Fin core.loopCount) :
    slotValence split.splitCore (core.markerVertex marker) = 2 := by
  rw [slotValence_eq_natSum]
  change split.splitCore.incidenceDegree (core.markerVertex marker) = 2
  rw [← CubicMatrixReplay.sum_pairMultiplicity_eq_incidenceDegree
    split.splitCore hCompatible.loopless]
  rw [Fin.sum_univ_add]
  change (∑ base : Fin n, explicitCoreMultiplicity split.splitCore
      (core.markerVertex marker) (core.baseVertex base)) +
    (∑ other : Fin core.loopCount, explicitCoreMultiplicity split.splitCore
      (core.markerVertex marker) (core.markerVertex other)) = 2
  simp_rw [hCompatible.multiplicity]
  simp [Pseudocore.SplitMetadata.expectedMultiplicity,
    Pseudocore.baseVertex, Pseudocore.markerVertex]

/-- Every displayed core vertex has valence at least two; base vertices in
fact have valence at least three and marker vertices exactly two. -/
theorem two_le_slotValence {n g : ℕ} {core : Pseudocore n}
    (split : core.SplitMetadata) (hValid : core.ValidAt g)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (vertex : Fin (n + core.loopCount)) :
    2 ≤ slotValence split.splitCore vertex := by
  obtain ⟨index, rfl⟩ := (@finSumFinEquiv n core.loopCount).surjective vertex
  rcases index with base | marker
  · change 2 ≤ slotValence split.splitCore (core.baseVertex base)
    rw [slotValence_baseVertex split hCompatible base]
    exact (by norm_num : 2 ≤ 3).trans (hValid.2.2.1 base)
  · change 2 ≤ slotValence split.splitCore (core.markerVertex marker)
    rw [slotValence_markerVertex split hCompatible marker]

/-- Every positive subdivision of a valid compatible pseudocore split is
connected. -/
theorem graphConnected {n g : ℕ} {core : Pseudocore n}
    (split : core.SplitMetadata) (hValid : core.ValidAt g)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : Spec (n + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore) :
    graphConnected spec.graph := by
  apply spec.graph_connected_of_coreConnected
  rw [hCore]
  exact PseudocoreSplitGlue.splitCore_connected_of_compatible split hValid.2.1
    hCompatible

/-- Every positive subdivision has the genus certified by the underlying
pseudocore. -/
theorem genus_eq {n g : ℕ} {core : Pseudocore n}
    (hValid : core.ValidAt g)
    (spec : Spec (n + core.loopCount) core.splitEdgeCount) :
    genus spec.graph = g := by
  rw [spec.genus_graph]
  exact core.splitTopologicalGenus_eq hValid

/-- Every positive subdivision of a stable compatible pseudocore split is
leafless.  Interior subdivision vertices have degree two; displayed core
vertices have degree at least two by `two_le_slotValence`. -/
theorem leafless {n g : ℕ} {core : Pseudocore n}
    (split : core.SplitMetadata) (hValid : core.ValidAt g)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : Spec (n + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore) :
    ∀ vertex : spec.graph.V, vertexDegree spec.graph vertex ≠ 1 := by
  intro vertex
  rcases vertex with coreVertex | interior
  · have hValence : 2 ≤ slotValence spec.core coreVertex := by
      rw [hCore]
      exact two_le_slotValence split hValid hCompatible coreVertex
    have hDegree := slotValence_eq_vertex_degree spec coreVertex
    have hDegreeLower : (2 : ℤ) ≤
        vertexDegree spec.graph (spec.coreVertex coreVertex) := by
      rw [← hDegree]
      exact_mod_cast hValence
    intro hOne
    change vertexDegree spec.graph (spec.coreVertex coreVertex) = 1 at hOne
    rw [hOne] at hDegreeLower
    norm_num at hDegreeLower
  · obtain ⟨edge, offset⟩ := interior
    change vertexDegree spec.graph (spec.interiorVertex edge offset) ≠ 1
    rw [spec.vertex_degree_interiorVertex_eq_two edge offset]
    norm_num

end Utilities.Certificate.PseudocoreSubdivisionProperties
