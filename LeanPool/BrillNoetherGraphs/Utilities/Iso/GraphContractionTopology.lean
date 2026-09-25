/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContraction
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover
import Mathlib.Tactic

/-!
# Topological graph-contraction certificates

`GraphContractionCertificate.Valid` records the quotient multiplicities.  A
topological contraction additionally has connected vertex fibres.  This file
expresses that condition by the same finite-cut criterion as
`graphConnected`, so it admits an exact Boolean replay checker.

The fibre condition is deliberately separate from `Valid`: quotient
multiplicities alone do not prevent a certificate from identifying two
disconnected pieces of the source graph.
-/

namespace Utilities.Certificate

open Finset

universe u v w

namespace GraphContractionCertificate

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- The fibre over `target` is connected, expressed by finite cuts of the
ambient source graph.  Only cuts which split that fibre need be crossed, and
the crossing edge is required to remain inside the fibre. -/
def FibreConnectedAt (c : GraphContractionCertificate G H) (target : H.V) : Prop :=
  ∀ S : Finset G.V,
    (∃ inside outside : G.V,
      inside ∈ S ∧ outside ∉ S ∧
        c.vertexMap inside = target ∧ c.vertexMap outside = target) →
    ∃ inside ∈ S, ∃ outside ∉ S,
      c.vertexMap inside = target ∧ c.vertexMap outside = target ∧
        numEdges G inside outside > 0

/-- Every vertex fibre is connected. -/
def ConnectedFibres (c : GraphContractionCertificate G H) : Prop :=
  ∀ target : H.V, c.FibreConnectedAt target

/-- Exact finite Boolean replay of connectedness for every fibre. -/
def connectedFibresCheck (c : GraphContractionCertificate G H) : Bool :=
  AffineCover.allFinset (Finset.univ : Finset H.V) fun target =>
    AffineCover.allFinset (Finset.univ : Finset (Finset G.V)) fun S =>
      decide ((∃ inside outside : G.V,
        inside ∈ S ∧ outside ∉ S ∧
          c.vertexMap inside = target ∧ c.vertexMap outside = target) →
        ∃ inside ∈ S, ∃ outside ∉ S,
          c.vertexMap inside = target ∧ c.vertexMap outside = target ∧
            numEdges G inside outside > 0)

@[simp] theorem connectedFibresCheck_eq_true_iff
    (c : GraphContractionCertificate G H) :
    c.connectedFibresCheck = true ↔ c.ConnectedFibres := by
  simp [connectedFibresCheck, ConnectedFibres, FibreConnectedAt]

/-- A quotient certificate whose fibres are actual connected subgraphs. -/
def TopologicalValid (c : GraphContractionCertificate G H) : Prop :=
  c.Valid ∧ c.ConnectedFibres

/-- Exact Boolean checker for a topological contraction certificate. -/
def topologicalCheck (c : GraphContractionCertificate G H) : Bool :=
  c.check && c.connectedFibresCheck

@[simp] theorem topologicalCheck_eq_true_iff
    (c : GraphContractionCertificate G H) :
    c.topologicalCheck = true ↔ c.TopologicalValid := by
  simp [topologicalCheck, TopologicalValid]

/-- A valid contraction is onto on vertices.  This small formulation keeps
marked-lift arguments from having to unpack `Valid` directly. -/
theorem exists_source_of_vertexMap_eq
    (c : GraphContractionCertificate G H) (hValid : c.Valid) (target : H.V) :
    ∃ source : G.V, c.vertexMap source = target :=
  hValid.1 target

/-- A topological quotient of a connected graph cannot have a disconnected
source.  Indeed, a source cut with no crossing edge cannot split a connected
fibre; it therefore descends to a nontrivial target cut, whose crossing edge
lifts through the quotient multiplicity equation. -/
theorem graph_connected_of_topologicalValid
    (c : GraphContractionCertificate G H) (hTopological : c.TopologicalValid)
    (hTarget : _root_.graphConnected H) :
    _root_.graphConnected G := by
  classical
  intro S hSplit
  obtain ⟨x, y, hxS, hyS⟩ := hSplit
  by_contra hNoCross
  have hSaturated : ∀ target : H.V, ∀ source : G.V,
      source ∈ S → c.vertexMap source = target →
        ∀ other : G.V, c.vertexMap other = target → other ∈ S := by
    intro target source hSource hMap other hOtherMap
    by_contra hOther
    obtain ⟨inside, hInside, outside, hOutside, hInsideMap, hOutsideMap, hEdge⟩ :=
      hTopological.2 target S ⟨source, other, hSource, hOther, hMap, hOtherMap⟩
    exact hNoCross ⟨inside, hInside, outside, hOutside, hEdge⟩
  let T : Finset H.V := S.image c.vertexMap
  have hxT : c.vertexMap x ∈ T := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
  have hyT : c.vertexMap y ∉ T := by
    intro hyT
    obtain ⟨source, hSource, hMap⟩ := Finset.mem_image.mp hyT
    exact hyS (hSaturated (c.vertexMap y) source hSource hMap y rfl)
  obtain ⟨a, haT, b, hbT, hTargetEdge⟩ :=
    hTarget T ⟨c.vertexMap x, c.vertexMap y, hxT, hyT⟩
  obtain ⟨sourceA, hSourceAS, hSourceAMap⟩ := Finset.mem_image.mp haT
  have hab : a ≠ b := by
    intro hab
    exact hbT (by simpa [hab] using haT)
  have hSum : 0 < ∑ source : G.V, ∑ other : G.V,
      if c.vertexMap source = a ∧ c.vertexMap other = b then
        numEdges G source other else 0 := by
    rw [← hTopological.1.2 a b hab]
    exact hTargetEdge
  have hOuter : ∃ source : G.V, 0 < ∑ other : G.V,
      if c.vertexMap source = a ∧ c.vertexMap other = b then
        numEdges G source other else 0 := by
    obtain ⟨source, _, hSource⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hSum
    exact ⟨source, hSource⟩
  obtain ⟨source, hSourceSum⟩ := hOuter
  obtain ⟨other, _, hTerm⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hSourceSum
  by_cases hMaps : c.vertexMap source = a ∧ c.vertexMap other = b
  · have hSourceS : source ∈ S :=
      hSaturated a sourceA hSourceAS hSourceAMap source hMaps.1
    have hOtherNotS : other ∉ S := by
      intro hOtherS
      exact hbT (Finset.mem_image.mpr ⟨other, hOtherS, hMaps.2⟩)
    exact hNoCross ⟨source, hSourceS, other, hOtherNotS,
      by simpa [hMaps] using hTerm⟩
  · simp [hMaps] at hTerm

/-- Connected fibres are invariant under a checked relabeling of the source
graph.  A cut of a relabeled fibre is carried across the vertex equivalence,
the original fibre condition supplies a crossing edge, and that edge is then
pulled back. -/
theorem connectedFibres_precomposeLaplacianEquiv {G' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv G' G)
    (hFibres : c.ConnectedFibres) :
    (c.precomposeLaplacianEquiv equivalence).ConnectedFibres := by
  intro target S hSplit
  let carried : Finset G.V := S.map equivalence.toEquiv.toEmbedding
  have hSplit' : ∃ inside outside : G.V,
      inside ∈ carried ∧ outside ∉ carried ∧
        c.vertexMap inside = target ∧ c.vertexMap outside = target := by
    obtain ⟨inside, outside, hInside, hOutside, hInsideMap, hOutsideMap⟩ := hSplit
    refine ⟨equivalence inside, equivalence outside, ?_, ?_, ?_, ?_⟩
    · simpa [carried] using hInside
    · simpa [carried] using hOutside
    · change c.vertexMap (equivalence inside) = target at hInsideMap
      exact hInsideMap
    · change c.vertexMap (equivalence outside) = target at hOutsideMap
      exact hOutsideMap
  obtain ⟨inside, hInside, outside, hOutside, hInsideMap, hOutsideMap, hEdge⟩ :=
    hFibres target carried hSplit'
  refine ⟨equivalence.toEquiv.symm inside, ?_, equivalence.toEquiv.symm outside,
    ?_, ?_, ?_, ?_⟩
  · simpa [carried] using hInside
  · simpa [carried] using hOutside
  · change c.vertexMap (equivalence (equivalence.toEquiv.symm inside)) = target
    simpa using hInsideMap
  · change c.vertexMap (equivalence (equivalence.toEquiv.symm outside)) = target
    simpa using hOutsideMap
  · rw [← equivalence.num_edges_eq]
    simpa using hEdge

/-- Topological validity is invariant under a checked relabeling of the
source graph. -/
theorem topologicalValid_precomposeLaplacianEquiv {G' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv G' G)
    (hTopological : c.TopologicalValid) :
    (c.precomposeLaplacianEquiv equivalence).TopologicalValid :=
  ⟨c.valid_precomposeLaplacianEquiv equivalence hTopological.1,
    c.connectedFibres_precomposeLaplacianEquiv equivalence hTopological.2⟩

/-- Connected fibres are invariant under a checked relabeling of the quotient
target. -/
theorem connectedFibres_postcomposeLaplacianEquiv {H' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv H H')
    (hFibres : c.ConnectedFibres) :
    (c.postcomposeLaplacianEquiv equivalence).ConnectedFibres := by
  intro target S hSplit
  have hSplit' : ∃ inside outside : G.V,
      inside ∈ S ∧ outside ∉ S ∧
        c.vertexMap inside = equivalence.toEquiv.symm target ∧
          c.vertexMap outside = equivalence.toEquiv.symm target := by
    obtain ⟨inside, outside, hInside, hOutside, hInsideMap, hOutsideMap⟩ := hSplit
    refine ⟨inside, outside, hInside, hOutside, ?_, ?_⟩
    · apply equivalence.toEquiv.injective
      change equivalence (c.vertexMap inside) = target at hInsideMap
      simpa using hInsideMap
    · apply equivalence.toEquiv.injective
      change equivalence (c.vertexMap outside) = target at hOutsideMap
      simpa using hOutsideMap
  obtain ⟨inside, hInside, outside, hOutside, hInsideMap, hOutsideMap, hEdge⟩ :=
    hFibres (equivalence.toEquiv.symm target) S hSplit'
  refine ⟨inside, hInside, outside, hOutside, ?_, ?_, hEdge⟩
  · simp [postcomposeLaplacianEquiv, hInsideMap]
  · simp [postcomposeLaplacianEquiv, hOutsideMap]

/-- Topological validity is invariant under a checked relabeling of the
quotient target. -/
theorem topologicalValid_postcomposeLaplacianEquiv {H' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv H H')
    (hTopological : c.TopologicalValid) :
    (c.postcomposeLaplacianEquiv equivalence).TopologicalValid :=
  ⟨c.valid_postcomposeLaplacianEquiv equivalence hTopological.1,
    c.connectedFibres_postcomposeLaplacianEquiv equivalence hTopological.2⟩

end GraphContractionCertificate

end Utilities.Certificate
