/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocorePresentation
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreMarkerWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.GraphIsoLaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.OneVertexCutFactors
public import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoTopology
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.GraphIsoCuts

/-!
# Pseudocore presentation in bridgeless genus two

This is the constructive bivalent-path reduction behind the topological
classification of a bridgeless genus-two graph.  It specializes the generic
pseudocore normalization to show that the retained base core has at most two
vertices; bivalent semantic-loop markers are retained by the pseudocore
construction rather than accidentally suppressed.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.PseudocorePresentation
open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore

/-- The two topological models produced by the genus-two pseudocore
normalization.  The wedge branch deliberately records the intrinsic
pointed-rigid genus-one factors; replacing them by explicitly indexed cycles
is a separate genus-one presentation step. -/
inductive BridgelessGenusTwoCoreNormalForm (G : CFGraph.{0}) : Prop
  | theta (B : Banana 2) (equivalence : LaplacianEquiv G B.graph) :
      BridgelessGenusTwoCoreNormalForm G
  | rigidWedge (base factor : CFGraph.{0}) (attachment : base.V) (root : factor.V)
      (baseConnected : _root_.graphConnected base) (baseGenus : genus base = 1)
      (baseCut : TwoEdgeCutCondition base) (factorCut : TwoEdgeCutCondition factor)
      (wedgeCut : TwoEdgeCutCondition (vertexWedge base factor attachment root))
      (baseRigid : PointedGenusOneRigid base attachment)
      (factorRigid : PointedGenusOneRigid factor root)
      (equivalence : LaplacianEquiv G (vertexWedge base factor attachment root)) :
      BridgelessGenusTwoCoreNormalForm G

/-- The same structural alternatives with the two marked vertices carried
explicitly to the model graph. -/
inductive MarkedBridgelessGenusTwoCoreNormalForm
    (G : CFGraph.{0}) (u v : G.V) : Prop
  | theta (B : Banana 2) (u' v' : B.graph.V)
      (equivalence : CFGraphIso G B.graph)
      (uEquation : equivalence.vertexEquiv u = u')
      (vEquation : equivalence.vertexEquiv v = v') :
      MarkedBridgelessGenusTwoCoreNormalForm G u v
  | rigidWedge (base factor : CFGraph.{0}) (attachment : base.V) (root : factor.V)
      (u' v' : (vertexWedge base factor attachment root).V)
      (baseConnected : _root_.graphConnected base) (baseGenus : genus base = 1)
      (baseCut : TwoEdgeCutCondition base) (factorCut : TwoEdgeCutCondition factor)
      (wedgeCut : TwoEdgeCutCondition (vertexWedge base factor attachment root))
      (baseRigid : PointedGenusOneRigid base attachment)
      (factorRigid : PointedGenusOneRigid factor root)
      (equivalence : CFGraphIso G (vertexWedge base factor attachment root))
      (uEquation : equivalence.vertexEquiv u = u')
      (vEquation : equivalence.vertexEquiv v = v') :
      MarkedBridgelessGenusTwoCoreNormalForm G u v

/-- A valid genus-two pseudocore with at most two base vertices has either
one or two base vertices.  The impossible zero-vertex case already
contradicts the Euler edge equation. -/
theorem pseudocore_baseVertexCount_eq_one_or_two
    {n : ℕ} (core : Pseudocore n) (hValid : core.ValidAt 2) (hBound : n ≤ 2) :
    n = 1 ∨ n = 2 := by
  have hPositive : 0 < n := by
    by_contra hNotPositive
    have hn : n = 0 := Nat.eq_zero_of_not_pos hNotPositive
    subst n
    have hEdges := hValid.2.2.2
    simp [Pseudocore.edgeCount, Pseudocore.loopCount,
      Pseudocore.nonloopEdgeCount] at hEdges
  omega

/-- In the two-base-vertex genus-two pseudocore case, semantic loops occur
at both base vertices or at neither.  These are respectively the two-cycle
wedge and theta branches after splitting loop markers. -/
theorem pseudocore_loopCount_eq_zero_or_two_of_two_base_vertices
    (core : Pseudocore 2) (hValid : core.ValidAt 2) :
    core.loopCount = 0 ∨ core.loopCount = 2 := by
  rcases hValid with ⟨hWF, _hConnected, hStable, hEdges⟩
  rcases hWF with ⟨hDiagonal, hSymmetric⟩
  have hZero := hStable 0
  have hOne := hStable 1
  simp [Pseudocore.valence, Fin.sum_univ_two] at hZero hOne
  rw [hDiagonal 0] at hZero
  rw [hDiagonal 1, hSymmetric 1 0] at hOne
  simp [Pseudocore.edgeCount, Pseudocore.loopCount,
    Pseudocore.nonloopEdgeCount, Fin.sum_univ_two] at hEdges ⊢
  omega

/-- The one-base-vertex genus-two pseudocore consists of two semantic loops. -/
theorem pseudocore_loopCount_eq_two_of_one_base_vertex
    (core : Pseudocore 1) (hValid : core.ValidAt 2) : core.loopCount = 2 := by
  have hEdges := hValid.2.2.2
  simp [Pseudocore.edgeCount, Pseudocore.loopCount,
    Pseudocore.nonloopEdgeCount] at hEdges ⊢
  omega

/-- A valid genus-two pseudocore on two base vertices is exactly cubic. -/
theorem pseudocore_valence_eq_three_of_two_base_vertices
    (core : Pseudocore 2) (hValid : core.ValidAt 2) :
    ∀ vertex : Fin 2, core.valence vertex = 3 := by
  rcases hValid with ⟨hWF, _hConnected, hStable, hEdges⟩
  have hHandshake := Pseudocore.sum_valence_eq core hWF
  have hEdgeCount : core.edgeCount = 3 := by omega
  rw [hEdgeCount, Fin.sum_univ_two] at hHandshake
  have hZero : 3 ≤ core.valence (0 : Fin 2) := hStable 0
  have hOne : 3 ≤ core.valence (1 : Fin 2) := hStable 1
  intro vertex
  fin_cases vertex
  · simpa using (show core.valence (0 : Fin 2) = 3 by omega)
  · simpa using (show core.valence (1 : Fin 2) = 3 by omega)

/-- A loop-free two-base-vertex genus-two pseudocore presentation is already
a theta (`Banana 2`) presentation.  No separate graph construction is needed:
a positive subdivision with two core vertices and three slots is definitionally
the banana model. -/
theorem thetaPresentation_of_loopFree_twoBasePseudocore
    (core : Pseudocore 2) (hValid : core.ValidAt 2)
    (hLoops : core.loopCount = 0)
    (spec : Spec (2 + core.loopCount) core.splitEdgeCount)
    {G : CFGraph.{0}}
    (hPresentation : Nonempty (LaplacianEquiv G spec.graph)) :
    ∃ B : Banana 2, Nonempty (LaplacianEquiv G B.graph) := by
  have hEdgeCount : core.edgeCount = 3 := by
    have hEdges := hValid.2.2.2
    omega
  have hSlots : core.splitEdgeCount = 3 := by
    rw [core.splitEdgeCount_eq_edgeCount_add_loopCount, hEdgeCount, hLoops]
  generalize hLoopsDef : core.loopCount = loopCount at spec hPresentation hLoops hSlots ⊢
  generalize hSlotsDef : core.splitEdgeCount = slotCount at spec hPresentation hSlots ⊢
  cases hLoops
  cases hSlots
  exact ⟨spec, hPresentation⟩

/-- Every nontrivial bridgeless genus-two graph is Laplacian-equivalent to a
positive subdivision of the loopless split of a valid genus-two pseudocore
with at most two base vertices. -/
theorem bridgelessGenusTwo_pseudocorePresentation
    (G : CFGraph.{0}) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) :
    ∃ (k : ℕ) (core : Pseudocore k) (split : core.SplitMetadata),
      k ≤ 2 ∧ core.ValidAt 2 ∧ PseudocoreSplitGlue.Compatible split ∧
      ∃ spec : Spec (k + core.loopCount) core.splitEdgeCount,
        spec.core = split.splitCore ∧ Nonempty (LaplacianEquiv G spec.graph) := by
  classical
  have hDeg : ∀ vertex : G.V, 2 ≤ vertexDegree G vertex :=
    hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial
  obtain ⟨N, P, spec, hPresent, hReduced⟩ :=
    exists_reduced (Fintype.card G.V) G.edges.card
      (UnitSubdivisionPresentation.spec G)
  obtain ⟨reduction⟩ := hPresent
  have equivalence : LaplacianEquiv G spec.graph :=
    (UnitSubdivisionPresentation.laplacianEquiv G).trans reduction
  have hSpecConnected : _root_.graphConnected spec.graph :=
    equivalence.graphConnected hConnected
  have hSpecGenus : genus spec.graph = 2 := by
    rw [equivalence.genus_eq, hGenus]
  have hSpecDegree : ∀ v : Fin N, 2 ≤ slotValence spec.core v := by
    intro v
    have hCast := slotValence_eq_vertex_degree spec v
    have hBack := equivalence.vertexDegree_eq
      (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [Equiv.apply_symm_apply] at hBack
    have hGe := hDeg (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [← hBack, ← hCast] at hGe
    exact_mod_cast hGe
  obtain ⟨shape⟩ :=
    exists_markedShapeAt spec hReduced hSpecConnected hSpecGenus (by norm_num) hSpecDegree
  simpa only [Nat.reduceSub, Nat.mul_one] using
    pseudocorePresentation_of_markedShapeAt spec shape hSpecConnected
      hSpecGenus ⟨equivalence⟩

/-- Construct the theta-or-rigid-wedge structural form of every nontrivial
bridgeless genus-two graph. -/
theorem bridgelessGenusTwo_coreNormalForm
    (G : CFGraph.{0}) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) : BridgelessGenusTwoCoreNormalForm G := by
  obtain ⟨k, core, split, hBound, hValid, hCompatible, spec, hCore,
    hPresentation⟩ := bridgelessGenusTwo_pseudocorePresentation
      G hConnected hCut hNontrivial hGenus
  obtain ⟨presentation⟩ := hPresentation
  have hSpecConnected : _root_.graphConnected spec.graph :=
    presentation.graphConnected hConnected
  have hSpecGenus : genus spec.graph = 2 := by
    rw [presentation.genus_eq, hGenus]
  have hSpecCut : TwoEdgeCutCondition spec.graph :=
    (presentation.toGraphIso.twoEdgeCutCondition_map_iff).mpr hCut
  have hSplitConnected : split.splitCore.Connected := by
    have hConnectedCore := core_connected_of_graph_connected spec hSpecConnected
    rwa [hCore] at hConnectedCore
  rcases pseudocore_baseVertexCount_eq_one_or_two core hValid hBound with hOne | hTwo
  · subst k
    have hLoops := pseudocore_loopCount_eq_two_of_one_base_vertex core hValid
    let marker : Fin core.loopCount := ⟨0, by omega⟩
    exact .rigidWedge
      (PseudocoreMarkerWedge.MarkerPackage.base split spec marker hCore hCompatible)
      (PseudocoreMarkerWedge.MarkerPackage.factor split spec marker hCore hCompatible)
      (PseudocoreMarkerWedge.MarkerPackage.attachment split spec marker hCore hCompatible)
      (PseudocoreMarkerWedge.MarkerPackage.root split spec marker hCore hCompatible)
      (PseudocoreMarkerWedge.MarkerPackage.base_connected split spec marker hCore
        hCompatible hSplitConnected)
      (by
        rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
          hCompatible, hSpecGenus]
        norm_num)
      ((PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
        hCompatible).twoEdgeCutCondition_rightGraph hSpecCut)
      ((PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
        hCompatible).twoEdgeCutCondition_leftGraph hSpecCut)
      (((PseudocoreMarkerWedge.MarkerPackage.wedgeEquiv split spec marker hCore
        hCompatible presentation).toGraphIso.twoEdgeCutCondition_map_iff).mpr hCut)
      (by
        apply pointedGenusOneRigid_of_twoEdgeCutCondition
        · exact PseudocoreMarkerWedge.MarkerPackage.base_connected split spec marker
            hCore hCompatible hSplitConnected
        · rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
            hCompatible, hSpecGenus]
          norm_num
        · apply exists_vertex_ne_of_genus_pos
          rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
            hCompatible, hSpecGenus]
          norm_num
        · exact (PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
            hCompatible).twoEdgeCutCondition_rightGraph hSpecCut)
      (PseudocoreMarkerWedge.MarkerPackage.factor_rigid split spec marker hCore
        hCompatible hSplitConnected)
      (PseudocoreMarkerWedge.MarkerPackage.wedgeEquiv split spec marker hCore
        hCompatible presentation)
  · subst k
    rcases pseudocore_loopCount_eq_zero_or_two_of_two_base_vertices core hValid with hLoops | hLoops
    · obtain ⟨B, hTheta⟩ := thetaPresentation_of_loopFree_twoBasePseudocore
        core hValid hLoops spec ⟨presentation⟩
      obtain ⟨equivalence⟩ := hTheta
      exact .theta B equivalence
    · let marker : Fin core.loopCount := ⟨0, by omega⟩
      exact .rigidWedge
        (PseudocoreMarkerWedge.MarkerPackage.base split spec marker hCore hCompatible)
        (PseudocoreMarkerWedge.MarkerPackage.factor split spec marker hCore hCompatible)
        (PseudocoreMarkerWedge.MarkerPackage.attachment split spec marker hCore hCompatible)
        (PseudocoreMarkerWedge.MarkerPackage.root split spec marker hCore hCompatible)
        (PseudocoreMarkerWedge.MarkerPackage.base_connected split spec marker hCore
          hCompatible hSplitConnected)
        (by
          rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
            hCompatible, hSpecGenus]
          norm_num)
        ((PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
          hCompatible).twoEdgeCutCondition_rightGraph hSpecCut)
        ((PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
          hCompatible).twoEdgeCutCondition_leftGraph hSpecCut)
        (((PseudocoreMarkerWedge.MarkerPackage.wedgeEquiv split spec marker hCore
          hCompatible presentation).toGraphIso.twoEdgeCutCondition_map_iff).mpr hCut)
        (by
          apply pointedGenusOneRigid_of_twoEdgeCutCondition
          · exact PseudocoreMarkerWedge.MarkerPackage.base_connected split spec marker
              hCore hCompatible hSplitConnected
          · rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
              hCompatible, hSpecGenus]
            norm_num
          · apply exists_vertex_ne_of_genus_pos
            rw [PseudocoreMarkerWedge.MarkerPackage.base_genus split spec marker hCore
              hCompatible, hSpecGenus]
            norm_num
          · exact (PseudocoreMarkerWedge.MarkerPackage.cut split spec marker hCore
              hCompatible).twoEdgeCutCondition_rightGraph hSpecCut)
        (PseudocoreMarkerWedge.MarkerPackage.factor_rigid split spec marker hCore
          hCompatible hSplitConnected)
        (PseudocoreMarkerWedge.MarkerPackage.wedgeEquiv split spec marker hCore
          hCompatible presentation)

/-- Transport the two marks through the structural core normal form. -/
theorem marked_bridgelessGenusTwo_coreNormalForm
    (G : CFGraph.{0}) (u v : G.V) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) :
    MarkedBridgelessGenusTwoCoreNormalForm G u v := by
  cases bridgelessGenusTwo_coreNormalForm G hConnected hCut hNontrivial hGenus with
  | theta B equivalence =>
    let graphIso := equivalence.toGraphIso
    exact .theta B (graphIso.vertexEquiv u) (graphIso.vertexEquiv v) graphIso rfl rfl
  | rigidWedge base factor attachment root hBaseConnected hBaseGenus hBaseCut hFactorCut
      hWedgeCut hBaseRigid hFactorRigid equivalence =>
    let graphIso := equivalence.toGraphIso
    exact .rigidWedge base factor attachment root
      (graphIso.vertexEquiv u) (graphIso.vertexEquiv v)
      hBaseConnected hBaseGenus hBaseCut hFactorCut hWedgeCut hBaseRigid hFactorRigid graphIso rfl
        rfl

end Bananas
