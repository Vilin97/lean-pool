/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.TrivalentExpansionClosed
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusFiveVertexCut
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreMarkerWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreSubdivisionProperties

/-!
# Structural coverage of genus-five pseudocores

A semantic loop in the pseudocore split is a pointed rigid genus-one wedge
factor.  Removing it leaves a connected genus-four base, so the public
genus-four pencil theorem and the generic corrected wedge construction give a
degree-four pencil on the original subdivision.  Thus the finite cubic atlas
only has to handle the loopless pseudocore branch.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFivePseudocoreCoverage

open Utilities
open Utilities.Certificate
open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore
open Utilities.Certificate.PseudocoreMarkerWedge
open Utilities.Certificate.PseudocoreSubdivisionProperties
open Utilities.Certificate.PseudocorePresentation
open Utilities.Subdivision.CoreExpansion
open Utilities.Subdivision.TrivalentExpansion
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFiveConstructions
open AtanasovRanganathan.GenusFiveCubicAtlas

/-- Every valid genus-five pseudocore carrying at least one semantic loop is
solved by splitting off one displayed rigid cycle. -/
theorem bnExists_of_loopCount_pos
    (genusFour : GenusFourRankOneExistence)
    {vertexCount : ℕ} {core : Pseudocore vertexCount}
    (split : core.SplitMetadata)
    (hValid : core.ValidAt 5)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec
      (vertexCount + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hLoopCount : 0 < core.loopCount) :
    BNExists spec.graph 1 4 := by
  let marker : Fin core.loopCount := ⟨0, hLoopCount⟩
  have hSplitConnected : split.splitCore.Connected :=
    PseudocoreSplitGlue.splitCore_connected_of_compatible split hValid.2.1
      hCompatible
  let base := MarkerPackage.base split spec marker hCore hCompatible
  let factor := MarkerPackage.factor split spec marker hCore hCompatible
  let attachment := MarkerPackage.attachment split spec marker hCore hCompatible
  let root := MarkerPackage.root split spec marker hCore hCompatible
  have hBaseConnected : graphConnected base :=
    MarkerPackage.base_connected split spec marker hCore hCompatible hSplitConnected
  have hSpecGenus : genus spec.graph = 5 := genus_eq hValid spec
  have hBaseGenus : genus base = 4 := by
    have h := MarkerPackage.base_genus split spec marker hCore hCompatible
    rw [hSpecGenus] at h
    simpa [base] using h
  have hFactorRigid : PointedGenusOneRigid factor root := by
    exact MarkerPackage.factor_rigid split spec marker hCore hCompatible hSplitConnected
  have hWedge : BNExists
      (vertexWedge base factor attachment root) 1 4 :=
    BNExists_vertexWedge_one_four_of_genus_four genusFour
      base factor attachment root hBaseConnected hBaseGenus hFactorRigid
  exact ((MarkerPackage.wedgeIso split spec marker hCore hCompatible).toLaplacianEquiv
    |>.bnExists_iff 1 4).mp hWedge

/-- In the absence of semantic loops, stability makes the displayed core a
minimum-valence-three core.  Its centipede expansion is a cubic `8/12` core.
The public classifier therefore either supplies one of the sixteen closed AR
constructions, which immediately descends to the original subdivision, or
identifies one of the four explicit bridge rows. -/
theorem bnExists_or_bridge_of_loopCount_zero
    (constructions : CubicAtlasConstructions)
    {vertexCount : ℕ} {core : Pseudocore vertexCount}
    (split : core.SplitMetadata)
    (hValid : core.ValidAt 5)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec
      (vertexCount + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hLoopCount : core.loopCount = 0) :
    BNExists spec.graph 1 4 ∨
      ∃ row ∈ bridgeAtlas,
        Nonempty ((data spec.core (fun vertex => by
          let base : Fin vertexCount := Fin.cast (by omega) vertex
          have hVertex : core.baseVertex base = vertex := by
            apply Fin.ext
            rfl
          rw [← hVertex, hCore,
            slotValence_baseVertex split hCompatible base]
          exact hValid.2.2.1 base)).bigCore.Relabeling row.core) := by
  have hDegree : ∀ vertex : Fin (vertexCount + core.loopCount),
      3 ≤ slotValence spec.core vertex := by
    intro vertex
    let base : Fin vertexCount := Fin.cast (by omega) vertex
    have hVertex : core.baseVertex base = vertex := by
      apply Fin.ext
      rfl
    rw [← hVertex, hCore, slotValence_baseVertex split hCompatible base]
    exact hValid.2.2.1 base
  have hConnected : graphConnected spec.graph :=
    PseudocoreSubdivisionProperties.graphConnected split hValid hCompatible spec hCore
  have hCoreConnected : spec.core.Connected :=
    core_connected_of_graph_connected spec hConnected
  have hGenus : genus spec.graph = 5 := genus_eq hValid spec
  have hSize : core.splitEdgeCount - (vertexCount + core.loopCount) = 4 := by
    have hEuler : (core.splitEdgeCount : ℤ) -
        (vertexCount + core.loopCount : ℕ) + 1 = 5 := by
      rw [← spec.genus_graph, hGenus]
    omega
  let D := data spec.core hDegree
  have hConditions : D.Conditions spec.core :=
    conditions spec.core hDegree spec.core_loopless
  have hCubic : D.bigCore.Cubic := bigCore_cubic spec.core hDegree
  have hBigConnected : D.bigCore.Connected :=
    bigCore_connected spec.core hDegree hCoreConnected
  rcases _root_.AtanasovRanganathan.GenusFiveCubicCoverage.classified_closed_or_bridge_of_sizes
      D.bigCore (by simp [hSize]) (by simp [hSize]) constructions
      hBigConnected (ExpansionData.loopless_of_conditions hConditions) hCubic with
    hClosed | hBridge
  · exact Or.inl (bnExists_of_closedConstruction spec.core hDegree spec rfl
      spec.core_loopless hClosed)
  · exact Or.inr hBridge

/-- Closed structural coverage of the four bridge rows turns the loopless
pseudocore reduction into an unconditional pencil. -/
theorem bnExists_of_loopCount_zero
    (constructions : CubicAtlasConstructions)
    (bridges : GenusFiveCubicCoverage.BridgeAtlasClosedCoverage)
    {vertexCount : ℕ} {core : Pseudocore vertexCount}
    (split : core.SplitMetadata)
    (hValid : core.ValidAt 5)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec
      (vertexCount + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hLoopCount : core.loopCount = 0) :
    BNExists spec.graph 1 4 := by
  have hDegree : ∀ vertex : Fin (vertexCount + core.loopCount),
      3 ≤ slotValence spec.core vertex := by
    intro vertex
    let base : Fin vertexCount := Fin.cast (by omega) vertex
    have hVertex : core.baseVertex base = vertex := by
      apply Fin.ext
      rfl
    rw [← hVertex, hCore, slotValence_baseVertex split hCompatible base]
    exact hValid.2.2.1 base
  have hConnected : graphConnected spec.graph :=
    PseudocoreSubdivisionProperties.graphConnected split hValid hCompatible spec hCore
  have hCoreConnected : spec.core.Connected :=
    core_connected_of_graph_connected spec hConnected
  have hGenus : genus spec.graph = 5 := genus_eq hValid spec
  have hSize : core.splitEdgeCount - (vertexCount + core.loopCount) = 4 := by
    have hEuler : (core.splitEdgeCount : ℤ) -
        (vertexCount + core.loopCount : ℕ) + 1 = 5 := by
      rw [← spec.genus_graph, hGenus]
    omega
  let D := data spec.core hDegree
  have hConditions : D.Conditions spec.core :=
    conditions spec.core hDegree spec.core_loopless
  have hClosed : ClosedSubdivisionDharConstruction D.bigCore (by
      have hPositive : 0 < 2 *
          (core.splitEdgeCount - (vertexCount + core.loopCount)) := by omega
      exact hPositive) :=
    GenusFiveCubicCoverage.classified_closed_of_sizes D.bigCore
      (by simp [hSize]) (by simp [hSize]) constructions bridges
      (bigCore_connected spec.core hDegree hCoreConnected)
      (ExpansionData.loopless_of_conditions hConditions)
      (bigCore_cubic spec.core hDegree)
  exact bnExists_of_closedConstruction spec.core hDegree spec rfl
    spec.core_loopless hClosed

/-- The genus-four theorem and the finite four-row bridge obligation discharge
the exact public genus-five pseudocore interface. -/
theorem genusFivePseudocorePencils_of_bridgeCoverage
    (genusFour : GenusFourRankOneExistence)
    (bridges : GenusFiveCubicCoverage.BridgeAtlasClosedCoverage) :
    GenusFivePseudocorePencils := by
  intro vertexCount core split _hSmall hValid hCompatible spec hCore
  by_cases hLoop : core.loopCount = 0
  · exact bnExists_of_loopCount_zero cubicAtlasConstructions bridges split
      hValid hCompatible spec hCore hLoop
  · exact bnExists_of_loopCount_pos genusFour split hValid hCompatible spec
      hCore (Nat.zero_lt_of_ne_zero hLoop)

/-- Public end-to-end assembly with only the genus-four theorem and the four
structural bridge rows exposed as inputs. -/
theorem brillNoetherExistenceThroughFive_of_bridgeCoverage
    (genusFour : GenusFourRankOneExistence)
    (bridges : GenusFiveCubicCoverage.BridgeAtlasClosedCoverage) :
    BrillNoetherExistenceThroughFive :=
  brillNoetherExistenceThroughFive_of_geometricInputs
    { genusFour := genusFour
      genusFivePseudocores :=
        genusFivePseudocorePencils_of_bridgeCoverage genusFour bridges }

end AtanasovRanganathan.GenusFivePseudocoreCoverage
