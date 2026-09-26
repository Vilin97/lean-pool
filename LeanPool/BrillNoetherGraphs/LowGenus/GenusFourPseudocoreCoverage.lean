/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence
public import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.TrivalentExpansionClosed
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.FossilTopology
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusThreeCycleWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreMarkerWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocorePresentation
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreSubdivisionProperties

/-!
# Public genus-four reduction to six closed cubic rows

After fossilization, a genus-four graph is connected and leafless.  Its
pseudocore has either a semantic loop, which splits off as a rigid genus-one
factor from a genus-three base, or no semantic loops.  In the latter case
stability permits the centipede expansion to a connected loopless cubic core
with exactly six vertices and nine slots.

Consequently the whole genus-four critical-pencil theorem reduces directly to
closed degree-three pencils on connected loopless cubic `6/9` cores.  No
111-row pseudocore catalog is needed by this unmarked proof.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFourPseudocoreCoverage

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore
open Utilities.Certificate.PseudocoreMarkerWedge
open Utilities.Certificate.PseudocorePresentation
open Utilities.Certificate.PseudocoreSubdivisionProperties
open Utilities.Subdivision.CoreExpansion
open Utilities.Subdivision.TrivalentExpansion
open AtanasovRanganathan.Configurations

/-- Exact finite input for the public genus-four reduction: every connected
loopless cubic `6/9` core carries a degree-three pencil on all of its nonloopy
forest faces. -/
def CubicClosedCoverage : Prop :=
  ∀ (candidate : Core 6 9), candidate.Connected →
    (∀ edge : Fin 9, candidate.tail edge ≠ candidate.head edge) →
    candidate.Cubic →
    ∀ (length : Fin 9 → ℕ)
      (hForest : IsForest candidate (zeroSlots length))
      (hNotLoopy : ¬ IsLoopy candidate (zeroSlots length)),
      BNExists (faceSpec candidate (by norm_num) length hForest hNotLoopy).graph 1 3

/-- Size-indexed form of cubic coverage, for the arithmetically sized
centipede expansion. -/
theorem closedPencil_of_sizes
    (coverage : CubicClosedCoverage)
    {n p : ℕ} (candidate : Core n p)
    (hVertices : n = 6) (hSlots : p = 9)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin p, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ∀ (length : Fin p → ℕ)
      (hForest : IsForest candidate (zeroSlots length))
      (hNotLoopy : ¬ IsLoopy candidate (zeroSlots length)),
      BNExists (faceSpec candidate (by omega) length hForest hNotLoopy).graph 1 3 := by
  subst n
  subst p
  exact coverage candidate hConnected hLoopless hCubic

/-- A semantic loop splits off as a rigid genus-one cycle from a connected
genus-three base, where the canonical degree-three wedge pencil applies. -/
theorem bnExists_of_loopCount_pos
    {vertexCount : ℕ} {core : Pseudocore vertexCount}
    (split : core.SplitMetadata)
    (hValid : core.ValidAt 4)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec
      (vertexCount + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hLoopCount : 0 < core.loopCount) :
    BNExists spec.graph 1 3 := by
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
  have hSpecGenus : genus spec.graph = 4 := genus_eq hValid spec
  have hBaseGenus : genus base = 3 := by
    have h := MarkerPackage.base_genus split spec marker hCore hCompatible
    rw [hSpecGenus] at h
    simpa [base] using h
  have hFactorRigid : PointedGenusOneRigid factor root :=
    MarkerPackage.factor_rigid split spec marker hCore hCompatible hSplitConnected
  have hWedge : BNExists (vertexWedge base factor attachment root) 1 3 :=
    MarkedGraphs.BNExists_vertexWedge_rankOneDegreeThree_of_genus_three
      base factor attachment root hBaseConnected hBaseGenus hFactorRigid
  exact ((MarkerPackage.wedgeIso split spec marker hCore hCompatible).toLaplacianEquiv
    |>.bnExists_iff 1 3).mp hWedge

/-- A loopless valid genus-four pseudocore expands to the `6/9` cubic closed
boundary and therefore inherits its degree-three pencil. -/
theorem bnExists_of_loopCount_zero
    (coverage : CubicClosedCoverage)
    {vertexCount : ℕ} {core : Pseudocore vertexCount}
    (split : core.SplitMetadata)
    (hValid : core.ValidAt 4)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec
      (vertexCount + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hLoopCount : core.loopCount = 0) :
    BNExists spec.graph 1 3 := by
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
  have hGenus : genus spec.graph = 4 := genus_eq hValid spec
  have hSize : core.splitEdgeCount - (vertexCount + core.loopCount) = 3 := by
    have hEuler : (core.splitEdgeCount : ℤ) -
        (vertexCount + core.loopCount : ℕ) + 1 = 4 := by
      rw [← spec.genus_graph, hGenus]
    omega
  let D := data spec.core hDegree
  have hConditions : D.Conditions spec.core :=
    conditions spec.core hDegree spec.core_loopless
  have hClosed : ∀ (length : Fin (3 *
      (core.splitEdgeCount - (vertexCount + core.loopCount))) → ℕ)
      (hForest : IsForest D.bigCore (zeroSlots length))
      (hNotLoopy : ¬ IsLoopy D.bigCore (zeroSlots length)),
      BNExists (faceSpec D.bigCore (by
        have hPositive : 0 < 2 *
            (core.splitEdgeCount - (vertexCount + core.loopCount)) := by omega
        exact hPositive) length hForest hNotLoopy).graph 1 3 := by
    intro length hForest hNotLoopy
    exact closedPencil_of_sizes coverage D.bigCore
      (by simp [hSize]) (by simp [hSize])
      (bigCore_connected spec.core hDegree hCoreConnected)
      (ExpansionData.loopless_of_conditions hConditions)
      (bigCore_cubic spec.core hDegree) length hForest hNotLoopy
  exact bnExists_of_closedPencil spec.core hDegree spec rfl
    spec.core_loopless hClosed

/-- Closed coverage of the six cubic rows implies the global genus-four
degree-three rank-one theorem. -/
theorem genusFourRankOneExistence_of_cubicClosedCoverage
    (coverage : CubicClosedCoverage) : GenusFourRankOneExistence := by
  intro G hConnected hGenus
  let F := fossil G
  have hFConnected : graphConnected F := graph_connected_fossil G hConnected
  have hFGenus : genus F = 4 := (genus_fossil G hConnected).trans hGenus
  have hFLeafless : ∀ vertex : F.V, vertexDegree F vertex ≠ 1 :=
    fossil_vertex_degree_ne_one G hConnected
  obtain ⟨vertexCount, core, split, _hSmall, hValid, hCompatible,
      spec, hCore, ⟨equivalence⟩⟩ :=
    pseudocorePresentation_of_leafless F hFConnected hFGenus (by norm_num)
      hFLeafless
  have hSpec : BNExists spec.graph 1 3 := by
    by_cases hLoop : core.loopCount = 0
    · exact bnExists_of_loopCount_zero coverage split hValid hCompatible spec
        hCore hLoop
    · exact bnExists_of_loopCount_pos split hValid hCompatible spec hCore
        (Nat.zero_lt_of_ne_zero hLoop)
  have hF : BNExists F 1 3 := (equivalence.bnExists_iff 1 3).mpr hSpec
  exact (BNExists_fossil_iff G hConnected 1 3).mpr hF

end AtanasovRanganathan.GenusFourPseudocoreCoverage
