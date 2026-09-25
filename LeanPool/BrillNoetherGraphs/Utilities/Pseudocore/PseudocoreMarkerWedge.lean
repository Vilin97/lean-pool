/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreMarkerCut
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.GraphIsoLaplacianEquiv
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.NestedOneVertexCut
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.PointedGenusOneRigidTransport

/-!
# Wedge packages extracted from pseudocore loop markers

A compatible split-loop marker is more than a local two-cycle: after an
arbitrary positive subdivision of the split core it canonically exhibits the
whole graph as a vertex wedge of a genus-one rigid factor and its complement.
This file packages that length-uniform statement in the orientation used by
the genus-five loop-aware normal-form interface: the complementary graph is
the left (base) factor and the marker cycle is the right factor.
-/
namespace Utilities.Certificate.PseudocoreMarkerWedge

open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore

namespace MarkerPackage

variable {n : ℕ} {core : Pseudocore n} (split : core.SplitMetadata)
variable (spec : Spec (n + core.loopCount) core.splitEdgeCount)

/-- The marker-cut data, transported across a displayed equality of cores. -/
noncomputable def data (marker : Fin core.loopCount)
    (_hCore : spec.core = split.splitCore) : CoreVertexCut.Data spec.core := by
  exact
    { glue := (PseudocoreMarkerCut.cut split marker).glue
      left := (PseudocoreMarkerCut.cut split marker).left }

theorem data_eq_cut (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore) :
    (data split spec marker hCore).glue =
      (PseudocoreMarkerCut.cut split marker).glue ∧
    (data split spec marker hCore).left =
      (PseudocoreMarkerCut.cut split marker).left := by
  exact ⟨rfl, rfl⟩

theorem data_valid (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (data split spec marker hCore).Valid := by
  unfold data
  rw [hCore]
  exact PseudocoreMarkerCut.cut_valid split marker hCompatible

theorem data_leftRigidConditions (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) :
    (data split spec marker hCore).LeftRigidConditions := by
  unfold CoreVertexCut.Data.LeftRigidConditions
  simp only [data]
  rw [hCore]
  exact PseudocoreMarkerCut.cut_leftRigidConditions split marker hCompatible hConnected

/-- A marker package uses the complementary induced graph as base and the
canonical marker cycle as rigid factor. -/
noncomputable def cut (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    OneVertexCut spec.graph :=
  (data split spec marker hCore).toOneVertexCut spec
    (data_valid split spec marker hCore hCompatible)

noncomputable def base (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) : CFGraph :=
  (cut split spec marker hCore hCompatible).rightGraph

noncomputable def factor (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) : CFGraph :=
  (cut split spec marker hCore hCompatible).leftGraph

noncomputable def attachment (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (base split spec marker hCore hCompatible).V :=
  (cut split spec marker hCore hCompatible).rightGlue

noncomputable def root (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (factor split spec marker hCore hCompatible).V :=
  (cut split spec marker hCore hCompatible).leftGlue

/-- The wedge isomorphism in base-first orientation. -/
noncomputable def wedgeIso (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    CFGraphIso
      (vertexWedge (base split spec marker hCore hCompatible)
        (factor split spec marker hCore hCompatible)
        (attachment split spec marker hCore hCompatible)
        (root split spec marker hCore hCompatible)) spec.graph :=
  (cut split spec marker hCore hCompatible).swap.graphIso

theorem factor_rigid (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) :
    PointedGenusOneRigid (factor split spec marker hCore hCompatible)
      (root split spec marker hCore hCompatible) := by
  exact (data split spec marker hCore).leftPointedGenusOneRigid spec
    (data_leftRigidConditions split spec marker hCore hCompatible hConnected)

theorem base_connected (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) :
    graphConnected (base split spec marker hCore hCompatible) := by
  exact (cut split spec marker hCore hCompatible).graph_connected_right_of_connected
    (spec.graph_connected_of_coreConnected (by
      rw [hCore]
      exact hConnected))

theorem base_genus (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    genus (base split spec marker hCore hCompatible) = genus spec.graph - 1 := by
  let c := data split spec marker hCore
  have hValid := data_valid split spec marker hCore hCompatible
  have hLeft : genus (c.toOneVertexCut spec hValid).leftGraph = 1 := by
    rw [c.leftGraph_genus spec hValid]
    unfold c data
    rw [hCore]
    exact PseudocoreMarkerCut.cut_leftGenus split marker hCompatible
  have hSum := (c.toOneVertexCut spec hValid).genus_eq
  change genus (c.toOneVertexCut spec hValid).rightGraph = genus spec.graph - 1
  omega

/-- Compose a presentation of `G` by the split subdivision with the
base-first marker wedge isomorphism. -/
noncomputable def wedgeEquiv {G : CFGraph} (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (presentation : LaplacianEquiv G spec.graph) :
    LaplacianEquiv G
      (vertexWedge (base split spec marker hCore hCompatible)
        (factor split spec marker hCore hCompatible)
        (attachment split spec marker hCore hCompatible)
        (root split spec marker hCore hCompatible)) :=
  presentation.trans (wedgeIso split spec marker hCore hCompatible).toLaplacianEquiv.symm

/-- A target vertex on the complementary side is transported to the base
summand of the base-first wedge. -/
theorem wedgeEquiv_apply_base {G : CFGraph} (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (presentation : LaplacianEquiv G spec.graph) (z : G.V)
    (hz : presentation z ∈ (cut split spec marker hCore hCompatible).right) :
    wedgeEquiv split spec marker hCore hCompatible presentation z =
      Sum.inl (⟨presentation z, hz⟩ :
        (base split spec marker hCore hCompatible).V) := by
  change (cut split spec marker hCore hCompatible).swap.graphIso.vertexEquiv.symm
    (presentation z) = _
  apply (cut split spec marker hCore hCompatible).swap.graphIso.vertexEquiv.injective
  rw [Equiv.apply_symm_apply]
  change presentation z =
    (cut split spec marker hCore hCompatible).swap.presentation.leftMap
      ⟨presentation z, hz⟩
  rfl

-- As of the v4.33 toolchain, `backward.isDefEq.respectTransparency` defaults
-- to `true`, so `rw`'s motive check only unfolds at `implicit` transparency,
-- not `default`.  That is not enough to see that `hz`'s membership in
-- `(cut ...).left` is the same as membership in `(cut ...).swap.right` (`swap`
-- is a semireducible `def ... where`), so the `rw` below stalls on that
-- subtype-coercion mismatch.
/-- A target vertex on the marker side is transported to the corresponding
vertex of the rigid factor in the base-first wedge. -/
theorem wedgeEquiv_apply_factor {G : CFGraph} (marker : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (presentation : LaplacianEquiv G spec.graph) (z : G.V)
    (hz : presentation z ∈ (cut split spec marker hCore hCompatible).left) :
    wedgeEquiv split spec marker hCore hCompatible presentation z =
      wedgeRightVertex
        (base split spec marker hCore hCompatible)
        (factor split spec marker hCore hCompatible)
        (attachment split spec marker hCore hCompatible)
        (root split spec marker hCore hCompatible)
        (⟨presentation z, hz⟩ :
          (factor split spec marker hCore hCompatible).V) := by
  change (cut split spec marker hCore hCompatible).swap.graphIso.vertexEquiv.symm
    (presentation z) = _
  apply (cut split spec marker hCore hCompatible).swap.graphIso.vertexEquiv.injective
  rw [Equiv.apply_symm_apply]
  change presentation z =
    (cut split spec marker hCore hCompatible).swap.presentation.graphIso.vertexEquiv
      (wedgeRightVertex
        (cut split spec marker hCore hCompatible).swap.leftGraph
        (cut split spec marker hCore hCompatible).swap.rightGraph
        (cut split spec marker hCore hCompatible).swap.leftGlue
        (cut split spec marker hCore hCompatible).swap.rightGlue
        ⟨presentation z, hz⟩)
  rw [VertexWedgePresentation.graphIso_apply_wedgeRightVertex
    (cut split spec marker hCore hCompatible).swap.presentation ⟨presentation z, hz⟩]
  rfl

/-- The second of two distinct marker cuts restricts to the complementary
factor of the first, uniformly in all positive subdivision lengths. -/
theorem cut_left_subset_right_of_ne (first second : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hNe : second ≠ first) :
    (cut split spec second hCore hCompatible).left ⊆
      (cut split spec first hCore hCompatible).right := by
  have hCoreSubset :
      (data split spec second hCore).left ⊆
        (data split spec first hCore).right := by
    exact PseudocoreMarkerCut.cut_left_subset_right_of_ne split first second hNe
  exact CoreVertexCut.Data.leftVertices_subset_rightVertices_of_left_subset_right
    spec (data split spec first hCore) (data split spec second hCore) hCoreSubset

/-- After restricting a second distinct marker cut through the first, its
left factor is still the same pointed rigid genus-one cycle. -/
theorem restricted_second_factor_rigid
    (first second : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) (hNe : second ≠ first) :
    let hSubset := cut_left_subset_right_of_ne split spec first second
      hCore hCompatible hNe
    let restricted := (cut split spec first hCore hCompatible).restrictRight
      (cut split spec second hCore hCompatible) hSubset
    PointedGenusOneRigid restricted.leftGraph restricted.leftGlue := by
  dsimp only
  let firstCut := cut split spec first hCore hCompatible
  let secondCut := cut split spec second hCore hCompatible
  let hSubset := cut_left_subset_right_of_ne split spec first second
    hCore hCompatible hNe
  let restricted := firstCut.restrictRight secondCut hSubset
  let flatten := firstCut.restrictRightLeftIso secondCut hSubset
  have hOriginal : PointedGenusOneRigid secondCut.leftGraph secondCut.leftGlue :=
    factor_rigid split spec second hCore hCompatible hConnected
  have hTransported := hOriginal.map flatten.symm
  have hRoot : flatten.symm.vertexEquiv secondCut.leftGlue = restricted.leftGlue := by
    change flatten.vertexEquiv.symm secondCut.leftGlue = restricted.leftGlue
    apply flatten.vertexEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact firstCut.restrictRightLeftIso_apply_leftGlue secondCut hSubset
  rw [hRoot] at hTransported
  exact hTransported

/-- The residual base after two distinct marker cuts is connected. -/
theorem restricted_base_connected
    (first second : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) (hNe : second ≠ first) :
    let hSubset := cut_left_subset_right_of_ne split spec first second
      hCore hCompatible hNe
    let restricted := (cut split spec first hCore hCompatible).restrictRight
      (cut split spec second hCore hCompatible) hSubset
    graphConnected restricted.rightGraph := by
  dsimp only
  exact ((cut split spec first hCore hCompatible).restrictRight_graph_connected_factors
    (cut split spec second hCore hCompatible)
    (cut_left_subset_right_of_ne split spec first second hCore hCompatible hNe)
    (spec.graph_connected_of_coreConnected (hCore ▸ hConnected))).2

/-- In a genus-five presentation, removing two distinct marker cycles leaves
a genus-three residual base. -/
theorem restricted_base_genus_three
    (first second : Fin core.loopCount)
    (hCore : spec.core = split.splitCore)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) (hNe : second ≠ first)
    (hGenus : genus spec.graph = 5) :
    let hSubset := cut_left_subset_right_of_ne split spec first second
      hCore hCompatible hNe
    let restricted := (cut split spec first hCore hCompatible).restrictRight
      (cut split spec second hCore hCompatible) hSubset
    genus restricted.rightGraph = 3 := by
  dsimp only
  let firstCut := cut split spec first hCore hCompatible
  let secondCut := cut split spec second hCore hCompatible
  let hSubset := cut_left_subset_right_of_ne split spec first second
    hCore hCompatible hNe
  let restricted := firstCut.restrictRight secondCut hSubset
  have hFirstGenus : genus firstCut.leftGraph = 1 :=
    (factor_rigid split spec first hCore hCompatible hConnected).genus_one
  have hSecondGenus : genus restricted.leftGraph = 1 :=
    (restricted_second_factor_rigid split spec first second hCore hCompatible
      hConnected hNe).genus_one
  have hSum := firstCut.genus_eq_nested_restrictRight secondCut hSubset
  change genus spec.graph = genus firstCut.leftGraph + genus restricted.leftGraph +
    genus restricted.rightGraph at hSum
  rw [hGenus, hFirstGenus, hSecondGenus] at hSum
  have hResult : genus restricted.rightGraph = 3 := by omega
  exact hResult

end MarkerPackage

end Utilities.Certificate.PseudocoreMarkerWedge
