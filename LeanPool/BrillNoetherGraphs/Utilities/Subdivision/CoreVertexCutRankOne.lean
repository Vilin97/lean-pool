/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusThreeCycleWedge
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutTwoRegular

/-!
# Rank one across a checked genus-three/genus-one core cut

A two-regular genus-one side of a valid core articulation is a pointed rigid
cycle after every positive subdivision.  The public genus-three rigid-wedge
theorem then supplies a degree-three rank-one divisor on the ambient graph.
-/

namespace Utilities.Certificate.CoreVertexCut.Data

open Utilities

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
  (cutData : CoreVertexCut.Data spec.core)

/-- A genus-three named side and rigid complementary genus-one side give a
degree-three pencil on every positive subdivision. -/
theorem bnExists_one_three_of_left_three_right_rigid
    (hLeftGenus : cutData.leftGenus = 3)
    (hRightRigid : cutData.RightRigidConditions) :
    BNExists spec.graph 1 3 := by
  let cut := cutData.toOneVertexCut spec hRightRigid.1
  have hConnected : graph_connected spec.graph :=
    spec.graph_connected_of_coreConnected hRightRigid.2.1
  have hLeftGraphGenus : genus cut.leftGraph = 3 := by
    dsimp only [cut]
    rw [cutData.leftGraph_genus spec hRightRigid.1, hLeftGenus]
  have hRigid : PointedGenusOneRigid cut.rightGraph cut.rightGlue := by
    dsimp only [cut]
    exact cutData.rightPointedGenusOneRigid spec hRightRigid
  apply (cut.BNExists_iff 1 3).mpr
  exact MarkedGraphs.BNExists_vertexWedge_rankOneDegreeThree_of_genus_three
    cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
    (cut.graph_connected_left_of_connected hConnected) hLeftGraphGenus hRigid

end Utilities.Certificate.CoreVertexCut.Data
