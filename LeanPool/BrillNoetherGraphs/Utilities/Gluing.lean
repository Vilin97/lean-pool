/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeContraction
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeCut
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeDivisors
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeGraph
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeRankOne
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CanonicalWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.ChainGluing
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.DegSpecLocalization
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusFiveVertexCut
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusFourVertexCut
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusThreeCycleWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusTwoTwoPole
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.InteriorScriptTransport
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.MarkedTwistDegree
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.OneVertexCutFactors
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.OneVertexCutReaches
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.SeparatingEdgeCut
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.SeparatingEdgePath
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPole
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPoleProfile
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPoleRank
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPoleReachability
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgePresentation
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeRankFormula

/-! Supporting modules for Brill–Noether theory and gonality of finite graphs. -/
