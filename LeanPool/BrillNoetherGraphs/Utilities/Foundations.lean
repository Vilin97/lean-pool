/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.AcyclicOrientation
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.BlockSlopeRounding
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.BrillNoetherRank
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CanonicalSlackPair
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CommonOffsetRounding
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ConvexIntegerRounding
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Duality
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.EdgeAddition
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.EffectiveDifference
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.InducedSubgraph
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Orientability
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.OrientationReversal
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankDeterminingSet
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ScriptClamping
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.TopologicalVertices
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.UnderlyingSimpleGraph

/-! Supporting modules for Brill–Noether theory and gonality of finite graphs. -/
