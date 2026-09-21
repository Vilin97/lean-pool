/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

import LeanPool.BKARForestFormula.Audit.ForestFormula.Solution
import LeanPool.BKARForestFormula.Audit.ForestFormula.SolutionBasic
import LeanPool.BKARForestFormula.Audit.ForestFormula
import LeanPool.BKARForestFormula.Audit
import LeanPool.BKARForestFormula.BKAR.CubePartition.Branches
import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders
import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Equiv
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Pair
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Singleton
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector
import LeanPool.BKARForestFormula.BKAR.CubePartition.Smoothness
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Contribution
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Growth
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Terminal
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
import LeanPool.BKARForestFormula.BKAR.CubePartition
import LeanPool.BKARForestFormula.BKAR.Differential
import LeanPool.BKARForestFormula.BKAR.Forest
import LeanPool.BKARForestFormula.BKAR.ForestGraph
import LeanPool.BKARForestFormula.BKAR.Formula
import LeanPool.BKARForestFormula.BKAR.Interpolation
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.Core
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.FollowOrder
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.LowRank
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly
import LeanPool.BKARForestFormula.BKAR.OrderedBranch
import LeanPool.BKARForestFormula.BKAR.OrderedExpansion
import LeanPool.BKARForestFormula.BKAR.OrderedForest
import LeanPool.BKARForestFormula.BKAR.OrderedParams
import LeanPool.BKARForestFormula.BKAR.OrderedRecursion
import LeanPool.BKARForestFormula.BKAR.OrderedRemainder
import LeanPool.BKARForestFormula.BKAR.OrderedSimplex
import LeanPool.BKARForestFormula.BKAR.OrderedTerminal
import LeanPool.BKARForestFormula.BKAR.OrderedTerminalGrowth
import LeanPool.BKARForestFormula.BKAR.PartialDeriv
import LeanPool.BKARForestFormula.BKAR.PartialDerivSymmetry
import LeanPool.BKARForestFormula.BKAR.Smoothness
import LeanPool.BKARForestFormula.BKAR.Threshold
import LeanPool.BKARForestFormula.BKAR.ThresholdComponents
import LeanPool.BKARForestFormula.BKAR.ThresholdLayerCake
import LeanPool.BKARForestFormula.BKAR

/-!
# The BKAR forest interpolation formula

Source: url:https://github.com/scottnarmstrong/bkarforestformula
Authors: Scott Armstrong
Status: verified
Main declarations: `BKAR.bkar_formula_forestIndex_cube_contributions`
Tags: analysis, graph-theory, mathematical-physics
MSC: 81T08, 05C05
-/
