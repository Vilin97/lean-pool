/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module


public import LeanPool.BKARForestFormula.Audit
public import LeanPool.BKARForestFormula.Audit.ForestFormula
public import LeanPool.BKARForestFormula.Audit.ForestFormula.Solution
public import LeanPool.BKARForestFormula.Audit.ForestFormula.SolutionBasic
public import LeanPool.BKARForestFormula.BKAR
public import LeanPool.BKARForestFormula.BKAR.CubePartition
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Branches
public import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral
public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Equiv
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Pair
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Singleton
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Smoothness
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Contribution
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Growth
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Terminal
public import LeanPool.BKARForestFormula.BKAR.Differential
public import LeanPool.BKARForestFormula.BKAR.Forest
public import LeanPool.BKARForestFormula.BKAR.ForestGraph
public import LeanPool.BKARForestFormula.BKAR.Formula
public import LeanPool.BKARForestFormula.BKAR.Interpolation
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.Core
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.FollowOrder
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.LowRank
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion
public import LeanPool.BKARForestFormula.BKAR.OrderedBranch
public import LeanPool.BKARForestFormula.BKAR.OrderedExpansion
public import LeanPool.BKARForestFormula.BKAR.OrderedForest
public import LeanPool.BKARForestFormula.BKAR.OrderedParams
public import LeanPool.BKARForestFormula.BKAR.OrderedRecursion
public import LeanPool.BKARForestFormula.BKAR.OrderedRemainder
public import LeanPool.BKARForestFormula.BKAR.OrderedSimplex
public import LeanPool.BKARForestFormula.BKAR.OrderedTerminal
public import LeanPool.BKARForestFormula.BKAR.OrderedTerminalGrowth
public import LeanPool.BKARForestFormula.BKAR.PartialDeriv
public import LeanPool.BKARForestFormula.BKAR.PartialDerivSymmetry
public import LeanPool.BKARForestFormula.BKAR.Smoothness
public import LeanPool.BKARForestFormula.BKAR.Threshold
public import LeanPool.BKARForestFormula.BKAR.ThresholdComponents
public import LeanPool.BKARForestFormula.BKAR.ThresholdLayerCake

/-!
# The BKAR forest interpolation formula

Source: url:https://github.com/scottnarmstrong/bkarforestformula
Authors: Scott Armstrong
Status: verified
Main declarations: `BKAR.bkar_formula_forestIndex_cube_contributions`
Tags: analysis, graph-theory, mathematical-physics
MSC: 81T08, 05C05
-/
