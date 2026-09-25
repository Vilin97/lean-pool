/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
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
public import LeanPool.BKARForestFormula.BKAR.OrderedTerminalGrowth
public import LeanPool.BKARForestFormula.BKAR.OrderedParams
public import LeanPool.BKARForestFormula.BKAR.OrderedRecursion
public import LeanPool.BKARForestFormula.BKAR.OrderedRemainder
public import LeanPool.BKARForestFormula.BKAR.OrderedSimplex
public import LeanPool.BKARForestFormula.BKAR.OrderedTerminal
public import LeanPool.BKARForestFormula.BKAR.PartialDeriv
public import LeanPool.BKARForestFormula.BKAR.PartialDerivSymmetry
public import LeanPool.BKARForestFormula.BKAR.Smoothness
public import LeanPool.BKARForestFormula.BKAR.Threshold
public import LeanPool.BKARForestFormula.BKAR.ThresholdComponents
public import LeanPool.BKARForestFormula.BKAR.ThresholdLayerCake

/-! # The Brydges–Kennedy–Abdesselam–Rivasseau forest interpolation formula

Root facade: importing this module brings in the whole development.

For a finite vertex set `V` and a function `ρ : (Edge V → ℝ) → ℝ` smooth
(`C^∞`) on the edge-coupling space (`BKARContDiff`), the BKAR forest
interpolation formula states

  `ρ(1,…,1) = ∑_{forests F} ∫_{[0,1]^{E(F)}} ∂_{E(F)} ρ (x^F(u)) du`,

summing over all acyclic edge subsets of the complete graph on `V` (the
empty forest contributing `ρ(0,…,0)`), where `∂_{E(F)}` is the mixed
partial derivative in the edge variables of `F` and `x^F(u)` is the
path-minimum interpolation: the coordinate of `x^F(u)` at an edge `{i, j}`
is the minimum of `u` along the unique forest path joining `i` to `j`, and
`0` when `i` and `j` lie in different components of `F`.

The flagship formal statement is
`BKAR.bkar_formula_forestIndex_cube_contributions` in `BKAR.Formula`, with
sector-form and empty-forest-split variants alongside, and a threshold /
layer-cake API for the interpolation points in the `BKAR.Threshold` files.

The formalization assumes `ρ` is `C^∞` (`BKARContDiff = ContDiff ℝ ⊤`)
where the classical statement needs only `C^{|V|-1}`; this is a deliberate
strengthening of the hypothesis.

## References

* D. Brydges, T. Kennedy, *Mayer expansions and the Hamilton–Jacobi
  equation*, J. Statist. Phys. 48 (1987) 19–49.
* A. Abdesselam, V. Rivasseau, *Trees, forests and jungles: a botanical
  garden for cluster expansions*, in Constructive Physics (Palaiseau 1994),
  Lecture Notes in Physics 446, Springer, 1995.  arXiv:hep-th/9409094.
-/


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
