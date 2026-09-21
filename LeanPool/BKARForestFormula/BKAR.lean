/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition
import LeanPool.BKARForestFormula.BKAR.CubePartition.Branches
import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders
import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Equiv
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Pair
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Singleton
import LeanPool.BKARForestFormula.BKAR.CubePartition.Smoothness
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Contribution
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Growth
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Terminal
import LeanPool.BKARForestFormula.BKAR.Differential
import LeanPool.BKARForestFormula.BKAR.Forest
import LeanPool.BKARForestFormula.BKAR.ForestGraph
import LeanPool.BKARForestFormula.BKAR.Formula
import LeanPool.BKARForestFormula.BKAR.Interpolation
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.Core
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.FollowOrder
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.LowRank
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion
import LeanPool.BKARForestFormula.BKAR.OrderedBranch
import LeanPool.BKARForestFormula.BKAR.OrderedExpansion
import LeanPool.BKARForestFormula.BKAR.OrderedForest
import LeanPool.BKARForestFormula.BKAR.OrderedTerminalGrowth
import LeanPool.BKARForestFormula.BKAR.OrderedParams
import LeanPool.BKARForestFormula.BKAR.OrderedRecursion
import LeanPool.BKARForestFormula.BKAR.OrderedRemainder
import LeanPool.BKARForestFormula.BKAR.OrderedSimplex
import LeanPool.BKARForestFormula.BKAR.OrderedTerminal
import LeanPool.BKARForestFormula.BKAR.PartialDeriv
import LeanPool.BKARForestFormula.BKAR.PartialDerivSymmetry
import LeanPool.BKARForestFormula.BKAR.Smoothness
import LeanPool.BKARForestFormula.BKAR.Threshold
import LeanPool.BKARForestFormula.BKAR.ThresholdComponents
import LeanPool.BKARForestFormula.BKAR.ThresholdLayerCake

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
