/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness

/-! # Ordered assembly layer (facade)

Re-exports the assembly of the ordered recursion into the final formula:
the all-branches expansion and its telescoping, regrouping by support and
order, the fiber analysis of the boundary tree sum, canonical forests
realizing each support, sectorwise canonicalization, and the fold into one
cube contribution per forest index.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
