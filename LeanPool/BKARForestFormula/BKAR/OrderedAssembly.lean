/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness

/-! # Ordered assembly layer (facade)

Re-exports the assembly of the ordered recursion into the final formula:
the all-branches expansion and its telescoping, regrouping by support and
order, the fiber analysis of the boundary tree sum, canonical forests
realizing each support, sectorwise canonicalization, and the fold into one
cube contribution per forest index.
-/


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
