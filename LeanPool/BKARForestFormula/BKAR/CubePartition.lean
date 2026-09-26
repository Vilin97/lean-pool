/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
public import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed
public import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral
public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector
public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite

/-! # Cube partition layer (facade)

Re-exports the conversion from the recursion's nested ordered-simplex
integrals to genuine set integrals over the unit cube `[0,1]^{E(F)}`: the
ordered sectors and their almost-everywhere disjoint partition of the cube,
the simplex-sector conversion, and the regrouping of contributions by
support.
-/


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
