/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed
import LeanPool.BKARForestFormula.BKAR.CubePartition.CubeIntegral
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasurePartition
import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite

/-! # Cube partition layer (facade)

Re-exports the conversion from the recursion's nested ordered-simplex
integrals to genuine set integrals over the unit cube `[0,1]^{E(F)}`: the
ordered sectors and their almost-everywhere disjoint partition of the cube,
the simplex-sector conversion, and the regrouping of contributions by
support.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
