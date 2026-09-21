/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.InverseHerbrandFunctionHerbrandFunction
/-!
# Upper groups at Herbrand indices

The public inverse Herbrand identity identifies the upper group at `φ(s)`
with the public real lower group at `s`.
-/

namespace ClassFieldTheory

/-- The upper group at the Herbrand image of a real lower index is exactly
the corresponding real lower group of the canonical valuation ring. -/
theorem upperRamificationGroup_herbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (s : ℝ) :
    upperRamificationGroup K L
      (herbrandFunction K (ValuativeRel.valuation L).valuationSubring s) =
    realLowerRamificationGroup K
      (ValuativeRel.valuation L).valuationSubring s := by
  unfold upperRamificationGroup
  rw [inverseHerbrandFunction_herbrandFunction K L s]

end ClassFieldTheory
