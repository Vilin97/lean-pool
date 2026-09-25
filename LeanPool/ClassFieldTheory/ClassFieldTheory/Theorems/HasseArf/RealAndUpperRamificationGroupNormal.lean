/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupNormal
/-!
# Normality of real lower and upper ramification groups

Upper groups are real lower groups evaluated at inverse Herbrand indices,
so their normality follows from normality of the real lower groups.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- Each canonical real upper ramification group is normal in its
decomposition group. -/
theorem upperRamificationGroup_normal
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    (upperRamificationGroup K L t).Normal :=
  realLowerRamificationGroup_normal K
    (ValuativeRel.valuation L).valuationSubring
    (inverseHerbrandFunction K L t)

end ClassFieldTheory
