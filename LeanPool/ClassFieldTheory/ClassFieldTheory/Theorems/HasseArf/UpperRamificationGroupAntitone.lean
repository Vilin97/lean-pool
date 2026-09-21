/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionCanonical
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionInverseHerbrandFunction
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupCanonical
/-! # Antitonicity of the canonical upper filtration -/

namespace ClassFieldTheory

/-- The public canonical upper ramification filtration decreases with its
real upper index. -/
theorem upperRamificationGroup_antitone
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Antitone (upperRamificationGroup K L) := by
  intro s t hst
  have hpsi : inverseHerbrandFunction K L s ≤ inverseHerbrandFunction K L t := by
    apply (herbrandFunction_canonical_strictMono K L).le_iff_le.mp
    rw [herbrandFunction_inverseHerbrandFunction K L s,
      herbrandFunction_inverseHerbrandFunction K L t]
    exact hst
  exact (realLowerRamificationGroup_canonical_antitone K L) hpsi

end ClassFieldTheory
