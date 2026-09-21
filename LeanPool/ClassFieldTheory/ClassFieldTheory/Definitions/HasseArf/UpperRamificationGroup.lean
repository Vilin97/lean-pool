/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
/-!
# Real-index upper ramification groups

The upper group at `t` is the public real lower group at the inverse
Herbrand index `ψ(t)`.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The upper ramification group of the canonical valuation ring of a
finite Abelian local extension, using the inverse public Herbrand function. -/
def upperRamificationGroup
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    Subgroup (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) :=
  realLowerRamificationGroup K
    (ValuativeRel.valuation L).valuationSubring
    (inverseHerbrandFunction K L t)

end ClassFieldTheory
