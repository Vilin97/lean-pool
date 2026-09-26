/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
/-!
# Upper ramification jumps

The right-limit group is the supremum of upper groups at strictly larger
indices. A jump occurs exactly when that right limit differs from the group
at the index itself.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- The upper ramification group immediately after a real index. -/
def upperRamificationGroupAfter
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    Subgroup (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) :=
  ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K L s

/-- A real upper index is a jump when the upper filtration changes
immediately to its right. -/
def IsUpperRamificationJump
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) : Prop :=
  upperRamificationGroup K L t ≠ upperRamificationGroupAfter K L t

end ClassFieldTheory
