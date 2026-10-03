/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.IsUpperRamificationJump
public import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.NumberTheory.LocalField.Basic
/-!
# Integrality of upper ramification jumps

The public upper filtration is transported to the existing local upper
filtration in the implementation layer, including its right limit.
-/

@[expose] public section

namespace ClassFieldTheory

/-- Every actual upper ramification jump of a finite Abelian local extension
is an integer, including the possible endpoint `-1`. -/
theorem isUpperRamificationJump_int
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {t : ℝ} (ht : IsUpperRamificationJump K L t) :
    ∃ z : ℤ, t = (z : ℝ) := by
  have hsource : RamificationTheory.LocalField.IsLocalUpperRamificationJump K L t := by
    intro heq
    apply ht
    apply (Subgroup.map_injective
      (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K).subtype_injective)
    calc
      (upperRamificationGroup K L t).map
          (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K).subtype =
          RamificationTheory.LocalField.localUpperRamificationGroup K L t :=
        HasseArf.upperRamificationGroup_map_subtype_eq_localUpperRamificationGroup
          K L t
      _ = RamificationTheory.LocalField.localUpperRamificationGroupAfter K L t := heq
      _ = (upperRamificationGroupAfter K L t).map
          (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K).subtype :=
        (HasseArf.upperRamificationGroupAfter_map_subtype_eq_localUpperRamificationGroupAfter
          K L t).symm
  exact HasseArf.isLocalUpperRamificationJump_int K L hsource

end ClassFieldTheory
