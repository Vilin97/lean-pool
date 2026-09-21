/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
/-!
# Artin filtrations of unramified local extensions

The Artin map kills valuation-ring units in an unramified finite extension,
so every positive principal-unit image is trivial.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalClassFieldTheory
open LocalFieldTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-! ## The Artin principal-unit filtration -/

/-- Every valuation-ring unit has trivial actual abelian Artin symbol in an
unramified finite extension. -/
theorem
    abelianLocalArtinMonoidHom_integerUnits_eq_one_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝒪[K]ˣ) :
    abelianLocalArtinMonoidHom K L
        (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          K u) = 1 := by
  unfold abelianLocalArtinMonoidHom
  rw [MonoidHom.comp_apply,
    localArtinMonoidHom_eq_frobenius_zpow K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits,
    zpow_zero, map_one]

/-- Every integral Artin principal-unit group of an unramified finite
abelian extension is trivial. -/
theorem artinPrincipalUnitGroup_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : ℕ) :
    artinPrincipalUnitGroup K L n = ⊥ := by
  apply le_antisymm
  · intro σ hσ
    rcases hσ with ⟨x, hx, rfl⟩
    rcases hx with ⟨u, hu, rfl⟩
    rw [
      abelianLocalArtinMonoidHom_integerUnits_eq_one_of_unramifiedValuation
        K L u]
    exact Subgroup.one_mem ⊥
  · exact bot_le

/-- The real ceiling-step Artin filtration is therefore trivial at every
index on an unramified finite abelian extension. -/
theorem artinPrincipalUnitStepGroup_eq_bot_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (t : ℝ) :
    artinPrincipalUnitStepGroup K L t = ⊥ := by
  exact
    artinPrincipalUnitGroup_eq_bot_of_unramifiedValuation
      K L ⌈t⌉₊

end LocalClassFieldTheory
