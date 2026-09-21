/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
/-!
# Filtered reciprocity for a compositum

At a nonnegative ramification index, an unramified factor contributes
trivially to both the principal-unit Artin image and the upper ramification
group.  Equality on the other factor can then be recovered upstairs from the
joint injectivity of the two restriction maps.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open RamificationTheory

open LocalClassFieldTheory
open LocalFieldTheory
open scoped ValuativeRel

/-- Filtered local reciprocity ascends from one factor of a compositum when
both filtrations restrict trivially to the other factor. -/
theorem filteredLocalReciprocity_of_compositum
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E₁ E₂ F : IntermediateField K (SeparableClosure K))
    (hE₁ : E₁ ≤ F) (hE₂ : E₂ ≤ F)
    [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    [FiniteDimensional K F]
    [IsAbelianGalois K E₁] [IsAbelianGalois K E₂]
    [IsAbelianGalois K F]
    (hsup : E₁ ⊔ E₂ = F)
    (t : ℝ)
    (hArtin₁ : artinPrincipalUnitStepGroup K E₁ t = ⊥)
    (hUpper₁ : localUpperRamificationGroup K E₁ t = ⊥)
    (hfiltered₂ :
      artinPrincipalUnitStepGroup K E₂ t =
        localUpperRamificationGroup K E₂ t) :
    artinPrincipalUnitStepGroup K F t =
      localUpperRamificationGroup K F t := by
  let r₁ := intermediateFieldRestrictNormalHom E₁ F hE₁
  let r₂ := intermediateFieldRestrictNormalHom E₂ F hE₂
  apply
    subgroup_eq_of_prod_map_injective_of_left_maps_eq_bot
      r₁ r₂
      (intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq
        K E₁ E₂ F hE₁ hE₂ hsup)
  · calc
      (artinPrincipalUnitStepGroup K F t).map r₁ =
          artinPrincipalUnitStepGroup K E₁ t := by
        simpa [r₁] using
          artinPrincipalUnitStepGroup_map_intermediateFieldRestrict
            K E₁ F hE₁ t
      _ = ⊥ := hArtin₁
  · calc
      (localUpperRamificationGroup K F t).map r₁ =
          localUpperRamificationGroup K E₁ t := by
        simpa [r₁] using
          localUpperRamificationGroup_map_restrict K E₁ F hE₁ t
      _ = ⊥ := hUpper₁
  · calc
      (artinPrincipalUnitStepGroup K F t).map r₂ =
          artinPrincipalUnitStepGroup K E₂ t := by
        simpa [r₂] using
          artinPrincipalUnitStepGroup_map_intermediateFieldRestrict
            K E₂ F hE₂ t
      _ = localUpperRamificationGroup K E₂ t := hfiltered₂
      _ = (localUpperRamificationGroup K F t).map r₂ := by
        symm
        simpa [r₂] using
          localUpperRamificationGroup_map_restrict K E₂ F hE₂ t

end LocalClassFieldTheory
