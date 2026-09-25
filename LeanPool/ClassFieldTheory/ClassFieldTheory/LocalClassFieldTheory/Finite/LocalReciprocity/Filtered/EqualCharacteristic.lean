/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristicDominatingExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristicStandardCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedFixedFieldComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
/-!
# Filtered local reciprocity in equal characteristic

Every finite abelian extension of a positive-characteristic local field
embeds in a standard finite abelian compositum.  Passing to the field range
inside the fixed separable closure lets filtered reciprocity descend by
restriction.  A base-linear equivalence from the original extension to that
field range then transports both the Artin and upper filtrations back.
-/

@[expose] public section

noncomputable
section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory

/-- Real filtered local reciprocity for an arbitrary finite abelian
extension of a positive-characteristic nonarchimedean local field. -/
theorem equalCharacteristic_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
  obtain ⟨ϖ, d, n, hϖ, hd, _hn, hEmbed⟩ :=
    exists_equalCharacteristicFiniteAbelianDominatingStandardCompositum
      K L p
  let P :=
    equalCharacteristicStandardFiniteAbelianCompositum
      K p ϖ hϖ d n hd
  let F :=
    abstractFixedField K (SeparableClosure K) P.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field
        (finiteAbelianSubextension_finite_over_absoluteBase K P)
  let : IsAbelianGalois K F :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  let i : L →ₐ[K] F := hEmbed.some
  let j : L →ₐ[K] SeparableClosure K := F.val.comp i
  let E : IntermediateField K (SeparableClosure K) :=
    AlgHom.fieldRange j
  have hEF : E ≤ F := by
    rintro x ⟨y, rfl⟩
    exact (i y).property
  let e : L ≃ₐ[K] E :=
    AlgEquiv.ofInjectiveField j
  let : FiniteDimensional K E :=
    e.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hEF)
  have hcover :
      ∀ s : ℝ, 0 ≤ s →
        artinPrincipalUnitStepGroup K F s =
          localUpperRamificationGroup K F s := by
    intro s hs
    exact
      equalCharacteristicStandardFiniteAbelianCompositum_filteredLocalReciprocity
        K p ϖ hϖ d n hd s hs
  have hupper :
      ∀ s : ℝ,
        Subgroup.map
            (RamificationTheory.intermediateFieldRestrictNormalHom E F hEF)
            (localUpperRamificationGroup K F s) =
          localUpperRamificationGroup K E s := by
    intro s
    exact localUpperRamificationGroup_map_restrict K E F hEF s
  have hEfiltered :
      artinPrincipalUnitStepGroup K E t =
        localUpperRamificationGroup K E t :=
    filteredLocalReciprocity_descends
      K E F hEF
      (localUpperRamificationGroup K E)
      (localUpperRamificationGroup K F)
      hupper hcover t ht
  let q : Gal(E/K) ≃* Gal(L/K) :=
    AlgEquiv.autCongr e.symm
  have hArtin :
      Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) =
        artinPrincipalUnitStepGroup K L t :=
    artinPrincipalUnitStepGroup_map_autCongr K E L e.symm t
  have hUpper :
      Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) =
        localUpperRamificationGroup K L t :=
    localUpperRamificationGroup_map_autCongr K E L e.symm t
  calc
    artinPrincipalUnitStepGroup K L t =
        Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) :=
      hArtin.symm
    _ =
        Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) := by
      rw [hEfiltered]
    _ = localUpperRamificationGroup K L t := hUpper

end LocalClassFieldTheory
