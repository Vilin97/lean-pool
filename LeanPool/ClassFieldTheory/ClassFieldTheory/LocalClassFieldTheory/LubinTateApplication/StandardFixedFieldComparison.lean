/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardFilteredArtinComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardLubinTate
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
/-!
# Filtered reciprocity on the named standard Lubin--Tate fixed field

The canonical standard Lubin--Tate level is retained by local existence as
a finite abelian subextension of the fixed separable closure.  Its canonical
algebra equivalence with the represented fixed field transports both the
Artin principal-unit filtration and the local upper filtration.
-/

@[expose] public section

noncomputable
section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField

open LocalClassFieldTheory
open LocalFieldTheory
open LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping the Artin principal-unit step group through a base-linear
equivalence gives the corresponding group on the equivalent extension. -/
theorem artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv
    (L M : Type) [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    (e : L ≃ₐ[K] M) (t : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
        (artinPrincipalUnitStepGroup K L t) =
      artinPrincipalUnitStepGroup K M t := by
  unfold artinPrincipalUnitStepGroup RamificationTheory.natCeilStepFiltration
    artinPrincipalUnitGroup
  rw [Subgroup.map_map]
  rw [abelianLocalArtinMonoidHom_autCongr K L M e]

/-- Real filtered local reciprocity for the named fixed field represented
by canonical standard Lubin--Tate level `m`. -/
theorem standardLubinTateFiniteAbelianSubextension_filteredLocalReciprocity
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let T := standardLubinTateFiniteAbelianSubextension K m
    let M :=
      abstractFixedField K (SeparableClosure K) T.field
    letI : FiniteDimensional K M :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) T.field
          (finiteAbelianSubextension_finite_over_absoluteBase K T)
    letI : IsAbelianGalois K M :=
      finiteAbelianSubextension_fixedField_isAbelianGalois K T
    artinPrincipalUnitStepGroup K M t =
      localUpperRamificationGroup K M t := by
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let E := standardLubinTateLevelField hπ m
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois
      (standardLocalField K) hπ m
  let T := standardLubinTateFiniteAbelianSubextension K m
  let M :=
    abstractFixedField K (SeparableClosure K) T.field
  let : FiniteDimensional K M :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) T.field
        (finiteAbelianSubextension_finite_over_absoluteBase K T)
  let : IsAbelianGalois K M :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K T
  let e : E ≃ₐ[K] M :=
    standardLubinTateFiniteAbelianSubextensionFixedFieldEquiv K m
  let q : Gal(E/K) ≃* Gal(M/K) :=
    AlgEquiv.autCongr e
  have hArtin :
      Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) =
        artinPrincipalUnitStepGroup K M t :=
    artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv
      K E M e t
  have hUpper :
      Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) =
        localUpperRamificationGroup K M t :=
    localUpperRamificationGroup_map_autCongr K E M e t
  have hStandard :
      artinPrincipalUnitStepGroup K E t =
        localUpperRamificationGroup K E t :=
    standardLubinTateCanonicalArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup
      K m t ht
  calc
    artinPrincipalUnitStepGroup K M t =
        Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) :=
      hArtin.symm
    _ =
        Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) := by
      rw [hStandard]
    _ = localUpperRamificationGroup K M t := hUpper

end LocalClassFieldTheory

end
