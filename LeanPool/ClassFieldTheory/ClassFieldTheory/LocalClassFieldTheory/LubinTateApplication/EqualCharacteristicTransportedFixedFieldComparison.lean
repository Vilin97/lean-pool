/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedRealFilteredComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Core
/-!
# Filtered reciprocity on the named transported Lubin--Tate fixed field

The transported Lubin--Tate level used by equal-characteristic existence is
represented inside the fixed separable closure by a named finite abelian
subextension.  The canonical algebra equivalence to that fixed field
transports both the local Artin filtration and the upper ramification
filtration, so real filtered reciprocity holds on the named factor.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping the Artin principal-unit step group along a base-linear
equivalence gives the corresponding group on the equivalent extension. -/
theorem artinPrincipalUnitStepGroup_map_autCongr
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

/-- Real filtered local reciprocity for the named fixed field representing
a transported equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateFixedField_filteredLocalReciprocity
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ m
    let T :=
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ m
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
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  let M :=
    abstractFixedField K (SeparableClosure K) T.field
  let : FiniteDimensional K M :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) T.field
        (finiteAbelianSubextension_finite_over_absoluteBase K T)
  let : IsAbelianGalois K M :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K T
  let e : E ≃ₐ[K] M :=
    equalCharacteristicTransportedLubinTateFixedFieldEquiv
      K p ϖ hϖ m
  let q : Gal(E/K) ≃* Gal(M/K) :=
    AlgEquiv.autCongr e
  have hArtin :
      Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) =
        artinPrincipalUnitStepGroup K M t :=
    artinPrincipalUnitStepGroup_map_autCongr K E M e t
  have hUpper :
      Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) =
        localUpperRamificationGroup K M t :=
    localUpperRamificationGroup_map_autCongr K E M e t
  have hExplicit :
      artinPrincipalUnitStepGroup K E t =
        localUpperRamificationGroup K E t :=
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup
      K p ϖ hϖ m t ht
  calc
    artinPrincipalUnitStepGroup K M t =
        Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) :=
      hArtin.symm
    _ =
        Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) := by
      rw [hExplicit]
    _ = localUpperRamificationGroup K M t := hUpper

end LocalClassFieldTheory
