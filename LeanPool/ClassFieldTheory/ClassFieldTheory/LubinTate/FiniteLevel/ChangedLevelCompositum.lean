/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
/-!
# A common valued field for original and changed Lubin--Tate levels

The standard level for a uniformizer `π` and the standard level for a unit
change `uπ` both live in the fixed separable closure of the base field.  Their
compositum therefore gives a literal common overfield.  This file chooses the
complete discrete valuation supplied by the integral closure of the base
valuation ring in that compositum.

Uniqueness of valuation extension from the complete base shows that the
chosen compositum valuation extends the already chosen valuation on each
level.  The two inclusions consequently preserve valuation-ring and
maximal-ideal membership.  Their normalized additive valuations scale by the
corresponding ramification index; no equality between the two levels and no
higher-unit hypothesis is used.
-/

@[expose] public section

noncomputable
section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- The compositum of the standard `π`-level and the standard `uπ`-level
inside the fixed separable closure. -/
abbrev standardLubinTateChangedLevelCompositumField
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  standardLubinTateLevelField hπ n ⊔
    standardLubinTateChangedLevelField hπ u n

/-- The original and changed finite levels have a finite-dimensional
compositum over the base field. -/
theorem standardLubinTateChangedLevelCompositumField_finiteDimensional
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    FiniteDimensional K
      (standardLubinTateChangedLevelCompositumField hπ u n) := by
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : FiniteDimensional K L' :=
    standardLubinTateLevelField_finiteDimensional hπ' n
  exact L.finiteDimensional_sup L'

/-- The compositum is separable over the base field. -/
theorem standardLubinTateChangedLevelCompositumField_isSeparable
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Algebra.IsSeparable K
      (standardLubinTateChangedLevelCompositumField hπ u n) := by
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : FiniteDimensional K L' :=
    standardLubinTateLevelField_finiteDimensional hπ' n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  let : IsGalois K L' :=
    standardLubinTateLevelField_isGalois (F := F) hπ' n
  infer_instance

/-- The compositum is Galois over the base field. -/
theorem standardLubinTateChangedLevelCompositumField_isGalois
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    IsGalois K
      (standardLubinTateChangedLevelCompositumField hπ u n) := by
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  let : IsGalois K L' :=
    standardLubinTateLevelField_isGalois (F := F) hπ' n
  let : Algebra.IsSeparable K M :=
    standardLubinTateChangedLevelCompositumField_isSeparable hπ u n
  exact
    { to_isSeparable := inferInstance
      to_normal := inferInstance }

private theorem
    standardLubinTateChangedLevelCompositumCompleteDVFData_exists
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    ∃ target : CompleteDVF.{u, 0}
        (standardLubinTateChangedLevelCompositumField hπ u n),
      ∃ hExt :
          F.toCompleteDVF.valuation.HasExtension target.valuation,
        letI :
            F.toCompleteDVF.valuation.HasExtension target.valuation :=
          hExt
        IsIntegralClosure target.valuationSubring F.valuationSubring
            (standardLubinTateChangedLevelCompositumField hπ u n) ∧
          degree F.toCompleteDVF.toDVF target.toDVF =
            ramificationIndex F.toCompleteDVF.toDVF target.toDVF *
              residueDegree F.toCompleteDVF.toDVF target.toDVF := by
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let : FiniteDimensional K M :=
    standardLubinTateChangedLevelCompositumField_finiteDimensional
      hπ u n
  let : Algebra.IsSeparable K M :=
    standardLubinTateChangedLevelCompositumField_isSeparable hπ u n
  exact
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := M) F.toCompleteDVF

/-- The complete discrete valuation on the common compositum selected from
the integral closure of the base valuation ring. -/
noncomputable def standardLubinTateChangedLevelCompositumCompleteDVF
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    CompleteDVF.{u, 0}
      (standardLubinTateChangedLevelCompositumField hπ u n) :=
  Classical.choose
    (standardLubinTateChangedLevelCompositumCompleteDVFData_exists
      hπ u n)

/-- The compositum valuation extends the base valuation. -/
theorem
    standardLubinTateChangedLevelCompositumCompleteDVF_hasExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    F.toCompleteDVF.valuation.HasExtension
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation :=
  Classical.choose
    (Classical.choose_spec
      (standardLubinTateChangedLevelCompositumCompleteDVFData_exists
        hπ u n))

noncomputable instance
    standardLubinTateChangedLevelCompositumCompleteDVF_hasExtensionInstance
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    F.toCompleteDVF.valuation.HasExtension
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation :=
  standardLubinTateChangedLevelCompositumCompleteDVF_hasExtension
    hπ u n

/-- The chosen compositum valuation ring is the integral closure of the base
valuation ring. -/
theorem
    standardLubinTateChangedLevelCompositumCompleteDVF_isIntegralClosure
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    IsIntegralClosure
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring
      F.valuationSubring
      (standardLubinTateChangedLevelCompositumField hπ u n) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (standardLubinTateChangedLevelCompositumCompleteDVFData_exists
        hπ u n))).1

/-- The chosen compositum valuation satisfies the finite-extension
fundamental identity. -/
theorem
    standardLubinTateChangedLevelCompositumCompleteDVF_fundamentalIdentity
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    let target :=
      standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
    degree F.toCompleteDVF.toDVF target.toDVF =
      ramificationIndex F.toCompleteDVF.toDVF target.toDVF *
        residueDegree F.toCompleteDVF.toDVF target.toDVF :=
  (Classical.choose_spec
    (Classical.choose_spec
      (standardLubinTateChangedLevelCompositumCompleteDVFData_exists
        hπ u n))).2

/-- Completeness of the base makes the chosen compositum valuation the unique
extension of the base valuation. -/
theorem
    standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueValuationExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension.{u, v, u,
      0, 0}
      (base := F.toCompleteDVF)
      (target :=
        standardLubinTateChangedLevelCompositumCompleteDVF hπ u n) := by
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let : FiniteDimensional K M :=
    standardLubinTateChangedLevelCompositumField_finiteDimensional
      hπ u n
  let : Algebra.IsSeparable K M :=
    standardLubinTateChangedLevelCompositumField_isSeparable hπ u n
  intro Gamma' _ v'
  exact
    (hasUniqueValuationExtension_of_finite_separable.{u, v, u, 0, 0}
      F.toCompleteDVF
      (standardLubinTateChangedLevelCompositumCompleteDVF hπ u n)) v'

/-- The same uniqueness statement after forgetting completeness. -/
theorem
    standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueDVFValuationExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, u, 0, 0}
      F.toCompleteDVF.toDVF
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).toDVF :=
  standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueValuationExtension
    hπ u n

/-- The literal inclusion of the original level into the common
compositum. -/
noncomputable def standardLubinTateLevelToChangedLevelCompositum
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateLevelField hπ n →ₐ[K]
      standardLubinTateChangedLevelCompositumField hπ u n :=
  IntermediateField.inclusion le_sup_left

/-- The literal inclusion of the changed level into the common
compositum. -/
noncomputable def standardLubinTateChangedLevelToCompositum
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedLevelField hπ u n →ₐ[K]
      standardLubinTateChangedLevelCompositumField hπ u n :=
  IntermediateField.inclusion le_sup_right

/-- The original-level inclusion is the ambient identity on separable-closure
elements. -/
@[simp]
theorem standardLubinTateLevelToChangedLevelCompositum_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateLevelField hπ n) :
    ((standardLubinTateLevelToChangedLevelCompositum hπ u n x :
        standardLubinTateChangedLevelCompositumField hπ u n) :
      SeparableClosure K) =
        (x : SeparableClosure K) :=
  IntermediateField.coe_inclusion le_sup_left x

/-- The changed-level inclusion is the ambient identity on
separable-closure elements. -/
@[simp]
theorem standardLubinTateChangedLevelToCompositum_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateChangedLevelField hπ u n) :
    ((standardLubinTateChangedLevelToCompositum hπ u n x :
        standardLubinTateChangedLevelCompositumField hπ u n) :
      SeparableClosure K) =
        (x : SeparableClosure K) :=
  IntermediateField.coe_inclusion le_sup_right x

/-- The original primitive generator has the same ambient value after
inclusion in the compositum. -/
theorem
    standardLubinTateLevelToChangedLevelCompositum_levelGenerator_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    ((standardLubinTateLevelToChangedLevelCompositum hπ u n
          (standardLubinTateLevelGenerator hπ n) :
        standardLubinTateChangedLevelCompositumField hπ u n) :
      SeparableClosure K) =
        chosenStandardLubinTatePrimitiveRoot hπ n := by
  simp

/-- The changed primitive generator has the same ambient value after
inclusion in the compositum. -/
theorem
    standardLubinTateChangedLevelToCompositum_levelGenerator_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    ((standardLubinTateChangedLevelToCompositum hπ u n
          (standardLubinTateChangedLevelGenerator hπ u n) :
        standardLubinTateChangedLevelCompositumField hπ u n) :
      SeparableClosure K) =
        chosenStandardLubinTatePrimitiveRoot
          (standardLubinTateChangedUniformizer_isUniformizer hπ u) n := by
  simp

/-- The algebra structure corresponding to the original-level inclusion. -/
@[reducible]
noncomputable def standardLubinTateLevelToChangedLevelCompositumAlgebra
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Algebra (standardLubinTateLevelField hπ n)
      (standardLubinTateChangedLevelCompositumField hπ u n) :=
  RingHom.toAlgebra
    (standardLubinTateLevelToChangedLevelCompositum
      hπ u n).toRingHom

/-- The algebra structure corresponding to the changed-level inclusion. -/
@[reducible]
noncomputable def standardLubinTateChangedLevelToCompositumAlgebra
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Algebra (standardLubinTateChangedLevelField hπ u n)
      (standardLubinTateChangedLevelCompositumField hπ u n) :=
  RingHom.toAlgebra
    (standardLubinTateChangedLevelToCompositum
      hπ u n).toRingHom

/-- The compositum valuation extends the chosen valuation on the original
level. -/
theorem standardLubinTateLevelToChangedLevelCompositum_hasExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    letI : Algebra (standardLubinTateLevelField hπ n)
        (standardLubinTateChangedLevelCompositumField hπ u n) :=
      standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
    (standardLubinTateLevelCompleteDVF hπ n).valuation.HasExtension
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let vcomap := target.valuation.comap (algebraMap L M)
  let : F.toCompleteDVF.valuation.HasExtension vcomap :=
    { val_isEquiv_comap := by
        rw [_root_.Valuation.isEquiv_iff_val_le_one]
        intro a
        change
          F.toCompleteDVF.valuation a ≤ 1 ↔
            target.valuation
              (algebraMap L M (algebraMap K L a)) ≤ 1
        rw [← IsScalarTower.algebraMap_apply K L M]
        exact
          (_root_.Valuation.HasExtension.val_map_le_one_iff
            (vR := F.toCompleteDVF.valuation)
            (vA := target.valuation) a).symm }
  exact
    { val_isEquiv_comap := by
        simpa only [vcomap] using
          standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension
            hπ n vcomap }

/-- The compositum valuation extends the chosen valuation on the changed
level. -/
theorem standardLubinTateChangedLevelToCompositum_hasExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    letI : Algebra (standardLubinTateChangedLevelField hπ u n)
        (standardLubinTateChangedLevelCompositumField hπ u n) :=
      standardLubinTateChangedLevelToCompositumAlgebra hπ u n
    (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuation.HasExtension
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : IsScalarTower K L' M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let vcomap := target.valuation.comap (algebraMap L' M)
  let : F.toCompleteDVF.valuation.HasExtension vcomap :=
    { val_isEquiv_comap := by
        rw [_root_.Valuation.isEquiv_iff_val_le_one]
        intro a
        change
          F.toCompleteDVF.valuation a ≤ 1 ↔
            target.valuation
              (algebraMap L' M (algebraMap K L' a)) ≤ 1
        rw [← IsScalarTower.algebraMap_apply K L' M]
        exact
          (_root_.Valuation.HasExtension.val_map_le_one_iff
            (vR := F.toCompleteDVF.valuation)
            (vA := target.valuation) a).symm }
  exact
    { val_isEquiv_comap := by
        simpa only [vcomap] using
          standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension
            hπ' n vcomap }

/-- The common valuation detects integrality of an original-level element
exactly as the chosen original-level valuation does. -/
theorem
    standardLubinTateLevelToChangedLevelCompositum_val_le_one_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateLevelField hπ n) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation
        (standardLubinTateLevelToChangedLevelCompositum
          hπ u n x) ≤ 1 ↔
      (standardLubinTateLevelCompleteDVF hπ n).valuation x ≤ 1 := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  change
    target.valuation (algebraMap L M x) ≤ 1 ↔
      level.valuation x ≤ 1
  exact
    _root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := level.valuation) (vA := target.valuation) x

/-- The common valuation detects maximal-ideal membership of an
original-level element. -/
theorem
    standardLubinTateLevelToChangedLevelCompositum_val_lt_one_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateLevelField hπ n) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation
        (standardLubinTateLevelToChangedLevelCompositum
          hπ u n x) < 1 ↔
      (standardLubinTateLevelCompleteDVF hπ n).valuation x < 1 := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  change
    target.valuation (algebraMap L M x) < 1 ↔
      level.valuation x < 1
  exact
    _root_.Valuation.HasExtension.val_map_lt_one_iff
      (vR := level.valuation) (vA := target.valuation) x

/-- The common valuation detects integrality of a changed-level element
exactly as the chosen changed-level valuation does. -/
theorem
    standardLubinTateChangedLevelToCompositum_val_le_one_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateChangedLevelField hπ u n) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation
        (standardLubinTateChangedLevelToCompositum hπ u n x) ≤ 1 ↔
      (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuation x ≤ 1 := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  change
    target.valuation (algebraMap L' M x) ≤ 1 ↔
      level.valuation x ≤ 1
  exact
    _root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := level.valuation) (vA := target.valuation) x

/-- The common valuation detects maximal-ideal membership of a changed-level
element. -/
theorem
    standardLubinTateChangedLevelToCompositum_val_lt_one_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (x : standardLubinTateChangedLevelField hπ u n) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuation
        (standardLubinTateChangedLevelToCompositum hπ u n x) < 1 ↔
      (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuation x < 1 := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  change
    target.valuation (algebraMap L' M x) < 1 ↔
      level.valuation x < 1
  exact
    _root_.Valuation.HasExtension.val_map_lt_one_iff
      (vR := level.valuation) (vA := target.valuation) x

/-- The ramification index of the original level inside the common
compositum. -/
noncomputable def
    standardLubinTateLevelToChangedLevelCompositumRamificationIndex
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) : ℕ := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  letI : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  letI : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  exact ramificationIndex level.toDVF target.toDVF

/-- The ramification index of the changed level inside the common
compositum. -/
noncomputable def
    standardLubinTateChangedLevelToCompositumRamificationIndex
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) : ℕ := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  letI : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  letI : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  exact ramificationIndex level.toDVF target.toDVF

/-- The valuation-ring map induced by the original-level inclusion. -/
noncomputable def
    standardLubinTateLevelToChangedLevelCompositumIntegerMap
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  letI : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  letI : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  exact integerMap level.toDVF target.toDVF

/-- The valuation-ring map induced by the changed-level inclusion. -/
noncomputable def
    standardLubinTateChangedLevelToCompositumIntegerMap
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuationSubring →+*
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  letI : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  letI : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  exact integerMap level.toDVF target.toDVF

/-- Coercion of the original-level integer map is the field inclusion. -/
@[simp]
theorem
    standardLubinTateLevelToChangedLevelCompositumIntegerMap_apply_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (a :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    (((standardLubinTateLevelToChangedLevelCompositumIntegerMap
          hπ u n a :
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring)) :
      standardLubinTateChangedLevelCompositumField hπ u n) =
        standardLubinTateLevelToChangedLevelCompositum
          hπ u n (a :
            standardLubinTateLevelField hπ n) := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  change
    (((integerMap level.toDVF target.toDVF a :
      target.valuationSubring)) : M) =
        standardLubinTateLevelToChangedLevelCompositum hπ u n (a : L)
  rw [integerMap_apply]
  rfl

/-- Coercion of the changed-level integer map is the field inclusion. -/
@[simp]
theorem
    standardLubinTateChangedLevelToCompositumIntegerMap_apply_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (a :
      (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuationSubring) :
    (((standardLubinTateChangedLevelToCompositumIntegerMap
          hπ u n a :
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring)) :
      standardLubinTateChangedLevelCompositumField hπ u n) =
        standardLubinTateChangedLevelToCompositum
          hπ u n (a :
            standardLubinTateChangedLevelField hπ u n) := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  change
    (((integerMap level.toDVF target.toDVF a :
      target.valuationSubring)) : M) =
        standardLubinTateChangedLevelToCompositum hπ u n (a : L')
  rw [integerMap_apply]
  rfl

/-- Normalized additive valuation along the original-level inclusion scales
by its ramification index in the compositum. -/
theorem standardLubinTateLevelToChangedLevelCompositum_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (a :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring
        (standardLubinTateLevelToChangedLevelCompositumIntegerMap
          hπ u n a) =
      standardLubinTateLevelToChangedLevelCompositumRamificationIndex
          hπ u n •
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF
            hπ n).valuationSubring a := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  change
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap level.toDVF target.toDVF a) =
      ramificationIndex level.toDVF target.toDVF •
        IsDiscreteValuationRing.addVal level.valuationSubring a
  exact
    addVal_integerMap_eq_ramificationIndex_nsmul level target a

/-- Normalized additive valuation along the changed-level inclusion scales
by its ramification index in the compositum. -/
theorem standardLubinTateChangedLevelToCompositum_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (a :
      (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuationSubring) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring
        (standardLubinTateChangedLevelToCompositumIntegerMap
          hπ u n a) =
      standardLubinTateChangedLevelToCompositumRamificationIndex
          hπ u n •
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF
            (standardLubinTateChangedUniformizer_isUniformizer
              hπ u) n).valuationSubring a := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  change
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap level.toDVF target.toDVF a) =
      ramificationIndex level.toDVF target.toDVF •
        IsDiscreteValuationRing.addVal level.valuationSubring a
  exact
    addVal_integerMap_eq_ramificationIndex_nsmul level target a

private theorem nat_eq_of_nsmul_enat_eq
    {a b d : ℕ} (hd : 0 < d)
    (h : a • (d : ℕ∞) = b • (d : ℕ∞)) :
    a = b := by
  have hmul :
      (a : ℕ∞) * (d : ℕ∞) = (b : ℕ∞) * (d : ℕ∞) := by
    simpa only [nsmul_eq_mul] using h
  have hmulNat := congrArg ENat.toNat hmul
  have habd : a * d = b * d := by
    simpa only [ENat.toNat_mul, ENat.toNat_natCast] using hmulNat
  exact Nat.eq_of_mul_eq_mul_right hd habd

/-- The original and changed levels have the same ramification index inside
their common compositum.

Both relative indices scale the valuation of the same base uniformizer.
That uniformizer has the common finite-level valuation
`(q - 1) * q ^ n` on either side, and its two images in the literal
compositum agree.  Positivity of the finite-level degree then permits
cancellation. -/
theorem
    standardLubinTateLevelToChangedLevelCompositumRamificationIndex_eq
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateLevelToChangedLevelCompositumRamificationIndex
        hπ u n =
      standardLubinTateChangedLevelToCompositumRamificationIndex
        hπ u n := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L' M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let d :=
    (Nat.card F.residueField - 1) *
      Nat.card F.residueField ^ n
  have holdBase :
      IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (standardLubinTateLevelCoefficientHom hπ n π) =
        (d : ℕ∞) := by
    simpa only [standardLubinTateLevelCoefficientHom, d] using
      standardLubinTateUniformizerInteger_map_addVal hπ hπ n
  have hchangedBase :
      IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ' n).valuationSubring
          (standardLubinTateLevelCoefficientHom hπ' n π) =
        (d : ℕ∞) := by
    simpa only [standardLubinTateLevelCoefficientHom, d] using
      standardLubinTateUniformizerInteger_map_addVal hπ' hπ n
  have hmap :
      standardLubinTateLevelToChangedLevelCompositumIntegerMap
          hπ u n (standardLubinTateLevelCoefficientHom hπ n π) =
    standardLubinTateChangedLevelToCompositumIntegerMap
          hπ u n (standardLubinTateLevelCoefficientHom hπ' n π) := by
    apply Subtype.ext
    rw [
      standardLubinTateLevelToChangedLevelCompositumIntegerMap_apply_coe,
      standardLubinTateChangedLevelToCompositumIntegerMap_apply_coe]
    change
      algebraMap L M
          (standardLubinTateLevelCoefficientHom hπ n π : L) =
        algebraMap L' M
          (standardLubinTateLevelCoefficientHom hπ' n π : L')
    rw [
      standardLubinTateLevelCoefficientHom_apply,
      standardLubinTateLevelCoefficientHom_apply]
    rw [← IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply K L' M]
  have hold :=
    standardLubinTateLevelToChangedLevelCompositum_addVal hπ u n
      (standardLubinTateLevelCoefficientHom hπ n π)
  have hchanged :=
    standardLubinTateChangedLevelToCompositum_addVal hπ u n
      (standardLubinTateLevelCoefficientHom hπ' n π)
  rw [holdBase] at hold
  rw [hchangedBase] at hchanged
  have hscaled :
      standardLubinTateLevelToChangedLevelCompositumRamificationIndex
            hπ u n • (d : ℕ∞) =
        standardLubinTateChangedLevelToCompositumRamificationIndex
            hπ u n • (d : ℕ∞) := by
    calc
      standardLubinTateLevelToChangedLevelCompositumRamificationIndex
            hπ u n • (d : ℕ∞) =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (standardLubinTateLevelToChangedLevelCompositumIntegerMap
              hπ u n
              (standardLubinTateLevelCoefficientHom hπ n π)) :=
        hold.symm
      _ =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (standardLubinTateChangedLevelToCompositumIntegerMap
              hπ u n
              (standardLubinTateLevelCoefficientHom hπ' n π)) := by
        rw [hmap]
      _ =
          standardLubinTateChangedLevelToCompositumRamificationIndex
              hπ u n • (d : ℕ∞) :=
        hchanged
  have hdpos : 0 < d := by
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Finite.one_lt_card :
        1 < Nat.card F.residueField))
      (pow_pos
        (Nat.zero_lt_one.trans (Finite.one_lt_card :
          1 < Nat.card F.residueField)) n)
  exact nat_eq_of_nsmul_enat_eq hdpos hscaled

/-- Original-level maximal-ideal depth scales by the ramification index in
the compositum. -/
theorem
    standardLubinTateLevelToChangedLevelCompositumIntegerMap_mem_maximalIdeal_pow
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n r : ℕ)
    {a :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
    (ha :
      a ∈ (standardLubinTateLevelCompleteDVF
        hπ n).maximalIdeal ^ r) :
    standardLubinTateLevelToChangedLevelCompositumIntegerMap hπ u n a ∈
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).maximalIdeal ^
          (standardLubinTateLevelToChangedLevelCompositumRamificationIndex
            hπ u n * r) := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  change
    integerMap level.toDVF target.toDVF a ∈
      target.maximalIdeal ^
        (ramificationIndex level.toDVF target.toDVF * r)
  exact
    integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex
      level target ha

/-- Changed-level maximal-ideal depth scales by the ramification index in
the compositum. -/
theorem
    standardLubinTateChangedLevelToCompositumIntegerMap_mem_maximalIdeal_pow
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n r : ℕ)
    {a :
      (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).valuationSubring}
    (ha :
      a ∈ (standardLubinTateLevelCompleteDVF
        (standardLubinTateChangedUniformizer_isUniformizer
          hπ u) n).maximalIdeal ^ r) :
    standardLubinTateChangedLevelToCompositumIntegerMap hπ u n a ∈
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).maximalIdeal ^
          (standardLubinTateChangedLevelToCompositumRamificationIndex
            hπ u n * r) := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateChangedLevelToCompositum_hasExtension hπ u n
  change
    integerMap level.toDVF target.toDVF a ∈
      target.maximalIdeal ^
        (ramificationIndex level.toDVF target.toDVF * r)
  exact
    integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex
      level target ha

end LubinTate

end
