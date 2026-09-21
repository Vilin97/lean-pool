/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusFixedField
/-!
# Intrinsic fixed-field prime comparison

This module compares intrinsic local Artin maps with the ambient fixed-field norm-residue symbol.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

section IntrinsicFixedFieldPrimeComparison

variable
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)

local notation "F" =>
  abstractFixedField K (SeparableClosure K) H.field

local notation "E" =>
  abstractRelativeFixedField K (SeparableClosure K) hJH

local notation "iFE" =>
  e.symm.toAlgHom.comp
    (IntermediateField.val
      (abstractRelativeFixedField
        K (SeparableClosure K) hJH))

local notation "EI" =>
  finiteGaloisAbstractExtensionOfEmbedding F E iFE

local notation "RF" =>
  FiniteAbstractField.toFiniteResidueAbstractField
    (intrinsicFiniteAbstractBase F)
    (localResidueDatum F)

local notation "RH" =>
  FiniteAbstractField.toFiniteResidueAbstractField
    H (localResidueDatum K)

local notation "qF" =>
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E iFE

local notation "qH" =>
  abstractExtensionQuotientEquivGaloisGroup
    K (SeparableClosure K) H.field J hJH hJnormal

local instance intrinsicPrimeComparison_separableClosureAlgebra :
    Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra

local instance intrinsicPrimeComparison_absoluteFinite :
    Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H.field (le_baseField H.field)) :=
  H.finite

local instance intrinsicPrimeComparison_fixedFieldFiniteDimensional :
    FiniteDimensional K F :=
  abstractFixedField_finiteDimensional
    K (SeparableClosure K) H.field H.finite

local instance intrinsicPrimeComparison_fixedFieldNormed :
    NontriviallyNormedField F :=
  finiteExtensionSpectralNormedField K F

local instance intrinsicPrimeComparison_fixedFieldValuative :
    ValuativeRel F :=
  finiteExtensionSpectralValuativeRel K F

local instance intrinsicPrimeComparison_fixedFieldLocal :
    IsNonarchimedeanLocalField F :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K F

local instance intrinsicPrimeComparison_extensionFiniteDimensional :
    FiniteDimensional F E :=
  abstractRelativeFixedField_finiteDimensional
    K (SeparableClosure K) H.field J hJH H.finite hJfinite

local instance intrinsicPrimeComparison_extensionGalois :
    IsGalois F E :=
  abstractRelativeFixedField_isGalois
    K (SeparableClosure K) H.field J hJH hJnormal

local instance intrinsicPrimeComparison_extensionNormal :
    (extensionSubgroup
      (intrinsicAbstractBase F) (EI).field (EI).below).Normal :=
  (EI).normal

local instance intrinsicPrimeComparison_extensionFinite :
    Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) (EI).field (EI).below) :=
  (EI).finite

local instance intrinsicPrimeComparison_residueExtensionFinite :
    Finite
      ((RF).field.toSubgroup ⧸
        extensionSubgroup (RF).field (EI).field (EI).below) := by
  change Finite
    ((intrinsicAbstractBase F).toSubgroup ⧸
      extensionSubgroup
        (intrinsicAbstractBase F) (EI).field (EI).below)
  exact intrinsicPrimeComparison_extensionFinite K H J hJH e

/-- The local Artin homomorphism of the actual finite fixed-field extension,
using the canonical local structure constructed from the original field. -/
noncomputable def intrinsicFixedFieldLocalArtinMonoidHom :
    Additive Fˣ →+ Additive (Abelianization Gal(E / F)) :=
  MonoidHom.toAdditive (localArtinMonoidHom F E)

/-- The concrete norm-residue symbol of the intrinsic finite extension,
evaluated at a unit of the finite fixed field. -/
noncomputable def intrinsicFixedFieldConcreteSymbolValue
    (x : Fˣ) : Abelianization Gal(E / F) :=
  concreteNormResidueSymbolOfEmbedding
    F E iFE
    (localResidueDatum F)
    (localHenselianValuation F)
    (separableClosureUnits_isClassFormation F) x

private def intrinsicFixedFieldConcretePrimeComparison
    (x : Fˣ) (z : Abelianization Gal(E/F)) : Prop :=
  intrinsicFixedFieldConcreteSymbolValue K H J hJH e x =
    z

private def intrinsicFixedFieldAmbientPrimeComparison
    (_e : intrinsicFixedFieldSeparableClosureEquiv K H)
    (x : Fˣ) (z : Abelianization Gal(E/F)) : Prop :=
  abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H.field J hJH (Additive.ofMul x) =
    Additive.ofMul z

/-- Map an intrinsic extension-quotient class to the abelianization of the
intrinsic finite-extension Galois group. -/
def intrinsicFixedFieldSourceFrobeniusAbelianization
    (q : (EI).extensionQuotient) :
    Abelianization Gal(E / F) :=
  Abelianization.of (qF q)

/-- Restrict a transported ambient Frobenius element and map the resulting
class to the abelianization of the intrinsic finite-extension Galois group. -/
def intrinsicFixedFieldAmbientFrobeniusAbelianization
    (σ :
      (localResidueDatum F).FrobeniusElements
        RF (EI).field (EI).below) :
    Abelianization Gal(E / F) :=
  (qH).abelianizationCongr
    (Abelianization.of
      ((localResidueDatum K).frobeniusRestriction
        RH J hJH
        (intrinsicFrobeniusElementToAmbientFixedField
          K H J hJH e σ)))

private structure IntrinsicFixedFieldPrimeComparisonData
    (z : Abelianization Gal(E/F)) where
  xPrime : Fˣ
  concrete :
    intrinsicFixedFieldConcretePrimeComparison
      K H J hJH e xPrime z
  ambient :
    intrinsicFixedFieldAmbientPrimeComparison
      K H J hJH e xPrime z

/-- The intrinsic closed subgroup fixed by the Frobenius element associated to
the finite fixed-field extension. -/
abbrev intrinsicFixedFieldFrobeniusSourceClosedField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :=
  (localResidueDatum F).frobeniusFixedField
    RF (EI).field (EI).below σ

/-- The intrinsic Frobenius-fixed closed subgroup lies below the intrinsic
absolute-base subgroup. -/
theorem intrinsicFixedFieldFrobeniusSourceBelow
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ).toSubgroup ≤
      (intrinsicAbstractBase F).toSubgroup :=
  (localResidueDatum F).frobeniusFixedField_le
    RF (EI).field (EI).below σ

/-- The intrinsic abstract fixed field cut out by the intrinsic
Frobenius-fixed closed subgroup. -/
abbrev intrinsicFixedFieldFrobeniusSourceField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :=
  abstractFixedField F (SeparableClosure F)
    (intrinsicFixedFieldFrobeniusSourceClosedField
      K H J hJH e σ)

/-- The ambient Frobenius-fixed closed subgroup obtained after transporting
the intrinsic Frobenius element. -/
abbrev intrinsicFixedFieldFrobeniusAmbientClosedField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :=
  (localResidueDatum K).frobeniusFixedField
    RH J hJH
    (intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ)

/-- The transported ambient Frobenius-fixed subgroup lies below the ambient
finite fixed subgroup. -/
theorem intrinsicFixedFieldFrobeniusAmbientBelow
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ).toSubgroup ≤ H.field.toSubgroup :=
  (localResidueDatum K).frobeniusFixedField_le
    RH J hJH
    (intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ)

/-- The ambient relative fixed field cut out by the transported
Frobenius-fixed subgroup. -/
abbrev intrinsicFixedFieldFrobeniusAmbientField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :=
  abstractRelativeFixedField K (SeparableClosure K)
    (intrinsicFixedFieldFrobeniusAmbientBelow
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceAlgebra
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  (intrinsicFixedFieldFrobeniusSourceField
    K H J hJH e σ).algebra

local instance intrinsicPrimeComparison_frobeniusSourceFiniteDimensional
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule F
        (intrinsicFixedFieldFrobeniusSourceField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusSourceAlgebra
          K H J hJH e σ)) := by
  let : Algebra F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
    intrinsicPrimeComparison_frobeniusSourceAlgebra
      K H J hJH e σ
  let _hRFFinite :
      Finite
        ((RF).field.toSubgroup ⧸
          extensionSubgroup (RF).field (EI).field (EI).below) :=
    intrinsicPrimeComparison_residueExtensionFinite
      K H J hJH e
  exact
    @abstractFixedField_finiteDimensional
      F (SeparableClosure F) _ _ inferInstance inferInstance
      (intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ)
      ((localResidueDatum F).frobeniusFixedField_absoluteFinite
        (intrinsicFiniteAbstractBase F) (EI).field (EI).below σ)

local instance intrinsicPrimeComparison_frobeniusSourceNormed
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    NontriviallyNormedField
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralNormedField F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceValuative
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ValuativeRel
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralValuativeRel F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceLocal
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceValuationExtension
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Valuation.HasExtension
      (ValuativeRel.valuation F)
      (ValuativeRel.valuation
        (intrinsicFixedFieldFrobeniusSourceField
          K H J hJH e σ)) :=
  finiteExtensionSpectralValuation_hasExtension F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientAlgebraK
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  (abstractFixedField K (SeparableClosure K)
    (intrinsicFixedFieldFrobeniusAmbientClosedField
      K H J hJH e σ)).algebra

local instance intrinsicPrimeComparison_frobeniusAmbientAlgebraF
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra F
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  (intrinsicFixedFieldFrobeniusAmbientField
    K H J hJH e σ).algebra

local instance intrinsicPrimeComparison_frobeniusAmbientFiniteDimensionalK
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule K
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusAmbientAlgebraK
          K H J hJH e σ)) := by
  let : Algebra K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
    intrinsicPrimeComparison_frobeniusAmbientAlgebraK
      K H J hJH e σ
  change FiniteDimensional K
    (abstractFixedField K (SeparableClosure K)
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ))
  exact
    abstractFixedField_finiteDimensional
      K (SeparableClosure K)
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ)
      ((localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH
        (intrinsicFrobeniusElementToAmbientFixedField
          K H J hJH e σ))

local instance intrinsicPrimeComparison_frobeniusAmbientNormed
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    NontriviallyNormedField
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralNormedField K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientValuative
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ValuativeRel
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralValuativeRel K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientLocal
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientValuationExtension
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Valuation.HasExtension
      (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)) :=
  finiteExtensionSpectralValuation_hasExtension K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientFiniteDimensionalF
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional F
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule F
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusAmbientAlgebraF
          K H J hJH e σ)) := by
  let : Algebra F
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
    intrinsicPrimeComparison_frobeniusAmbientAlgebraF
      K H J hJH e σ
  exact
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientBelow
        K H J hJH e σ)
      H.finite
      ((localResidueDatum K).frobeniusFixedField_finite
        RH J hJH
        (intrinsicFrobeniusElementToAmbientFixedField
          K H J hJH e σ))

/-- The canonical algebra embedding of the ambient Frobenius fixed field into
the ambient separable closure. -/
def intrinsicFixedFieldFrobeniusAmbientEmbedding
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ →ₐ[K]
      SeparableClosure K :=
  (abstractFixedField K (SeparableClosure K)
    (intrinsicFixedFieldFrobeniusAmbientClosedField
      K H J hJH e σ)).val

local instance intrinsicPrimeComparison_frobeniusAmbientSeparable
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra.IsSeparable K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  by
    change Algebra.IsSeparable K
      (abstractFixedField K (SeparableClosure K)
        (intrinsicFixedFieldFrobeniusAmbientClosedField
          K H J hJH e σ))
    infer_instance

/-- The canonical algebra equivalence from the intrinsic Frobenius fixed field
to the corresponding ambient Frobenius fixed field. -/
noncomputable def intrinsicFixedFieldFrobeniusAlgEquiv
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :=
  intrinsicFrobeniusFixedFieldEquivAmbientFixedField
    K H J hJH e σ

/-- The underlying ring equivalence of the canonical equivalence between the
intrinsic and ambient Frobenius fixed fields. -/
noncomputable def intrinsicFixedFieldFrobeniusRingEquiv
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ ≃+*
      intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ :=
  (intrinsicFixedFieldFrobeniusAlgEquiv
    K H J hJH e σ).toRingEquiv

/-- The canonical intrinsic-to-ambient Frobenius fixed-field equivalence
identifies their valuation subrings. -/
theorem intrinsicFixedFieldFrobenius_valuationSubring_mem
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (x :
      intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :
    x ∈
        (ValuativeRel.valuation
          (intrinsicFixedFieldFrobeniusSourceField
            K H J hJH e σ)).valuationSubring ↔
      intrinsicFixedFieldFrobeniusRingEquiv
          K H J hJH e σ x ∈
        (ValuativeRel.valuation
          (intrinsicFixedFieldFrobeniusAmbientField
            K H J hJH e σ)).valuationSubring := by
  exact
    valuationSubring_mem_iff_of_separableClosureRingEquiv
      F K
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ).val
      (intrinsicFixedFieldFrobeniusAmbientEmbedding
        K H J hJH e σ)
      e.toRingEquiv
      (localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv
        K H e)
      (intrinsicFixedFieldFrobeniusRingEquiv
        K H J hJH e σ)
      (fun y => by
        calc
          intrinsicFixedFieldFrobeniusAmbientEmbedding
                K H J hJH e σ
              (intrinsicFixedFieldFrobeniusRingEquiv
                K H J hJH e σ y) =
              ((intrinsicFrobeniusFixedFieldEquivAmbientFixedField
                    K H J hJH e σ y :
                  intrinsicFixedFieldFrobeniusAmbientField
                    K H J hJH e σ) :
                SeparableClosure K) := rfl
          _ = e (y : SeparableClosure F) :=
            intrinsicFrobeniusFixedFieldEquivAmbientFixedField_apply_val
              K H J hJH e σ y)
      x

private noncomputable def intrinsicFixedFieldFrobeniusSourcePrimeUnit
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)ˣ :=
  Classical.choose
    (exists_valuationOne_unit_of_ringEquiv
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusRingEquiv
        K H J hJH e σ)
      (intrinsicFixedFieldFrobenius_valuationSubring_mem
        K H J hJH e σ))

private theorem intrinsicFixedFieldFrobeniusSourcePrimeUnit_valuation
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField.valuationMap
        (intrinsicFixedFieldFrobeniusSourceField
          K H J hJH e σ)
        (Additive.ofMul
          (intrinsicFixedFieldFrobeniusSourcePrimeUnit
            K H J hJH e σ)) =
      1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusRingEquiv
        K H J hJH e σ)
      (intrinsicFixedFieldFrobenius_valuationSubring_mem
        K H J hJH e σ))).1

private noncomputable def intrinsicFixedFieldFrobeniusAmbientPrimeUnit
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)ˣ :=
  Units.mapEquiv
    (intrinsicFixedFieldFrobeniusRingEquiv
      K H J hJH e σ).toMulEquiv
    (intrinsicFixedFieldFrobeniusSourcePrimeUnit
      K H J hJH e σ)

private theorem intrinsicFixedFieldFrobeniusAmbientPrimeUnit_valuation
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField.valuationMap
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)
        (Additive.ofMul
          (intrinsicFixedFieldFrobeniusAmbientPrimeUnit
            K H J hJH e σ)) =
      1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusRingEquiv
        K H J hJH e σ)
      (intrinsicFixedFieldFrobenius_valuationSubring_mem
        K H J hJH e σ))).2

private noncomputable def intrinsicFixedFieldFrobeniusPrimeNorm
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) : Fˣ :=
  normUnits F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusSourcePrimeUnit
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceQuotientFinite
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F)
          (intrinsicFixedFieldFrobeniusSourceClosedField
            K H J hJH e σ)
          (intrinsicFixedFieldFrobeniusSourceBelow
            K H J hJH e σ)) := by
  change Finite
    ((RF).field.toSubgroup ⧸
      extensionSubgroup
        (RF).field
        (intrinsicFixedFieldFrobeniusSourceClosedField
          K H J hJH e σ)
        (intrinsicFixedFieldFrobeniusSourceBelow
          K H J hJH e σ))
  exact
    (localResidueDatum F).frobeniusFixedField_finite
      RF (EI).field (EI).below σ

/-- Package the intrinsic Frobenius-fixed subgroup as a finite abstract field
inside the intrinsic absolute Galois group. -/
def intrinsicFixedFieldFrobeniusSourceAbstractField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    FiniteAbstractField Gal(SeparableClosure F / F) := by
  letI _hExtensionFinite :
      Finite
        ((intrinsicAbstractBase F).toSubgroup ⧸
          extensionSubgroup
            (intrinsicAbstractBase F) (EI).field (EI).below) :=
    intrinsicPrimeComparison_extensionFinite
      K H J hJH e
  letI _hResidueExtensionFinite :
      Finite
        ((RF).field.toSubgroup ⧸
          extensionSubgroup (RF).field (EI).field (EI).below) :=
    intrinsicPrimeComparison_residueExtensionFinite
      K H J hJH e
  exact
    ⟨intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ,
      (localResidueDatum F).frobeniusFixedField_absoluteFinite
        (intrinsicFiniteAbstractBase F) (EI).field (EI).below σ⟩

private noncomputable def intrinsicFixedFieldFrobeniusSourcePrimeElement
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F)
      (intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ) :=
  abstractFixedFieldUnitsEquivGaloisFixed
    F (SeparableClosure F)
    (intrinsicFixedFieldFrobeniusSourceClosedField
      K H J hJH e σ)
    (Additive.ofMul
      (intrinsicFixedFieldFrobeniusSourcePrimeUnit
        K H J hJH e σ))

private theorem intrinsicFixedFieldFrobeniusSourcePrimeElement_isPrime
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (localHenselianValuation F).IsPrimeElement
      (intrinsicFixedFieldFrobeniusSourceAbstractField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusSourcePrimeElement
        K H J hJH e σ) :=
  localHenselianValuation_isPrimeElement_abstractFixedField
    F
    (intrinsicFixedFieldFrobeniusSourceAbstractField
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusSourcePrimeUnit
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusSourcePrimeUnit_valuation
      K H J hJH e σ)

private theorem intrinsicFixedFieldFrobeniusPrimeNorm_relativeNorm
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    relativeNorm
        (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F)
        (intrinsicFixedFieldFrobeniusSourceClosedField
          K H J hJH e σ)
        (intrinsicFixedFieldFrobeniusSourceBelow
          K H J hJH e σ)
        (intrinsicFixedFieldFrobeniusSourcePrimeElement
          K H J hJH e σ) =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul
          (intrinsicFixedFieldFrobeniusPrimeNorm
            K H J hJH e σ)) :=
  relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit
    F
    (intrinsicFixedFieldFrobeniusSourceClosedField
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusSourceBelow
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusSourcePrimeUnit
      K H J hJH e σ)

/-- Package the transported ambient Frobenius-fixed subgroup as a finite
abstract field inside the ambient absolute Galois group. -/
def intrinsicFixedFieldFrobeniusAmbientAbstractField
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    FiniteAbstractField Gal(SeparableClosure K / K) :=
  ⟨intrinsicFixedFieldFrobeniusAmbientClosedField
      K H J hJH e σ,
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J hJH
      (intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ)⟩

private noncomputable def intrinsicFixedFieldFrobeniusAmbientPrimeElement
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (SeparableClosure K))
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ) :=
  abstractRelativeFixedFieldUnitsEquivGaloisFixed
    K (SeparableClosure K) H.field
    (intrinsicFixedFieldFrobeniusAmbientClosedField
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusAmbientBelow
      K H J hJH e σ)
    (Additive.ofMul
      (intrinsicFixedFieldFrobeniusAmbientPrimeUnit
        K H J hJH e σ))

private theorem intrinsicFixedFieldFrobeniusAmbientPrimeElement_isPrime
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    (localHenselianValuation K).IsPrimeElement
      (intrinsicFixedFieldFrobeniusAmbientAbstractField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientPrimeElement
        K H J hJH e σ) :=
  localHenselianValuation_isPrimeElement_abstractFixedField
    K
    (intrinsicFixedFieldFrobeniusAmbientAbstractField
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusAmbientPrimeUnit
      K H J hJH e σ)
    (intrinsicFixedFieldFrobeniusAmbientPrimeUnit_valuation
      K H J hJH e σ)

private theorem intrinsicFixedFieldFrobeniusPrimeNorm_concrete
    (q : (EI).extensionQuotient)
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)
    (hσ :
      (localResidueDatum F).frobeniusRestriction
        RF (EI).field (EI).below σ = q) :
    intrinsicFixedFieldConcretePrimeComparison
      K H J hJH e
      (intrinsicFixedFieldFrobeniusPrimeNorm
        K H J hJH e σ)
      (intrinsicFixedFieldSourceFrobeniusAbelianization
        K H J hJH e q) := by
  unfold intrinsicFixedFieldConcretePrimeComparison
  unfold intrinsicFixedFieldSourceFrobeniusAbelianization
  unfold intrinsicFixedFieldConcreteSymbolValue
  exact
    concreteNormResidueSymbolOfEmbedding_apply_primeNorm
      F E iFE
      (localResidueDatum F)
      (localHenselianValuation F)
      (separableClosureUnits_isClassFormation F)
      q σ hσ
      (intrinsicFixedFieldFrobeniusSourcePrimeElement
        K H J hJH e σ)
      (by
        simpa only [intrinsicFixedFieldFrobeniusSourceAbstractField] using
          (intrinsicFixedFieldFrobeniusSourcePrimeElement_isPrime
            K H J hJH e σ))
      (intrinsicFixedFieldFrobeniusPrimeNorm
        K H J hJH e σ)
      (by
        simpa only [intrinsicFixedFieldFrobeniusSourceClosedField] using
          (intrinsicFixedFieldFrobeniusPrimeNorm_relativeNorm
            K H J hJH e σ).symm)

private theorem intrinsicFixedFieldFrobeniusPrimeNorm_ambient
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    intrinsicFixedFieldAmbientPrimeComparison
      K H J hJH e
      (intrinsicFixedFieldFrobeniusPrimeNorm
        K H J hJH e σ)
      (intrinsicFixedFieldAmbientFrobeniusAbelianization
        K H J hJH e σ) := by
  unfold intrinsicFixedFieldAmbientPrimeComparison
  unfold intrinsicFixedFieldAmbientFrobeniusAbelianization
  let phiF : F ≃+* F := RingEquiv.refl F
  let phi :=
    intrinsicFixedFieldFrobeniusRingEquiv
      K H J hJH e σ
  have hcomm :
      RingHom.comp
          (algebraMap F
            (intrinsicFixedFieldFrobeniusAmbientField
              K H J hJH e σ))
          phiF.toRingHom =
        RingHom.comp phi.toRingHom
          (algebraMap F
            (intrinsicFixedFieldFrobeniusSourceField
              K H J hJH e σ)) := by
    apply RingHom.ext
    intro x
    exact
      ((intrinsicFixedFieldFrobeniusAlgEquiv
        K H J hJH e σ).commutes x).symm
  exact
    abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit
      K F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      H J hJH
      (intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ)
      (_hLHNorm :=
        intrinsicPrimeComparison_frobeniusAmbientNormed
          K H J hJH e σ)
      (_hLHVal :=
        intrinsicPrimeComparison_frobeniusAmbientValuative
          K H J hJH e σ)
      (_hLHLocal :=
        intrinsicPrimeComparison_frobeniusAmbientLocal
          K H J hJH e σ)
      (_hF₀LHFinite :=
        intrinsicPrimeComparison_frobeniusAmbientFiniteDimensionalF
          K H J hJH e σ)
      phiF phi hcomm
      (intrinsicFixedFieldFrobenius_valuationSubring_mem
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientPrimeElement_isPrime
        K H J hJH e σ)


private noncomputable def intrinsicFixedFieldPrimeRepresentative
    (z : Abelianization Gal(E/F)) :
    (EI).extensionQuotient :=
  Classical.choose
    (QuotientGroup.mk_surjective
      ((qF).abelianizationCongr.symm z))

omit [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
private theorem intrinsicFixedFieldPrimeRepresentative_abelianization
    (z : Abelianization Gal(E/F)) :
    (qF).abelianizationCongr
        (Abelianization.of
          (intrinsicFixedFieldPrimeRepresentative
            K H J hJH e z)) =
      z := by
  let zF : Abelianization (EI).extensionQuotient :=
    (qF).abelianizationCongr.symm z
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  calc
    (qF).abelianizationCongr
        (Abelianization.of
          (intrinsicFixedFieldPrimeRepresentative
            K H J hJH e z)) =
        (qF).abelianizationCongr zF :=
      congrArg (qF).abelianizationCongr hq
    _ = z := (qF).abelianizationCongr.apply_symm_apply z

private noncomputable def intrinsicFixedFieldPrimeFrobeniusLift
    (z : Abelianization Gal(E/F)) :
    intrinsicFixedFieldFrobeniusElements K H J hJH e :=
  Classical.choose
    ((localResidueDatum F).frobeniusRestriction_surjective
      RF (EI).field (EI).below
      (intrinsicFixedFieldPrimeRepresentative
        K H J hJH e z))

private theorem intrinsicFixedFieldPrimeFrobeniusLift_restriction
    (z : Abelianization Gal(E/F)) :
    (localResidueDatum F).frobeniusRestriction
        RF (EI).field (EI).below
        (intrinsicFixedFieldPrimeFrobeniusLift
          K H J hJH e z) =
      intrinsicFixedFieldPrimeRepresentative
        K H J hJH e z :=
  Classical.choose_spec
    ((localResidueDatum F).frobeniusRestriction_surjective
      RF (EI).field (EI).below
      (intrinsicFixedFieldPrimeRepresentative
        K H J hJH e z))

private noncomputable def intrinsicFixedFieldPrimeComparisonWitness
    (z : Abelianization Gal(E/F)) : Fˣ :=
  intrinsicFixedFieldFrobeniusPrimeNorm
    K H J hJH e
    (intrinsicFixedFieldPrimeFrobeniusLift
      K H J hJH e z)

private theorem intrinsicFixedFieldPrimeComparisonWitness_concrete
    (z : Abelianization Gal(E/F)) :
    intrinsicFixedFieldConcretePrimeComparison
      K H J hJH e
      (intrinsicFixedFieldPrimeComparisonWitness
        K H J hJH e z) z := by
  have hprime :=
    intrinsicFixedFieldFrobeniusPrimeNorm_concrete
      K H J hJH e
      (intrinsicFixedFieldPrimeRepresentative
        K H J hJH e z)
      (intrinsicFixedFieldPrimeFrobeniusLift
        K H J hJH e z)
      (intrinsicFixedFieldPrimeFrobeniusLift_restriction
        K H J hJH e z)
  unfold intrinsicFixedFieldPrimeComparisonWitness
  unfold intrinsicFixedFieldConcretePrimeComparison at hprime ⊢
  unfold intrinsicFixedFieldSourceFrobeniusAbelianization at hprime
  exact
    hprime.trans
      ((abelianizationCongr_of qF
        (intrinsicFixedFieldPrimeRepresentative
          K H J hJH e z)).symm.trans
        (intrinsicFixedFieldPrimeRepresentative_abelianization
          K H J hJH e z))

private noncomputable def intrinsicFixedFieldAmbientQuotientResult
    (q :
      H.field.toSubgroup ⧸
        extensionSubgroup H.field J hJH) :
    Gal(E / F) :=
  qH q

private noncomputable def intrinsicFixedFieldSourceQuotientResult
    (q : (EI).extensionQuotient) :
    Gal(E / F) :=
  qF q

private noncomputable def
    intrinsicFixedFieldFrobeniusAmbientRestrictionResult
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Gal(E / F) :=
  intrinsicFixedFieldAmbientQuotientResult K H J hJH
    ((localResidueDatum K).frobeniusRestriction
      RH J hJH
      (intrinsicFrobeniusElementToAmbientFixedField
        K H J hJH e σ))

private noncomputable def
    intrinsicFixedFieldFrobeniusSourceRestrictionResult
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Gal(E / F) :=
  intrinsicFixedFieldSourceQuotientResult K H J hJH e
    ((localResidueDatum F).frobeniusRestriction
      RF (EI).field (EI).below σ)

omit [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
private theorem
    intrinsicFixedFieldQuotientResult_mk_compatibility
    (τ : (intrinsicAbstractBase F).toSubgroup) :
    intrinsicFixedFieldAmbientQuotientResult K H J hJH
        (QuotientGroup.mk
          (intrinsicBaseEquivAmbientFixedField K H e τ)) =
      intrinsicFixedFieldSourceQuotientResult K H J hJH e
        (QuotientGroup.mk τ) := by
  unfold intrinsicFixedFieldAmbientQuotientResult
  unfold intrinsicFixedFieldSourceQuotientResult
  exact fixedFieldQuotientEquiv_mk_compatibility
    K H J hJH e τ

private theorem
    intrinsicFixedFieldFrobeniusRestriction_mk_compatibility
    (τ : (intrinsicAbstractBase F).toSubgroup) :
    intrinsicFixedFieldAmbientQuotientResult K H J hJH
        ((localResidueDatum K).extensionRestriction
          H.field J hJH
          (intrinsicFrobeniusQuotientEquivAmbientFixedField
            K H J hJH e (QuotientGroup.mk τ))) =
      intrinsicFixedFieldSourceQuotientResult K H J hJH e
        ((localResidueDatum F).extensionRestriction
          (intrinsicAbstractBase F) (EI).field (EI).below
          (QuotientGroup.mk τ)) := by
  have hFrobenius :
      intrinsicFrobeniusQuotientEquivAmbientFixedField
          K H J hJH e (QuotientGroup.mk τ) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientFixedField K H e τ) :=
    intrinsicFrobeniusQuotientEquivAmbientFixedField_mk
      K H J hJH e τ
  have hAmbientRestriction :
      (localResidueDatum K).extensionRestriction
          H.field J hJH
          (intrinsicFrobeniusQuotientEquivAmbientFixedField
            K H J hJH e (QuotientGroup.mk τ)) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientFixedField K H e τ) := by
    calc
      _ =
          (localResidueDatum K).extensionRestriction
            H.field J hJH
            (QuotientGroup.mk
              (intrinsicBaseEquivAmbientFixedField K H e τ)) :=
        congrArg
          ((localResidueDatum K).extensionRestriction
            H.field J hJH)
          hFrobenius
      _ = _ :=
        (localResidueDatum K).extensionRestriction_mk
          H.field J hJH
          (intrinsicBaseEquivAmbientFixedField K H e τ)
  have hSourceRestriction :
      (localResidueDatum F).extensionRestriction
          (intrinsicAbstractBase F) (EI).field (EI).below
          (QuotientGroup.mk τ) =
        QuotientGroup.mk τ :=
    (localResidueDatum F).extensionRestriction_mk
      (intrinsicAbstractBase F) (EI).field (EI).below τ
  calc
    _ =
        intrinsicFixedFieldAmbientQuotientResult K H J hJH
          (QuotientGroup.mk
            (intrinsicBaseEquivAmbientFixedField K H e τ)) :=
      congrArg
        (intrinsicFixedFieldAmbientQuotientResult K H J hJH)
        hAmbientRestriction
    _ =
        intrinsicFixedFieldSourceQuotientResult K H J hJH e
          (QuotientGroup.mk τ) :=
      intrinsicFixedFieldQuotientResult_mk_compatibility
        K H J hJH e τ
    _ = _ :=
      congrArg
        (intrinsicFixedFieldSourceQuotientResult K H J hJH e)
        hSourceRestriction.symm

private theorem
    intrinsicFixedFieldFrobeniusAmbientRestrictionResult_eq
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    intrinsicFixedFieldFrobeniusAmbientRestrictionResult
        K H J hJH e σ =
      intrinsicFixedFieldFrobeniusSourceRestrictionResult
        K H J hJH e σ := by
  obtain ⟨τ, hτσ⟩ :=
    QuotientGroup.mk_surjective σ.1
  let ambient :=
    fun q : intrinsicFixedFieldFrobeniusQuotient K H J hJH e =>
      intrinsicFixedFieldAmbientQuotientResult K H J hJH
        ((localResidueDatum K).extensionRestriction
          H.field J hJH
          (intrinsicFrobeniusQuotientEquivAmbientFixedField
            K H J hJH e q))
  let source :=
    fun q : intrinsicFixedFieldFrobeniusQuotient K H J hJH e =>
      intrinsicFixedFieldSourceQuotientResult K H J hJH e
        ((localResidueDatum F).extensionRestriction
          (intrinsicAbstractBase F) (EI).field (EI).below q)
  change ambient σ.1 = source σ.1
  calc
    ambient σ.1 = ambient (QuotientGroup.mk τ) :=
      congrArg ambient hτσ.symm
    _ = source (QuotientGroup.mk τ) :=
      intrinsicFixedFieldFrobeniusRestriction_mk_compatibility
        K H J hJH e τ
    _ = source σ.1 :=
      congrArg source hτσ

private theorem
    intrinsicFixedFieldPrimeFrobeniusSourceRestrictionResult_eq
    (z : Abelianization Gal(E/F)) :
    intrinsicFixedFieldFrobeniusSourceRestrictionResult
        K H J hJH e
        (intrinsicFixedFieldPrimeFrobeniusLift
          K H J hJH e z) =
      qF
        (intrinsicFixedFieldPrimeRepresentative
          K H J hJH e z) := by
  unfold intrinsicFixedFieldFrobeniusSourceRestrictionResult
  unfold intrinsicFixedFieldSourceQuotientResult
  exact
    congrArg qF
      (intrinsicFixedFieldPrimeFrobeniusLift_restriction
        K H J hJH e z)

private theorem intrinsicFixedFieldPrimeFrobeniusLift_ambientRestriction
    (z : Abelianization Gal(E/F)) :
    intrinsicFixedFieldFrobeniusAmbientRestrictionResult
        K H J hJH e
        (intrinsicFixedFieldPrimeFrobeniusLift
          K H J hJH e z) =
      qF
        (intrinsicFixedFieldPrimeRepresentative
          K H J hJH e z) := by
  calc
    intrinsicFixedFieldFrobeniusAmbientRestrictionResult
          K H J hJH e
          (intrinsicFixedFieldPrimeFrobeniusLift
            K H J hJH e z) =
        intrinsicFixedFieldFrobeniusSourceRestrictionResult
          K H J hJH e
          (intrinsicFixedFieldPrimeFrobeniusLift
            K H J hJH e z) :=
      intrinsicFixedFieldFrobeniusAmbientRestrictionResult_eq
        K H J hJH e
        (intrinsicFixedFieldPrimeFrobeniusLift
          K H J hJH e z)
    _ =
      qF
        (intrinsicFixedFieldPrimeRepresentative
          K H J hJH e z) :=
      intrinsicFixedFieldPrimeFrobeniusSourceRestrictionResult_eq
        K H J hJH e z

private theorem intrinsicFixedFieldPrimeComparisonWitness_ambient
    (z : Abelianization Gal(E/F)) :
    intrinsicFixedFieldAmbientPrimeComparison
      K H J hJH e
      (intrinsicFixedFieldPrimeComparisonWitness
        K H J hJH e z) z := by
  let σ :=
    intrinsicFixedFieldPrimeFrobeniusLift
      K H J hJH e z
  let q :=
    intrinsicFixedFieldPrimeRepresentative
      K H J hJH e z
  let σH :=
    intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J hJH σH
  have hprime :=
    intrinsicFixedFieldFrobeniusPrimeNorm_ambient
      K H J hJH e σ
  have hrestriction : qH qAmbient = qF q := by
    simpa only [
      intrinsicFixedFieldFrobeniusAmbientRestrictionResult,
      intrinsicFixedFieldAmbientQuotientResult,
      σ, q, σH, qAmbient
    ] using
      intrinsicFixedFieldPrimeFrobeniusLift_ambientRestriction
        K H J hJH e z
  unfold intrinsicFixedFieldPrimeComparisonWitness
  unfold intrinsicFixedFieldAmbientPrimeComparison at hprime ⊢
  unfold intrinsicFixedFieldAmbientFrobeniusAbelianization at hprime
  calc
    _ = Additive.ofMul
        ((qH).abelianizationCongr
          (Abelianization.of qAmbient)) :=
      hprime
    _ = Additive.ofMul z := by
      apply Additive.ext
      exact
        (abelianizationCongr_of qH qAmbient).trans
          ((congrArg Abelianization.of hrestriction).trans
            ((abelianizationCongr_of qF q).symm.trans
              (intrinsicFixedFieldPrimeRepresentative_abelianization
                K H J hJH e z)))

private noncomputable def intrinsicFixedFieldPrimeComparison
    (z : Abelianization Gal(E/F)) :
    IntrinsicFixedFieldPrimeComparisonData
      K H J hJH e z :=
  { xPrime :=
      intrinsicFixedFieldPrimeComparisonWitness
        K H J hJH e z
    concrete :=
      intrinsicFixedFieldPrimeComparisonWitness_concrete
        K H J hJH e z
    ambient :=
      intrinsicFixedFieldPrimeComparisonWitness_ambient
        K H J hJH e z }

/-- Every abelianized Galois element of the intrinsic finite fixed-field
extension is represented by a unit with both its concrete norm-residue value
and its actual ambient fixed-field norm-residue value. -/
theorem exists_intrinsicFixedFieldPrimeComparison
    (z : Abelianization Gal(E/F)) :
    ∃ x : Fˣ,
      concreteNormResidueSymbolOfEmbedding
          F E iFE
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) x = z ∧
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) =
          Additive.ofMul z := by
  let comparison :=
    intrinsicFixedFieldPrimeComparison
      K H J hJH e z
  exact
    ⟨comparison.xPrime, comparison.concrete, comparison.ambient⟩

include e in
/-- Every unit of the intrinsic finite fixed field has a norm-class-equivalent
representative whose ambient fixed-field norm-residue value is the actual
local Artin value of the original unit. -/
theorem exists_intrinsicFixedFieldNormClassRepresentative
    (a : Fˣ) :
    ∃ x : Fˣ,
      normClass F E a = normClass F E x ∧
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) =
          intrinsicFixedFieldLocalArtinMonoidHom
            K H J hJH (Additive.ofMul a) := by
  let z : Abelianization Gal(E / F) :=
    concreteNormResidueSymbolOfEmbedding
      F E iFE
      (localResidueDatum F)
      (localHenselianValuation F)
      (separableClosureUnits_isClassFormation F) a
  obtain ⟨x, hxconcrete, hxambient⟩ :=
    exists_intrinsicFixedFieldPrimeComparison K H J hJH e z
  refine ⟨x, ?_, ?_⟩
  · apply
      (concreteReciprocityEquivOfEmbedding
        F E iFE
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)).symm.injective
    change
      concreteNormResidueSymbolOfEmbedding
          F E iFE
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) a =
        concreteNormResidueSymbolOfEmbedding
          F E iFE
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) x
    simpa only [z] using hxconcrete.symm
  · calc
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) =
          Additive.ofMul z :=
        hxambient
      _ = intrinsicFixedFieldLocalArtinMonoidHom
          K H J hJH (Additive.ofMul a) := by
        change Additive.ofMul z =
          Additive.ofMul (localArtinMonoidHom F E a)
        dsimp only [z]
        exact
          congrArg Additive.ofMul
            (DFunLike.congr_fun
              (localArtinMonoidHom_eq_of_embedding F E iFE) a).symm

end IntrinsicFixedFieldPrimeComparison

end LocalClassFieldTheory
