/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport
public import Mathlib.GroupTheory.Abelianization.Defs
/-!
# Ambient embedded norm-residue values

This module defines the ambient fixed-field norm-residue value attached
to a unit of the intrinsically presented base field, both before and
after identifying the abelianization of an abelian Galois group with
the group itself.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel
open scoped IsMulCommutative

/-- The separable-closure equivalence used to compare the intrinsic extension
over `F` with its realization inside the ambient separable closure of `K`. -/
abbrev ambientEmbeddedSeparableClosureEquiv
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    (j : E →ₐ[K] SeparableClosure K) :=
  @AlgEquiv F (SeparableClosure F) (SeparableClosure K)
    _ _ _
    (separableClosure F (AlgebraicClosure F)).algebra
    (j.comp (IsScalarTower.toAlgHom K F E)).toRingHom.toAlgebra

/-- A finite fixed-field presentation of an embedded finite Galois extension.

The object records the actual ambient fixed-field quotient, its realization of
the embedded base field, and the quotient map to the original Galois group.
It is the common interface for calculations that use the ambient
norm-residue value without unfolding the construction of that presentation. -/
structure AmbientEmbeddedFixedFieldPresentation
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) where
  /-- The given base field embedded in the ambient separable closure. -/
  baseEmbedding : F →ₐ[K] SeparableClosure K
  /-- The finite ambient fixed field representing the embedded base field. -/
  base : FiniteAbstractField Gal(SeparableClosure K/K)
  /-- The finite Galois ambient fixed-field extension representing `E / F`. -/
  extension : FiniteGaloisSubextension base.field
  /-- The base embedding is induced by the embedding of the top field. -/
  baseEmbedding_eq :
    baseEmbedding = j.comp (IsScalarTower.toAlgHom K F E)
  /-- The ambient base subgroup fixes precisely the range of the base embedding. -/
  base_field_eq :
    base.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange baseEmbedding)
  /-- The ambient top subgroup fixes precisely the range of the top embedding. -/
  extension_field_eq :
    extension.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange j)
  /-- The actual equivalence from the given base field to its ambient fixed field. -/
  baseEquiv :
    F ≃ₐ[K] abstractFixedField K (SeparableClosure K) base.field
  /-- The base-field equivalence realizes the chosen ambient embedding. -/
  baseEquiv_apply (x : F) :
    ((baseEquiv x :
      abstractFixedField K (SeparableClosure K) base.field) :
        SeparableClosure K) =
      baseEmbedding x
  /-- The actual quotient equivalence to the original Galois group. -/
  quotientEquiv : extension.extensionQuotient ≃* Gal(E/F)
  /-- The quotient equivalence acts through the supplied ambient embedding. -/
  quotientEquiv_mk_apply
      (sigma : base.field.toSubgroup) (x : E) :
    j (quotientEquiv (extension.extensionQuotientMk sigma) x) =
      sigma.1 (j x)

namespace AmbientEmbeddedFixedFieldPresentation

/-- The canonical quotient equivalence from an ambient finite fixed-field
extension to the Galois group of its relative fixed field. -/
noncomputable def fixedFieldQuotientEquiv
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j) :
    P.extension.extensionQuotient ≃*
      Gal(abstractRelativeFixedField K (SeparableClosure K)
        P.extension.below/abstractFixedField K (SeparableClosure K) P.base.field) :=
  P.extension.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) P.base.field P.extension.field
      P.extension.below P.extension.normal)

/-- The actual additive equivalence obtained by transporting abelianized
relative fixed-field Galois elements through an ambient fixed-field
presentation. -/
noncomputable def abelianizedTransport
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j) :
    Additive
      (Abelianization
        Gal(abstractRelativeFixedField K (SeparableClosure K)
          P.extension.below/abstractFixedField K (SeparableClosure K) P.base.field)) ≃+
      Additive (Abelianization Gal(E/F)) :=
  (P.fixedFieldQuotientEquiv.abelianizationCongr.toAdditive.symm).trans
    P.quotientEquiv.abelianizationCongr.toAdditive

/-- Evaluate the ambient fixed-field norm-residue construction using this
presentation's actual finite quotient and base-field realization. -/
noncomputable def normResidueAbelianElement
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j)
    (a : Fˣ) : Abelianization Gal(E/F) := by
  letI : (extensionSubgroup
      P.base.field P.extension.field P.extension.below).Normal :=
    P.extension.normal
  letI : Finite
      (P.base.field.toSubgroup ⧸
        extensionSubgroup P.base.field P.extension.field
          P.extension.below) :=
    P.extension.finite
  letI : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          P.base.field (le_baseField P.base.field)) :=
    P.base.finite
  exact
    Additive.toMul
      (P.abelianizedTransport
        (abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          P.base.field P.extension.field P.extension.below
          (Additive.ofMul
            (Units.mapEquiv P.baseEquiv.toMulEquiv a))))

/-- The presentation-level evaluation formula for the ambient norm-residue
value.  It exposes only the actual finite quotient equivalences carried by
the presentation. -/
theorem normResidueAbelianElement_apply
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j)
    (a : Fˣ) :
    letI : (extensionSubgroup
        P.base.field P.extension.field P.extension.below).Normal :=
      P.extension.normal
    letI : Finite
        (P.base.field.toSubgroup ⧸
          extensionSubgroup P.base.field P.extension.field
            P.extension.below) :=
      P.extension.finite
    letI : Finite
        ((baseField
          Gal(SeparableClosure K/K)).toSubgroup ⧸
          extensionSubgroup
            (baseField Gal(SeparableClosure K/K))
            P.base.field (le_baseField P.base.field)) :=
      P.base.finite
    P.normResidueAbelianElement a =
      P.quotientEquiv.abelianizationCongr
        (P.fixedFieldQuotientEquiv.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              P.base.field P.extension.field P.extension.below
              (Additive.ofMul
                (Units.mapEquiv P.baseEquiv.toMulEquiv a))))) :=
  rfl

end AmbientEmbeddedFixedFieldPresentation

/-- The canonical ambient fixed-field presentation of an embedded finite
Galois local extension. -/
noncomputable def ambientEmbeddedFixedFieldPresentation
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j) :
    AmbientEmbeddedFixedFieldPresentation K F E j := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI _hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI _hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI _hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
        H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K/K) :=
    ⟨H₀, _hHabsolute⟩
  let T : FiniteGaloisSubextension H.field :=
    ⟨J₀, hJH, _hTargetNormal, _hTargetFinite⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  refine
    { baseEmbedding := i
      base := H
      extension := T
      baseEmbedding_eq := rfl
      base_field_eq := rfl
      extension_field_eq := rfl
      baseEquiv := phiF
      baseEquiv_apply := ?_
      quotientEquiv := T.extensionQuotientMulEquiv.trans qE
      quotientEquiv_mk_apply := ?_ }
  · intro x
    rfl
  · intro sigma x
    change
      j (qE
        (T.extensionQuotientMulEquiv
          (T.extensionQuotientMk sigma)) x) =
        sigma.1 (j x)
    rw [T.extensionQuotientMk_apply]
    exact
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
        K F E j e sigma x

/-- The abelianized ambient fixed-field norm-residue value attached to a unit
of the intrinsically presented base field. -/
noncomputable def ambientEmbeddedNormResidueAbelianElement
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (a : Fˣ) : Abelianization Gal(E/F) :=
  (ambientEmbeddedFixedFieldPresentation K F E j e).normResidueAbelianElement a

/-- The ambient fixed-field norm-residue value in `Gal(E/F)`, obtained
from its abelianized value using the canonical equivalence for an abelian extension. -/
noncomputable def ambientEmbeddedNormResidueElement
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (a : Fˣ) : Gal(E/F) :=
  (Abelianization.equivOfComm (H := Gal(E/F))).symm
    (ambientEmbeddedNormResidueAbelianElement K F E j e a)

end LocalClassFieldTheory
