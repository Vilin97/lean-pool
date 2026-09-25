/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport
/-!
# Ambient Frobenius targets

This module identifies the ambient abelianized Frobenius target associated with a chosen
intrinsic lift and proves its compatibility with quotient equivalences.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Transporting an identified abelianized prime value back through one
quotient equivalence and forward through another preserves its target. -/
theorem abelianizationCongr_symm_eq_primeTarget
    {Q₀ G₀ G : Type}
    [Group Q₀] [Group G₀] [Group G]
    (q₀ : Q₀ ≃* G₀)
    (qE : Q₀ ≃* G)
    (qAmbient : Q₀)
    (r : Additive (Abelianization G₀))
    (hprime :
      r =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient))) :
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
      qE.abelianizationCongr
        (Abelianization.of qAmbient) := by
  have hprimeMul :=
    congrArg Additive.toMul hprime
  change
    Additive.toMul r =
      q₀.abelianizationCongr
        (Abelianization.of qAmbient) at hprimeMul
  calc
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
        qE.abelianizationCongr
          (q₀.abelianizationCongr.symm
            (q₀.abelianizationCongr
              (Abelianization.of qAmbient))) :=
      congrArg qE.abelianizationCongr
        (congrArg q₀.abelianizationCongr.symm hprimeMul)
    _ = qE.abelianizationCongr
          (Abelianization.of qAmbient) := by
      rw [q₀.abelianizationCongr.symm_apply_apply]

/-- The ambient abelianized Frobenius target associated with the same
chosen intrinsic Frobenius lift as the prime witness. -/
noncomputable def ambientEmbeddedPrimeTarget
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
    (z : Abelianization Gal(E/F)) :
    Abelianization Gal(E/F) := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
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
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K/K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  exact
    qE.abelianizationCongr
      (Abelianization.of qAmbient)

end LocalClassFieldTheory
