/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
/-!
# Naturality of the global norm-residue symbol

This file records the same-base restriction specialization of abstract
norm-residue naturality in the rational absolute class formation.  All
closed subgroups remain in one fixed separable-closure ambient, so the
statement is directly usable by fixed-field overextension arguments.
-/

open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u

@[instance_reducible]
private noncomputable def naturalityIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] naturalityIdeleClassCommGroup

local instance ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative


/-- Two finite Galois subextensions with the same underlying closed subgroup
are equal; the remaining structure fields are proof-irrelevant. -/
private theorem finiteGaloisSubextension_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    (A B : FiniteGaloisSubextension K)
    (h : A.field = B.field) :
    A = B := by
  cases A with
  | mk A hA nA fA =>
      cases B with
      | mk B hB nB fB =>
          dsimp only at h
          cases h
          rfl

/-- Rebase a finite Galois subextension along equality of its bundled base.
The field equality is the only data component; the remaining fields are
proof-irrelevant. -/
private theorem finiteGaloisSubextension_transport_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    (Q : FiniteGaloisSubextension B.field)
    (hfield : P.field = Q.field) :
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField G =>
          FiniteGaloisSubextension X.field)
        hAB)
      P = Q := by
  cases hAB
  exact finiteGaloisSubextension_eq_of_field_eq P Q hfield

/-- Transporting an additive equivalence between rational ambient fixed
subgroups does not change the underlying direct-limit class. -/
private theorem rationalAmbientFixedAddEquiv_transport_apply_val
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    {X : Type} [AddGroup X]
    (e : X ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (x : X) :
    ((Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            X ≃+ ambientFixedAddSubgroup
              rationalIdeleClassRepresentation Y.field)
          hAB)
        e x).1) =
      (e x).1 := by
  cases hAB
  rfl

/-- Changing only the bundled subgroup of an additive subgroup element
does not change its value in the ambient group. -/
private theorem addSubgroupCongr_apply_val
    {A : Type} [AddGroup A]
    {H K : AddSubgroup A}
    (h : H = K) (x : H) :
    ((AddEquiv.addSubgroupCongr h x).1 : A) = x.1 := by
  cases h
  rfl

/-- Transporting an idele class along a field equality and the corresponding
algebra equivalence leaves its rational direct-limit representative fixed. -/
private theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]

/-- Transporting the target intermediate field of a base-field equivalence
preserves its rational fixed-part representative. -/
private theorem rationalIdeleClassEquivFixed_transport_baseEquiv_val
    {T : Type} [Field T] [NumberField T]
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B) (e : T ≃ₐ[ℚ] B)
    (c : IdeleClassGroup T) :
    ((rationalIdeleClassEquivFixed A)
      (Additive.ofMul
        (ideleClassCongr (K := T) (M := A)
          (e.trans (IntermediateField.equivOfEq h).symm) c))).1 =
    ((rationalIdeleClassEquivFixed B)
      (Additive.ofMul (ideleClassCongr (K := T) (M := B) e c))).1 := by
  cases h
  have he :
      e.trans (IntermediateField.equivOfEq (rfl : A = A)).symm = e := by
    ext x
    rfl
  rw [he]

/-- Equality of the lower and upper closed subgroups transports the raw
extension quotient without exposing dependent rewrites to clients. -/
private def extensionQuotientMulEquivOfEq
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal] :
    (H.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H J hJH) ≃*
      (H'.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H' J' hJH') := by
  cases hH
  cases hJ
  exact MulEquiv.refl _

/-- The quotient transport sends a quotient representative to the same
ambient group element, rebundled in the equal lower subgroup. -/
@[simp]
private theorem extensionQuotientMulEquivOfEq_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal]
    (σ : H.toSubgroup) :
    extensionQuotientMulEquivOfEq hH hJ hJH hJH'
        (QuotientGroup.mk σ) =
      QuotientGroup.mk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup hH)) σ) := by
  cases hH
  cases hJ
  rfl

/-- Rebundling an element along equality of closed subgroups preserves its
underlying ambient group element. -/
private theorem closedSubgroupCongr_apply_val
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' : ClosedSubgroup G}
    (hH : H = H') (σ : H.toSubgroup) :
    (((MulEquiv.subgroupCongr
        (congrArg ClosedSubgroup.toSubgroup hH)) σ).1 : G) = σ.1 := by
  cases hH
  rfl

/-- Rebase an abelianized extension-quotient equivalence together with its
finite abstract base. -/
private def abelianizedExtensionQuotientAddEquiv_transportBase
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive
        (Abelianization
          (Eq.mp
            (congrArg
              (fun Y : FiniteAbstractField G =>
                FiniteGaloisSubextension Y.field)
              hAB)
            P).extensionQuotient) ≃+ X := by
  cases hAB
  exact e

/-- Rebase an abelianized equivalence along equality of finite Galois
subextensions over a fixed abstract base. -/
private def abelianizedExtensionQuotientAddEquiv_transportExtension
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    {P Q : FiniteGaloisSubextension K}
    (hPQ : P = Q)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive (Abelianization Q.extensionQuotient) ≃+ X := by
  cases hPQ
  exact e

/-- The explicit quotient equivalence induced by rebasing a finite Galois
subextension. -/
private def extensionQuotientMulEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q) :
    Q.extensionQuotient ≃* P.extensionQuotient := by
  cases hAB
  cases hPQ
  exact MulEquiv.refl _

/-- Quotient rebasing sends a canonical representative to the same ambient
group element rebundled in the old base subgroup. -/
@[simp]
private theorem extensionQuotientMulEquiv_transportFiniteGalois_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    (σ : B.field.toSubgroup) :
    extensionQuotientMulEquiv_transportFiniteGalois hAB P hPQ
        (Q.extensionQuotientMk σ) =
      P.extensionQuotientMk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup
            (congrArg FiniteAbstractField.field hAB).symm)) σ) := by
  cases hAB
  cases hPQ
  rfl

/-- Abelianization commutes with simultaneous transport of the abstract base
and its finite Galois subextension. -/
private theorem abelianizedCanonicalEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    {X : Type} [CommGroup X]
    (e : P.extensionQuotient ≃* X) :
    abelianizedExtensionQuotientAddEquiv_transportExtension hPQ
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P
          (MulEquiv.toAdditive
            (e.abelianizationCongr.trans
              (Abelianization.equivOfComm : X ≃* Abelianization X).symm))) =
      MulEquiv.toAdditive
        (((extensionQuotientMulEquiv_transportFiniteGalois
            hAB P hPQ).trans e).abelianizationCongr.trans
          (Abelianization.equivOfComm : X ≃* Abelianization X).symm) := by
  cases hAB
  cases hPQ
  rfl

/-- Package the entire rational finite norm-residue evaluation so that its
dependent base, extension, quotient and comparison maps move together. -/
private def rationalFiniteNormResidueValue
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) : X := by
  letI :
      Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field L.field L.below) :=
    L.finite
  exact
    eGalois
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L
        (finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below (eIdele c)))

/-- The packaged norm-residue value is invariant under rebasing the finite
abstract field together with all dependent data. -/
private theorem rationalFiniteNormResidueValue_transportBase
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A P eIdele eGalois c =
      rationalFiniteNormResidueValue B
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAB)
          P)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAB)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P eGalois)
        c := by
  cases hAB
  rfl

/-- The packaged norm-residue value is invariant under equality of the finite
Galois subextension. -/
private theorem rationalFiniteNormResidueValue_transportExtension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    {P Q : FiniteGaloisSubextension K.field}
    (hPQ : P = Q)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue K P eIdele eGalois c =
      rationalFiniteNormResidueValue K Q eIdele
        (abelianizedExtensionQuotientAddEquiv_transportExtension
          hPQ eGalois)
        c := by
  cases hPQ
  rfl

/-- Evaluation of the canonical abelianization comparison induced by a
multiplicative equivalence into a commutative group. -/
private theorem abelianizationCongrToComm_apply
    {Q R : Type*} [Group Q] [CommGroup R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        (e.abelianizationCongr.trans
          (Abelianization.equivOfComm : R ≃* Abelianization R).symm)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm
        (e.abelianizationCongr (Abelianization.of q)) = e q
  rw [abelianizationCongr_of]
  exact
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm_apply_apply _

/-- Evaluation of the canonical quotient from the abelianization of a
commutative group. -/
private theorem commutativeAbelianizationEquiv_apply
    {Q R : Type*} [CommGroup Q] [Group R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm.trans e)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    e ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm
      (Abelianization.of q)) = e q
  exact congrArg e
    ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm_apply_apply q)

section AbstractFixedFieldInclusion

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

local instance naturalityAbstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

local instance naturalityAbstractFixedFieldRelativeQuotientFinite :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H.field P.field P.below) :=
  P.finite

noncomputable local instance
    naturalityAbstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    naturalityAbstractRelativeFixedFieldFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below H.finite P.finite

local instance naturalityAbstractFixedFieldRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance naturalityAbstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

/-- Use the same direct fixed-field Galois witness as the intrinsic
norm-residue construction.  This prevents the dependent Galois-group type
from being synthesized through a second `IsAbelianGalois` instance path. -/
noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below P.normal

noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsAbelianGalois :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P

/-- The lower subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original lower closed subgroup. -/
private theorem
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedBaseSubgroup F E j = H.field := by
  dsimp only
  have hi :
      numberFieldEmbeddedLowerEmbedding
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below)
          ((abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) =
        (abstractFixedField
          ℚ (SeparableClosure ℚ) H.field).val := by
    ext x
    rfl
  have hRange :
      (numberFieldEmbeddedLowerEmbedding
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below)
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ)).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) H.field := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change
        numberFieldEmbeddedLowerEmbedding
            (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below)
            ((abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) y ∈
          abstractFixedField ℚ (SeparableClosure ℚ) H.field
      rw [hi]
      exact y.property
    · intro hx
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hi]
      rfl
  rw [numberFieldEmbeddedBaseSubgroup, hRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) H.field

/-- The upper subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original upper closed subgroup. -/
private theorem
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedTopSubgroup F E j = P.field := by
  dsimp only
  rw [numberFieldEmbeddedTopSubgroup]
  have hjRangeSelf :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).restrictScalars ℚ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hjRange :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) P.field := by
    exact hjRangeSelf.trans
      (IntermediateField.extendScalars_restrictScalars
        (abstractFixedField_le
          ℚ (SeparableClosure ℚ) P.below))
  rw [hjRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) P.field

/-- Transport a packaged rational norm-residue value directly from an equal
abstract base to the finite Galois extension underlying `P`.  Keeping the two
dependent transports in their own declaration prevents their elaboration cost
from accumulating in the main fixed-field comparison theorem. -/
private theorem rationalFiniteNormResidueValue_transportToAbstractExtension
    {A : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAH : A = H)
    (L : FiniteGaloisSubextension A.field)
    (hLP :
      Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L =
        P.toFiniteGaloisExtension)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A L eIdele eGalois c =
      rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportExtension hLP
          (abelianizedExtensionQuotientAddEquiv_transportBase
            hAH L eGalois))
        c := by
  calc
    _ = rationalFiniteNormResidueValue H
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c :=
      rationalFiniteNormResidueValue_transportBase
        (A := A) (B := H) (C := C) (X := X)
        hAH L eIdele eGalois c
    _ = _ :=
      rationalFiniteNormResidueValue_transportExtension
        (K := H)
        (P := Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Q := P.toFiniteGaloisExtension) (C := C) (X := X)
        hLP
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c

/-- The packaged value at the literal fixed-field realization is the ambient
fixed-part norm-residue homomorphism evaluated at the same idele class. -/
private theorem rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
        (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
        (Additive.ofMul c) =
      ambientFixedGlobalNormResidueAddMonoidHom H P
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          H.field (Additive.ofMul c)) := by
  let eRec :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      H P.toFiniteGaloisExtension
  let eGal :=
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P
  change
    eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c)))) =
      eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c))))
  rfl

/-- The packaged norm-residue value for the literal fixed-field realization
is the intrinsic abstract fixed-field norm-residue value. -/
private theorem rationalFiniteNormResidueValue_abstractFixedField_apply
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    Additive.toMul
        (rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
          (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
            H P)
          (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c := by
  let a :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      H.field (Additive.ofMul c)
  have hAbstract :=
    abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply H P a
  calc
    _ = Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom H P
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field (Additive.ofMul c))) := by
      exact congrArg Additive.toMul
        (rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
          (H := H) (P := P) c)
    _ = _ := by
      simpa only [a, AddEquiv.symm_apply_apply, toMul_ofMul] using
        hAbstract.symm

/-- The finite abstract field reconstructed from the literal fixed-field
inclusion is the original packaged abstract field.  Keeping this structure
equality separate avoids repeatedly rebuilding all of its proof fields. -/
private theorem
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedFiniteAbstractField F E j = H := by
  dsimp only
  exact FiniteAbstractField.eq_of_field_eq _ _
    (numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P)

/-- Pointwise specification of the idele-class comparison after transporting
the explicitly embedded abstract field to the canonical packaged field.  The
transport is kept at the value boundary, so clients never compare the two
dependent additive equivalences themselves. -/
private theorem
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    let HEmbedded :=
      numberFieldEmbeddedFiniteAbstractField F E j
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            Additive (IdeleClassGroup F) ≃+
              ambientFixedAddSubgroup
                rationalIdeleClassRepresentation X.field)
          hHEmbedded)
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c =
      rationalAbstractFixedFieldIdeleClassEquivFixed H.field c := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hHEmbedded :
      numberFieldEmbeddedFiniteAbstractField F E j = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hFixedBase :
      abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j) = F :=
    congrArg
      (abstractFixedField ℚ (SeparableClosure ℚ)) hBase
  let eBase : F ≃ₐ[ℚ] F :=
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j).trans
      (IntermediateField.equivOfEq hFixedBase)
  have heBase :
      eBase = (AlgEquiv.refl : F ≃ₐ[ℚ] F) := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change x.1 = x.1
    rfl
  let hEmbeddedQuotientFinite :=
    numberFieldEmbeddedAbsoluteQuotientFinite F E j
  let hEmbeddedFixedFiniteDimensional :=
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional F E j
  apply Subtype.ext
  rw [rationalAmbientFixedAddEquiv_transport_apply_val
    hHEmbedded
    (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c]
  dsimp only [numberFieldEmbeddedIdeleClassEquivAmbientFixed]
  simp only [AddEquiv.trans_apply]
  change
    ((rationalIdeleClassEquivFixed
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j)))
      (MulEquiv.toAdditive
        (ideleClassCongr
          (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)) c)).1 =
      ((rationalIdeleClassEquivFixed F) c).1
  exact rationalIdeleClassEquivFixed_congr_apply_val
    hFixedBase
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)
    heBase c

/-- Transporting the finite Galois subextension reconstructed from the literal
fixed-field inclusion recovers the canonical subextension packaged by `P`.
This is the sole dependent structure equality used by the later quotient
comparisons. -/
private theorem
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    let HEmbedded :=
      numberFieldEmbeddedFiniteAbstractField F E j
    let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
      numberFieldEmbeddedFiniteGaloisSubextension F E j
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            FiniteGaloisSubextension X.field)
          hHEmbedded)
        PEmbedded =
      P.toFiniteGaloisExtension := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  exact finiteGaloisSubextension_transport_eq_of_field_eq
    hHEmbedded PEmbedded P.toFiniteGaloisExtension
    (numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P)

/-- Opaque endpoint for the extension-quotient comparison supplied by the
literal embedding.  Its domain is already the canonical quotient of `P`, so
no client has to reconstruct the two subgroup transports. -/
private noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  letI hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  letI hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      ((extensionQuotientMulEquivOfEq
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).trans
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep))

/-- Opaque canonical endpoint for the same quotient, obtained directly from
the abstract fixed-field realization. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field P.field P.below P.normal)

/-- Pointwise opaque endpoint of the embedded quotient equivalence. -/
private noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv H P q

/-- Pointwise opaque endpoint of the canonical quotient equivalence. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P q

/-- Fully applied ambient value of the embedded quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- Fully applied ambient value of the canonical quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- The ambient Galois value attached to a representative of the canonical
quotient, packaged behind a literal result type. -/
private noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  letI hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  letI hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  exact
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      ℚ F E j eSep (QuotientGroup.mk σEmbedded)

/-- Fully applied ambient value of the packaged representative endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ x :
    SeparableClosure ℚ)

/-- Ambient action of the representative after rebundling it in the embedded
base subgroup. -/
private noncomputable def
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  exact σEmbedded.1.1 (x : SeparableClosure ℚ)

/-- The embedded quotient endpoint sends a canonical representative to the
packaged ambient value above. -/
private theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  simp only [
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact congrArg
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
    (extensionQuotientMulEquivOfEq_mk
      hBase.symm hTop.symm P.below
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)

/-- The packaged ambient endpoint evaluates to the action of the rebundled
representative. -/
private theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hmk :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
      ℚ F E j eSep σEmbedded x
  change
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep (QuotientGroup.mk σEmbedded) x :
        SeparableClosure ℚ) =
      σEmbedded.1.1 (x : SeparableClosure ℚ) at hmk
  simpa only [
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal] using hmk

/-- Rebundling the representative does not change its action in the ambient
separable closure. -/
private theorem
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hσEmbedded :
      (σEmbedded.1 : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) = σ.1 :=
    closedSubgroupCongr_apply_val hBase.symm σ
  change σEmbedded.1.1 (x : SeparableClosure ℚ) = _
  rw [hσEmbedded]

/-- The packaged ambient representative acts by the original automorphism on
the underlying separable-closure value. -/
private theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  exact
    (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
      H P σ x).trans
      (abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq H P σ x)

/-- Evaluation of the embedded quotient endpoint on a canonical quotient
representative, stated only in the ambient separable closure. -/
private theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  calc
    _ = abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
        H P σ x := by
      exact congrArg
        (fun g => (g x : SeparableClosure ℚ))
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
          H P σ)
    _ = _ :=
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
        H P σ x

/-- Evaluation of the canonical abstract quotient endpoint on a quotient
representative, again exposed only through its ambient value. -/
private theorem
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  simp only [
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal,
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue,
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact
    (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field P.field P.below P.normal σ x).symm

/-- The embedded and canonical quotient endpoints agree on each quotient
class.  This pointwise boundary is intentionally weaker than equality of the
dependent `MulEquiv` structures. -/
private theorem
    abstractFixedFieldInclusionExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q)
    q ?_
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact
    (abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
      H P σ x).trans
      (abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
        H P σ x).symm

/-- Opaque quotient endpoint obtained by transporting the explicitly embedded
finite Galois subextension back to the canonical package. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  exact
    (extensionQuotientMulEquiv_transportFiniteGalois
      hHEmbedded PEmbedded hPEmbedded).trans
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j)

/-- Pointwise opaque endpoint of the transported quotient equivalence. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P q

/-- Transporting a canonical representative of the embedded finite Galois
package preserves its Galois value. -/
private theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  have hFieldEq :
      (congrArg FiniteAbstractField.field hHEmbedded).symm = hBase.symm :=
    Subsingleton.elim _ _
  simp only [
    abstractFixedFieldInclusionTransportedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    extensionQuotientMulEquiv_transportFiniteGalois_mk,
    FiniteGaloisSubextension.extensionQuotientMk_apply,
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup]
  rw [hFieldEq]
  change
    ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep
        (QuotientGroup.mk
          ((MulEquiv.subgroupCongr
            (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ)) = _
  exact
    (congrArg
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
      (extensionQuotientMulEquivOfEq_mk
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)).symm

/-- Transporting the embedded finite Galois package preserves the value of
its extension-quotient comparison. -/
private theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q)
    q ?_
  intro σ
  exact abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    H P σ

/-- Opaque abelianized equivalence obtained by transporting the explicitly
embedded finite Galois package to the canonical one. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  exact
    abelianizedExtensionQuotientAddEquiv_transportExtension hPEmbedded
      (abelianizedExtensionQuotientAddEquiv_transportBase
        hHEmbedded PEmbedded
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          F E j))

/-- Canonical abelianization comparison built from the already transported
opaque extension-quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let Q :=
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field))
  exact
    MulEquiv.toAdditive
      ((MulEquiv.abelianizationCongr
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P)).trans
          (Abelianization.equivOfComm : Q ≃* Abelianization Q).symm)

/-- Pointwise opaque value of the transported abelianized equivalence. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldInclusionTransportedAbelianizedEquiv H P z

/-- Pointwise opaque value of the canonical abelianization comparison built
from the transported quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv H P z

/-- Pointwise opaque value of the intrinsic abstract fixed-field
abelianization comparison. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P z

/-- The transported abelianized endpoint agrees pointwise with the canonical
abelianization comparison built from the transported quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
        H P z := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let qEmbedded : PEmbedded.extensionQuotient ≃* Gal(E / F) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j
  have hCanonical :
      abstractFixedFieldInclusionTransportedAbelianizedEquiv H P =
        abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
          H P := by
    simpa only [
      abstractFixedFieldInclusionTransportedAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup,
      qEmbedded] using
      (abelianizedCanonicalEquiv_transportFiniteGalois
        hHEmbedded PEmbedded hPEmbedded qEmbedded)
  exact DFunLike.congr_fun hCanonical z

/-- On an abelianization representative, the transported canonical endpoint
is the additive value of the transported quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) := by
  simpa only [
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue,
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
    abstractFixedFieldInclusionTransportedExtensionQuotientValue] using
    (abelianizationCongrToComm_apply
      (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P) q)

/-- On the same representative, the intrinsic fixed-field endpoint is the
additive value of the canonical quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) := by
  let hRawQuotientCommGroup :
      CommGroup P.toFiniteGaloisExtension.extensionQuotient :=
    { (inferInstance :
        Group P.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := P.commutative.is_comm.comm }
  let qAbstractRaw :=
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P
  change
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm :
          P.toFiniteGaloisExtension.extensionQuotient ≃*
            Abelianization
              P.toFiniteGaloisExtension.extensionQuotient).symm.trans
          qAbstractRaw)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (qAbstractRaw q)
  exact commutativeAbelianizationEquiv_apply qAbstractRaw q

/-- The canonical abelianization comparison built after transport agrees
pointwise with the intrinsic abstract fixed-field comparison. -/
private theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z := by
  let q : P.toFiniteGaloisExtension.extensionQuotient :=
    Quotient.out z.toMul
  have hz : Additive.ofMul (Abelianization.of q) = z := by
    apply Additive.ext
    exact Quotient.out_eq' z.toMul
  rw [← hz]
  calc
    _ = Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) :=
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
        H P q
    _ = Additive.ofMul
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
          H P q)
    _ = Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionExtensionQuotientEquiv_apply H P q)
    _ = _ :=
      (abstractFixedFieldInclusionCanonicalAbelianizedValue_of H P q).symm

/-- The transported abelianized equivalence agrees pointwise with the
intrinsic abstract fixed-field Galois comparison. -/
private theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z :=
  (abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    H P z).trans
    (abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
      H P z)

/-- Opaque packaged norm-residue value before transporting the explicitly
embedded abstract field and finite Galois package. -/
private noncomputable def
    abstractFixedFieldInclusionEmbeddedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  exact
    rationalFiniteNormResidueValue HEmbedded PEmbedded
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j)
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        F E j)
      c

/-- Opaque packaged value after transporting both dependent structures to
the canonical `H` and `P` endpoints. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eIdeleOverH :
      Additive (IdeleClassGroup F) ≃+
        ambientFixedAddSubgroup rationalIdeleClassRepresentation H.field :=
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
          Additive (IdeleClassGroup F) ≃+
            ambientFixedAddSubgroup
              rationalIdeleClassRepresentation X.field)
        hHEmbedded)
      eIdeleEmbedded
  exact
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
      eIdeleOverH
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      c

/-- Opaque intrinsic packaged norm-residue value at the canonical endpoints. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
    (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
    (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
    c

/-- Simultaneous transport of the embedded abstract field and finite Galois
package sends the embedded norm-residue value to the transported endpoint. -/
private theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionTransportedNormResidueValue H P c := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eGaloisEmbedded :=
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup F E j
  simpa only [
    abstractFixedFieldInclusionEmbeddedNormResidueValue,
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionTransportedAbelianizedEquiv,
    eIdeleEmbedded,
    eGaloisEmbedded] using
    (rationalFiniteNormResidueValue_transportToAbstractExtension
      (H := H) (P := P)
      (A := HEmbedded)
      (C := Additive (IdeleClassGroup F))
      (X := Additive Gal(E / F))
      hHEmbedded PEmbedded hPEmbedded
      eIdeleEmbedded eGaloisEmbedded c)

/-- A packaged finite norm-residue value depends only on the value of its
idele comparison at the chosen input and the value of its Galois comparison
at the resulting norm class. -/
private theorem rationalFiniteNormResidueValue_congr_apply
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele eIdele' : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois eGalois' :
      Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C)
    (heIdele : eIdele c = eIdele' c)
    (heGalois : ∀ z, eGalois z = eGalois' z) :
    rationalFiniteNormResidueValue K L eIdele eGalois c =
      rationalFiniteNormResidueValue K L eIdele' eGalois' c := by
  unfold rationalFiniteNormResidueValue
  rw [heIdele]
  exact heGalois _

/-- The transported packaged value is the intrinsic canonical packaged value;
only the idele input and the eventual abelianized value are compared. -/
private theorem
    abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionTransportedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eIdeleOverH :
      Additive (IdeleClassGroup F) ≃+
        ambientFixedAddSubgroup rationalIdeleClassRepresentation H.field :=
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
          Additive (IdeleClassGroup F) ≃+
            ambientFixedAddSubgroup
              rationalIdeleClassRepresentation X.field)
        hHEmbedded)
      eIdeleEmbedded
  simpa only [
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionCanonicalNormResidueValue,
    eIdeleEmbedded,
    eIdeleOverH] using
    (rationalFiniteNormResidueValue_congr_apply
      H P.toFiniteGaloisExtension
      eIdeleOverH
      (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
      c
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply H P c)
      (fun z => abstractFixedFieldInclusionTransportedAbelianizedValue_eq
        H P z))

/-- The explicitly embedded and intrinsic packaged norm-residue values agree. -/
private theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c :=
  (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    H P c).trans
    (abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
      H P c)

/-- For the literal fixed fields attached to an abstract finite abelian
extension, the norm-residue map obtained from their canonical inclusion in
the rational separable closure is the intrinsic fixed-field norm-residue
map. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    globalNormResidueMonoidHomOfEmbedding F E j =
      abstractFixedFieldGlobalNormResidueMonoidHom H P := by
  dsimp only
  apply MonoidHom.ext
  intro c
  rw [globalNormResidueMonoidHomOfEmbedding_apply]
  change
    Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue
          H P (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c
  calc
    _ = Additive.toMul
        (abstractFixedFieldInclusionCanonicalNormResidueValue
          H P (Additive.ofMul c)) :=
      congrArg Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
          H P (Additive.ofMul c))
    _ = _ := by
      simpa only [abstractFixedFieldInclusionCanonicalNormResidueValue] using
        (rationalFiniteNormResidueValue_abstractFixedField_apply
          (H := H) (P := P) c)

end AbstractFixedFieldInclusion

section EmbeddedNumberFieldRestriction

variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']


/-- Rebracketing the compatible tower does not change its embedded lower
fixing subgroup. -/
private theorem numberFieldEmbeddedBaseSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
  have hi :
      numberFieldEmbeddedLowerEmbedding K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j) =
        numberFieldEmbeddedLowerEmbedding K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
    ext x
    simp only [numberFieldEmbeddedLowerEmbedding, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  simp only [numberFieldEmbeddedBaseSubgroup, hi]

omit [Field K] [NumberField K]
    [Algebra K K'] [Algebra K L'] [IsScalarTower K K' L'] in
/-- The top subgroup of the rebracketed base-change tower is the embedded
fixing subgroup of the intermediate field. -/
private theorem numberFieldEmbeddedTopSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K' L' j := by
  rfl

/-- Reidentify the two presentations of the embedded lower fixing subgroup
without transporting dependent subgroup data through an equality. -/
private noncomputable def numberFieldEmbeddedBaseChangeBaseEquiv
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ≃*
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup :=
  MulEquiv.subgroupCongr
    (congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedBaseSubgroup_baseChange_eq K K' L L' j))

/-- Under the identity equivalence of the two lower fixing subgroups, the
relative subgroup for the base change is exactly the target presentation. -/
private theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))).map
          (numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j).toMonoidHom =
      CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))
        (numberFieldEmbeddedBaseSubgroup K' L' j)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hTop :
      (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup =
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup :=
    congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedTopSubgroup_baseChange_eq
        (K := K) (K' := K') (L' := L') j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change
      ((e y :
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_apply, ← hTop]
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change
      (((e.symm x :
          (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup)
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_symm_apply, hTop]
    exact hx

/-- Normality of the relative subgroup between the two embedded base fields
in a finite Galois base change. -/
private theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_normal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hNormal :=
    (numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)).map
        e.toMonoidHom e.surjective
  rw [numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    K K' L L' j] at hNormal
  exact hNormal

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal :=
  numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j

/-- Finiteness of the relative quotient between the two embedded base fields
in a finite Galois base change. -/
private theorem numberFieldEmbeddedBaseChangeExtensionQuotient_finite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  let N :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
  let M :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
  let hNNormal : N.Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  let hMNormal : M.Normal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j
  let hNFinite :
      Finite
        ((numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) :=
    numberFieldEmbeddedExtensionQuotient_finite K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  have hmap : N.map e.toMonoidHom = M :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq K K' L L' j
  have hle : N ≤ M.comap e.toMonoidHom := by
    rw [← hmap]
    exact Subgroup.le_comap_map e.toMonoidHom N
  let f :
      ((numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) →*
        ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.map N M e.toMonoidHom hle
  have hmk : Function.Surjective
      (QuotientGroup.mk ∘ e :
        (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup →
          (numberFieldEmbeddedBaseSubgroup K L
              (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.mk_surjective.comp e.surjective
  have hsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective
      (N := N) M e.toMonoidHom hmk hle
  exact Finite.of_surjective f hsurj

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  numberFieldEmbeddedBaseChangeExtensionQuotient_finite K K' L L' j

/-- Reuse the canonical absolute fixed-field witness for the lower embedded
tower.  The base-change relative witness below needs this exact instance path
when forming the absolute finite-dimensional tower. -/
noncomputable local instance
    numberFieldEmbeddedBaseChangeBaseFixedFieldFiniteDimensional
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))) :=
  numberFieldEmbeddedAbstractFixedFieldFiniteDimensional K L
    (j.comp (IsScalarTower.toAlgHom ℚ L L'))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j)

local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldScalarTower

    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldIsGalois
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j)

/-- In one common rational-separable-closure realization, the canonical
quotient-to-Galois comparisons intertwine abstract restriction with
ordinary restriction of the actual number-field automorphisms. -/
theorem
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (z :
      Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension
          K' L' j).extensionQuotient) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let J :=
      numberFieldEmbeddedTopSubgroup K L jLower
    let J' :=
      numberFieldEmbeddedTopSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    let hJ'J :=
      numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
    let hJH :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
    let hJ'H' :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
    letI _ :
        (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K L jLower
    letI _ :
        (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K' L' j
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j (Additive.ofMul z))) =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J'
              hJH hJ'H'
              hH'H hJ'J)
            (Additive.ofMul z))) := by
  dsimp only
  let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ L L')
  let H :=
    numberFieldEmbeddedBaseSubgroup K L jLower
  let H' :=
    numberFieldEmbeddedBaseSubgroup K' L' j
  let J :=
    numberFieldEmbeddedTopSubgroup K L jLower
  let J' :=
    numberFieldEmbeddedTopSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K' L' j
  let hLowerNormal :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hUpperNormal :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let qLower :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K L jLower
  let qUpper :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K' L' j
  let qLowerRaw :
      (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) ≃*
        Gal(L / K) := by
    exact
      { qLower.toEquiv with
        map_mul' := fun x y => qLower.map_mul x y }
  let qUpperRaw :
      (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') ≃*
        Gal(L' / K') := by
    exact
      { qUpper.toEquiv with
        map_mul' := fun x y => qUpper.map_mul x y }
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  obtain ⟨q, rfl⟩ :=
    QuotientGroup.mk_surjective z
  obtain ⟨σ, rfl⟩ :=
    (numberFieldEmbeddedFiniteGaloisSubextension
      K' L' j).extensionQuotientMk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpperRaw.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk σ)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLowerRaw.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (Abelianization.of (QuotientGroup.mk σ))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpperRaw (QuotientGroup.mk σ)) =
      qLowerRaw
        (QuotientGroup.mk (Subgroup.inclusion hH'H σ))
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  let hUpperAlgebra : Algebra K' (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K' L' j
  let eUpper :=
    numberFieldEmbeddedSeparableClosureEquiv K' L' j
  let hLowerAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L jLower
  let eLower :=
    numberFieldEmbeddedSeparableClosureEquiv K L jLower
  calc
    jLower
        (restrictActual
          (qUpperRaw (QuotientGroup.mk σ)) x) =
        j
          ((qUpperRaw (QuotientGroup.mk σ))
            (algebraMap L L' x)) := by
      exact congrArg j
        (AlgEquiv.restrictNormal_commutes
          ((AlgEquiv.restrictScalarsHom K)
            (qUpperRaw (QuotientGroup.mk σ)))
          L x)
    _ = σ.1.1
        (j (algebraMap L L' x)) := by
      exact
        ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K' L' j eUpper σ (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H σ).1.1
        (jLower x) := rfl
    _ = jLower
        (qLowerRaw
          (QuotientGroup.mk
            (Subgroup.inclusion hH'H σ)) x) := by
      exact
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K L jLower eLower
          (Subgroup.inclusion hH'H σ) x).symm

/-- In a compatible common embedding, the fixed-part relative norm
between two (Galois-related) base fields is the genuine ordinary
idele-class norm. -/
theorem numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    letI _ : Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
      numberFieldEmbeddedBaseChangeExtensionQuotientFinite
        K K' L L' j
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower
        (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
  intro jLower H H'
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hnormal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hH'H
  let _ :
      (CyclicCohomology.extensionSubgroup H H' hH'H).Normal :=
    hnormal
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
      K K' L L' j
  let _ :
      Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            H (le_baseField H)) :=
    numberFieldEmbeddedAbsoluteQuotientFinite K L jLower
  let _ : NumberField F :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K L jLower
  let _ : NumberField E :=
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
      K K' L L' j
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ E
    exact
      numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
        K K' L L' j
  let _ : NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H') :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K' L' j
  have hE :
      E.restrictScalars ℚ =
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.extendScalars_restrictScalars
      (abstractFixedField_le
        ℚ (SeparableClosure ℚ) hH'H)
  let eRel :
      E ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.equivOfEq hE
  let eK :
      K ≃ₐ[ℚ] F :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K L jLower
  let eK'Base :
      K' ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K' L' j
  let eK' : K' ≃ₐ[ℚ] E :=
    eK'Base.trans eRel.symm
  have hcompat (x : K) :
      eK' (algebraMap K K' x) =
        algebraMap F E (eK x) := by
    apply eRel.injective
    apply Subtype.ext
    change
      j (algebraMap K' L' (algebraMap K K' x)) =
        j (algebraMap L L' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  have hupper :
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c)) =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c) := by
    apply Subtype.ext
    change
      ((rationalIdeleClassEquivFixed (E.restrictScalars ℚ))
          (Additive.ofMul (ideleClassCongr eK' c))).1 =
        ((rationalIdeleClassEquivFixed
            (abstractFixedField ℚ (SeparableClosure ℚ) H'))
          (Additive.ofMul (ideleClassCongr eK'Base c))).1
    exact rationalIdeleClassEquivFixed_transport_baseEquiv_val
      (T := K') (A := E.restrictScalars ℚ)
      (B := abstractFixedField ℚ (SeparableClosure ℚ) H') hE eK'Base c
  have hrelative :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
      H H' hH'H hnormal
        (Additive.ofMul (ideleClassCongr eK' c))
  change
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E
            (ideleClassCongr eK' c)))
    at hrelative
  calc
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H (Additive.ofMul (ideleClassCongr eK' c))) :=
      congrArg (relativeNorm rationalIdeleClassRepresentation H H' hH'H)
        hupper.symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) := hrelative
    _ = numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
      change
        rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) =
          rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (ideleClassCongr eK (_root_.ideleClassNorm K K' c)))
      apply congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed H)
      apply congrArg Additive.ofMul
      exact
        (ideleClassCongr_ideleClassNorm
          (K := K) (K' := F) (L := K') (L' := E) eK eK' hcompat c).symm

/-- For one common compatible embedding of a Galois base-change
diamond, the genuine global norm-residue maps commute with ordinary
idele-class norm and actual restriction of automorphisms. -/
theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalNormResidueMonoidHomOfEmbedding K' L' j) =
      (globalNormResidueMonoidHomOfEmbedding K L jLower).comp
        (_root_.ideleClassNorm K K') := by
  dsimp only
  let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ L L')
  let H :=
    numberFieldEmbeddedBaseSubgroup K L jLower
  let H' :=
    numberFieldEmbeddedBaseSubgroup K' L' j
  let J :=
    numberFieldEmbeddedTopSubgroup K L jLower
  let J' :=
    numberFieldEmbeddedTopSubgroup K' L' j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let _ :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) :=
    numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let _ :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let _ :
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') :=
    numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let hHH'finite :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j
  let T :
      FiniteAbstractFieldExtension
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldEmbeddedFiniteAbstractField K' L' j
      base := numberFieldEmbeddedFiniteAbstractField K L jLower
      below := hH'H
      finiteQuotient := hHH'finite }
  let hTBaseNormal :
      (CyclicCohomology.extensionSubgroup
        T.base.field J hJH).Normal := by
    change
      (CyclicCohomology.extensionSubgroup H J hJH).Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hTBaseFinite :
      Finite
        (T.base.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.base.field J hJH) := by
    change
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH)
    exact numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let hTFieldNormal :
      (CyclicCohomology.extensionSubgroup
        T.field.field J' hJ'H').Normal := by
    change
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let hTFieldFinite :
      Finite
        (T.field.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.field.field J' hJ'H') := by
    change
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H')
    exact numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  apply MonoidHom.ext
  intro c
  let a :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
      K' L' j (Additive.ofMul c)
  have hnat :=
    DegreeData.normResidueNaturality_norm_restriction
      (D := rationalCyclotomicDegreeData)
      (A := rationalIdeleClassRepresentation)
      (v := rationalCyclotomicIdeleClassValuationData)
      (hcf := rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (T := T) (L := J) (L' := J')
      (hLnormal := hTBaseNormal)
      (hL'normal := hTFieldNormal)
      (hLKfinite := hTBaseFinite)
      (hL'K'finite := hTFieldFinite)
      hJH hJ'H' hJ'J
  have hnatc :=
    DFunLike.congr_fun hnat
      (finiteNormClass rationalIdeleClassRepresentation
        H' J' hJ'H' a)
  change _ =
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      T.base
      { field := J
        below := hJH
        normal := hTBaseNormal
        finite := hTBaseFinite }
      (finiteReciprocityNaturalityNormMap
        rationalIdeleClassRepresentation
        T.base.field T.field.field J J'
        hJH hJ'H' T.below hJ'J
        (finiteNormClass rationalIdeleClassRepresentation
          T.field.field J' hJ'H' a)) at hnatc
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass]
    at hnatc
  have hnorm :
      relativeNorm rationalIdeleClassRepresentation
          H H' hH'H a =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K L jLower
          (Additive.ofMul (_root_.ideleClassNorm K K' c)) :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
      K K' L L' j c
  calc
    restrictActual
        (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      restrictActual
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      rw [globalNormResidueMonoidHomOfEmbedding_apply]
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J' hJH hJ'H' hH'H hJ'J)
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      exact
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
          K K' L L' j _
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L jLower)
            (numberFieldEmbeddedFiniteGaloisSubextension K L jLower)
            (finiteNormClass rationalIdeleClassRepresentation
              H J hJH
              (relativeNorm rationalIdeleClassRepresentation
                H H' hH'H a)))) := by
      exact congrArg
        (fun z =>
          Additive.toMul
            (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
              K L jLower z))
        hnatc
    _ =
      globalNormResidueMonoidHomOfEmbedding K L jLower
        (_root_.ideleClassNorm K K' c) := by
      rw [hnorm,
        ← globalNormResidueMonoidHomOfEmbedding_apply]

end EmbeddedNumberFieldRestriction

variable
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]

/-- Same-base norm-residue naturality in a compatible ambient:
restriction from the larger finite Galois subextension commutes with
the canonical projection between its finite norm quotient and the
norm quotient of an intermediate subextension. -/
theorem normResidueSymbol_restriction_sameBase
    (D : DegreeData G)
    (A : Rep ℤ G)
    (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G)
    (M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal :
      (CyclicCohomology.extensionSubgroup
        K.field L (hLM.trans hMK)).Normal]
    [hMnormal :
      (CyclicCohomology.extensionSubgroup K.field M hMK).Normal]
    [hLfinite :
      Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field L
            (hLM.trans hMK))] :
    letI _ : Finite
        (M.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite
        K.field M L hLM hMK
    letI hIntermediateFinite : Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field M hMK) :=
      abstractReciprocity_intermediateQuotient_finite
        K.field M L hLM hMK
    let EM : FiniteGaloisSubextension K.field :=
      ⟨M, hMK, hMnormal, hIntermediateFinite⟩
    let EL : FiniteGaloisSubextension K.field :=
      ⟨L, hLM.trans hMK, hLnormal, hLfinite⟩
    let hEL_EM : EL.field.toSubgroup ≤ EM.field.toSubgroup :=
      hLM
    let QL : Type :=
      FiniteNormQuotient A K.field L (hLM.trans hMK)
    let QM : Type :=
      FiniteNormQuotient A K.field M hMK
    let AL : Type :=
      Additive
        (Abelianization
          (K.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup
              K.field L (hLM.trans hMK)))
    let AM : Type :=
      Additive
        (Abelianization
          (K.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup K.field M hMK))
    let restriction :
        AL →+ AM :=
      MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedRestriction
          K.field K.field EM.field EL.field
          EM.below EL.below le_rfl hEL_EM)
    let projection :
        QL →+ QM :=
      abstractReciprocityNormProjection
        A K.field EM.field EL.field hEL_EM EM.below
    let normEL :
        QL →+ AL :=
      (DegreeData.normResidueSymbol
        (D := D) (A := A) (v := v) (hcf := hcf)
        (K := K) (L := EL)).toAddMonoidHom
    let normEM :
        QM →+ AM :=
      (DegreeData.normResidueSymbol
        (D := D) (A := A) (v := v) (hcf := hcf)
        (K := K) (L := EM)).toAddMonoidHom
    (restriction.comp normEL :
        QL →+ AM) =
      (normEM.comp projection :
        QL →+ AM) := by
  let _ : Finite
      (M.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite
      K.field M L hLM hMK
  let hIntermediateFinite : Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K.field M hMK) :=
    abstractReciprocity_intermediateQuotient_finite
      K.field M L hLM hMK
  let EM : FiniteGaloisSubextension K.field :=
    ⟨M, hMK, hMnormal, hIntermediateFinite⟩
  let EL : FiniteGaloisSubextension K.field :=
    ⟨L, hLM.trans hMK, hLnormal, hLfinite⟩
  let hEL_EM : EL.field.toSubgroup ≤ EM.field.toSubgroup :=
    hLM
  let QL : Type :=
    FiniteNormQuotient A K.field L (hLM.trans hMK)
  let QM : Type :=
    FiniteNormQuotient A K.field M hMK
  let AL : Type :=
    Additive
      (Abelianization
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field L (hLM.trans hMK)))
  let AM : Type :=
    Additive
      (Abelianization
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field M hMK))
  let restriction :
      AL →+ AM :=
    MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedRestriction
        K.field K.field EM.field EL.field
        EM.below EL.below le_rfl hEL_EM)
  let projection :
      QL →+ QM :=
    abstractReciprocityNormProjection
      A K.field EM.field EL.field hEL_EM EM.below
  let T : FiniteAbstractFieldExtension G :=
    { base := K
      field := K
      below := le_rfl
      finiteQuotient :=
        (FiniteGaloisSubextension.refl K.field).finite }
  have hnat :=
    D.normResidueNaturality_norm_restriction
      (hLnormal := hMnormal) (hL'normal := hLnormal)
      (hLKfinite := hIntermediateFinite) (hL'K'finite := hLfinite)
      A v hcf T M L hMK (hLM.trans hMK) hLM
  rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection]
    at hnat
  dsimp only [T, restriction, projection, EM, EL, hEL_EM, QL, QM, AL, AM,
    FiniteGaloisSubextension.extensionQuotient] at hnat ⊢
  exact hnat

end Reciprocity
end GlobalClassFieldTheory
