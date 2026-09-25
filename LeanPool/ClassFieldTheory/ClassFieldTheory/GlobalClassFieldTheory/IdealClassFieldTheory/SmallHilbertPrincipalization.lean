/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTheorem
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTransfer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified
/-!
# Principalization in the selected small Hilbert class field

The selected second small Hilbert class field is Galois over the
canonical fixed-field copy of the original base, and its maximal
abelian intermediate field is the selected first small Hilbert class
field.  Witt transfer therefore places every idele class extended from
that fixed-field copy in the norm range from the second stage.
Functoriality of actual idele extension along the degree-one
identification of the original field with its fixed-field copy gives
the same range inclusion for idele classes extended from the original
field itself.

The exact second-stage norm subgroup is the intrinsic small-Hilbert
subgroup, so the genuine map from the original field on small-Hilbert
quotients is trivial.  Its naturality with extension of ideal classes
then gives the class-group, integral-ideal, and fractional-ideal forms
of principalization over the original number field.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

open scoped Classical in
local instance
    smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] smallHilbertPrincipalization_ideleClassGroupIsMulCommutative

open scoped Classical in
local instance
    smallHilbertPrincipalization_ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

attribute [local instance] smallHilbertPrincipalization_ideleClassSubgroupNormal

open scoped Classical in
/-- The idele class quotient by the small Hilbert norm subgroup carries its quotient group
structure. -/
local instance
    smallHilbertPrincipalizationSmallHilbertQuotientGroup
    {F : Type} [Field F] [NumberField F] :
    Group
      (IdeleClassGroup F ⧸
        smallHilbertClassFieldNormSubgroup (K := F)) :=
  QuotientGroup.Quotient.group
    (smallHilbertClassFieldNormSubgroup (K := F))

attribute [local instance] smallHilbertPrincipalizationSmallHilbertQuotientGroup

open scoped Classical in
/-- The identity in the small Hilbert norm quotient is inherited from its chosen quotient group
structure. -/
local instance
    smallHilbertPrincipalizationSmallHilbertQuotientOne
    {F : Type} [Field F] [NumberField F] :
    One
      (IdeleClassGroup F ⧸
        smallHilbertClassFieldNormSubgroup (K := F)) :=
  ⟨(smallHilbertPrincipalizationSmallHilbertQuotientGroup
    (F := F)).one⟩

attribute [local instance] smallHilbertPrincipalizationSmallHilbertQuotientOne

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
private theorem smallHilbertClassFieldIdeleExtensionMap_apply_eq_one
    (q : IdeleClassGroup K ⧸
      smallHilbertClassFieldNormSubgroup (K := K)) :
    smallHilbertClassFieldIdeleExtensionMap
        K (smallHilbertClassField K) q =
      (1 : IdeleClassGroup (smallHilbertClassField K) ⧸
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K)) := by
  induction q using QuotientGroup.induction_on with
  | _ c =>
      change
        smallHilbertClassFieldIdeleExtensionMap
            K (smallHilbertClassField K)
            (QuotientGroup.mk'
              (smallHilbertClassFieldNormSubgroup (K := K)) c) =
          1
      have hcontainment :=
        smallHilbertClassField_ideleClassExtension_range_le_secondNormRange K
      unfold smallHilbertClassFieldSecondNormRangeContainment at hcontainment
      have hmembership :
          ideleClassExtension K (smallHilbertClassField K) c ∈
            smallHilbertClassFieldNormSubgroup
              (K := smallHilbertClassField K) :=
        hcontainment ⟨c, rfl⟩
      calc
        smallHilbertClassFieldIdeleExtensionMap
              K (smallHilbertClassField K)
              (QuotientGroup.mk'
                (smallHilbertClassFieldNormSubgroup (K := K)) c) =
            QuotientGroup.mk'
              (smallHilbertClassFieldNormSubgroup
                (K := smallHilbertClassField K))
              (ideleClassExtension K (smallHilbertClassField K) c) :=
          smallHilbertClassFieldIdeleExtensionMap_mk'
            K (smallHilbertClassField K) c
        _ = 1 :=
          (QuotientGroup.eq_one_iff
            (ideleClassExtension K (smallHilbertClassField K) c)).2
              hmembership

open scoped Classical in
/-- The map induced by genuine idele extension from the original
number field on the two small-Hilbert reciprocity quotients is
trivial. -/
theorem smallHilbertClassFieldIdeleExtensionMap_eq_one :
    @Eq
      ((IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) →*
        (IdeleClassGroup (smallHilbertClassField K) ⧸
          smallHilbertClassFieldNormSubgroup
            (K := smallHilbertClassField K)))
      (smallHilbertClassFieldIdeleExtensionMap
        K (smallHilbertClassField K))
      (1 :
        (IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) →*
        (IdeleClassGroup (smallHilbertClassField K) ⧸
          smallHilbertClassFieldNormSubgroup
            (K := smallHilbertClassField K))) := by
  apply MonoidHom.ext
  intro q
  simpa only [MonoidHom.one_apply] using
    smallHilbertClassFieldIdeleExtensionMap_apply_eq_one K q

open scoped Classical in
private theorem smallHilbertClassFieldClassGroupExtension_apply_eq_one
    (c : ClassGroup (𝓞 K)) :
    ClassGroup.extendedHom
        (𝓞 K) (𝓞 (smallHilbertClassField K)) c =
      (1 : ClassGroup (𝓞 (smallHilbertClassField K))) := by
  obtain ⟨q, rfl⟩ :=
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).surjective c
  have hidele :=
    smallHilbertClassFieldIdeleExtensionMap_apply_eq_one K q
  have hnaturality :=
    smallHilbertClassFieldIdeleExtensionMap_naturality
      K (smallHilbertClassField K) q
  calc
    ClassGroup.extendedHom
          (𝓞 K) (𝓞 (smallHilbertClassField K))
          (smallHilbertClassFieldQuotientEquivClassGroup (K := K) q) =
        smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K)
          (smallHilbertClassFieldIdeleExtensionMap
            K (smallHilbertClassField K) q) :=
      hnaturality.symm
    _ = smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K) 1 :=
      congrArg
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K)) hidele
    _ = 1 :=
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := smallHilbertClassField K)).map_one

open scoped Classical in
/-- Extension of ideal classes from a number field to its selected
small Hilbert class field is the trivial homomorphism.  This follows
directly from the naturality equality identifying actual idele
extension with actual extension of ideal classes. -/
theorem smallHilbertClassFieldClassGroupExtension_eq_one :
    @Eq
      (ClassGroup (𝓞 K) →*
        ClassGroup (𝓞 (smallHilbertClassField K)))
      (ClassGroup.extendedHom
        (𝓞 K) (𝓞 (smallHilbertClassField K)))
      (1 : ClassGroup (𝓞 K) →*
        ClassGroup (𝓞 (smallHilbertClassField K))) := by
  apply MonoidHom.ext
  intro c
  simpa only [MonoidHom.one_apply] using
    smallHilbertClassFieldClassGroupExtension_apply_eq_one K c

open scoped Classical in
/-- Every ideal of a number field becomes principal after extension
to the selected small Hilbert class field. -/
theorem allIdealsBecomePrincipalInSmallHilbertClassField :
    ∀ I : Ideal (𝓞 K),
      (I.map
        (algebraMap
          (𝓞 K)
          (𝓞 (smallHilbertClassField K)))).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_ideal_map_isPrincipal
    (𝓞 K) (𝓞 (smallHilbertClassField K))).1
    (smallHilbertClassFieldClassGroupExtension_eq_one K)

open scoped Classical in
/-- Every nonzero fractional ideal of a number field becomes a
principal fractional ideal after extension to the selected small
Hilbert class field. -/
theorem allFractionalIdealsBecomePrincipalInSmallHilbertClassField :
    ∀ I : FractionalIdealGroup K,
      FractionalIdealGroup.extension
          K (smallHilbertClassField K) I ∈
        (toPrincipalIdeal
          (𝓞 (smallHilbertClassField K))
          (smallHilbertClassField K)).range := by
  intro I
  apply
    (IdeleGroup.classGroup_mk_eq_one_iff
      (FractionalIdealGroup.extension
        K (smallHilbertClassField K) I)).1
  rw [
    FractionalIdealGroup.classGroup_mk_extension,
    smallHilbertClassFieldClassGroupExtension_eq_one]
  rfl

end IdealClassFieldTheory
end GlobalClassFieldTheory
