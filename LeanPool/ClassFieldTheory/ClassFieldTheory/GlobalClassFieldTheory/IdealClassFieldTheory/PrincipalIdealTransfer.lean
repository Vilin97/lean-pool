/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.AbstractCapitulation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFixedFieldBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Compatibility
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.MembershipTypes
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.ZeroTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FiniteNormClass
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified
/-!
# Transfer input for the principal ideal theorem

At the generic level, the Galois correspondence realizes a subgroup
`S ≤ Gal(M / K)` as an intermediate field, while the transfer construction
independently realizes `Gal(M / M^S)` inside `Gal(M / K)`.  Identifying these
subgroups puts the commutator transfer in the form covered by Witt's theorem.
This generic input assumes neither a class-field realization nor a
norm-subgroup equality.

The theorems below specialize that input to the selected actual two-stage
small Hilbert tower and transport it to genuine idèle-class extension and
norm maps.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
local instance
    principalIdealTransferIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] principalIdealTransferIdeleClassGroupIsMulCommutative

open scoped Classical in
local instance
    principalIdealTransferIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

attribute [local instance] principalIdealTransferIdeleClassSubgroupNormal

open scoped Classical in
/-- Extension-range containment descends along the lower leg of a finite
Galois tower. -/
private theorem ideleClassExtension_range_le_of_intermediate
    (F E U : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Field U] [NumberField U]
    [Algebra F U] [FiniteDimensional F U] [IsGalois F U]
    [Algebra F E] [Algebra E U] [IsScalarTower F E U]
    [FiniteDimensional F E] [FiniteDimensional E U]
    [IsGalois F E] [IsGalois E U]
    (N : Subgroup (IdeleClassGroup U))
    (hcontainment : (ideleClassExtension E U).range ≤ N) :
    (ideleClassExtension F U).range ≤ N := by
  rintro _ ⟨c, rfl⟩
  have hcomp :
      ideleClassExtension E U (ideleClassExtension F E c) =
        ideleClassExtension F U c := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun (ideleClassExtension_comp F U E) c
  rw [← hcomp]
  exact hcontainment ⟨ideleClassExtension F E c, rfl⟩

open scoped Classical in
/-- Internal bridge from the opaque rational transfer endpoint to the
explicit relative norm range used by the selected tower. -/
private theorem
    rationalFiniteNormTransferCanonicalMembership_to_explicitNormMembership
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hHKnormal : (CyclicCohomology.extensionSubgroup K H hHK).Normal)
    (hLHnormal : (CyclicCohomology.extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ CyclicCohomology.extensionSubgroup K H hHK)]
    [hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H))]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K)
    (hmembership :
      rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
        K H L hHK hLH hHKnormal hLHnormal c) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hHK
    let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
    letI : FiniteDimensional ℚ F :=
      RationalFiniteNormTransferInternal.fixedFiniteDimensional
        (hKfinite := hKfinite) K
    letI : FiniteDimensional F E :=
      RationalFiniteNormTransferInternal.relativeFiniteDimensional
        (hKfinite := hKfinite) (hfinite := hKHfinite)
        K H hHK
    letI : IsScalarTower ℚ F E :=
      RationalFiniteNormTransferInternal.relativeScalarTower K H hHK
    letI : FiniteDimensional ℚ E :=
      RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
        (hKfinite := hKfinite) (hfinite := hKHfinite)
        K H hHK
    letI : NumberField F :=
      RationalFiniteNormTransferInternal.fixedNumberField
        (hKfinite := hKfinite) K
    letI : NumberField E :=
      RationalFiniteNormTransferInternal.relativeNumberField
        (hKfinite := hKfinite) (hfinite := hKHfinite)
        K H hHK
    letI : FiniteDimensional ℚ U :=
      RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH
    letI : NumberField U :=
      RationalFiniteNormTransferInternal.relativeNumberField
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH
    letI : Algebra E U := by
      change Algebra
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U
      exact U.algebra
    letI : Module E U := by
      change Module
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U
      exact
        (U.algebra : Algebra
          (abstractFixedField ℚ (SeparableClosure ℚ) H) U).toModule
    letI : FiniteDimensional E U := by
      change FiniteDimensional
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U
      exact RationalFiniteNormTransferInternal.relativeFiniteDimensional
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH
    letI : IsScalarTower ℚ E U := by
      change IsScalarTower ℚ
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U
      exact RationalFiniteNormTransferInternal.relativeScalarTower H L hLH
    letI : IsGalois F E :=
      RationalFiniteNormTransferInternal.relativeIsGalois
        K H hHK hHKnormal
    letI : IsGalois E U := by
      change IsGalois
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U
      exact RationalFiniteNormTransferInternal.relativeIsGalois
        H L hLH hLHnormal
    ideleClassExtension F E c ∈ (_root_.ideleClassNorm E U).range := by
  dsimp only
  unfold
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
    at hmembership
  unfold rationalFiniteNormTransferRelativeNormMembership at hmembership
  unfold
    rationalFiniteNormTransferOrdinaryExtensionRepresentative
    at hmembership
  exact hmembership

open scoped Classical in
/-- The commutator transfer supplies the canonical zero class used by the
rational finite-norm bridge. -/
private theorem
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_of_commutator
    (K₀ : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (M : FiniteGaloisSubextension K₀.field)
    (H T : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hTH : T.toSubgroup ≤ H.toSubgroup)
    (hHK : H.toSubgroup ≤ K₀.field.toSubgroup)
    (hmiddle : M.intermediateField (commutator M.extensionQuotient) = H)
    (htop : M.field = T)
    [hHTfinite : Finite
      (H.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H T hTH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := K₀.finite) K₀.field) :
    rationalFiniteNormTransferCanonicalFiniteNormClassZero
      (hKfinite := K₀.finite) (hHLfinite := hHTfinite)
      K₀.field H T hHK hTH c := by
  let S := commutator M.extensionQuotient
  let : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K₀.field M.field M.below) :=
    M.finite
  let : Finite
      ((M.intermediateField S).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (M.intermediateField S) M.field
          (M.field_le_intermediateField S)) :=
    M.extension_over_intermediate_finite S
  let a :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K₀.field :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K₀.field
      (Additive.ofMul c)
  have hzeroMap :
      M.intermediateNormQuotientInclusion
          rationalIdeleClassRepresentation S =
        0 :=
    intermediateNormQuotientInclusion_commutator_eq_zero
      rationalCyclotomicDegreeData rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K₀ M
  have hzero :
      M.intermediateNormQuotientInclusion
          rationalIdeleClassRepresentation S
          (finiteNormClass rationalIdeleClassRepresentation
            K₀.field M.field M.below a) =
        0 := by
    rw [hzeroMap]
    rfl
  have hincludeRaw :=
    ClassFormation.FiniteGaloisSubextension.intermediateNormQuotientInclusion_finiteNormClass
      rationalIdeleClassRepresentation M S a
  have transportInclude
      (J V : ClosedSubgroup
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      (hJ : M.intermediateField S = J)
      (hV : M.field = V)
      (hVJ : V.toSubgroup ≤ J.toSubgroup)
      (hJK : J.toSubgroup ≤ K₀.field.toSubgroup)
      [Finite
        (J.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup J V hVJ)] :
      (0 : FiniteNormQuotient rationalIdeleClassRepresentation
        J V hVJ) =
        finiteNormClass rationalIdeleClassRepresentation
          J V hVJ
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K₀.field J hJK a) := by
    subst J
    subst V
    exact hzero.symm.trans hincludeRaw
  unfold rationalFiniteNormTransferCanonicalFiniteNormClassZero
  simpa only [a, S] using
    (transportInclude H T hmiddle htop hTH hHK)

open scoped Classical in
/-- The selected two-stage tower supplies a canonical zero finite-norm class
for every idele class over its base fixed field. -/
@[irreducible]
private noncomputable def
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement : Prop :=
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  letI hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  ∀ c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := K₀.finite) K₀.field,
    rationalFiniteNormTransferCanonicalFiniteNormClassZero
      (hKfinite := K₀.finite) (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH c

open scoped Classical in
private theorem
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement_proof :
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement K := by
  unfold smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement
  dsimp only
  intro c
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let M := smallHilbertTowerGaloisRealization K
  let H := L.field
  have hmiddle :
      M.intermediateField (commutator M.extensionQuotient) = H := by
    change M.abelianIntermediateField = L.field
    have h :=
      congrArg
        (fun A : FiniteAbelianSubextension K₀.field => A.field)
        (smallHilbertTower_maximalAbelianSubextension_eq_firstStage K)
    simpa only [M, L, maximalAbelianSubextension_field] using h
  have htop : M.field = N.field := by
    rfl
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  let hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  change
    rationalFiniteNormTransferCanonicalFiniteNormClassZero
      (hKfinite := K₀.finite) (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH c
  exact
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_of_commutator
      (hHTfinite := hHMfinite)
      K₀ M H N.field hMH hHK hmiddle htop c

open scoped Classical in
/-- The canonical zero classes of the selected tower satisfy the opaque
rational relative norm-membership endpoint. -/
@[irreducible]
private noncomputable def
    smallHilbertClassFieldCanonicalNormMembershipStatement : Prop :=
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  let hHKnormal :
      (CyclicCohomology.extensionSubgroup K₀.field H hHK).Normal :=
    L.normal
  let hMHnormal :
      (CyclicCohomology.extensionSubgroup H N.field hMH).Normal :=
    N.normal
  letI hKHfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K₀.field H hHK) :=
    L.finite
  letI hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  ∀ c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := K₀.finite) K₀.field,
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
      (hKfinite := K₀.finite) (hKHfinite := hKHfinite)
      (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH hHKnormal hMHnormal c

open scoped Classical in
private theorem
    smallHilbertClassFieldCanonicalNormMembershipStatement_proof :
    smallHilbertClassFieldCanonicalNormMembershipStatement K := by
  unfold smallHilbertClassFieldCanonicalNormMembershipStatement
  dsimp only
  intro c
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  let hHKnormal :
      (CyclicCohomology.extensionSubgroup K₀.field H hHK).Normal :=
    L.normal
  let hMHnormal :
      (CyclicCohomology.extensionSubgroup H N.field hMH).Normal :=
    N.normal
  let hKHfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K₀.field H hHK) :=
    L.finite
  let hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  have hincludeAll :=
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement_proof K
  unfold
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement
    at hincludeAll
  have hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        (hKfinite := K₀.finite) (hHLfinite := hHMfinite)
        K₀.field H N.field hHK hMH c := by
    exact hincludeAll c
  change
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
      (hKfinite := K₀.finite) (hKHfinite := hKHfinite)
      (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH hHKnormal hMHnormal c
  exact
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_implies_normMembership
      (hKfinite := K₀.finite) (hKHfinite := hKHfinite)
      (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH hHKnormal hMHnormal
      c hincludeCanonical

open scoped Classical in
/-- The selected rational transfer endpoint, exposed on the explicit
relative fixed-field spine used by the tower containment. -/
private noncomputable abbrev
    smallHilbertClassFieldExplicitNormMembershipStatement : Prop :=
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  let hHKnormal :
      (CyclicCohomology.extensionSubgroup K₀.field H hHK).Normal :=
    L.normal
  let hMHnormal :
      (CyclicCohomology.extensionSubgroup H N.field hMH).Normal :=
    N.normal
  letI hKHfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K₀.field H hHK) :=
    L.finite
  letI hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  letI hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H)) :=
    FiniteGaloisSubextension.finite_extension_trans
      hHK (le_baseField K₀.field)
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K₀.field
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hHK
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hMH
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional
      (hKfinite := K₀.finite) K₀.field
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      (hKfinite := K₀.finite) (hfinite := hKHfinite)
      K₀.field H hHK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower K₀.field H hHK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      (hKfinite := K₀.finite) (hfinite := hKHfinite)
      K₀.field H hHK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField
      (hKfinite := K₀.finite) K₀.field
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      (hKfinite := K₀.finite) (hfinite := hKHfinite)
      K₀.field H hHK
  letI : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      (hKfinite := hHfinite) (hfinite := hHMfinite)
      H N.field hMH
  letI : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      (hKfinite := hHfinite) (hfinite := hHMfinite)
      H N.field hMH
  letI : Algebra E U := by
    change Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact U.algebra
  letI : Module E U := by
    change Module
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact
      (U.algebra : Algebra
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U).toModule
  letI : FiniteDimensional E U := by
    change FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeFiniteDimensional
      (hKfinite := hHfinite) (hfinite := hHMfinite)
      H N.field hMH
  letI : IsScalarTower ℚ E U := by
    change IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeScalarTower
      H N.field hMH
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K₀.field H hHK hHKnormal
  letI : IsGalois E U := by
    change IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeIsGalois
      H N.field hMH hMHnormal
  ∀ c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := K₀.finite) K₀.field,
    ideleClassExtension F E c ∈ (_root_.ideleClassNorm E U).range

open scoped Classical in
private structure SmallHilbertClassFieldExplicitNormMembershipData
    (K : Type) [Field K] [NumberField K] : Prop where
  membership : smallHilbertClassFieldExplicitNormMembershipStatement K

open scoped Classical in
/-- The canonical norm-membership statement realizes the literal two-stage fixed-field tower. -/
private theorem smallHilbertClassFieldExplicitNormMembershipStatement_proof :
    smallHilbertClassFieldExplicitNormMembershipStatement K := by
  unfold smallHilbertClassFieldExplicitNormMembershipStatement
  dsimp only
  intro c
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  let hHKnormal :
      (CyclicCohomology.extensionSubgroup K₀.field H hHK).Normal :=
    L.normal
  let hMHnormal :
      (CyclicCohomology.extensionSubgroup H N.field hMH).Normal :=
    N.normal
  let hKHfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K₀.field H hHK) :=
    L.finite
  let hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H)) :=
    FiniteGaloisSubextension.finite_extension_trans
      hHK (le_baseField K₀.field)
  have hmembershipAll :=
    smallHilbertClassFieldCanonicalNormMembershipStatement_proof K
  unfold
    smallHilbertClassFieldCanonicalNormMembershipStatement
    at hmembershipAll
  have hmembership :
      rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
        (hKfinite := K₀.finite) (hKHfinite := hKHfinite)
        (hHLfinite := hHMfinite)
        K₀.field H N.field hHK hMH hHKnormal hMHnormal c :=
    hmembershipAll c
  exact
    rationalFiniteNormTransferCanonicalMembership_to_explicitNormMembership
      (hKfinite := K₀.finite) (hKHfinite := hKHfinite)
      (hHfinite := hHfinite) (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH hHKnormal hMHnormal c hmembership

open scoped Classical in
private theorem
    smallHilbertClassFieldExplicitNormMembershipData_proof :
    SmallHilbertClassFieldExplicitNormMembershipData K where
  membership := smallHilbertClassFieldExplicitNormMembershipStatement_proof K

open scoped Classical in
/-- The named proposition underlying the fixed-field-base form of the
two-stage transfer containment.  Keeping the dependent idele maps behind one
opaque boundary prevents every consumer from reconstructing their instance
towers while elaborating a theorem signature. -/
@[irreducible]
noncomputable def smallHilbertClassFieldBaseSecondNormRangeContainment : Prop :=
  (ideleClassExtension
    (smallHilbertClassFieldBase K)
    (smallHilbertClassField K)).range ≤
      smallHilbertClassFieldNormSubgroup
        (K := smallHilbertClassField K)

open scoped Classical in
/-- Witt transfer for the genuine selected two-stage tower: every
idele class extended from the selected base fixed field to the first
small Hilbert class field is a norm from the actual second stage. -/
theorem
    smallHilbertClassFieldBase_ideleClassExtension_range_le_secondNormRange :
    smallHilbertClassFieldBaseSecondNormRangeContainment K := by
  unfold smallHilbertClassFieldBaseSecondNormRangeContainment
  change
    (ideleClassExtension
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).range ≤
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K)
  have hrawMembershipAll :=
    (smallHilbertClassFieldExplicitNormMembershipData_proof K).membership
  unfold
    smallHilbertClassFieldExplicitNormMembershipStatement
    at hrawMembershipAll
  rintro _ ⟨c, rfl⟩
  exact
    Eq.mp
      (congrArg
        (fun A : Subgroup (IdeleClassGroup (smallHilbertClassField K)) =>
          ideleClassExtension
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K) c ∈ A)
        (smallHilbertTowerSecondStage_ideleClassNorm_range K))
      (hrawMembershipAll c)

open scoped Classical in
/-- The named proposition underlying the original-base form of the two-stage
transfer containment. -/
@[irreducible]
noncomputable def smallHilbertClassFieldSecondNormRangeContainment : Prop :=
  (ideleClassExtension K (smallHilbertClassField K)).range ≤
      smallHilbertClassFieldNormSubgroup
        (K := smallHilbertClassField K)

open scoped Classical in
private structure SmallHilbertClassFieldSecondNormRangeContainmentData
    (K : Type) [Field K] [NumberField K] : Prop where
  containment : smallHilbertClassFieldSecondNormRangeContainment K

open scoped Classical in
private theorem
    smallHilbertClassFieldSecondNormRangeContainmentData_proof :
    SmallHilbertClassFieldSecondNormRangeContainmentData K where
  containment := by
    unfold smallHilbertClassFieldSecondNormRangeContainment
    let : IsGalois K (smallHilbertClassFieldBase K) :=
      IsGalois.of_algEquiv
        (smallHilbertClassFieldBaseEquivOverOriginal K)
    have hbase :=
      smallHilbertClassFieldBase_ideleClassExtension_range_le_secondNormRange K
    unfold smallHilbertClassFieldBaseSecondNormRangeContainment at hbase
    exact
      ideleClassExtension_range_le_of_intermediate
        K (smallHilbertClassFieldBase K) (smallHilbertClassField K)
        (smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K)) hbase

open scoped Classical in
/-- Every idele class extended from the original number field to its
selected small Hilbert class field is a norm from the actual second
stage.  This is the original-base form of the middle vertical arrow in
the principal-ideal-theorem diagram. -/
theorem
    smallHilbertClassField_ideleClassExtension_range_le_secondNormRange :
    smallHilbertClassFieldSecondNormRangeContainment K :=
  (smallHilbertClassFieldSecondNormRangeContainmentData_proof K).containment

end IdealClassFieldTheory
end GlobalClassFieldTheory
