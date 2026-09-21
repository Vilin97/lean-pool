/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedLocalGlobalCompatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm
/-!
# The finite p-adic auxiliary field

This module realizes the simultaneous finite/cyclotomic lift as an actual
number field and proves the subgroup and intermediate-field identities
needed by the auxiliary-field argument.
-/

open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra

local instance finitePadicAuxiliaryExtensionNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

local instance finitePadicAuxiliaryExtensionQuotientFinite :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L

noncomputable local instance finitePadicAuxiliaryExtensionQuotientIsMulCommutative :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm
                (e x) (e y)⟩ }

/-- The concrete auxiliary fixed field attached to a simultaneous
finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IntermediateField ℚ (SeparableClosure ℚ) := by
  exact
    IntermediateField.fixedField
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup

/-- A nonzero-degree lift produces a genuine number field: its
concrete fixed field is finite over `ℚ`. -/
theorem numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteDimensional ℚ
      (numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ) := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  apply
    (InfiniteGalois.isOpen_iff_finite
      (K := SeparableClosure ℚ) F).1
  change IsOpen
    (IntermediateField.fixedField S.toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField S]
  exact
    numberFieldTowerFinitePadicCyclicFixedSubgroup_isOpen
      (K := K) (L := L) p τ hτ

/-- The compatible embedded copy of `K` lies in every auxiliary
cyclic fixed field. -/
theorem numberFieldTowerBaseField_le_finitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    numberFieldTowerBaseField K L ≤
      numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ := by
  intro x hx
  change x ∈ IntermediateField.fixedField
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change
    σ ∈
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup at hσ
  obtain ⟨u, hu, rfl⟩ := hσ
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldTowerBaseField K L) u.1).1 u.2 x hx

/-- The compatible embedding of the original base field into the
genuine auxiliary fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    K →ₐ[ℚ]
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  exact
    (numberFieldTowerLowerEmbedding K L).codRestrict F.toSubalgebra
      (fun x =>
        numberFieldTowerBaseField_le_finitePadicCyclicFixedField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary base embedding recovers the fixed lower embedding
into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) =
        numberFieldTowerLowerEmbedding K L x := by
  rfl

/-- The compatible copy of the original top field lies in the
auxiliary compositum fixed field. -/
theorem numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    {x : SeparableClosure ℚ}
    (hx : x ∈ numberFieldInRationalSeparableClosure L) :
    x ∈
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  change x ∈ IntermediateField.fixedField
    (S.toSubgroup ⊓ T.toSubgroup)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσT : σ ∈ T.toSubgroup :=
    hσ.2
  change
    σ ∈
      (numberFieldInRationalSeparableClosure L).fixingSubgroup
        at hσT
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldInRationalSeparableClosure L) σ).1
      hσT x hx

/-- The compatible embedding of the original top field into the
auxiliary compositum fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryTopEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    L →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  exact
    (numberFieldSeparableClosureEmbedding L).codRestrict
      (E.restrictScalars ℚ).toSubalgebra
      (fun x =>
        numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary top embedding recovers the chosen top-field
embedding into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : L) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        numberFieldSeparableClosureEmbedding L x := by
  rfl

/-- The compatible base and top embeddings form the actual
base-change square inside the rational separable closure. -/
theorem numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ (algebraMap K L x) :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) := by
  rfl

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_baseRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_topRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp
      (IsScalarTower.toAlgHom ℚ K L)).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

instance
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ))
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact
    numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
      (K := K) (L := L) p τ x

/-- The genuine auxiliary fixed field is Galois over the original
base field through the compatible embedding above. -/
theorem numberFieldTowerFinitePadicAuxiliaryBase_isGalois
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsGalois K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let hSH :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  let B :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let FB :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH
  let auxiliaryBaseAlgebra : Algebra B FB :=
    (LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH).algebra
  let auxiliaryBaseGalois : IsGalois B FB :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H S hSH
      (numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
        (K := K) (L := L) p τ)
  let eK :=
    numberFieldTowerAbstractBaseFieldEquiv K L
  refine
    @IsGalois.of_equiv_equiv
      B FB _ _ auxiliaryBaseAlgebra
      K F _ _
      (numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ)
      auxiliaryBaseGalois
      eK.symm.toRingEquiv (RingEquiv.refl F) ?_
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change
    ((eK (eK.symm x) : B) : SeparableClosure ℚ) =
      (x : SeparableClosure ℚ)
  exact
    congrArg Subtype.val (eK.apply_symm_apply x)

/-- The distinguished absolute lift, regarded as an element of the
auxiliary base subgroup. -/
noncomputable def numberFieldTowerFinitePadicAuxiliarySubgroupLift
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup :=
  ⟨τ.1,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_generator_mem
      (K := K) (L := L) p τ⟩

/-- The actual automorphism of the auxiliary compositum induced by
the distinguished simultaneous finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryAutomorphism
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    Gal(
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below /
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S) := by
  dsimp only
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ)
      S P.field P.below
      P.toFiniteGaloisExtension.normal
      (QuotientGroup.mk'
        (extensionSubgroup
          S P.field P.below)
        σS)

/-- On the common separable closure, the auxiliary automorphism acts
by the original distinguished ambient lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
    ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        τ.1 (x : SeparableClosure ℚ) := by
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ)
        S P.field P.below
        P.toFiniteGaloisExtension.normal σS x).symm

/-- Restricting the auxiliary automorphism through the actual
base-change square recovers the finite quotient coordinate of the
distinguished lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ) =
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  apply AlgEquiv.ext
  intro x
  apply (numberFieldSeparableClosureEmbedding L).injective
  calc
    numberFieldSeparableClosureEmbedding L
        (((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE x) =
      ((σE (algebraMap L E x) : E) :
        SeparableClosure ℚ) := by
          exact congrArg Subtype.val
            (AlgEquiv.restrictNormal_commutes
              ((AlgEquiv.restrictScalarsHom K) σE) L x)
    _ = τ.1 (numberFieldSeparableClosureEmbedding L x) := by
      rw [
        numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
          (K := K) (L := L) p τ]
      rfl
    _ =
      numberFieldSeparableClosureEmbedding L
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) x) := by
      exact
        (numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_apply
          (K := K) (L := L) τ x).symm

/-- Restriction of the chosen separable-closure place to the genuine
auxiliary base field.  This is an exact extension of the original
finite place of `K`, not merely an equivalent valuation. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := F.val.toRingHom) F.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- Restriction of the same separable-closure place to the genuine
auxiliary compositum.  Its restriction to `K` agrees exactly with the
original normalized finite absolute value. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := E.val.toRingHom) E.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- The centre of the restricted place on the auxiliary compositum
lies above the centre of the same place on the auxiliary base field. -/
theorem
    numberFieldTowerFinitePadicAuxiliaryTopPlace_below
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸
          extensionSubgroup S P.field P.below) :=
      P.finite
    letI _ : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI _ : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    letI _ : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI _ : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI _ : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI _ : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI _ : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    finitePlaceBelow (K := F)
        (finitePlaceExtensionCentre
          (K := K) (L := E) v
          (numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
            (K := K) (L := L) v p τ)) =
      finitePlaceExtensionCentre
        (K := K) (L := F) v
        (numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
          (K := K) (L := L) v p τ) := by
  dsimp only
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    (numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ).finite
  let hPfinite : Finite
      (S.toSubgroup ⧸
        extensionSubgroup S P.field P.below) :=
    P.finite
  let auxiliaryBaseFiniteDimensional : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let auxiliaryTopFiniteDimensional : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      S P.field P.below hHfinite hPfinite
  let auxiliaryScalarTower : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let auxiliaryAbsoluteFiniteDimensional : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let auxiliaryBaseNumberField : NumberField F :=
    NumberField.of_module_finite ℚ F
  let auxiliaryTopNumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  apply HeightOneSpectrum.ext
  ext x
  change
    algebraMap (𝓞 F) (𝓞 E) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := E) v wE ↔
      x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := F) v wF
  rw [
    mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl

/-- Evaluation of the distinguished auxiliary automorphism through the
restricted top-field place.  Isolating this coercion calculation prevents the
whole decomposition-group proof from normalizing the fixed-field tower. -/
private opaque
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    ∀ x : E,
      wE.1 (σE x) =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v (chosenFinitePlaceExtension (L := L) v)).1
            (τ.1 (x : SeparableClosure ℚ)) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only
  intro x
  change
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)).1
        ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ x :
            LocalClassFieldTheory.abstractRelativeFixedField
              ℚ (SeparableClosure ℚ)
              (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
                (K := K) (L := L) p τ).below) : SeparableClosure ℚ) = _
  rw [
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
      (K := K) (L := L) p τ]

/-- The distinguished auxiliary automorphism preserves the top-field place
obtained by restricting the original separable-closure place. -/
private opaque numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    σE ∈ absoluteValueDecompositionGroup F wE.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only at hdecomposition ⊢
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  intro x
  change
    wE.1 (σE x) < 1 ↔
      wE.1 x < 1
  rw [
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
      (K := K) (L := L) v p τ x,
    show
      wE.1 x =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v
          (chosenFinitePlaceExtension (L := L) v)).1
            (x : SeparableClosure ℚ) from rfl]
  exact hdecomposition (x : SeparableClosure ℚ)

/-- The restricted top-field place and the chosen extension above its centre
have the same decomposition group. -/
private opaque numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) := P.finite
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
    letI : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois F E :=
      GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
    letI : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    let wF := numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
    absoluteValueDecompositionGroup F wE.1 =
      absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
  dsimp only
  let H :=
    numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  let hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
  let : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  let : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
  let W := finitePlaceExtensionCentre (K := K) (L := E) v wE
  let Wover :
      {W' : HeightOneSpectrum (𝓞 E) //
        finitePlaceBelow (K := F) W' = V} :=
    ⟨W,
      numberFieldTowerFinitePadicAuxiliaryTopPlace_below
        (K := K) (L := L) v p τ hτ⟩
  let wFE :
      AbsoluteValueExtension
        (NumberField.HeightOneSpectrum.adicAbv F V) E :=
    (finitePlaceExtensionEquivAbove
      (K := F) (L := E) V).symm Wover
  have hwFEcentre :
      finitePlaceExtensionCentre
          (K := F) (L := E) V wFE =
        W := by
    exact
      congrArg Subtype.val
        ((finitePlaceExtensionEquivAbove
          (K := F) (L := E) V).apply_symm_apply Wover)
  have hwEquiv : wE.1.IsEquiv wFE.1 := by
    apply
      finitePlaceExtensions_isEquiv_of_centres_eq
        (F := K) (M := F) v V wE wFE
    exact hwFEcentre.symm
  calc
    absoluteValueDecompositionGroup F wE.1 =
        absoluteValueDecompositionGroup F wFE.1 :=
      absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
        (F := F) wE.1 wFE.1 hwEquiv
    _ =
      absoluteValueDecompositionGroup F
          (chosenFinitePlaceExtension (L := E) V).1 :=
      absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
        (F := F)
        (NumberField.HeightOneSpectrum.adicAbv F V)
        (RayClass.adicAbv_isNontrivial V)
        wFE
        (chosenFinitePlaceExtension (L := E) V)

/-- Pointwise form of norm/restriction naturality.  Keeping the function
equality and its coercion normalization in this small declaration prevents
the auxiliary-field witness construction below from repeatedly elaborating
the full pair of composite homomorphisms. -/
private theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      globalNormResidueMonoidHomOfEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))
        (_root_.ideleClassNorm K K' c) := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L) (K' := K') (L' := L') j) c



/-- The auxiliary-field construction produces a lower local unit
whose chosen local Artin value and global norm-residue value are both
the finite quotient coordinate of the distinguished lift. -/
opaque numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    {z : (v.adicCompletion K)ˣ //
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ) ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ)} := by
  let H :=
    numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  letI hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  letI hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  letI auxiliaryBaseNumberField : NumberField F := by
    let : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    exact NumberField.of_module_finite ℚ F
  letI auxiliaryTopNumberField : NumberField E := by
    let : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    exact NumberField.of_module_finite F E
  letI auxiliaryAbelianGalois : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  letI auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopAlgebra : Algebra L E :=
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseTopAlgebra : Algebra K E :=
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopScalarTower : IsScalarTower K L E :=
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryBaseTopScalarTower : IsScalarTower K F E :=
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseGalois : IsGalois K F :=
    numberFieldTowerFinitePadicAuxiliaryBase_isGalois
      (K := K) (L := L) p τ
  let auxiliaryOriginalTopAlgHom : L →ₐ[ℚ] E :=
    numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V :=
    finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  have hVbelow : finitePlaceBelow (K := K) V = v :=
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  let Vover :
      {V' : HeightOneSpectrum (𝓞 F) //
        finitePlaceBelow (K := K) V' = v} :=
    ⟨V, hVbelow⟩
  letI auxiliaryCompletionAlgebra :
      Algebra (v.adicCompletion K) (V.adicCompletion F) :=
    (finitePlaceAdicCompletionMap K F v Vover).toAlgebra
  let σE : Gal(E / F) :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  have hσtop :
      σE ∈ absoluteValueDecompositionGroup F wE.1 :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
      (K := K) (L := L) v p τ hdecomposition
  have hgroup :=
    numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
      (K := K) (L := L) v p τ hτ
  have hσchosen :
      σE ∈ absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
    rw [← hgroup]
    exact hσtop
  have hRange :
      σE ∈ (chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) V).range := by
    rw [chosenFinitePlaceArtinMonoidHom_range (K := F) (L := E) V]
    exact hσchosen
  let y : (V.adicCompletion F)ˣ := Classical.choose hRange
  have hy :
      chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y =
        numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ :=
    Classical.choose_spec hRange
  let z : (v.adicCompletion K)ˣ :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (V.adicCompletion F) y
  have hz :
      z = LocalFieldTheory.normUnits
        (v.adicCompletion K) (V.adicCompletion F) y := by
    rfl
  let σK : Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ)
  let restriction : Gal(E / F) →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hrestrict : restriction σE = σK :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
      (K := K) (L := L) p τ
  have hlocal :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
        σK := by
    rw [hz]
    have hnat :=
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
          (K := K) (L := L) (K' := F) (L' := E)
          v V hVbelow) y
    calc
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (V.adicCompletion F) y) =
        restriction
          (chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y) := by
            simpa only [
              MonoidHom.coe_comp, Function.comp_apply, restriction]
              using hnat.symm
      _ = restriction σE := congrArg restriction hy
      _ = σK := hrestrict
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hjLower :
      j.comp auxiliaryOriginalTopAlgHom =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
    apply AlgHom.ext
    intro a
    exact
      numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
        (K := K) (L := L) p τ a
  have hPUnramified :
      P.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension_isUnramified
      (K := K) (L := L) p τ n hn hdegree hprimaryQuotient
  have hcompat :
      (globalNormResidueMonoidHomOfEmbedding F E j).comp
          (IdeleGroup.finitePlaceIdeleClass V) =
        chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V :=
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
      H P hPUnramified V
  have hupper :
      globalNormResidueMonoidHomOfEmbedding F E j
          (IdeleGroup.finitePlaceIdeleClass V y) =
        σE :=
    (congrArg
      (fun φ : (V.adicCompletion F)ˣ →* Gal(E / F) => φ y)
      hcompat).trans hy
  have hnormClass :
      _root_.ideleClassNorm K F
          (IdeleGroup.finitePlaceIdeleClass V y) =
        IdeleGroup.finitePlaceIdeleClass v z := by
    rw [hz]
    simpa only [Vover] using
      (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
        (K := K) (L := F) v Vover y)
  have hglobal :
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
        σK := by
    calc
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          globalNormResidueMonoidHom K L
            (_root_.ideleClassNorm K F
              (IdeleGroup.finitePlaceIdeleClass V y)) :=
        congrArg (globalNormResidueMonoidHom K L) hnormClass.symm
      _ = globalNormResidueMonoidHomOfEmbedding K L
          (j.comp auxiliaryOriginalTopAlgHom)
          (_root_.ideleClassNorm K F
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        rw [hjLower,
          ← globalNormResidueMonoidHom_eq_ofEmbedding_standard]
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding F E j
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        apply Eq.symm
        apply
          globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE :=
        congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) hupper
      _ = restriction σE := rfl
      _ = σK := hrestrict
  exact ⟨z, hlocal, hglobal⟩


/-- Every genuine finite-place decomposition automorphism has a
compatible embedded absolute lift with the same finite quotient class
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_numberFieldTowerFinitePadicLift_of_finitePlace
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain ⟨τΩ, hτΩrestrict, n, hn, hτΩdegree⟩ :=
    exists_finitePlaceSeparableClosureLift_with_positivePadicCyclotomicDegree
      (K := K) (L := L) v p σ
  let τ :
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
    numberFieldTowerSeparableClosureEquivBaseSubgroup
      K L τΩ.1
  have hfinite :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 := by
    change
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (QuotientGroup.mk
            (numberFieldTowerSeparableClosureEquivBaseSubgroup
              K L τΩ.1)) =
        σ.1
    rw [
      numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_baseSubgroupEquiv]
    exact congrArg Subtype.val hτΩrestrict
  have hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
    exact hτΩdegree
  have hdecomposition :
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 := by
    simpa only [τ, MulEquiv.symm_apply_apply] using τΩ.2
  refine
    ⟨τ, hfinite, hdecomposition, ?_, n, hn, hdegree⟩
  rw [hdegree]
  exact
    PadicInt.multiplicative_positiveNatDegree_ne_one
      p.1 n hn

/-- Generation of the actual finite Galois group transports back
through the compatible finite quotient coordinate. -/
theorem
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (σ : Gal(L / K))
    (hτσ :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ)
    (hσ : Subgroup.closure ({σ} : Set (Gal(L / K))) = ⊤) :
    Subgroup.closure
        ({numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ} :
          Set
            ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
              extensionSubgroup
                (numberFieldTowerBaseSubgroup K L)
                (numberFieldTowerTopSubgroup L)
                (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
      ⊤ := by
  let e :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  let q :
      (numberFieldTowerFiniteGaloisSubextension
        K L).extensionQuotient :=
    numberFieldTowerFiniteQuotientCoordinate
      (K := K) (L := L) τ
  have hq : e.toMonoidHom q = σ := by
    exact hτσ
  change
    Subgroup.closure
        ({q} :
          Set
            (numberFieldTowerFiniteGaloisSubextension
              K L).extensionQuotient) =
      ⊤
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [MonoidHom.map_closure, Set.image_singleton,
    hq, hσ,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- If the finite quotient coordinate of a lift generates the whole
finite Galois quotient, then its cyclic preimage together with the
top-field subgroup generates the whole embedded absolute Galois
group. -/
theorem
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ⊔
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) =
      ⊤ := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let finiteProjection :
      P.toSubgroup →*
        Q :=
    (MonoidHom.fst Q
      (Multiplicative ℤ_[p.1])).comp
        P.toSubgroup.subtype
  have hprojection :
      Γ.toSubgroup.map finiteProjection = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    apply (Subgroup.closure_le _).2
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    refine
      ⟨γ,
        (ClassFormation.padicCyclicClosureGenerator γ).2,
        ?_⟩
    rfl
  have hquotientSurjective :
      ∀ q : Q,
        ∃ u : H.toSubgroup,
          u ∈
              (numberFieldTowerFinitePadicCyclicPreimage
                (K := K) (L := L) p τ).toSubgroup ∧
            numberFieldTowerFiniteQuotientCoordinate
                (K := K) (L := L) u =
              q := by
    intro q
    have hq :
        q ∈ Γ.toSubgroup.map finiteProjection := by
      rw [hprojection]
      trivial
    obtain ⟨z, hzΓ, hzq⟩ := hq
    obtain ⟨u, hu⟩ :=
      numberFieldTowerFinitePadicRangeRestriction_surjective
        (K := K) (L := L) p z
    refine ⟨u, ?_, ?_⟩
    · change rangeRestriction u ∈ Γ.toSubgroup
      rw [hu]
      exact hzΓ
    · calc
        numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) u =
            finiteProjection (rangeRestriction u) := rfl
        _ = finiteProjection z := congrArg finiteProjection hu
        _ = q := hzq
  apply top_unique
  intro h _
  obtain ⟨u, huU, huq⟩ :=
    hquotientSurjective
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) h)
  let k : H.toSubgroup :=
    h * u⁻¹
  have hkN : k ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) k).mp
    change
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) (h * u⁻¹) =
        1
    rw [map_mul, map_inv, huq, mul_inv_cancel]
  have hkSup :
      k ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_right :
      N ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) hkN
  have huSup :
      u ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_left :
      (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) huU
  have hku :
      k * u = h := by
    simp only [k, inv_mul_cancel_right]
  rw [← hku]
  exact
    ((numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ).toSubgroup ⊔ N).mul_mem
      hkSup huSup

/-- Ambient form of the generation statement: the auxiliary cyclic
fixed subgroup together with the subgroup fixing `L` generates the
subgroup fixing `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ⊔
        (numberFieldTowerTopSubgroup L).toSubgroup =
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup
      H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  have hrelative :
      U.toSubgroup ⊔ N = ⊤ :=
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
      (K := K) (L := L) p τ hgenerate
  have hNmap :
      N.map H.toSubgroup.subtype =
        T.toSubgroup := by
    exact
      Subgroup.map_subgroupOf_eq_of_le
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  change
    U.toSubgroup.map H.toSubgroup.subtype ⊔
        T.toSubgroup =
      H.toSubgroup
  rw [← hNmap, ← Subgroup.map_sup,
    hrelative, ← MonoidHom.range_eq_map,
    H.toSubgroup.range_subtype]

/-- The concrete auxiliary fixed field is linearly disjoint from `L`
over the compatible embedded copy of `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedField_inf_topField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let H :=
    numberFieldTowerBaseSubgroup K L
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L),
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldTowerBaseField K L)]
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        IntermediateField.fixedField T.toSubgroup =
      IntermediateField.fixedField H.toSubgroup
  rw [
    ← IntermediateField.fixedField_sup_eq_inf,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
      (K := K) (L := L) p τ hgenerate]

/-- If the finite quotient coordinate is `p`-primary, adjoining the
actual rational `p`-primary cyclotomic field to the auxiliary fixed
field contains the compatible copy of `L`.

This is the field-theoretic conclusion of the simultaneous
finite/cyclotomic lift: the intersection of the two fixing subgroups
already fixes `L`, hence their fixed-field compositum contains `L`. -/
theorem
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    numberFieldInRationalSeparableClosure L ≤
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊔
        rationalCyclotomicPadicField p := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  let C : @IntermediateField ℚ (SeparableClosure ℚ) _ _
      rationalSeparableClosureAlgebra :=
    rationalCyclotomicPadicField p
  have hfixing :
      (F ⊔ C).fixingSubgroup ≤
        T.toSubgroup := by
    change
      (IntermediateField.fixedField S.toSubgroup ⊔ C).fixingSubgroup ≤
        T.toSubgroup
    rw [
      IntermediateField.fixingSubgroup_sup,
      InfiniteGalois.fixingSubgroup_fixedField S]
    intro σ hσ
    apply
      numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
        (K := K) (L := L) p τ n hn hdegree hprimary
    refine ⟨hσ.1, ?_⟩
    let : Algebra ℚ rationalCyclotomicZHatField :=
      rationalCyclotomicZHatField.algebra'
    let : @Normal ℚ rationalCyclotomicZHatField _ _
        rationalCyclotomicZHatField.algebra' :=
      rationalCyclotomicZHatField_normal
    let E :=
      rationalCyclotomicPadicFieldWithinZHat p
    change
      rationalCyclotomicPadicCoordinate p
          (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) =
        1
    have hr :
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ ∈
          E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have hfix :
          σ x.1 = x.1 :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IntermediateField.lift E) σ).1 hσ.2 x.1
            ((IntermediateField.mem_lift x).2 hx)
      exact
        (AlgEquiv.restrictNormal_commutes
          σ rationalCyclotomicZHatField x).trans hfix
    rw [rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup]
      at hr
    exact hr
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L)]
  change
    IntermediateField.fixedField T.toSubgroup ≤
      F ⊔ C
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (F ⊔ C)]
  exact
    IntermediateField.fixedField_le hfixing

/-- For a finite-place automorphism generating `Gal(L/K)`, construct
the genuine auxiliary number field used in the cyclotomic reduction.

The field is finite over `ℚ`, contains the compatible copy of `K`, and
has intersection with the compatible copy of `L` exactly equal to that
copy of `K`.  Its defining lift has the prescribed local restriction
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_finitePlaceCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hσ :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        n, hn, hdegree⟩ :=
    exists_numberFieldTowerFinitePadicLift_of_finitePlace
      (K := K) (L := L) v p σ
  have hgenerate :=
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
      (K := K) (L := L) τ σ.1 hτσ hσ
  refine
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
        (K := K) (L := L) p τ hτdegree,
      numberFieldTowerBaseField_le_finitePadicCyclicFixedField
        (K := K) (L := L) p τ,
      numberFieldTowerFinitePadicCyclicFixedField_inf_topField
        (K := K) (L := L) p τ hgenerate,
      n, hn, hdegree⟩

/-- A `p`-primary local generator admits a genuine auxiliary number
field whose compositum with the rational `p`-primary cyclotomic field
contains `L`.

Besides the field containment, the construction records the two
properties needed for descent: the auxiliary field meets `L` exactly
in `K`, and the chosen absolute lift has positive integral
cyclotomic degree. -/
theorem exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤)
    (hprimary :
      σ.1 ∈
        CommGroup.primaryComponent
          (Gal(L / K)) p.1) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
      numberFieldInRationalSeparableClosure L ≤
        numberFieldTowerFinitePadicCyclicFixedField
              (K := K) (L := L) p τ ⊔
          rationalCyclotomicPadicField p ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        hfinite, hbase, hintersection,
        n, hn, hdegree⟩ :=
    exists_finitePlaceCyclotomicAuxiliaryFixedField
      (K := K) (L := L) v p σ hgenerate
  have hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1 := by
    obtain ⟨m, hm⟩ := hprimary
    refine ⟨m, ?_⟩
    let e :=
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
    let q :=
      numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ
    let N : ℕ := p.1 ^ m
    have hq : e q = σ.1 := by
      exact hτσ
    have hmN : σ.1 ^ N = 1 := by
      exact hm
    change q ^ N = 1
    apply e.injective
    calc
      e (q ^ N) = (e q) ^ N := by
        exact map_pow e q N
      _ = σ.1 ^ N := by rw [hq]
      _ = 1 := hmN
      _ = e 1 := (map_one e).symm
  have hcontainment :=
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
      (K := K) (L := L) p τ n hn hdegree
        hprimaryQuotient
  exact
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      hfinite, hbase, hintersection,
      hcontainment, n, hn, hdegree⟩

end Reciprocity
end GlobalClassFieldTheory
