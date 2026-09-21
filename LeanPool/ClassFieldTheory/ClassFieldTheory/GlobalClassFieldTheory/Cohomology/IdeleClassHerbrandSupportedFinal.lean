/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Local
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyFinite
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyCardinality
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Factors
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlace
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.HerbrandExactSequence
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
/-!
# Supported ideles and the idele-class norm index

This file joins the unrestricted local calculation, the vanishing of
the unramified integral factors outside the support, and the exact
sequence from `S`-units to supported ideles and idele classes.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Outside the canonical Herbrand support, the chosen completed local
extension is unramified. -/
theorem
    chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ ideleClassHerbrandSupport (K := K) (L := L)) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (K := K) (L := L) v
  apply isUnramifiedAt_of_notMem_ideleClassHerbrandSupport
    (K := K) (L := L) v hv
  exact
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)

omit [NumberField L] in
/-- If every chosen finite extension outside `S` is unramified, both
low-degree Tate cohomology groups of the product of its integral
factors are singletons. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    Subsingleton
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)) ∧
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ) := by
  let componentAction :
      ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        MulDistribMulAction (L ≃ₐ[K] L)
          (relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) :=
    herbrandH0PiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1)
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ :=
    herbrandHMinusOnePiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) σ
  constructor
  · constructor
    intro x y
    apply e0.injective
    funext w
    let :
        Subsingleton
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1)) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandH0_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _
  · constructor
    intro x y
    apply em.injective
    funext w
    let :
        Subsingleton
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandHMinusOne_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _

omit [NumberField L] in
/-- The product of integral factors outside an unramified support has
Herbrand quotient one. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 = 1 := by
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  have hsub :=
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
      (K := K) (L := L) S σ hgen hUnram
  let h0Subsingleton := hsub.1
  let hmSubsingleton := hsub.2
  let h :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_subsingleton, Finite.of_subsingleton⟩
  refine ⟨h, ?_⟩
  let h0Finite := h.1
  let hmFinite := h.2
  let : Inhabited
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    ⟨1⟩
  let : Inhabited
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    ⟨1⟩
  let : Unique
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    Unique.mk' _
  let : Unique
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    Unique.mk' _
  rw [herbrandQuotient_eq_card_ratio,
    Nat.card_unique,
    Nat.card_unique]
  norm_num

/-- After the unramified outside factors have been removed, the supported
relative ideles have Herbrand quotient equal to the product of the local
degrees at the unrestricted factors. -/
theorem
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := by
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let unrestrictedAction :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let hU :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen,
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen⟩
  obtain ⟨hO, hOq⟩ :=
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
      (K := K) (L := L) S σ hgen hUnram
  let hU0 := hU.1
  let hUm := hU.2
  let hO0 := hO.1
  let hOm := hO.2
  let hProd0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S)) :=
    herbrandH0ProdFinite _ _
  let hProdm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ) :=
    herbrandHMinusOneProdFinite _ _ σ
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) ≃*
        HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) :=
    relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside
      (K := K) (L := L) S
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ ≃*
        HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
    relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside
      (K := K) (L := L) S σ
  let hSupported :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_equiv _ e0.symm.toEquiv,
      Finite.of_equiv _ em.symm.toEquiv⟩
  refine ⟨hSupported, ?_⟩
  let hS0 := hSupported.1
  let hSm := hSupported.2
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A :=
            RelativeUnrestrictedSPlaceFactors
                (K := K) (L := L) S ×
              RelativeOutsideSPlaceFactors
                (K := K) (L := L) S) σ :=
      herbrandQuotient_eq_of_equivariantMulEquiv
        (relativeIdeleSupportedEquivUnrestrictedProdOutside
          (K := K) (L := L) S)
        (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
          (K := K) (L := L) S) σ
    _ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
      herbrandQuotient_prod _ _ σ
    _ =
        (∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ)) * 1 := by
      rw [
        relativeUnrestrictedSPlaceFactors_herbrandQuotient
          (K := K) (L := L) S σ hgen,
        hOq]
    _ =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := mul_one _

/-- The diagonal map from extension-field `S`-units directly into the
supported relative ideles. -/
noncomputable def sUnitToRelativeIdeleSupported
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →*
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S :=
  ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype.comp
    (sUnitToRelativePrincipalSupportedIntersection
      (K := K) (L := L) S)

/-- The restriction of the idele-class quotient map to the supported
relative ideles. -/
noncomputable def relativeIdeleSupportedToClass
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S →*
      RelativeIdeleGroup.ClassGroup K L :=
  (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)).comp
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S).subtype

omit [IsGalois K L] in
/-- Equivariance of the diagonal `S`-unit map into supported relative
ideles. -/
theorem sUnitToRelativeIdeleSupported_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      sUnitMulDistribMulAction K L
        (finitePlacesAbove (K := K) (L := L) S)
        (finitePlacesAbove_isGaloisStable
          (K := K) (L := L) S)
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∀ (σ : L ≃ₐ[K] L)
      (x :
        SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S)),
      sUnitToRelativeIdeleSupported
          (K := K) (L := L) S (σ • x) =
        σ •
          sUnitToRelativeIdeleSupported
            (K := K) (L := L) S x := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  intro σ x
  apply Subtype.ext
  change
    RelativeIdeleGroup.principalIdele K L
        (((σ • x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) :
          Lˣ)) =
      σ • RelativeIdeleGroup.principalIdele K L (x : Lˣ)
  rw [sUnit_smul_coe]
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ (x : Lˣ)).symm

omit [NumberField L] [IsGalois K L] in
/-- Equivariance of the supported-idele quotient map. -/
theorem relativeIdeleSupportedToClass_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI := ideleClassMulDistribMulAction K L
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S),
      relativeIdeleSupportedToClass
          (K := K) (L := L) S (σ • z) =
        σ •
          relativeIdeleSupportedToClass
            (K := K) (L := L) S z := by
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let classAction := ideleClassMulDistribMulAction K L
  intro σ z
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        ((σ • z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :
          RelativeIdeleGroup K L) =
      σ •
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (z : RelativeIdeleGroup K L)
  rw [
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe]
  exact ideleClassQuotientMap_equivariant K L σ z

omit [IsGalois K L] in
/-- The diagonal `S`-unit map into supported relative ideles is
injective. -/
theorem sUnitToRelativeIdeleSupported_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitToRelativeIdeleSupported
        (K := K) (L := L) S) := by
  intro x y hxy
  apply
    (sUnitEquivRelativePrincipalSupportedIntersection
      (K := K) (L := L) S).injective
  apply
    ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype_injective
  exact hxy

omit [NumberField L] [IsGalois K L] in
/-- If the supported and principal relative ideles generate all
relative ideles, the restricted map to idele classes is surjective. -/
theorem relativeIdeleSupportedToClass_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤) :
    Function.Surjective
      (relativeIdeleSupportedToClass
        (K := K) (L := L) S) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S ⊔
            RelativeIdeleGroup.principalSubgroup K L := by
    rw [hSP]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨s, hs, p, hp, hsp⟩ := hg
  refine ⟨⟨s, hs⟩, ?_⟩
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) g
  rw [← hsp, map_mul]
  have hpone :
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) p =
        1 :=
    (QuotientGroup.eq_one_iff
      (N := RelativeIdeleGroup.principalSubgroup K L)
      (x := p)).2 hp
  rw [hpone]
  exact
    (mul_one
      (QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s)).symm

omit [IsGalois K L] in
/-- Exactness at the supported relative ideles of
`S`-units → supported ideles → idele classes. -/
theorem sUnit_supportedIdele_ideleClass_exact
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ z :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S,
      relativeIdeleSupportedToClass
          (K := K) (L := L) S z = 1 ↔
        ∃ x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S),
          sUnitToRelativeIdeleSupported
              (K := K) (L := L) S x =
            z := by
  intro z
  constructor
  · intro hz
    have hzPrincipal :
        (z : RelativeIdeleGroup K L) ∈
          RelativeIdeleGroup.principalSubgroup K L := by
      exact
        (QuotientGroup.eq_one_iff
          (N := RelativeIdeleGroup.principalSubgroup K L)
          (x := (z : RelativeIdeleGroup K L))).1 hz
    let y :
        (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :=
      ⟨z, hzPrincipal⟩
    obtain ⟨x, hx⟩ :=
      (sUnitEquivRelativePrincipalSupportedIntersection
        (K := K) (L := L) S).surjective y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hcoerce :=
      congrArg
        (fun a :
          (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) =>
          (a :
            relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S))
        hx
    exact congrArg Subtype.val hcoerce
  · rintro ⟨x, rfl⟩
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (RelativeIdeleGroup.principalIdele K L (x : Lˣ)) =
        1
    exact
      (QuotientGroup.eq_one_iff
        (N := RelativeIdeleGroup.principalSubgroup K L)
        (x :=
          RelativeIdeleGroup.principalIdele K L (x : Lˣ))).2
        ⟨(x : Lˣ), rfl⟩

/-- Finiteness of the low Tate groups of the `S`-unit module for the
support pulled back from `K`. -/
def AboveSUnitHerbrandQuotientDefined
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) : Prop :=
  letI :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  HerbrandQuotientDefined
    (L ≃ₐ[K] L)
    (SUnitGroup (K := L)
      (finitePlacesAbove (K := K) (L := L) S)) σ

/-- Finiteness of the low Tate groups of the supported relative-idele
module. -/
def RelativeIdeleSupportedHerbrandQuotientDefined
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) : Prop :=
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  HerbrandQuotientDefined
    (L ≃ₐ[K] L)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) σ

/-- The permutation-representation presentation of the action on
logarithmic places above a base support.  This is the presentation used
by the `S`-unit Herbrand theorem. -/
@[reducible]
noncomputable def aboveSLogPlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :=
  permutationMulAction
    (logPlacePermutationHom K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S))

/-- Send a logarithmic place of `L` lying over the pulled-back support
to its underlying unrestricted place of `K`. -/
noncomputable def logPlaceBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →
      RelativeUnrestrictedSPlaceIndex (K := K) S
  | Sum.inl W =>
      Sum.inl (W.comap (algebraMap K L))
  | Sum.inr W =>
      Sum.inr
        ⟨finitePlaceBelow (K := K) W.1,
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W.1).1 W.2⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The place-below map is constant on Galois orbits of logarithmic
places. -/
theorem logPlaceBelowRelativeUnrestrictedIndex_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (σ • q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q := by
  let logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  cases q with
  | inl W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inl W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inl W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inl ((σ • W).comap (algebraMap K L)) =
          Sum.inl (W.comap (algebraMap K L))
      congr 1
      rw [NumberField.InfinitePlace.comap_smul]
      congr 1
      ext x
      exact σ.symm.commutes x
  | inr W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inr W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inr W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inr
            (⟨finitePlaceBelow (K := K)
                (finitePlaceEquiv K L σ W.1), _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
          Sum.inr
            (⟨finitePlaceBelow (K := K) W.1, _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      congr 1
      apply Subtype.ext
      exact
        finitePlaceBelow_finitePlaceEquiv
          (K := K) (L := L) σ W.1

/-- The map on Galois orbits induced by taking the place below. -/
noncomputable def logPlaceOrbitBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) →
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  letI logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  exact
    Quotient.lift
      (logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S)
      (by
        intro a b hab
        rcases hab with ⟨σ, hσ⟩
        rw [← hσ]
        exact
          logPlaceBelowRelativeUnrestrictedIndex_smul
            (K := K) (L := L) S σ b)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Evaluating the orbit-descended log-place map on a quotient class gives
the original map on any representative. -/
@[simp]
theorem logPlaceOrbitBelowRelativeUnrestrictedIndex_mk
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceOrbitBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (Quotient.mk'' q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q :=
  rfl

/-- Galois orbits of logarithmic places of `L` above `S` are
canonically indexed by all infinite places of `K` and the finite
places in `S`. -/
noncomputable def
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) ≃
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  letI stableFiniteAction :=
    stableFinitePlaceMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  letI logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  let f :=
    logPlaceOrbitBelowRelativeUnrestrictedIndex
      (K := K) (L := L) S
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | _ a =>
      induction y using Quotient.inductionOn' with
      | _ b =>
        apply Quotient.sound
        change a ∈ MulAction.orbit (L ≃ₐ[K] L) b
        cases a with
        | inl W₁ =>
            cases b with
            | inl W₂ =>
                have hbelow :
                    W₁.comap (algebraMap K L) =
                      W₂.comap (algebraMap K L) := by
                  exact Sum.inl.inj hxy
                obtain ⟨σ, hσ⟩ :=
                  NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
                    hbelow
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inl W₂) =
                    Sum.inl W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inl (σ⁻¹ • W₂) = Sum.inl W₁
                rw [← hσ, inv_smul_smul]
            | inr W₂ =>
                change
                  Sum.inl (W₁.comap (algebraMap K L)) =
                    Sum.inr
                      (⟨finitePlaceBelow (K := K) W₂.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
                  at hxy
                exact (Sum.inl_ne_inr hxy).elim
        | inr W₁ =>
            cases b with
            | inl W₂ =>
                change
                  Sum.inr
                      (⟨finitePlaceBelow (K := K) W₁.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
                    Sum.inl (W₂.comap (algebraMap K L))
                  at hxy
                exact (Sum.inr_ne_inl hxy).elim
            | inr W₂ =>
                have hbelow :
                    finitePlaceBelow (K := K) W₁.1 =
                      finitePlaceBelow (K := K) W₂.1 := by
                  exact congrArg Subtype.val (Sum.inr.inj hxy)
                let v :=
                  finitePlaceBelow (K := K) W₁.1
                let : Finite (L ≃ₐ[K] L) :=
                  IsGaloisGroup.finite (L ≃ₐ[K] L) K L
                let :
                    IsGaloisGroup
                      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
                  IsGaloisGroup.of_isFractionRing
                    (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
                let : W₁.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    simp only [v, finitePlaceBelow_asIdeal]⟩
                let : W₂.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    have h :=
                      congrArg HeightOneSpectrum.asIdeal hbelow
                    simpa only [v, finitePlaceBelow_asIdeal]
                      using h⟩
                obtain ⟨σ, hσ⟩ :=
                  HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
                    v.asIdeal W₁.1.asIdeal W₂.1.asIdeal
                    (L ≃ₐ[K] L)
                have hplace :
                    finitePlaceEquiv K L σ W₁.1 = W₂.1 := by
                  apply HeightOneSpectrum.ext
                  rw [finitePlaceEquiv_asIdeal]
                  exact hσ
                have hsubtype : σ • W₁ = W₂ := by
                  apply Subtype.ext
                  exact hplace
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inr W₂) =
                    Sum.inr W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inr (σ⁻¹ • W₂) = Sum.inr W₁
                rw [← hsubtype, inv_smul_smul]
  · intro i
    cases i with
    | inl v =>
        refine
          ⟨Quotient.mk''
              (Sum.inl
                (chosenInfinitePlaceAbove (L := L) v)), ?_⟩
        exact
          congrArg Sum.inl
            (chosenInfinitePlaceAbove_comap
              (L := L) v)
    | inr v =>
        let w :=
          chosenFinitePlaceExtension (L := L) v.1
        let W :=
          finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWbelow :
            finitePlaceBelow (K := K) W = v.1 :=
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWmem :
            W ∈ finitePlacesAbove
              (K := K) (L := L) S :=
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W).2
            (hWbelow ▸ v.2)
        refine
          ⟨Quotient.mk''
              (Sum.inr
                (⟨W, hWmem⟩ :
                  finitePlacesAbove
                    (K := K) (L := L) S)), ?_⟩
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hWbelow

/-- The local degree attached to a logarithmic place agrees with the
local degree attached to its place below. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S
        (logPlaceBelowRelativeUnrestrictedIndex
          (K := K) (L := L) S q) =
      logPlaceLocalDegree K L
        (finitePlacesAbove (K := K) (L := L) S) q := by
  cases q with
  | inl W =>
      let W₀ :=
        chosenInfinitePlaceAbove
          (L := L) (W.comap (algebraMap K L))
      change
        Nat.card (absoluteValueDecompositionGroup K W₀.1) =
          if NumberField.InfinitePlace.IsUnramified K W
          then 1 else 2
      rw [
        absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer W₀,
        NumberField.InfinitePlace.card_stabilizer]
      have hcomap :
          W₀.comap (algebraMap K L) =
            W.comap (algebraMap K L) :=
        chosenInfinitePlaceAbove_comap
          (L := L) (W.comap (algebraMap K L))
      obtain ⟨τ, hτ⟩ :=
        NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
          hcomap
      rw [← hτ,
        NumberField.InfinitePlace.isUnramified_smul_iff]
  | inr W =>
      let v :=
        finitePlaceBelow (K := K) W.1
      let w :=
        chosenFinitePlaceExtension (L := L) v
      let W₀ :=
        finitePlaceExtensionCentre
          (K := K) (L := L) v w
      let finiteAction := finitePlaceMulAction K L
      let : Finite (L ≃ₐ[K] L) :=
        IsGaloisGroup.finite (L ≃ₐ[K] L) K L
      let :
          IsGaloisGroup
            (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
        IsGaloisGroup.of_isFractionRing
          (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
      let : W₀.asIdeal.LiesOver v.asIdeal :=
        ⟨(finitePlaceExtensionCentreIdeal_under
          (K := K) (L := L) v w).symm⟩
      let : W.1.asIdeal.LiesOver v.asIdeal :=
        ⟨by
          simp only [v, finitePlaceBelow_asIdeal]⟩
      obtain ⟨τ, hτ⟩ :=
        HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
          v.asIdeal W₀.asIdeal W.1.asIdeal
          (L ≃ₐ[K] L)
      have hplace :
          finitePlaceEquiv K L τ W₀ = W.1 := by
        apply HeightOneSpectrum.ext
        rw [finitePlaceEquiv_asIdeal]
        exact hτ
      have hcard :
          Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W₀) =
            Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W.1) :=
        Nat.card_congr
          (MulAction.stabilizerEquivStabilizer
            hplace.symm).toEquiv
      change
        Nat.card (absoluteValueDecompositionGroup K w.1) =
          finiteLogPlaceLocalDegree K L W.1
      rw [
        absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
          (K := K) (L := L) v w]
      exact
        hcard.trans
          (finitePlace_stabilizer_card_eq_localDegree
            K L W.1)

/-- The local-degree product occurring in the supported-idele
calculation is exactly the orbit-indexed local-degree product occurring
in the `S`-unit calculation. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    letI :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
      Fintype.ofFinite _
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
      ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
        (logPlaceLocalDegree K L
          (finitePlacesAbove (K := K) (L := L) S)
          ω.out : ℚ) := by
  let logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace
            (K := L)
            (finitePlacesAbove
              (K := K) (L := L) S))) :=
    Fintype.ofFinite _
  let e :=
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
      (K := K) (L := L) S
  calc
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
        ∏ ω,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S (e ω) : ℚ) :=
      (e.prod_comp
        (fun i =>
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ))).symm
    _ =
        ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
          (logPlaceLocalDegree K L
            (finitePlacesAbove (K := K) (L := L) S)
            ω.out : ℚ) := by
      apply Finset.prod_congr rfl
      intro ω hω
      have he :
          e ω =
            logPlaceBelowRelativeUnrestrictedIndex
              (K := K) (L := L) S ω.out := by
        calc
          e ω = e (Quotient.mk'' ω.out) :=
            congrArg e (Quotient.out_eq' ω).symm
          _ =
              logPlaceBelowRelativeUnrestrictedIndex
                (K := K) (L := L) S ω.out := rfl
      rw [he]
      exact_mod_cast
        relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
          (K := K) (L := L) S ω.out

omit [IsGalois K L] in
/-- Cancellation on the supported short exact sequence: if supported
ideles and `S`-units have quotients `q` and `q / |G|`, respectively,
then the idele-class quotient is `|G|`. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnitDefined :
      AboveSUnitHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (hSupportedDefined :
      RelativeIdeleSupportedHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (q : ℚ) (hq : q ≠ 0)
    (hSupported :
      letI :=
        relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S)) :=
        hSupportedDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) σ) :=
        hSupportedDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ = q)
    (hUnit :
      letI :=
        sUnitMulDistribMulAction K L
          (finitePlacesAbove (K := K) (L := L) S)
          (finitePlacesAbove_isGaloisStable
            (K := K) (L := L) S)
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
        hUnitDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)) σ) :=
        hUnitDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let classAction := ideleClassMulDistribMulAction K L
  let hU0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S))) :=
    hUnitDefined.1
  let hUm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ) :=
    hUnitDefined.2
  let hS0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)) :=
    hSupportedDefined.1
  let hSm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ) :=
    hSupportedDefined.2
  let i :
      SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S) →*
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S :=
    sUnitToRelativeIdeleSupported
      (K := K) (L := L) S
  let j :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S →*
        RelativeIdeleGroup.ClassGroup K L :=
    relativeIdeleSupportedToClass
      (K := K) (L := L) S
  have hi :
      ∀ (τ : L ≃ₐ[K] L)
        (x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)),
        i (τ • x) = τ • i x := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_equivariant
        (K := K) (L := L) S)
  have hj :
      ∀ (τ : L ≃ₐ[K] L)
        (z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S),
        j (τ • z) = τ • j z := by
    simpa [j] using
      (relativeIdeleSupportedToClass_equivariant
        (K := K) (L := L) S)
  have hker :
      ∀ z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S,
        j z = 1 ↔
          ∃ x :
            SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S),
            i x = z := by
    simpa [i, j] using
      (sUnit_supportedIdele_ideleClass_exact
        (K := K) (L := L) S)
  have hinj : Function.Injective i := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_injective
        (K := K) (L := L) S)
  have hsurj : Function.Surjective j := by
    simpa [j] using
      (relativeIdeleSupportedToClass_surjective
        (K := K) (L := L) S hSP)
  let hC :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotientDefined_right_of_left_middle
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj
      σ hgen hUnitDefined hSupportedDefined
  let hC0 := hC.1
  let hCm := hC.2
  have hmul :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotient_multiplicative_of_shortExact
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj σ hgen
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfactor :
      q / (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    div_ne_zero hq hcard
  refine ⟨hC, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)
            _ _ _ _ σ hC.1 hC.2 =
        q := by
      rw [← hUnit, ← hmul, hSupported]
    _ =
        (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      rw [div_mul_cancel₀ q hcard]

/-- The norm-index lower bound obtained from the supported short exact
sequence. -/
theorem
    card_le_ideleClassNorm_index_of_sUnit_supported_values
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnitDefined :
      AboveSUnitHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (hSupportedDefined :
      RelativeIdeleSupportedHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (q : ℚ) (hq : q ≠ 0)
    (hSupported :
      letI :=
        relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S)) :=
        hSupportedDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) σ) :=
        hSupportedDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ = q)
    (hUnit :
      letI :=
        sUnitMulDistribMulAction K L
          (finitePlacesAbove (K := K) (L := L) S)
          (finitePlacesAbove_isGaloisStable
            (K := K) (L := L) S)
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
        hUnitDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)) σ) :=
        hUnitDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  let classAction := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
      (K := K) (L := L) S σ hgen hSP
      hUnitDefined hSupportedDefined q hq hSupported hUnit
  let hC0 := hC.1
  let hCm := hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

/-- With all local and `S`-unit calculations substituted, an unramified
sufficiently large support gives an idele-class Herbrand quotient equal
to the order of the Galois group. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let T :=
    finitePlacesAbove (K := K) (L := L) S
  let hT :
      IsGaloisStableFinitePlaces K L T :=
    finitePlacesAbove_isGaloisStable
      (K := K) (L := L) S
  let ρ :=
    logPlacePermutationHom K L T hT
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) T) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) T) :=
    sUnitMulDistribMulAction K L T hT
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) T)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) T),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hUnit, hUnitValue⟩ :=
    sUnit_herbrandQuotient_eq_localDegreeProduct_div_card
      (K := K) (L := L) hT σ hgen
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  obtain ⟨hSupported, hSupportedValue⟩ :=
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
      (K := K) (L := L) S σ hgen hUnram
  let q : ℚ :=
    ∏ i,
      (relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S i : ℚ)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact
      Nat.cast_ne_zero.mpr
        (show
          relativeUnrestrictedSPlaceLocalDegree
              (K := K) (L := L) S i ≠ 0 by
          unfold relativeUnrestrictedSPlaceLocalDegree
          exact Nat.card_pos.ne')
  have hProducts :
      q =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) T),
          (logPlaceLocalDegree K L T ω.out : ℚ) := by
    simpa [q, T, hT, ρ] using
      (relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
        (K := K) (L := L) S)
  have hUnitValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) T)
          _ _ _ _ σ hUnit.1 hUnit.2 =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
    rw [hProducts]
    simpa only [indexAction, ρ, T, hT] using hUnitValue
  have hSupportedValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        q := by
    exact hSupportedValue
  exact
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
      (K := K) (L := L) S σ hgen hSP
      hUnit hSupported q hq
      hSupportedValue' hUnitValue'

/-- The corresponding norm-index lower bound with all supported local
calculations substituted. -/
theorem
    card_le_ideleClassNorm_index_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  let classAction := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
      (K := K) (L := L) S σ hgen hSP hUnram
  let hC0 := hC.1
  let hCm := hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

/-- Unconditional norm-index lower bound for a cyclic extension, in
Galois-group-order form. -/
theorem card_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
  card_le_ideleClassNorm_index_of_supported_local_calculation
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
    σ hgen
    (relativeSupportedAboveHerbrandSupport_sup_principal_eq_top
      (K := K) (L := L))
    (chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := L))

/-- Unconditional norm-index lower bound in extension-degree form. -/
theorem finrank_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Module.finrank K L ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  simpa only [Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank K L] using
    card_le_ideleClassNorm_index
      (K := K) (L := L) σ hgen

end Cohomology
end GlobalClassFieldTheory
