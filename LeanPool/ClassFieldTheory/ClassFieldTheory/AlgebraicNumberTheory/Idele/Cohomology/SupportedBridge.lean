/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Reassociation
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SufficientlyLarge
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Permutation.Module
/-!
# A sufficiently large unramified support for the idele-class calculation

This file constructs the finite set used in the idele-class Herbrand calculation.  It
contains the contractions of a sufficiently large set of places of `L`
and every finite place of `K` at which some place of `L` ramifies.

It also compares the concrete tensor-coordinate supported subgroup of
relative ideles with the ordinary supported idele subgroup of `L`.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The finite set of places of `L` lying above a finite set of places
of `K`. -/
noncomputable def finitePlacesAbove
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 L)) :=
  (Set.Finite.preimage_finitePlaceBelow
    (K := K) (L := L) S.finite_toSet).toFinset

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem mem_finitePlacesAbove_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : HeightOneSpectrum (𝓞 L)) :
    W ∈ finitePlacesAbove (K := K) (L := L) S ↔
      finitePlaceBelow (K := K) W ∈ S := by
  simp [finitePlacesAbove]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Galois conjugation does not change the place lying below a finite
place of the extension field. -/
@[simp]
theorem finitePlaceBelow_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceBelow (K := K) (finitePlaceEquiv K L σ W) =
      finitePlaceBelow (K := K) W := by
  apply HeightOneSpectrum.ext
  rw [finitePlaceBelow_asIdeal, finitePlaceBelow_asIdeal,
    finitePlaceEquiv_asIdeal]
  ext x
  rw [Ideal.mem_under, Ideal.mem_under]
  have hfix :
      NumberField.RingOfIntegers.mapAlgEquiv σ
          (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap (𝓞 K) (𝓞 L) x := by
    apply NumberField.RingOfIntegers.ext
    exact σ.commutes (x : K)
  conv_lhs => rw [← hfix]
  exact
    (Ideal.apply_mem_of_equiv_iff
      (I := W.asIdeal)
      (f :=
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
      (x := algebraMap (𝓞 K) (𝓞 L) x))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The full set of extension places above a base support is stable
under the concrete Galois action. -/
theorem finitePlacesAbove_isGaloisStable
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsGaloisStableFinitePlaces K L
      (finitePlacesAbove (K := K) (L := L) S) := by
  intro σ W
  simp only [mem_finitePlacesAbove_iff]
  change
    finitePlaceBelow (K := K) W ∈ S ↔
      finitePlaceBelow (K := K)
        (finitePlaceEquiv K L σ W) ∈ S
  rw [finitePlaceBelow_finitePlaceEquiv]

omit [IsGalois K L] in
/-- Scalar extension carries the concrete supported
relative ideles exactly to the ordinary ideles supported at all places
above the same base support. -/
theorem relativeIdeleBaseChange_mem_supportedAt_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : RelativeIdeleGroup K L) :
    z ∈ relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ↔
      relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z ∈
        IdeleGroup.supportedAt (K := L)
          (finitePlacesAbove (K := K) (L := L) S : Set _) := by
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff,
    IdeleGroup.mem_supportedAt_iff]
  constructor
  · intro hz W hW
    have hbelow :
        finitePlaceBelow (K := K) W ∉ S := by
      intro hmem
      exact hW ((mem_finitePlacesAbove_iff
        (K := K) (L := L) S W).2 hmem)
    have hlocal :=
      (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W) z)).1
        (hz (finitePlaceBelow (K := K) W) hbelow) ⟨W, rfl⟩
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply]
    exact hlocal
  · intro hz w hw
    apply
      (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
        (K := K) (L := L) w
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z)).2
    intro W
    rcases W with ⟨W, hWbelow⟩
    subst w
    have hW :
        W ∉ (finitePlacesAbove (K := K) (L := L) S :
          Set (HeightOneSpectrum (𝓞 L))) := by
      intro hmem
      exact hw ((mem_finitePlacesAbove_iff
        (K := K) (L := L) S W).1 hmem)
    have hlocal := hz W hW
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply] at hlocal
    exact hlocal

omit [IsGalois K L] in
/-- Subgroup-level form of
`relativeIdeleBaseChange_mem_supportedAt_iff`. -/
theorem relativeIdeleLocalTensorDecompositionSupportedSubgroup_map_baseChange
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S).map
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).toMonoidHom =
      IdeleGroup.supportedAt (K := L)
        (finitePlacesAbove (K := K) (L := L) S : Set _) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact
      (relativeIdeleBaseChange_mem_supportedAt_iff
        (K := K) (L := L) S z).1 hz
  · intro hy
    refine ⟨(relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).symm y, ?_, ?_⟩
    · apply
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S _).2
      simpa using hy
    · exact
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).apply_symm_apply y

omit [IsGalois K L] in
/-- If the supported ordinary ideles and principal ideles generate
`I_L`, then their relative counterparts generate the full relative
idele group. -/
theorem relativeIdeleSupported_sup_principal_eq_top
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hOrdinary :
      IdeleGroup.supportedAt (K := L)
          (finitePlacesAbove (K := K) (L := L) S : Set _) ⊔
        IdeleGroup.principalSubgroup L = ⊤) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ⊔
        RelativeIdeleGroup.principalSubgroup K L =
  ⊤ := by
  apply
    Subgroup.map_injective
      (f :=
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).toMonoidHom)
      (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).injective
  rw [Subgroup.map_sup,
    relativeIdeleLocalTensorDecompositionSupportedSubgroup_map_baseChange,
    relativeIdelePrincipalSubgroup_map_baseChange,
    hOrdinary,
    Subgroup.map_top_of_surjective
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).toMonoidHom
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).surjective]

/-- A diagonal idele is supported at `T` exactly when its defining
field unit is a `T`-unit. -/
theorem principalIdele_mem_supportedAt_iff_sUnit
    (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : Lˣ) :
    IdeleGroup.principalIdele L x ∈
        IdeleGroup.supportedAt (K := L) (T : Set _) ↔
      x ∈ SUnitGroup (K := L) T := by
  rw [IdeleGroup.mem_supportedAt_iff, mem_SUnitGroup_iff]
  constructor
  · intro hx W hW
    have hunit := hx W (by simpa using hW)
    rw [
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
        at hunit
    change
      Valued.v
          (((IdeleGroup.finiteComponent W
            (IdeleGroup.principalIdele L x) :
              (W.adicCompletion L)ˣ) :
            W.adicCompletion L)) = 1 at hunit
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hunit
    exact hunit
  · intro hx W hW
    rw [
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change
      Valued.v
          (((IdeleGroup.finiteComponent W
            (IdeleGroup.principalIdele L x) :
              (W.adicCompletion L)ˣ) :
            W.adicCompletion L)) = 1
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hx W (by simpa using hW)

/-- The diagonal map from extension-field `S`-units into the
intersection of the relative principal and supported subgroups. -/
noncomputable def sUnitToRelativePrincipalSupportedIntersection
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →*
      (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) where
  toFun x := by
    have hOrdinary :
        IdeleGroup.principalIdele L (x : Lˣ) ∈
          IdeleGroup.supportedAt (K := L)
            (finitePlacesAbove (K := K) (L := L) S : Set _) :=
      (principalIdele_mem_supportedAt_iff_sUnit
        (L := L)
        (finitePlacesAbove (K := K) (L := L) S)
        (x : Lˣ)).2 x.property
    have hRelative :
        RelativeIdeleGroup.principalIdele K L (x : Lˣ) ∈
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S := by
      apply
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S _).2
      simpa using hOrdinary
    exact
      ⟨⟨RelativeIdeleGroup.principalIdele K L (x : Lˣ),
          hRelative⟩,
        ⟨(x : Lˣ), rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The intersection of the relative principal ideles with the
relative `S`-idele subgroup is precisely the ordinary group of
`S`-units of `L`. -/
noncomputable def sUnitEquivRelativePrincipalSupportedIntersection
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) ≃*
      (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) :=
  MulEquiv.ofBijective
    (sUnitToRelativePrincipalSupportedIntersection
      (K := K) (L := L) S)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply IdeleGroup.principalIdele_injective L
      have hRelative :=
        congrArg
          (fun z :
            (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
              (relativeIdeleLocalTensorDecompositionSupportedSubgroup
                (K := K) (L := L) S) =>
            ((z :
                relativeIdeleLocalTensorDecompositionSupportedSubgroup
                  (K := K) (L := L) S) :
              RelativeIdeleGroup K L))
          hxy
      change
        RelativeIdeleGroup.principalIdele K L (x : Lˣ) =
          RelativeIdeleGroup.principalIdele K L (y : Lˣ)
        at hRelative
      have hOrdinary :=
        congrArg
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L))
          hRelative
      simpa using hOrdinary,
    by
      intro y
      obtain ⟨x, hx⟩ := y.property
      have hRelative :
          RelativeIdeleGroup.principalIdele K L x ∈
            relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S := by
        rw [hx]
        exact y.1.property
      have hOrdinary :=
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S
          (RelativeIdeleGroup.principalIdele K L x)).1 hRelative
      have hxS :
          x ∈ SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S) := by
        apply
          (principalIdele_mem_supportedAt_iff_sUnit
            (L := L)
            (finitePlacesAbove (K := K) (L := L) S) x).1
        simpa using hOrdinary
      refine ⟨⟨x, hxS⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hx⟩

/-- The restricted Galois action on the intersection of the relative
principal and supported subgroups. -/
@[reducible]
noncomputable def relativePrincipalSupportedIntersectionAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S)) := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  exact
    CyclicCohomology.stableSubgroupMulDistribMulAction
      ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S))
      (by
        intro σ z hz
        change
          (((σ • z :
              relativeIdeleLocalTensorDecompositionSupportedSubgroup
                (K := K) (L := L) S) :
            RelativeIdeleGroup K L)) ∈
              RelativeIdeleGroup.principalSubgroup K L
        rw [
          relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe]
        obtain ⟨x, hx⟩ := hz
        refine
          ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
        calc
          RelativeIdeleGroup.principalIdele K L
              (Units.map σ.toRingEquiv.toMonoidHom x) =
              σ • RelativeIdeleGroup.principalIdele K L x :=
            (RelativeIdeleGroup.smul_principalIdele
              K L σ x).symm
          _ = σ • (z : RelativeIdeleGroup K L) :=
            congrArg (fun a : RelativeIdeleGroup K L => σ • a) hx)

omit [IsGalois K L] in
/-- The `S`-unit description of the principal-supported intersection
is equivariant for the genuine Galois actions. -/
theorem
    sUnitEquivRelativePrincipalSupportedIntersection_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (x :
      SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      sUnitMulDistribMulAction K L
        (finitePlacesAbove (K := K) (L := L) S)
        (finitePlacesAbove_isGaloisStable
          (K := K) (L := L) S)
    letI :=
      relativePrincipalSupportedIntersectionAction
        (K := K) (L := L) S
    sUnitEquivRelativePrincipalSupportedIntersection
        (K := K) (L := L) S (σ • x) =
      σ •
        sUnitEquivRelativePrincipalSupportedIntersection
          (K := K) (L := L) S x := by
  let :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let :=
    relativePrincipalSupportedIntersectionAction
      (K := K) (L := L) S
  apply Subtype.ext
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

/-- The finite base places at which at least one extension prime is
ramified. -/
noncomputable def ramifiedBaseFinitePlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)).toFinset

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem mem_ramifiedBaseFinitePlaces_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ ramifiedBaseFinitePlaces (K := K) (L := L) ↔
      ∃ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal ∧
          ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  simp [ramifiedBaseFinitePlaces]

/-- The idele-class Herbrand support: contractions of a sufficiently large support
for `I_L`, together with every ramified base finite place. -/
noncomputable def ideleClassHerbrandSupport :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    (IdeleGroup.sufficientlyLargeFiniteSet (K := L)).image
        (finitePlaceBelow (K := K)) ∪
      ramifiedBaseFinitePlaces (K := K) (L := L)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every place in the sufficiently large support of `L` lies above
the chosen base support. -/
theorem sufficientlyLargeFiniteSet_subset_finitePlacesAbove_support :
    (IdeleGroup.sufficientlyLargeFiniteSet (K := L) :
        Set (HeightOneSpectrum (𝓞 L))) ⊆
      ((finitePlacesAbove
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) :
            Finset (HeightOneSpectrum (𝓞 L))) :
        Set (HeightOneSpectrum (𝓞 L))) := by
  intro W hW
  change W ∈ finitePlacesAbove
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
  rw [mem_finitePlacesAbove_iff]
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨W, hW, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The ordinary ideles supported above the chosen base support,
together with principal ideles, generate all of `I_L`. -/
theorem supportedAboveHerbrandSupport_sup_principal_eq_top :
    IdeleGroup.supportedAt (K := L)
        (finitePlacesAbove
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) : Set _) ⊔
      IdeleGroup.principalSubgroup L = ⊤ := by
  apply top_unique
  rw [← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
    (K := L)]
  exact sup_le_sup
    (IdeleGroup.supportedAt_mono
      (sufficientlyLargeFiniteSet_subset_finitePlacesAbove_support
      (K := K) (L := L)))
    le_rfl

omit [IsGalois K L] in
/-- The relative ideles supported at the Herbrand support, together
with the relative principal ideles, generate the full relative idele
group. -/
theorem relativeSupportedAboveHerbrandSupport_sup_principal_eq_top :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) ⊔
        RelativeIdeleGroup.principalSubgroup K L =
      ⊤ :=
  relativeIdeleSupported_sup_principal_eq_top
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
    (supportedAboveHerbrandSupport_sup_principal_eq_top
      (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Outside the chosen base support, every finite place of `L` is
algebraically unramified over `K`. -/
theorem isUnramifiedAt_of_notMem_ideleClassHerbrandSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ ideleClassHerbrandSupport (K := K) (L := L))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : finitePlaceBelow (K := K) W = v) :
    Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  classical
  by_contra hram
  apply hv
  apply Finset.mem_union_right
  rw [mem_ramifiedBaseFinitePlaces_iff]
  refine ⟨W, ?_, hram⟩
  exact ⟨(congrArg HeightOneSpectrum.asIdeal hW).symm⟩
