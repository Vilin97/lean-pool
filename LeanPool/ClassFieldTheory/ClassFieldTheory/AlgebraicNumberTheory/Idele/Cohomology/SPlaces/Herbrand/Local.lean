/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.FamilyClassAxiom
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
/-!
# Cohomology of the unrestricted factors of a relative `S`-idele

This file combines finite local class field theory with the explicit
real/complex norm calculation.  It treats the finite family consisting
of all infinite places and the finite places in `S`.
-/

@[expose] public section

open scoped NumberField BigOperators ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- The local degree attached to one unrestricted place.  At a finite
place it is the degree of the chosen localization; at an infinite place
it is one or two according as the place is unramified or ramified. -/
noncomputable def relativeUnrestrictedSPlaceLocalDegree
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S → ℕ :=
  fun i =>
    Nat.card
      (absoluteValueDecompositionGroup K
        ((relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S i).extension.1))

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- The decomposition-group localization equivalence identifies the order of a decomposition
group with
the degree of its localized completion. -/
theorem absoluteValueDecompositionGroup_card_eq_localizedDegree
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    Nat.card (absoluteValueDecompositionGroup K w.1) =
      Module.finrank vK.Completion
        (LocalizedCompletion vK w) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  calc
    Nat.card (absoluteValueDecompositionGroup K w.1) =
        Nat.card
          (LocalizedCompletion vK w ≃ₐ[vK.Completion]
            LocalizedCompletion vK w) :=
      Nat.card_congr
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w).toEquiv
    _ = Module.finrank vK.Completion
        (LocalizedCompletion vK w) :=
      IsGalois.card_aut_eq_finrank
        vK.Completion (LocalizedCompletion vK w)

omit [NumberField L] in
open scoped Classical in
/-- Every local degree-zero Herbrand group in the unrestricted family is
finite. -/
theorem relativeUnrestrictedLocalHerbrandH0Finite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : Fintype
        (absoluteValueDecompositionGroup K (d i).extension.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ) := by
  cases i with
  | inl v =>
      exact
        infinitePlaceLocalHerbrandH0Finite
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      exact
        localHerbrandH0Finite
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen

omit [NumberField L] in
open scoped Classical in
/-- Every local degree-minus-one Herbrand group in the unrestricted
family is finite. -/
theorem relativeUnrestrictedLocalHerbrandHMinusOneFinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : Fintype
        (absoluteValueDecompositionGroup K (d i).extension.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) := by
  cases i with
  | inl v =>
      exact
        infinitePlaceLocalHerbrandHMinusOneFinite
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
          σ hgen
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      exact
        localHerbrandHMinusOneFinite
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen

omit [NumberField L] in
open scoped Classical in
/-- The cardinality of one local degree-zero term is its local degree. -/
theorem relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : Fintype
        (absoluteValueDecompositionGroup K (d i).extension.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI : Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) =
      relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S i := by
  cases i with
  | inl v =>
      dsimp only [relativeUnrestrictedSPlaceDatum,
        relativeUnrestrictedSPlaceLocalDegree]
      let w := chosenInfinitePlaceAbove (L := L) v
      let hw := chosenInfinitePlaceAbove_comap
        (L := L) v
      have hcard :=
        infinitePlaceLocalHerbrandH0_card_eq_localDegree
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
      have hgroup :
          Nat.card (absoluteValueDecompositionGroup K w.1) =
            if w.IsUnramified K then 1 else 2 := by
        rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
          InfinitePlace.card_stabilizer]
      exact hcard.trans hgroup.symm
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      dsimp only [relativeUnrestrictedSPlaceDatum,
        relativeUnrestrictedSPlaceLocalDegree]
      exact
        (localHerbrandH0_card_eq_localDegree
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen).trans
        (absoluteValueDecompositionGroup_card_eq_localizedDegree
          (K := K) (L := L)
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)).symm

omit [NumberField L] in
open scoped Classical in
/-- Every local degree-minus-one term has cardinality one. -/
theorem relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : Fintype
        (absoluteValueDecompositionGroup K (d i).extension.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI : Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) = 1 := by
  cases i with
  | inl v =>
      dsimp only [relativeUnrestrictedSPlaceDatum]
      exact
        (infinitePlaceLocalClassAxiom_cards
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
          σ hgen).1
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      dsimp only [relativeUnrestrictedSPlaceDatum]
      exact
        localHerbrandHMinusOne_card_eq_one
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen
