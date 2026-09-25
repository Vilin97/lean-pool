/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyFinite
/-!
# Cardinalities of finite unrestricted local-block families

This leaf computes the two finite-family Herbrand cardinalities from the
finiteness results and the canonical family instance providers.
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

omit [NumberField L] in
open scoped Classical in
/-- The degree-zero cardinality of the unrestricted local-block family
is the product of its local degrees. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          (d i).base (d i).base_isNontrivial
          (d i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      S σ hgen
  calc
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) =
      Nat.card
        (∀ i,
          HerbrandH0
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            (LocalizedCompletion
              (d i).base (d i).extension)ˣ) :=
      Nat.card_congr
        (localBlockFamilyHerbrandH0Equiv
          d σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
      Nat.card_pi
    _ = ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree
          S i σ hgen

omit [NumberField L] in
open scoped Classical in
/-- The degree-minus-one cardinality of the unrestricted local-block
family is one. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          (d i).base (d i).base_isNontrivial
          (d i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) = 1 := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      S σ hgen
  calc
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) =
      Nat.card
        (∀ i,
          HerbrandHMinusOne
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            (LocalizedCompletion
              (d i).base (d i).extension)ˣ
            (subgroupGeneratorOfGenerator
              (absoluteValueDecompositionGroup K
                (d i).extension.1)
              σ hgen)) :=
      Nat.card_congr
        (localBlockFamilyHerbrandHMinusOneEquiv
          d σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
      Nat.card_pi
    _ = ∏ _i :
        RelativeUnrestrictedSPlaceIndex (K := K) S, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one
          S i σ hgen
    _ = 1 := by simp
