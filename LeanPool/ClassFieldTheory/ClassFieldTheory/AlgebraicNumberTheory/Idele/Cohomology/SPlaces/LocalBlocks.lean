/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Decomposition
/-!
# The local blocks occurring in a relative `S`-idele

For a finite set `S` of finite places, the unrestricted factors consist
of every infinite place and the finite places in `S`.  This file packages
those two kinds of concrete tensor factors into one finite dependent
family and identifies it equivariantly with the induced local blocks of
the local tensor decomposition.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations
open CyclicCohomology
open HilbertRamification

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A fixed infinite place of `L` above the given infinite place of
`K`. -/
noncomputable def chosenInfinitePlaceAbove
    (v : InfinitePlace K) : InfinitePlace L :=
  Classical.choose
    (InfinitePlace.comap_surjective (K := L) v)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The chosen infinite place above `v` restricts back to `v`. -/
@[simp]
theorem chosenInfinitePlaceAbove_comap
    (v : InfinitePlace K) :
    (chosenInfinitePlaceAbove (L := L) v).comap
        (algebraMap K L) = v :=
  Classical.choose_spec
    (InfinitePlace.comap_surjective (K := L) v)

/-- Infinite places and the selected finite places form the finite
unrestricted index family of a relative `S`-idele. -/
abbrev RelativeUnrestrictedSPlaceIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Sum (InfinitePlace K)
    {v : HeightOneSpectrum (𝓞 K) // v ∈ S}

/-- The chosen local-place data at every unrestricted place. -/
noncomputable def relativeUnrestrictedSPlaceDatum
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S →
      LocalPlaceDatum K L
  | Sum.inl v =>
      { base := v.1
        base_isNontrivial := v.isNontrivial
        extension :=
          infinitePlaceAbsoluteValueExtension
            v (chosenInfinitePlaceAbove (L := L) v)
            (chosenInfinitePlaceAbove_comap
              (L := L) v) }
  | Sum.inr v =>
      { base := HeightOneSpectrum.adicAbv K v.1
        base_isNontrivial :=
          RayClass.adicAbv_isNontrivial v.1
        extension :=
          chosenFinitePlaceExtension
            (L := L) v.1 }

/-- The actual tensor-unit type attached to one unrestricted place. -/
abbrev RelativeUnrestrictedSPlaceFactor
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S → Type
  | Sum.inl v => (v.Completion ⊗[K] L)ˣ
  | Sum.inr v => (v.1.adicCompletion K ⊗[K] L)ˣ

/-- Each unrestricted local tensor-unit factor is a commutative group. -/
noncomputable instance relativeUnrestrictedSPlaceFactorCommGroup
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S) :
    CommGroup
      (RelativeUnrestrictedSPlaceFactor
        (K := K) (L := L) S i) := by
  cases i <;> infer_instance

/-- The finite family of actual unrestricted tensor factors. -/
abbrev RelativeUnrestrictedSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ∀ i : RelativeUnrestrictedSPlaceIndex (K := K) S,
    RelativeUnrestrictedSPlaceFactor
      (K := K) (L := L) S i

/-- The componentwise scalar-conjugation action on the unrestricted
tensor factors. -/
@[reducible]
noncomputable def relativeUnrestrictedSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ i :
      RelativeUnrestrictedSPlaceIndex (K := K) S,
      MulDistribMulAction (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactor
          (K := K) (L := L) S i) :=
    fun i => by
      cases i with
      | inl v =>
          exact
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := v.Completion)
      | inr v =>
          exact
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := v.1.adicCompletion K)
  exact
    piMulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactor
        (K := K) (L := L) S)

/-- The componentwise local tensor equivalence for every unrestricted place in `S`. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S ≃*
      LocalBlockFamily
        (relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S) :=
  MulEquiv.piCongrRight fun i => by
    cases i with
    | inl v =>
        exact
          infinitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v v.isNontrivial
            (infinitePlaceAbsoluteValueExtension
              v (chosenInfinitePlaceAbove (L := L) v)
              (chosenInfinitePlaceAbove_comap
                (L := L) v))
    | inr v =>
        exact
          finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v.1
            (chosenFinitePlaceExtension
              (L := L) v.1)

omit [NumberField L] in
/-- The unrestricted-factor realization is equivariant for the full
global Galois action. -/
theorem
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : RelativeUnrestrictedSPlaceFactors
      (K := K) (L := L) S) :
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S
        ((relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S).smul σ z) =
      (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)).smul σ
        (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
          (K := K) (L := L) S z) := by
  funext i
  cases i with
  | inl v =>
      let u :=
        infinitePlaceAbsoluteValueExtension
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap (L := L) v)
      let :=
        scalarTensorUnitsAction
          (K := K) (L := L) (A := v.Completion)
      let :=
        decompositionGroupLocalUnitsAction
          v.1 v.isNontrivial u
      let : MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock v.1 v.isNontrivial u) :=
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K u.1)
      change
        infinitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v v.isNontrivial u
            (σ • z (Sum.inl v)) =
          σ •
            infinitePlaceTensorUnitsEquivLocalPlaceBlock
              (K := K) (L := L) v v.isNontrivial u
              (z (Sum.inl v))
      exact
        infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
          (K := K) (L := L) v v.isNontrivial u
          σ (z (Sum.inl v))
  | inr v =>
      let u := chosenFinitePlaceExtension (L := L) v.1
      let :=
        scalarTensorUnitsAction
          (K := K) (L := L) (A := v.1.adicCompletion K)
      let :=
        decompositionGroupLocalUnitsAction
          (HeightOneSpectrum.adicAbv K v.1)
          (RayClass.adicAbv_isNontrivial v.1) u
      let : MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (HeightOneSpectrum.adicAbv K v.1)
            (RayClass.adicAbv_isNontrivial v.1) u) :=
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K u.1)
      change
        finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v.1 u
            (σ • z (Sum.inr v)) =
          σ •
            finitePlaceTensorUnitsEquivLocalPlaceBlock
              (K := K) (L := L) v.1 u
              (z (Sum.inr v))
      exact
        finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
          (K := K) (L := L) v.1 u
          σ (z (Sum.inr v))

/-- Reassociate the displayed unrestricted factors of
`RelativeIdeleSPlaceFactors` as the finite dependent family above. -/
noncomputable def relativeUnrestrictedSPlaceFactorsEquivProd
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S ≃*
      (∀ v : InfinitePlace K,
          (v.Completion ⊗[K] L)ˣ) ×
        (∀ v :
          {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
          (v.1.adicCompletion K ⊗[K] L)ˣ) where
  toFun z :=
    ⟨fun v => z (Sum.inl v),
      fun v => z (Sum.inr v)⟩
  invFun z
    | Sum.inl v => z.1 v
    | Sum.inr v => z.2 v
  left_inv z := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
