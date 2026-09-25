/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.BinaryProduct
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces
public import Mathlib.Algebra.GroupWithZero.Action.Prod
/-!
# Reassociation of supported relative-idele factors

The factor model of a supported relative idele is reassociated into the
finite family of unrestricted places and the product of integral factors
outside the support.  The comparison respects the concrete Galois
actions.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The product of the actual integral tensor-unit factors outside
`S`. -/
abbrev RelativeOutsideSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w.1

/-- The componentwise Galois action on the integral factors outside
`S`. -/
@[reducible]
noncomputable def relativeOutsideSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeOutsideSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      MulDistribMulAction (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  exact
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
          relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1)

/-- The componentwise Galois action on the product of unrestricted and
outside-integral local factors. -/
@[reducible]
noncomputable def relativeUnrestrictedProdOutsideAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) := by
  letI :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  letI :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  infer_instance

/-- Reassociate all supported local factors as
`(unrestricted factors) × (outside integral factors)`. -/
noncomputable def
    relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeIdeleSPlaceFactors (K := K) (L := L) S ≃*
      RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S where
  toFun z :=
    ⟨fun i =>
      match i with
      | Sum.inl w => z.1 w
      | Sum.inr w => z.2.1 w,
      z.2.2⟩
  invFun z :=
    ⟨fun w => z.1 (Sum.inl w),
      ⟨fun w => z.1 (Sum.inr w), z.2⟩⟩
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext
    · funext i
      cases i <;> rfl
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · funext i
      cases i <;> rfl
    · rfl

omit [NumberField L] [IsGalois K L] in
/-- The reassociation of supported local factors is Galois
equivariant. -/
theorem
    relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleSPlaceFactors
      (K := K) (L := L) S) :
    relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
        (K := K) (L := L) S
        ((relativeIdeleSPlaceFactorsAction
          (K := K) (L := L) S).smul σ z) =
      (relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S).smul σ
        (relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
          (K := K) (L := L) S z) := by
  apply Prod.ext
  · funext i
    cases i <;> rfl
  · rfl

/-- The complete supported relative-idele group, with its restricted-product
condition already built into the subtype, is the product of the unrestricted
local factors in `S` and the integral local factors outside `S`. -/
noncomputable def
    relativeIdeleSupportedEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ≃*
      RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S :=
  (relativeIdeleSupportedEquivSPlaceFactors
      (K := K) (L := L) S).trans
    (relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
      (K := K) (L := L) S)

omit [IsGalois K L] in
/-- The supported relative-idele decomposition is equivariant for the
concrete Galois action on every factor. -/
theorem
    relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) :
    relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S
        ((relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S).smul σ z) =
      (relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S).smul σ
        (relativeIdeleSupportedEquivUnrestrictedProdOutside
          (K := K) (L := L) S z) := by
  apply Prod.ext
  · funext i
    cases i with
    | inl w =>
        let :=
          scalarTensorUnitsAction
            (K := K) (L := L) (A := w.Completion)
        exact
          RelativeIdeleGroup.infiniteComponent_smul
            (K := K) (L := L) w σ z
    | inr w =>
        let :=
          scalarTensorUnitsAction
            (K := K) (L := L)
            (A := w.1.adicCompletion K)
        exact
          RelativeIdeleGroup.finiteComponent_smul
            (K := K) (L := L) w.1 σ z
  · funext w
    apply Subtype.ext
    let :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.1.adicCompletion K)
    exact
      RelativeIdeleGroup.finiteComponent_smul
        (K := K) (L := L) w.1 σ z

/-- Transport of degree-zero Tate cohomology from the actual
supported relative ideles to the unrestricted and outside-integral
factorization. -/
noncomputable def
    relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI :=
      relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S
    HerbrandH0 (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) ≃*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S ×
          RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  letI :=
    relativeUnrestrictedProdOutsideAction
      (K := K) (L := L) S
  exact
    herbrandH0EquivariantMulEquiv
      (relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S)
      (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
        (K := K) (L := L) S)

/-- Transport of degree-minus-one Tate cohomology from the
actual supported relative ideles to the unrestricted and outside-integral
factorization. -/
noncomputable def
    relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI :=
      relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) σ ≃*
      HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S ×
          RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  letI :=
    relativeUnrestrictedProdOutsideAction
      (K := K) (L := L) S
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S)
      (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
        (K := K) (L := L) S) σ
