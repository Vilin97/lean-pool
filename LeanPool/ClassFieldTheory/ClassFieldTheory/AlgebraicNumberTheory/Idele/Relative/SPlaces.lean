/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralLocalFactor
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
/-!
# Finite-place support for relative ideles

This file packages a restricted-product assertion for relative ideles. At
every finite place outside a finite
set, a relative idele belongs to the actual product of valuation-ring
unit groups supplied by the completion decomposition. The resulting supported
subgroups are stable under the Galois action and exhaust the full
relative idele group.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open CyclicCohomology


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Relative ideles that are integral units in every local tensor
factor outside the finite set `S`. -/
noncomputable def relativeIdeleLocalTensorDecompositionSupportedSubgroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (RelativeIdeleGroup K L) :=
  ⨅ w : HeightOneSpectrum (𝓞 K),
    ⨅ (_ : w ∉ S),
      (relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w).comap
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w)

omit [NumberField L] [IsGalois K L] in
/-- Membership in the supported relative-idele subgroup is exactly
valuation-ring integrality at every finite place outside `S`. -/
@[simp]
theorem mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : RelativeIdeleGroup K L) :
    z ∈ relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w
          (RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w z) := by
  simp only [relativeIdeleLocalTensorDecompositionSupportedSubgroup,
    Subgroup.mem_iInf, Subgroup.mem_comap,
    mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff]

omit [NumberField L] [IsGalois K L] in
/-- Enlarging the exceptional set enlarges the supported subgroup. -/
theorem relativeIdeleLocalTensorDecompositionSupportedSubgroup_mono
    {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S ≤
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) T := by
  intro z hz
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff] at hz ⊢
  intro w hw
  exact hz w (fun hws => hw (hST hws))

omit [IsGalois K L] in
/-- The explicit coefficient-and-lattice support of a relative idele
is an exceptional set witnessing restricted-product integrality. -/
theorem relativeIdele_mem_localTensorDecompositionSupportedSubgroup
    (z : RelativeIdeleGroup K L) :
    z ∈ relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L)
        (relativeIdeleLocalTensorDecompositionSupport
          (K := K) (L := L) z) := by
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff]
  intro w hw
  exact
    relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) z w hw

omit [IsGalois K L] in
/-- The finite-support subgroups exhaust the complete relative idele
group. -/
theorem iSup_relativeIdeleLocalTensorDecompositionSupportedSubgroup_eq_top :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 K)),
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S =
      (⊤ : Subgroup (RelativeIdeleGroup K L)) := by
  apply top_unique
  intro z hz
  exact
    (le_iSup
      (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S)
      (relativeIdeleLocalTensorDecompositionSupport
        (K := K) (L := L) z))
      (relativeIdele_mem_localTensorDecompositionSupportedSubgroup
        (K := K) (L := L) z)

/-- The finite local factors of a relative `S`-idele: unrestricted
tensor units on `S`, and actual local tensor integral units away
from `S`. -/
abbrev RelativeFiniteSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
      (w.1.adicCompletion K ⊗[K] L)ˣ) ×
    (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w.1)

/-- The complete local-factor model attached to a finite support. -/
abbrev RelativeIdeleSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ) ×
    RelativeFiniteSPlaceFactors (K := K) (L := L) S

/-- The same local-factor model after applying the local tensor decomposition at
every finite place. -/
abbrev RelativeIdeleSPlaceLocalTensorDecompositionFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ) ×
    ((∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
        ∀ wL : AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w.1) L,
          wL.1.Completionˣ) ×
      (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        ∀ wL : AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w.1) L,
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w.1)
              (HeightOneSpectrum.isNonarchimedean_adicAbv
                K w.1) wL))ˣ))

/-- The componentwise local tensor decomposition identifies the finite tensor-unit
factors with products of the actual completion unit groups, retaining
valuation-ring units away from `S`. -/
noncomputable def
    relativeIdeleSPlaceFactorsEquivLocalTensorDecomposition
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeIdeleSPlaceFactors (K := K) (L := L) S ≃*
      RelativeIdeleSPlaceLocalTensorDecompositionFactors
        (K := K) (L := L) S :=
  (MulEquiv.refl
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ)).prodCongr
    ((MulEquiv.piCongrRight fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∈ S} =>
      finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w.1).prodCongr
      (MulEquiv.piCongrRight fun w :
          {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
          (K := K) (L := L) w.1))

omit [NumberField L] [IsGalois K L] in
/-- Membership in the chosen basis lattice is exactly the coefficient
integrality needed by the restricted local-product model. -/
theorem relativeBasisIntegralAt_repr_mem
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (hx : RelativeBasisIntegralAt
      (K := K) (L := L) w x)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr x i ∈
      w.adicCompletionIntegers K := by
  classical
  rcases hx with ⟨c, rfl⟩
  simp only [map_sum, Algebra.TensorProduct.basis_repr_tmul, Module.Basis.repr_self,
    Finsupp.mapRange_single, map_one, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simpa only [Finsupp.single_eq_same] using (c i).property
  · intro j _ hji
    simp [hji]
  · simp

/-- Extract all local factors from an integrally supported
relative idele. -/
noncomputable def relativeIdeleSupportedComponents
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S →*
      RelativeIdeleSPlaceFactors (K := K) (L := L) S where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      ⟨fun w =>
          RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w.1 z,
        fun w =>
          ⟨RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1 z,
            (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
              (K := K) (L := L) w.1 _).2
              ((mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
                (K := K) (L := L) S z).1 z.property
                w.1 w.2)⟩⟩⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact
        map_one
          (RelativeIdeleGroup.infiniteComponent
            (K := K) (L := L) w)
    · apply Prod.ext
      · funext w
        exact
          map_one
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
      · funext w
        apply Subtype.ext
        exact
          map_one
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact
        map_mul
          (RelativeIdeleGroup.infiniteComponent
            (K := K) (L := L) w)
          (x : RelativeIdeleGroup K L)
          (y : RelativeIdeleGroup K L)
    · apply Prod.ext
      · funext w
        exact
          map_mul
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L)
      · funext w
        apply Subtype.ext
        exact
          map_mul
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L)

omit [NumberField L] [IsGalois K L] in
/-- The infinite component of the displayed supported-factor map is the
original infinite component of the relative idele. -/
@[simp]
theorem relativeIdeleSupportedComponents_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : InfinitePlace K) :
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S z).1 w =
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] [IsGalois K L] in
/-- At a finite place in `S`, the displayed supported-factor map is the
unrestricted finite component. -/
@[simp]
theorem relativeIdeleSupportedComponents_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S}) :
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S z).2.1 w =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w.1 z :=
  rfl

omit [NumberField L] [IsGalois K L] in
/-- Outside `S`, coercing the integral factor back to tensor units recovers
the original finite component. -/
@[simp]
theorem relativeIdeleSupportedComponents_outside_coe
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S}) :
    ((relativeIdeleSupportedComponents
        (K := K) (L := L) S z).2.2 w :
      (w.1.adicCompletion K ⊗[K] L)ˣ) =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w.1 z :=
  rfl

omit [NumberField L] [IsGalois K L] in
/-- All local components determine a supported relative idele. -/
theorem relativeIdeleSupportedComponents_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (relativeIdeleSupportedComponents
        (K := K) (L := L) S) := by
  intro x y hxy
  apply Subtype.ext
  apply relativeIdeleLocalComponents_injective
  apply Prod.ext
  · funext w
    exact congrArg (fun q => q.1 w) hxy
  · funext w
    by_cases hw : w ∈ S
    · exact
        congrArg
          (fun q => q.2.1
            (⟨w, hw⟩ :
              {w : HeightOneSpectrum (𝓞 K) // w ∈ S}))
          hxy
    · exact
        congrArg Subtype.val
          (congrArg
            (fun q => q.2.2
              (⟨w, hw⟩ :
                {w : HeightOneSpectrum (𝓞 K) // w ∉ S}))
            hxy)

/-- Assemble the complete `S`-place factor family as restricted local
idele data.  Away from `S` and the finite discriminant set, the converse
part of the local tensor decomposition supplies the required coefficient integrality. -/
noncomputable def relativeLocalIdeleDataOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S) :
    RelativeLocalIdeleData (K := K) (L := L) := by
  classical
  let f :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ :=
    fun w =>
      if hw : w ∈ S then
        x.2.1 ⟨w, hw⟩
      else
        (x.2.2 ⟨w, hw⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ)
  refine
    { infinite := x.1
      finite := f
      eventually_integral := ?_
      eventually_inverse_integral := ?_ }
  · intro i
    refine
      (S ∪ integralTensorComparisonBadPlaces
        (K := K) (L := L)).eventually_cofinite_notMem.mono ?_
    intro w hw
    have hwS : w ∉ S := by
      intro h
      exact hw (Finset.mem_union_left _ h)
    have hwBad :
        w ∉ integralTensorComparisonBadPlaces
          (K := K) (L := L) := by
      intro h
      exact hw (Finset.mem_union_right _ h)
    have hProp :
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w (f w) := by
      rw [show f w =
        (x.2.2 ⟨w, hwS⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) by
        simp [f, hwS]]
      exact
        (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
          (K := K) (L := L) w _).1
          (x.2.2 ⟨w, hwS⟩).property
    have hBasis :
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (f w) :=
      localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
        (K := K) (L := L) w hwBad hProp
    exact
      relativeBasisIntegralAt_repr_mem
        (K := K) (L := L) w (f w : _)
        hBasis.1 i
  · intro i
    refine
      (S ∪ integralTensorComparisonBadPlaces
        (K := K) (L := L)).eventually_cofinite_notMem.mono ?_
    intro w hw
    have hwS : w ∉ S := by
      intro h
      exact hw (Finset.mem_union_left _ h)
    have hwBad :
        w ∉ integralTensorComparisonBadPlaces
          (K := K) (L := L) := by
      intro h
      exact hw (Finset.mem_union_right _ h)
    have hProp :
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w (f w) := by
      rw [show f w =
        (x.2.2 ⟨w, hwS⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) by
        simp [f, hwS]]
      exact
        (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
          (K := K) (L := L) w _).1
          (x.2.2 ⟨w, hwS⟩).property
    have hBasis :
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (f w) :=
      localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
        (K := K) (L := L) w hwBad hProp
    exact
      relativeBasisIntegralAt_repr_mem
        (K := K) (L := L) w
        (((f w)⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L)
        hBasis.2 i

omit [IsGalois K L] in
/-- The assembled local-idele data has the prescribed infinite component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : InfinitePlace K) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).infinite w = x.1 w :=
  rfl

omit [IsGalois K L] in
/-- At a finite place in `S`, the assembled local-idele data has the
prescribed unrestricted component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_finite_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∈ S) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).finite w =
        x.2.1 ⟨w, hw⟩ := by
  simp [relativeLocalIdeleDataOfSPlaceFactors, hw]

omit [IsGalois K L] in
/-- At a finite place outside `S`, the assembled local-idele data is the
coercion of the prescribed integral component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_finite_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ S) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).finite w =
        (x.2.2 ⟨w, hw⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) := by
  simp [relativeLocalIdeleDataOfSPlaceFactors, hw]

/-- Assemble prescribed local factors into the actual supported
relative idele. -/
noncomputable def relativeIdeleOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S := by
  refine
    ⟨relativeIdeleOfLocalData
        (K := K) (L := L)
        (relativeLocalIdeleDataOfSPlaceFactors
          (K := K) (L := L) S x), ?_⟩
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff]
  intro w hw
  rw [relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_outside
      (K := K) (L := L) S x w hw]
  exact
    (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
      (K := K) (L := L) w _).1
      (x.2.2 ⟨w, hw⟩).property

omit [IsGalois K L] in
/-- The relative idele assembled from displayed `S`-place factors has the
prescribed infinite component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_infiniteComponent
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : InfinitePlace K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      x.1 w := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_infiniteComponent]
  rfl

omit [IsGalois K L] in
/-- At a finite place in `S`, the assembled relative idele has the
prescribed unrestricted component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_finiteComponent_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∈ S) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      x.2.1 ⟨w, hw⟩ := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_inside
      (K := K) (L := L) S x w hw]

omit [IsGalois K L] in
/-- At a finite place outside `S`, the assembled relative idele has the
coercion of the prescribed integral component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_finiteComponent_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ S) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      (x.2.2 ⟨w, hw⟩ :
        (w.adicCompletion K ⊗[K] L)ˣ) := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_outside
      (K := K) (L := L) S x w hw]

omit [IsGalois K L] in
/-- Every complete family of local factors is realized by a supported
relative idele. -/
theorem relativeIdeleSupportedComponents_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (relativeIdeleSupportedComponents
        (K := K) (L := L) S) := by
  intro x
  refine
    ⟨relativeIdeleOfSPlaceFactors
        (K := K) (L := L) S x, ?_⟩
  apply Prod.ext
  · funext w
    exact
      relativeIdeleOfSPlaceFactors_infiniteComponent
        (K := K) (L := L) S x w
  · apply Prod.ext
    · funext w
      exact
        relativeIdeleOfSPlaceFactors_finiteComponent_inside
          (K := K) (L := L) S x w.1 w.2
    · funext w
      apply Subtype.ext
      exact
        relativeIdeleOfSPlaceFactors_finiteComponent_outside
          (K := K) (L := L) S x w.1 w.2

/-- The exact relative finite-support decomposition:

`I_{L/K}^S` is the product of all archimedean tensor-unit factors,
the unrestricted finite tensor-unit factors over `S`, and the genuine
valuation-ring unit factors away from `S`. -/
noncomputable def relativeIdeleSupportedEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S ≃*
      RelativeIdeleSPlaceFactors (K := K) (L := L) S :=
  MulEquiv.ofBijective
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S)
    ⟨relativeIdeleSupportedComponents_injective
        (K := K) (L := L) S,
      relativeIdeleSupportedComponents_surjective
        (K := K) (L := L) S⟩

/-- The natural Galois action restricts to every finite-support
subgroup. -/
@[reducible]
noncomputable def
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S) := by
  letI :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  exact
    { smul := fun σ z =>
        ⟨σ • (z : RelativeIdeleGroup K L), by
          rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff]
          intro w hw
          let :=
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := w.adicCompletion K)
          rw [RelativeIdeleGroup.finiteComponent_smul]
          exact
            relativeLocalTensorDecompositionIntegralUnitAt_smul
              (K := K) (L := L) w σ
              (RelativeIdeleGroup.finiteComponent
                (K := K) (L := L) w z)
              ((mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
                (K := K) (L := L) S z).1 z.property w hw)⟩
      one_smul := by
        intro z
        apply Subtype.ext
        change
          (1 : L ≃ₐ[K] L) •
              (z : RelativeIdeleGroup K L) =
            (z : RelativeIdeleGroup K L)
        exact one_smul (L ≃ₐ[K] L) _
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact
          mul_smul σ τ
            (z : RelativeIdeleGroup K L)
      smul_one := by
        intro σ
        apply Subtype.ext
        change
          σ • (1 : RelativeIdeleGroup K L) = 1
        exact smul_one σ
      smul_mul := by
        intro σ x y
        apply Subtype.ext
        exact
          smul_mul' σ
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L) }

omit [NumberField L] [IsGalois K L] in
/-- Coercing the supported-subgroup action to the relative idele group
recovers the ambient Galois action. -/
@[simp]
theorem
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ((σ • z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) :
      RelativeIdeleGroup K L) =
      letI :=
        relativeIdeleRestrictedMulDistribMulAction
          (K := K) (L := L)
      σ • (z : RelativeIdeleGroup K L) :=
  rfl

/-- Coordinatewise Galois action on the complete local-factor model. -/
@[reducible]
noncomputable def relativeIdeleSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (RelativeIdeleSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ w : InfinitePlace K,
      MulDistribMulAction
        (L ≃ₐ[K] L) (w.Completion ⊗[K] L)ˣ :=
    fun w =>
      scalarTensorUnitsAction
        (K := K) (L := L) (A := w.Completion)
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : InfinitePlace K,
        (w.Completion ⊗[K] L)ˣ) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w : InfinitePlace K =>
        (w.Completion ⊗[K] L)ˣ)
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
      MulDistribMulAction
        (L ≃ₐ[K] L)
        (w.1.adicCompletion K ⊗[K] L)ˣ :=
    fun w =>
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.1.adicCompletion K)
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
        (w.1.adicCompletion K ⊗[K] L)ˣ) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∈ S} =>
          (w.1.adicCompletion K ⊗[K] L)ˣ)
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      MulDistribMulAction
        (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
          relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1)
  exact inferInstance

omit [NumberField L] [IsGalois K L] in
/-- The complete local-component map is equivariant. -/
theorem relativeIdeleSupportedComponents_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI :=
      relativeIdeleSPlaceFactorsAction
        (K := K) (L := L) S
    relativeIdeleSupportedComponents
        (K := K) (L := L) S (σ • z) =
      σ • relativeIdeleSupportedComponents
        (K := K) (L := L) S z := by
  let :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let :=
    relativeIdeleSPlaceFactorsAction
      (K := K) (L := L) S
  apply Prod.ext
  · funext w
    let :=
      scalarTensorUnitsAction
        (K := K) (L := L) (A := w.Completion)
    exact
      RelativeIdeleGroup.infiniteComponent_smul
        (K := K) (L := L) w σ z
  · apply Prod.ext
    · funext w
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
