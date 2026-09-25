/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FiniteIntegralNormPreimage
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
/-!
# Absolute and relative norms of ideles

This module exposes the absolute norm on the idele group and assembles
compatible local determinant-norm preimages into a global relative idele.
-/

@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable
section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- Assemble compatible local determinant-norm preimages into an actual
relative idele.  The only restricted-product input is simultaneous
basis-integrality of the finite preimage and its inverse at almost every
finite place. -/
theorem exists_relativeIdele_norm_eq_of_localTensorPreimages
    (a : IdeleGroup K)
    (zInfinite :
      ∀ w : InfinitePlace K,
        (w.Completion ⊗[K] L)ˣ)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hInfinite :
      ∀ w : InfinitePlace K,
        infiniteTensorDetNorm (K := K) (L := L) w
            (zInfinite w) =
          IdeleGroup.infiniteComponent w a)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    ∃ z : RelativeIdeleGroup K L,
      RelativeIdeleGroup.norm K L z = a := by
  let d : RelativeLocalIdeleData (K := K) (L := L) :=
    { infinite := zInfinite
      finite := zFinite
      eventually_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.1 i
      eventually_inverse_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.2 i }
  refine
    ⟨relativeIdeleOfLocalData (K := K) (L := L) d, ?_⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.infiniteComponent w a
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      relativeIdeleOfLocalData_infiniteComponent]
    exact hInfinite w
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.finiteComponent w a
    rw [RelativeIdeleGroup.finiteComponent_norm,
      relativeIdeleOfLocalData_finiteComponent]
    exact hFinite w

omit [NumberField L] [IsGalois K L] in
/-- Membership in every local norm image, together with a restricted
choice of finite local preimages, implies membership in the image of the
global relative-idele norm. -/
theorem idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
    (a : IdeleGroup K)
    (hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    a ∈ (RelativeIdeleGroup.norm K L).range := by
  have hInfinite' :
      ∀ w : InfinitePlace K,
        ∃ z : (w.Completion ⊗[K] L)ˣ,
          infiniteTensorDetNorm (K := K) (L := L) w z =
            IdeleGroup.infiniteComponent w a := by
    intro w
    simpa [infiniteTensorNormSubgroup] using hInfinite w
  choose zInfinite hNorm using hInfinite'
  obtain ⟨z, hz⟩ :=
    exists_relativeIdele_norm_eq_of_localTensorPreimages
      (K := K) (L := L) a zInfinite zFinite hNorm hFinite hIntegral
  exact ⟨z, hz⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each finite local
determinant-norm image. -/
theorem finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent w a ∈
      (_root_.localTensorNorm
        (K := K) (L := L) w).range := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) w z).symm⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each infinite local
determinant-norm image. -/
theorem infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : InfinitePlace K) :
    IdeleGroup.infiniteComponent w a ∈
      infiniteTensorNormSubgroup
        (K := K) (L := L) w := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) w z).symm⟩

/-- **Local-to-global norm criterion for ideles.**  An idele is an
actual global relative-idele norm if and only if all of its finite and
infinite components belong to the corresponding determinant-norm
images.  The restrictedness of the global preimage is automatic: at the
cofinitely many places where the given idele is a local integer unit, the
finite local preimage is chosen valuation-integral and is therefore
basis-integral away from the fixed discriminant support. -/
theorem mem_relativeIdeleNorm_range_iff_localTensorNorms
    (a : IdeleGroup K) :
    a ∈ (RelativeIdeleGroup.norm K L).range ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈
          (_root_.localTensorNorm
            (K := K) (L := L) w).range) := by
  constructor
  · intro ha
    exact
      ⟨fun w =>
          infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w,
        fun w =>
          finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w⟩
  · rintro ⟨hInfinite, hFinite⟩
    have hChoice :
        ∀ w : HeightOneSpectrum (𝓞 K),
          ∃ z : (w.adicCompletion K ⊗[K] L)ˣ,
            _root_.localTensorNorm
                (K := K) (L := L) w z =
              IdeleGroup.finiteComponent w a ∧
            (IdeleGroup.finiteComponent w a ∈
                (w.adicCompletionIntegers K).units →
              RelativeLocalTensorDecompositionIntegralUnitAt
                (K := K) (L := L) w z) := by
      intro w
      by_cases hwUnit :
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units
      · obtain ⟨z, hz, hzIntegral⟩ :=
          exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq
            (K := K) (L := L) w
            (IdeleGroup.finiteComponent w a)
            (hFinite w) hwUnit
        exact ⟨z, hz, fun _ => hzIntegral⟩
      · obtain ⟨z, hz⟩ := hFinite w
        exact ⟨z, hz, fun h => (hwUnit h).elim⟩
    choose zFinite hFiniteNorm hFiniteIntegral using hChoice
    have hEventuallyUnit :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units := by
      simpa [IdeleGroup.finiteComponent_apply] using
        FiniteIdeleGroup.eventually_mem_localUnits a.2
    have hIntegral :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          RelativeBasisIntegralUnitAt
            (K := K) (L := L) w (zFinite w) := by
      filter_upwards [
        hEventuallyUnit,
        (integralTensorComparisonBadPlaces
          (K := K) (L := L)).eventually_cofinite_notMem] with
          w hwUnit hwBad
      exact
        localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
          (K := K) (L := L) w hwBad
          (hFiniteIntegral w hwUnit)
    exact
      idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
        (K := K) (L := L) a hInfinite zFinite hFiniteNorm hIntegral
