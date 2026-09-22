/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
/-!
# Scalar extension from relative to ordinary adeles

This file upgrades the relative-to-ordinary idele comparison to the
underlying adele rings.  The additive structure is needed to transport
determinant norms in a field tower.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The finite local tensor algebra, decomposed into the concrete adic
completions above the chosen base place. -/
noncomputable def finitePlaceTensorRingEquivAboveAdic
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  let e₁ :
      (w.adicCompletion K ⊗[K] L) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm.toRingEquiv.trans
      (completionTensorDecompositionLeft
        (K := K) (L := L) vK hvK).toRingEquiv
  let e₂ :
      (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) :=
    RingEquiv.piCongrRight fun u =>
      finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w u
  let e₃ :
      (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) ≃+*
        (∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          W.1.adicCompletion L) :=
    RingEquiv.piCongrLeft
      (fun W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} =>
        W.1.adicCompletion L)
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w)
  exact e₁.trans (e₂.trans e₃)

/-- Evaluation of the finite-place tensor equivalence at an extension of
the given adic absolute value. -/
@[simp]
theorem finitePlaceTensorRingEquivAboveAdic_apply_extension
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (u : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w x
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w u) =
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w u x) := by
  let P :=
    fun W : {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = w} =>
      W.1.adicCompletion L
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) w
  let f : ∀ a, P (e a) := fun a =>
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
      (finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w a x)
  exact Equiv.piCongrLeft_apply_apply P e f u

/-- On a pure tensor, the finite-place relative-to-ordinary comparison
is the canonical completion map on the local coefficient multiplied by
the diagonal image of the extension-field factor. -/
theorem finitePlaceTensorRingEquivAboveAdic_tmul
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (a : w.adicCompletion K)
    (x : L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        (a ⊗ₜ[K] x) W =
      finitePlaceAdicCompletionMap K L w W a *
        algebraMap L (W.1.adicCompletion L) x := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorRingEquivAboveAdic_apply_extension,
    finitePlaceLocalTensorDecompositionComponent_tmul, map_mul]
  change
    finitePlaceExtensionAdicCompletionMap K L w u a *
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u
          (AbsoluteValue.toCompletion u.1 x) =
      _
  rw [
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- Reindex the archimedean relative-tensor product by concrete places
above `w`, before replacing the completion wrappers. -/
noncomputable def infiniteCompletionRingProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completion) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completion := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completion)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_add' := by
        intro x y
        funext W
        rfl
      map_mul' := by
        intro x y
        funext W
        rfl }

/-- The archimedean local tensor algebra, decomposed into the concrete
infinite completions above the chosen base place. -/
noncomputable def infinitePlaceTensorRingEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toRingEquiv.trans
    ((completionTensorDecompositionLeft
        (K := K) (L := L) w.1
        w.isNontrivial).toRingEquiv.trans
      ((infiniteCompletionRingProductReindexAbove
          (K := K) (L := L) w).trans
        (RingEquiv.piCongrRight fun W =>
          (InfinitePlace.Completion.equiv W.1).symm)))

/-- Evaluation of the infinite-place tensor equivalence at a place above
the chosen base place. -/
@[simp]
theorem infinitePlaceTensorRingEquivAbove_apply
    (w : InfinitePlace K)
    (z : w.Completion ⊗[K] L)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w z W =
      (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecompositionLeft
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w z)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) :=
  rfl

/-- On a pure tensor, the infinite-place relative-to-ordinary comparison
is the canonical completion map on the local coefficient multiplied by
the diagonal image of the extension-field factor. -/
theorem infinitePlaceTensorRingEquivAbove_tmul
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (a : w.Completion)
    (x : L) :
    letI : W.1.1.LiesOver w.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w
        (a ⊗ₜ[K] x) W =
      NumberField.LiesOver.completionMap
          (v := w) (w := W.1) a *
        algebraMap L W.1.Completion x := by
  let : W.1.1.LiesOver w.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  rw [infinitePlaceTensorRingEquivAbove_apply]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecompositionLeft
          w.1 w.isNontrivial
          ((infinitePlaceCompletionAlgEquiv w a) ⊗ₜ[K] x)
          (infinitePlaceAboveToExtension
            (K := K) (L := L) w W)) =
      NumberField.LiesOver.completionMap
          (v := w) (w := W.1) a *
        algebraMap L W.1.Completion x
  dsimp only [infinitePlaceAboveToExtension]
  rw [completionTensorDecomposition_left_tmul_apply, map_mul]
  congr 1

/-- Flatten the products over finite base places and places above them
to the product over all finite places of the extension field. -/
noncomputable def finitePlaceAbovePiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L where
  toFun f W :=
    f (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- All finite local tensor rings, flattened to the concrete finite
completion family of the extension field. -/
noncomputable def relativeFiniteTensorPiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L :=
  (RingEquiv.piCongrRight fun w =>
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).trans
    (finitePlaceAbovePiRingEquiv (K := K) (L := L))

/-- Coordinate formula for the relative finite tensor product
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiRingEquiv_apply
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteTensorPiRingEquiv
        (K := K) (L := L) x W =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative finite tensor product
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiRingEquiv_symm_apply
    (y : ∀ W : HeightOneSpectrum (𝓞 L),
      W.adicCompletion L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm y w =
      (finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- Flatten the products over infinite base places and places above
them to the product over all infinite places of the extension field. -/
noncomputable def infinitePlaceAbovePiRingEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion) ≃+*
      ∀ W : InfinitePlace L, W.Completion where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- All infinite local tensor rings, flattened to the concrete infinite
completion family of the extension field. -/
noncomputable def relativeInfiniteTensorPiRingEquiv :
    (∀ w : InfinitePlace K,
      w.Completion ⊗[K] L) ≃+*
      ∀ W : InfinitePlace L, W.Completion :=
  (RingEquiv.piCongrRight fun w =>
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w).trans
    (infinitePlaceAbovePiRingEquiv (K := K) (L := L))

/-- Coordinate formula for the relative infinite tensor product
equivalence. -/
@[simp]
theorem relativeInfiniteTensorPiRingEquiv_apply
    (x : ∀ w : InfinitePlace K,
      w.Completion ⊗[K] L)
    (W : InfinitePlace L) :
    relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L) x W =
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (x (infinitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative infinite tensor product
equivalence. -/
@[simp]
theorem relativeInfiniteTensorPiRingEquiv_symm_apply
    (y : ∀ W : InfinitePlace L, W.Completion)
    (w : InfinitePlace K) :
    (relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm y w =
      (infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- Integrality in the relative-tensor factors is exactly integrality
of every concrete finite completion coordinate. -/
theorem relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) :
    RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w x ↔
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w x W ∈
          W.1.adicCompletionIntegers L := by
  constructor
  · intro hx W
    let u :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).symm W
    have hW :
        finitePlaceExtensionEquivAbove
            (K := K) (L := L) w u = W :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).apply_symm_apply W
    rw [← hW,
      finitePlaceTensorRingEquivAboveAdic_apply_extension]
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).2 (hx u)
  · intro hx u
    have h :=
      hx (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w u)
    rw [finitePlaceTensorRingEquivAboveAdic_apply_extension] at h
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).1 h

omit [NumberField L] in
/-- Outside its coefficient support, a relative adele finite component
belongs to the fixed local basis lattice. -/
theorem relativeAdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeAdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w z) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L) z i).2 w, by
        by_contra hi
        apply hw
        exact
          (mem_relativeAdeleCoefficientSupport_iff
            (K := K) (L := L) z w).2 ⟨i, hi⟩⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w

/-- A relative adele becomes integral in every concrete completion
above almost every finite base place. -/
theorem relativeAdele_eventually_aboveAdicIntegral
    (z : RelativeAdeleRing K L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w
            (relativeAdeleFiniteComponent
              (K := K) (L := L) w z) W ∈
          W.1.adicCompletionIntegers L := by
  classical
  filter_upwards [
    (relativeAdeleCoefficientSupport
      (K := K) (L := L) z).eventually_cofinite_notMem,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hs hbad
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).1
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).1
  exact relativeAdele_finiteComponent_basisIntegral_of_notMem
    (K := K) (L := L) z w hs

/-- The forward ring-level scalar-extension map on adeles. -/
noncomputable def relativeAdeleToAdele
    (z : RelativeAdeleRing K L) :
    NumberField.AdeleRing (𝓞 L) L :=
  ⟨relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)
      (fun w =>
        relativeAdeleInfiniteComponent
          (K := K) (L := L) w z),
    ⟨relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z),
      (eventually_finitePlace_iff_eventually_all_above
        (K := K) (L := L)
        (fun W =>
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z) W ∈
            W.adicCompletionIntegers L)).2 <| by
        filter_upwards [
          relativeAdele_eventually_aboveAdicIntegral
            (K := K) (L := L) z] with w hw
        intro W
        rcases W with ⟨W, hW⟩
        subst w
        exact hw ⟨W, rfl⟩⟩⟩

/-- The infinite component of the underlying adele of a relative adele. -/
@[simp]
theorem relativeAdeleToAdele_infinite
    (z : RelativeAdeleRing K L)
    (W : InfinitePlace L) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).1 W =
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (relativeAdeleInfiniteComponent
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl

/-- The finite component of the underlying adele of a relative adele. -/
@[simp]
theorem relativeAdeleToAdele_finite
    (z : RelativeAdeleRing K L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).2 W =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (relativeAdeleFiniteComponent
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl

/-- Pull the finite coordinates of an ordinary adele back to the
relative local tensor family. -/
noncomputable def finiteAdeleRelativeTensorFamily
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L :=
  (relativeFiniteTensorPiRingEquiv
    (K := K) (L := L)).symm (fun W => y W)

/-- The pulled-back finite tensor family is basis-integral at almost
every finite place. -/
theorem finiteAdeleRelativeTensorFamily_eventually_basisIntegral
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      RelativeBasisIntegralAt
        (K := K) (L := L) w
        (finiteAdeleRelativeTensorFamily
          (K := K) (L := L) y w) := by
  have habove :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          y W.1 ∈ W.1.adicCompletionIntegers L :=
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W => y W ∈ W.adicCompletionIntegers L)).1 y.2
  filter_upwards [
    habove,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hw hbad
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).2
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).2
  intro W
  have hcomponent :=
    congrFun
      ((finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).apply_symm_apply
          (fun W => y W.1)) W
  rw [finiteAdeleRelativeTensorFamily,
    relativeFiniteTensorPiRingEquiv_symm_apply,
    hcomponent]
  exact hw W

/-- Pull an ordinary adele back to restricted relative local data. -/
noncomputable def adeleToRelativeLocalAdeleData
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite :=
    (relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)).symm (fun W => y.1 W)
  finite :=
    finiteAdeleRelativeTensorFamily
      (K := K) (L := L) y.2
  eventually_integral i :=
    (finiteAdeleRelativeTensorFamily_eventually_basisIntegral
      (K := K) (L := L) y.2).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw i

/-- The inverse ring-level scalar-extension map on adeles. -/
noncomputable def adeleToRelativeAdele
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeAdeleRing K L :=
  relativeAdeleOfLocalData
    (K := K) (L := L)
    (adeleToRelativeLocalAdeleData
      (K := K) (L := L) y)

/-- The infinite component of the relative adele reconstructed from an
ordinary adele. -/
@[simp]
theorem adeleToRelativeAdele_infiniteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.1 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_infiniteComponent]
  rfl

/-- The finite component of the relative adele reconstructed from an
ordinary adele. -/
@[simp]
theorem adeleToRelativeAdele_finiteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.2 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_finiteComponent]
  rfl

/-- Scalar extension of relative adeles preserves addition componentwise. -/
private theorem relativeAdeleToAdele_map_add (x y : RelativeAdeleRing K L) :
    relativeAdeleToAdele (K := K) (L := L) (x + y) =
      relativeAdeleToAdele (K := K) (L := L) x +
        relativeAdeleToAdele (K := K) (L := L) y := by
  apply Prod.ext
  · funext W
    change
      relativeInfiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w (x + y)) W =
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w x) W +
          relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w y) W
    rw [show
      (fun w =>
        relativeAdeleInfiniteComponent
          (K := K) (L := L) w (x + y)) =
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w x) +
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w y) by
        funext w
        exact map_add _ _ _,
      map_add]
    rfl
  · apply Subtype.ext
    funext W
    change
      relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w (x + y)) W =
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w x) W +
          relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w y) W
    rw [show
      (fun w =>
        relativeAdeleFiniteComponent
          (K := K) (L := L) w (x + y)) =
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w x) +
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w y) by
        funext w
        exact map_add _ _ _,
      map_add]
    rfl

/-- Scalar extension of relative adeles preserves multiplication componentwise. -/
private theorem relativeAdeleToAdele_map_mul (x y : RelativeAdeleRing K L) :
    relativeAdeleToAdele (K := K) (L := L) (x * y) =
      relativeAdeleToAdele (K := K) (L := L) x *
        relativeAdeleToAdele (K := K) (L := L) y := by
  apply Prod.ext
  · funext W
    change
      relativeInfiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w (x * y)) W =
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w x) W *
          relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w y) W
    rw [show
      (fun w =>
        relativeAdeleInfiniteComponent
          (K := K) (L := L) w (x * y)) =
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w x) *
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w y) by
        funext w
        exact map_mul _ _ _,
      map_mul]
    rfl
  · apply Subtype.ext
    funext W
    change
      relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w (x * y)) W =
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w x) W *
          relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w y) W
    rw [show
      (fun w =>
        relativeAdeleFiniteComponent
          (K := K) (L := L) w (x * y)) =
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w x) *
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w y) by
        funext w
        exact map_mul _ _ _,
      map_mul]
    rfl

/-- Scalar extension identifies the relative adele ring over `K` with
the ordinary adele ring of `L`. -/
noncomputable def relativeAdeleBaseChangeRingEquiv :
    RelativeAdeleRing K L ≃+*
      NumberField.AdeleRing (𝓞 L) L where
  toFun :=
    relativeAdeleToAdele (K := K) (L := L)
  invFun :=
    adeleToRelativeAdele (K := K) (L := L)
  left_inv z := by
    apply relativeAdele_ext_of_components
    · intro w
      rw [adeleToRelativeAdele_infiniteComponent]
      change
        (relativeInfiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w z
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
    · intro w
      rw [adeleToRelativeAdele_finiteComponent]
      change
        (relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
  right_inv y := by
    apply Prod.ext
    · funext W
      rw [relativeAdeleToAdele_infinite,
        adeleToRelativeAdele_infiniteComponent]
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            ((relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)).symm
              (fun W => y.1 W)) W =
          y.1 W
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
    · apply DFunLike.coe_injective
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w
                (adeleToRelativeAdele
                  (K := K) (L := L) y)) W =
          y.2 W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w
            (adeleToRelativeAdele
              (K := K) (L := L) y)) =
          (relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)).symm
            (fun W => y.2 W) by
          funext w
          exact adeleToRelativeAdele_finiteComponent
            (K := K) (L := L) y w]
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
  map_add' := relativeAdeleToAdele_map_add
  map_mul' := relativeAdeleToAdele_map_mul

/-- Finite-coordinate formula for scalar extension of a pure relative
adele tensor. -/
@[simp]
theorem relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L) (a ⊗ₜ[K] x)).2 W =
      finitePlaceAdicCompletionMap K L
          (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
          (a.2 (finitePlaceBelow (K := K) W)) *
        algebraMap L (W.adicCompletion L) x := by
  change
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (a.2 (finitePlaceBelow (K := K) W) ⊗ₜ[K] x)
        ⟨W, rfl⟩ =
      _
  exact
    finitePlaceTensorRingEquivAboveAdic_tmul
      (K := K) (L := L)
      (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
      (a.2 (finitePlaceBelow (K := K) W)) x

/-- Infinite-coordinate formula for scalar extension of a pure relative
adele tensor. -/
@[simp]
theorem relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L)
    (W : InfinitePlace L) :
    let v := infinitePlaceBelow (K := K) W
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L) (a ⊗ₜ[K] x)).1 W =
      NumberField.LiesOver.completionMap
          (v := v) (w := W) (a.1 v) *
        algebraMap L W.Completion x := by
  let v := infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  change
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) v
        (a.1 v ⊗ₜ[K] x) ⟨W, rfl⟩ =
      NumberField.LiesOver.completionMap
          (v := v) (w := W) (a.1 v) *
        algebraMap L W.Completion x
  exact
    infinitePlaceTensorRingEquivAbove_tmul
      (K := K) (L := L) v ⟨W, rfl⟩ (a.1 v) x

/-- A diagonal extension-field element has its expected concrete
finite component under the ring comparison. -/
theorem finitePlaceTensorRingEquivAboveAdic_tmul_one
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        ((1 : w.adicCompletion K) ⊗ₜ[K] x) W =
      algebraMap L (W.1.adicCompletion L) x := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorRingEquivAboveAdic_apply_extension,
    finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, one_mul,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- A diagonal extension-field element has its expected concrete
archimedean component under the ring comparison. -/
theorem infinitePlaceTensorRingEquivAbove_tmul_one
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : L) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w
        ((1 : w.Completion) ⊗ₜ[K] x) W =
      algebraMap L W.1.Completion x := by
  rw [infinitePlaceTensorRingEquivAbove_apply]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecompositionLeft
          w.1 w.isNontrivial
          ((1 : w.1.Completion) ⊗ₜ[K] x)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) =
      algebraMap L W.1.Completion x
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  apply InfinitePlace.Completion.ext
  rfl

/-- The ring comparison carries the diagonal copy of `L` to the
ordinary diagonal adele. -/
theorem relativeAdeleBaseChangeRingEquiv_fieldInclusion
    (x : L) :
    relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x := by
  change
    relativeAdeleToAdele
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x
  apply Prod.ext
  · funext W
    rw [relativeAdeleToAdele_infinite]
    change
      infinitePlaceTensorRingEquivAbove
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          ((1 :
            (infinitePlaceBelow
              (K := K) W).Completion) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L W.Completion x
    exact infinitePlaceTensorRingEquivAbove_tmul_one
      (K := K) (L := L)
      (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩ x
  · apply DFunLike.coe_injective
    funext W
    rw [relativeAdeleToAdele_finite]
    change
      finitePlaceTensorRingEquivAboveAdic
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          ((1 :
            (finitePlaceBelow
              (K := K) W).adicCompletion K) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L (W.adicCompletion L) x
    exact finitePlaceTensorRingEquivAboveAdic_tmul_one
      (K := K) (L := L)
      (finitePlaceBelow (K := K) W) ⟨W, rfl⟩ x

/-- The finite local unit comparison is induced by the corresponding
ring equivalence. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    ((finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w x W :
        (W.1.adicCompletion L)ˣ) :
        W.1.adicCompletion L) =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        (x : w.adicCompletion K ⊗[K] L) W := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension,
    finitePlaceTensorRingEquivAboveAdic_apply_extension]
  rfl

/-- The flattened finite unit comparison is induced by the flattened
finite ring comparison. -/
theorem relativeFiniteTensorPiMulEquiv_coe
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
    (W : HeightOneSpectrum (𝓞 L)) :
    ((relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) x W :
        (W.adicCompletion L)ˣ) :
        W.adicCompletion L) =
      relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          (x w : w.adicCompletion K ⊗[K] L)) W := by
  rw [relativeFiniteTensorPiMulEquiv_apply,
    relativeFiniteTensorPiRingEquiv_apply]
  exact finitePlaceTensorUnitsEquivAboveAdic_coe
    (K := K) (L := L)
    (finitePlaceBelow (K := K) W)
    (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩

/-- The previously constructed idele comparison is the unit-group map
induced by the ring comparison. -/
theorem relativeIdeleBaseChangeMulEquiv_eq_ringUnits
    (z : RelativeIdeleGroup K L) :
    IdeleGroup.equivAdeleRingUnits
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) =
      Units.mapEquiv
        (relativeAdeleBaseChangeRingEquiv
          (K := K) (L := L)).toMulEquiv z := by
  apply Units.ext
  apply Prod.ext
  · funext W
    change
      ((IdeleGroup.infiniteComponent W
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z) :
          W.Completionˣ) : W.Completion) =
        (relativeAdeleToAdele
          (K := K) (L := L)
          (z : RelativeAdeleRing K L)).1 W
    rfl
  · apply DFunLike.coe_injective
    funext W
    change
      ((((relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z).2 W :
          (W.adicCompletion L)ˣ)) :
          W.adicCompletion L) =
        relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w
              (z : RelativeAdeleRing K L)) W
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply]
    exact relativeFiniteTensorPiMulEquiv_coe
      (K := K) (L := L)
      (fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z) W

/-- The relative-to-ordinary comparison sends the extension-field
diagonal to the ordinary diagonal idele. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_principalIdele
    (x : Lˣ) :
    relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L x) =
      IdeleGroup.principalIdele L x := by
  apply Prod.ext
  · apply Units.ext
    funext W
    change
      infinitePlaceTensorUnitsEquivAbove
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          ((relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L x)).infinite
              (infinitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        algebraMap L W.Completion (x : L)
    simp only [relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.infiniteComponent_principalIdele,
      infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion]
    simp
  · rw [relativeIdeleBaseChangeMulEquiv_finite]
    apply RestrictedProduct.ext
    intro W
    rw [relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply]
    change
      finitePlaceTensorUnitsEquivAboveAdic
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          ((relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L x)).finite
              (finitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        Units.map (FinitePlace.embedding (K := L) W) x
    simp only [relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.finiteComponent_principalIdele,
      finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion]
