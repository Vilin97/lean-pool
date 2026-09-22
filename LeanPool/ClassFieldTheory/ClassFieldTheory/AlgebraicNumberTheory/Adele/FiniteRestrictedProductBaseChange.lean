/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces
/-!
# Finite restricted products under scalar extension

This file flattens the finite local tensor factors of a relative idele over
`K` into the ordinary finite-place factors of `L`.  The local map is
The canonical local tensor decomposition followed by the comparison between an exact-extension
completion and the concrete adic completion at its centre.

The main point is restrictedness: coefficientwise restrictedness in a fixed
`K`-basis of `L` is equivalent, up to the already isolated finite comparison
set, to the usual valuation-ring-unit condition at almost every finite place
of `L`.
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

/-- Reindex a dependent product along an equivalence, retaining its
coordinatewise multiplicative structure. -/
noncomputable def piCongrLeftMulEquiv
    {ι ι' : Type*} (M : ι' → Type*)
    [∀ i, Mul (M i)] (e : ι ≃ ι') :
    (∀ i, M (e i)) ≃* ∀ j, M j where
  toEquiv := Equiv.piCongrLeft M e
  map_mul' f g := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change
      Equiv.piCongrLeft M e (f * g) (e i) =
        Equiv.piCongrLeft M e f (e i) *
          Equiv.piCongrLeft M e g (e i)
    rw [Equiv.piCongrLeft_apply_apply,
      Equiv.piCongrLeft_apply_apply,
      Equiv.piCongrLeft_apply_apply]
    rfl

/-- At one finite place of `K`, the canonical local tensor decomposition followed by completion
comparison identifies the tensor-unit group with the product of the concrete
adic unit groups at all finite places of `L` above it. -/
noncomputable def finitePlaceTensorUnitsEquivAboveAdic
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ ≃*
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        (W.1.adicCompletion L)ˣ :=
  (finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w).trans
    ((MulEquiv.piCongrRight fun u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L =>
      Units.mapEquiv
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv).trans
      (piCongrLeftMulEquiv
        (fun W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w} =>
          (W.1.adicCompletion L)ˣ)
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w)))

/-- Evaluation of the finite-place tensor units equivalence at an
extension of the given adic absolute value. -/
@[simp]
theorem finitePlaceTensorUnitsEquivAboveAdic_apply_extension
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (u : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w x
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w u) =
      Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) w u).toMulEquiv
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x) := by
  let P :=
    fun W : {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = w} =>
      (W.1.adicCompletion L)ˣ
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) w
  let f : ∀ a, P (e a) := fun a =>
    Units.mapEquiv
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w a).toMulEquiv
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w x a)
  exact
    (Equiv.piCongrLeft_apply_apply P e f u).trans
      (congrArg
        (Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) w u).toMulEquiv)
        (finitePlaceLocalTensorDecompositionUnitsEquiv_apply
          (K := K) (L := L) w x u))

/-- On a diagonal extension-field unit, the finite local
relative-to-ordinary comparison is the ordinary diagonal embedding. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : Lˣ) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w
        (localFieldIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (FinitePlace.embedding (K := L) W.1)
        x := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
  apply Units.ext
  simp only [Units.coe_map]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w a
          (1 ⊗ₜ[K] (x : L))) =
      FinitePlace.embedding
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a)
        (x : L)
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, one_mul,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]

/-- Flatten products first over finite places of `K` and then over places
above them into one product over all finite places of `L`. -/
noncomputable def finitePlaceAbovePiMulEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        (W.1.adicCompletion L)ˣ) ≃*
      ∀ W : HeightOneSpectrum (𝓞 L),
        (W.adicCompletion L)ˣ where
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
  map_mul' f g := by
    funext W
    rfl

/-- The unrestricted product of all finite local tensor-unit groups is the
unrestricted product of all concrete finite local unit groups of `L`. -/
noncomputable def relativeFiniteTensorPiMulEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ) ≃*
      ∀ W : HeightOneSpectrum (𝓞 L),
        (W.adicCompletion L)ˣ :=
  (MulEquiv.piCongrRight fun w =>
      finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).trans
    (finitePlaceAbovePiMulEquiv (K := K) (L := L))

/-- Coordinate formula for the relative finite tensor units
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiMulEquiv_apply
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) x W =
      finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative finite tensor units
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiMulEquiv_symm_apply
    (y : ∀ W : HeightOneSpectrum (𝓞 L),
      (W.adicCompletion L)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm y w =
      (finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- A multiplicative equivalence carries units of one submonoid to units
of another exactly when it carries their underlying elements between
the two submonoids. -/
theorem unitsMapEquiv_mem_units_iff
    {R S : Type*} [CommMonoid R] [CommMonoid S]
    (e : R ≃* S) (A : Submonoid R) (B : Submonoid S)
    (h : ∀ y : R, e y ∈ B ↔ y ∈ A)
    (x : Rˣ) :
    Units.mapEquiv e x ∈ B.units ↔ x ∈ A.units := by
  rw [Submonoid.mem_units_iff, Submonoid.mem_units_iff]
  constructor
  · rintro ⟨hval, hinv⟩
    constructor
    · exact (h (x : R)).mp (by simpa using hval)
    · apply (h ((x⁻¹ : Rˣ) : R)).mp
      rw [← (Units.mapEquiv e).map_inv x] at hinv
      exact hinv
  · rintro ⟨hval, hinv⟩
    constructor
    · simpa using (h (x : R)).mpr hval
    · rw [← (Units.mapEquiv e).map_inv x]
      exact (h ((x⁻¹ : Rˣ) : R)).mpr hinv

/-- The local tensor unit is integral in every relative-tensor factor
exactly when its flattened concrete components are local integer units at
every finite place above the base place. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x ↔
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L) w x W ∈
          (W.1.adicCompletionIntegers L).units := by
  rw [relativeLocalTensorDecompositionIntegralUnitAt_iff]
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
    rw [← hW]
    rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
    exact
      (unitsMapEquiv_mem_units_iff
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w) u)).toSubmonoid
        ((finitePlaceExtensionCentre
          (K := K) (L := L) w u).adicCompletionIntegers L).toSubmonoid
        (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
          (K := K) (L := L) w u)
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x)).2 (hx u)
  · intro hx u
    have h :=
      hx (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w u)
    rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension] at h
    exact
      (unitsMapEquiv_mem_units_iff
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w) u)).toSubmonoid
        ((finitePlaceExtensionCentre
          (K := K) (L := L) w u).adicCompletionIntegers L).toSubmonoid
        (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
          (K := K) (L := L) w u)
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x)).1 h

/-- Cofinite quantification over finite places of `L` is equivalent to
cofinite quantification over finite places of `K`, uniformly over every
place above the chosen base place. -/
theorem eventually_finitePlace_iff_eventually_all_above
    (P : ∀ _W : HeightOneSpectrum (𝓞 L), Prop) :
    (∀ᶠ W : HeightOneSpectrum (𝓞 L) in Filter.cofinite, P W) ↔
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
          P W.1 := by
  constructor
  · intro h
    have hbad :
        {W : HeightOneSpectrum (𝓞 L) | ¬ P W}.Finite :=
      Filter.eventually_cofinite.mp h
    have himage :
        (finitePlaceBelow (K := K) ''
          {W : HeightOneSpectrum (𝓞 L) | ¬ P W}).Finite :=
      hbad.image _
    apply Filter.eventually_cofinite.mpr
    apply himage.subset
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    rw [Set.mem_image]
    push Not at hw
    rcases hw with ⟨W, hW⟩
    exact ⟨W.1, hW, W.2⟩
  · intro h
    have hfibre (w : HeightOneSpectrum (𝓞 K)) :
        Finite {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} := by
      let : Fintype
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L) :=
        completionTensorDecompositionExtensionFintype
          (HeightOneSpectrum.adicAbv K w)
          (RayClass.adicAbv_isNontrivial w)
      exact
        Finite.of_equiv
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w)
    have htendsto :
        Filter.Tendsto
          (finitePlaceBelow (K := K))
          Filter.cofinite Filter.cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton
        (f := finitePlaceBelow (K := K) (L := L))
        fun w => by
          change
            {W : HeightOneSpectrum (𝓞 L) |
              finitePlaceBelow (K := K) W = w}.Finite
          exact Set.finite_coe_iff.mp (hfibre w)
    filter_upwards [htendsto.eventually h] with W hW
    exact hW ⟨W, rfl⟩

/-- The finite part of the relative restricted local product.  This is
the source model whose flattening is the ordinary finite idele group of
`L`. -/
structure RelativeFiniteIdeleData where
  /-- The unit in each finite local tensor factor. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ
  /-- Every basis coordinate of the finite component is integral at
  all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w : w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K
  /-- Every basis coordinate of the inverse finite component is integral
  at all but finitely many places. -/
  eventually_inverse_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (↑((finite w)⁻¹) :
              w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K

omit [NumberField L] in
/-- Relative finite idele data are equal when their finite components
are equal. -/
@[ext]
theorem RelativeFiniteIdeleData.ext
    {a b : RelativeFiniteIdeleData (K := K) (L := L)}
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Adjoin the trivial infinite family, so that the established relative
idele support theorem can be applied to finite restricted data. -/
noncomputable def RelativeFiniteIdeleData.toLocalData
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite _ := 1
  finite := a.finite
  eventually_integral := a.eventually_integral
  eventually_inverse_integral := a.eventually_inverse_integral

/-- A finite relative restricted family is integral in every concrete
completion factor over almost every base finite place. -/
theorem RelativeFiniteIdeleData.eventually_aboveAdicUnit
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L) w (a.finite w) W ∈
          (W.1.adicCompletionIntegers L).units := by
  let z : RelativeIdeleGroup K L :=
    relativeIdeleOfLocalData
      (K := K) (L := L) a.toLocalData
  filter_upwards [
    (relativeIdeleLocalTensorDecompositionSupport
      (K := K) (L := L) z).eventually_cofinite_notMem] with w hw
  apply
    (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
      (K := K) (L := L) w (a.finite w)).mp
  have hz :=
    relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) z w hw
  simpa [z, RelativeFiniteIdeleData.toLocalData] using hz

/-- Flatten a finite relative restricted family into an ordinary finite
idele of `L`. -/
noncomputable def relativeFiniteIdeleToFiniteIdele
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    FiniteIdeleGroup L :=
  ⟨relativeFiniteTensorPiMulEquiv
      (K := K) (L := L) a.finite,
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W =>
        relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite W ∈
          (W.adicCompletionIntegers L).units)).mpr <| by
      filter_upwards [a.eventually_aboveAdicUnit] with w hw
      intro W
      rcases W with ⟨W, hW⟩
      subst w
      exact hw ⟨W, rfl⟩⟩

/-- Evaluation of the map from relative finite idele data to finite
ideles. -/
@[simp]
theorem relativeFiniteIdeleToFiniteIdele_apply
    (a : RelativeFiniteIdeleData (K := K) (L := L))
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L) a W =
      relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) a.finite W :=
  rfl

/-- Pull an ordinary finite idele back to the unrestricted family of
finite tensor-unit factors. -/
noncomputable def finiteIdeleRelativeTensorFamily
    (y : FiniteIdeleGroup L) :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ :=
  (relativeFiniteTensorPiMulEquiv
    (K := K) (L := L)).symm (fun W => y W)

/-- The pulled-back tensor family is basis-integral, together with its
inverse, at almost every finite place of `K`. -/
theorem finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
    (y : FiniteIdeleGroup L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      RelativeBasisIntegralUnitAt
        (K := K) (L := L) w
        (finiteIdeleRelativeTensorFamily
          (K := K) (L := L) y w) := by
  have habove :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          y W.1 ∈ (W.1.adicCompletionIntegers L).units :=
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W => y W ∈
        (W.adicCompletionIntegers L).units)).mp
      (FiniteIdeleGroup.eventually_mem_localUnits y)
  filter_upwards [
    habove,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hw hbad
  apply
    (relativeBasisIntegralUnitAt_iff_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) w hbad).mpr
  apply
    (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
      (K := K) (L := L) w
      (finiteIdeleRelativeTensorFamily
        (K := K) (L := L) y w)).mpr
  intro W
  have hcomponent :=
    congrFun
      ((finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).apply_symm_apply
          (fun W => y W.1)) W
  rw [finiteIdeleRelativeTensorFamily,
    relativeFiniteTensorPiMulEquiv_symm_apply,
    hcomponent]
  exact hw W

/-- Pull an ordinary finite idele back to finite relative restricted
data. -/
noncomputable def finiteIdeleToRelativeFiniteIdeleData
    (y : FiniteIdeleGroup L) :
    RelativeFiniteIdeleData (K := K) (L := L) where
  finite :=
    finiteIdeleRelativeTensorFamily
      (K := K) (L := L) y
  eventually_integral i :=
    (finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
      (K := K) (L := L) y).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw.1 i
  eventually_inverse_integral i :=
    (finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
      (K := K) (L := L) y).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw.2 i

/-- The finite relative restricted product is the ordinary finite idele
group of the extension field. -/
noncomputable def relativeFiniteIdeleEquiv :
    RelativeFiniteIdeleData (K := K) (L := L) ≃
      FiniteIdeleGroup L where
  toFun :=
    relativeFiniteIdeleToFiniteIdele
      (K := K) (L := L)
  invFun :=
    finiteIdeleToRelativeFiniteIdeleData
      (K := K) (L := L)
  left_inv a := by
    apply RelativeFiniteIdeleData.ext
    change
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm
          (relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite) =
        a.finite
    exact
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm_apply_apply a.finite
  right_inv y := by
    apply Subtype.ext
    change
      relativeFiniteTensorPiMulEquiv
          (K := K) (L := L)
          ((relativeFiniteTensorPiMulEquiv
            (K := K) (L := L)).symm (fun W => y W)) =
        fun W => y W
    exact
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).apply_symm_apply (fun W => y W)

/-- The transported group structure on the finite relative restricted
product. -/
noncomputable instance relativeFiniteIdeleDataGroup :
    Group (RelativeFiniteIdeleData (K := K) (L := L)) :=
  (relativeFiniteIdeleEquiv
    (K := K) (L := L)).group

/-- The finite restricted-product comparison as a multiplicative
equivalence. -/
noncomputable def relativeFiniteIdeleMulEquiv :
    RelativeFiniteIdeleData (K := K) (L := L) ≃*
      FiniteIdeleGroup L :=
  (relativeFiniteIdeleEquiv
    (K := K) (L := L)).mulEquiv

/-- The relative finite idele equivalence agrees with the underlying
finite-idele map. -/
@[simp]
theorem relativeFiniteIdeleMulEquiv_apply
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    relativeFiniteIdeleMulEquiv
        (K := K) (L := L) a =
      relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L) a :=
  rfl
