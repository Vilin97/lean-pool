/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
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
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
/-!
# Integral finite-place preimages of local tensor norms

If a finite local component is both a determinant norm and a local
integer unit, its determinant-norm preimage can be chosen integral in
every factor of the canonical local tensor decomposition.  This is the local restricted-product
input needed to assemble pointwise local norm preimages globally.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.Completion

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

universe u

omit [NumberField L] [IsGalois K L] in
/-- The finite-place completion comparison restricts to an inclusion of
integer-unit groups: an integral unit on the adic-completion side has an
integer-unit preimage on the absolute-value-completion side. -/
theorem exists_finitePlaceCompletionIntegerUnit_of_unitsEquiv_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    (x : (v₀.adicCompletion K)ˣ)
    (hx :
      finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    ∃ x₀O : 𝒪[vK.Completion]ˣ,
      integerUnitsToFieldUnits vK.Completion x₀O = x₀ := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  rw [Submonoid.mem_units_iff] at hxUnit
  have hx₀norm :
      ‖(x₀ : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K)) hx
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            (x₀ : vK.Completion)‖ =
          ‖(x₀ : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          (x₀ : vK.Completion) = (x : v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hxUnit.1
  have hx₀invnorm :
      ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K))
        (congrArg Inv.inv hx)
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            ((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ =
          ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          ((x₀⁻¹ : vK.Completionˣ) : vK.Completion) =
        ((x⁻¹ : (v₀.adicCompletion K)ˣ) :
          v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hxUnit.2
  let x₀O : 𝒪[vK.Completion]ˣ :=
    { val :=
        ⟨x₀,
          (finitePlaceCompletion_mem_integers_iff_norm_le_one
            vK hvKna (x₀ : vK.Completion)).2 hx₀norm⟩
      inv :=
        ⟨x₀⁻¹,
          by
            simpa using
              (finitePlaceCompletion_mem_integers_iff_norm_le_one
                vK hvKna
                ((x₀⁻¹ : vK.Completionˣ) :
                  vK.Completion)).2 hx₀invnorm⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  refine ⟨x₀O, ?_⟩
  apply Units.ext
  rfl

/-- If the norm of an extension-field unit comes from a base valuation-ring
unit, then the extension-field unit has normalized valuation zero. -/
theorem v_eq_zero_of_normUnits_eq_integerUnitsToFieldUnits
    (F E : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation E)]
    [IsIntegralClosure 𝒪[E] 𝒪[F] E]
    (xO : 𝒪[F]ˣ)
    (y : Eˣ)
    (hy :
      LocalFieldTheory.normUnits F E y =
        integerUnitsToFieldUnits F xO) :
    v E (Additive.ofMul y) = 0 := by
  have hNormValuation :=
    v_normUnits_eq_residue_finrank_mul_of_isGalois F E y
  rw [hy, v_integerUnitsToFieldUnits] at hNormValuation
  have hf :
      (Module.finrank 𝓀[F] 𝓀[E] : Int) ≠ 0 := by
    exact_mod_cast
      (Module.finrank_pos :
        0 < Module.finrank 𝓀[F] 𝓀[E]).ne'
  exact
    (mul_eq_zero.mp hNormValuation.symm).resolve_left hf

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- A unit of a localized completion whose underlying element and inverse
have norm at most one determines an integer unit in the full completion. -/
theorem exists_absoluteValueCompletionIntegerUnit_of_localizedCompletion_norm_bounds
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)
    (y : (LocalizedCompletion vK w)ˣ)
    (hy : ‖(y : LocalizedCompletion vK w)‖ ≤ 1)
    (hyInv :
      ‖((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w)‖ ≤ 1) :
    ∃ yO :
        (absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w))ˣ,
      ((Units.map
        (absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w)).subtype yO :
          w.1.Completionˣ) :
        w.1.Completion) =
      ((y : LocalizedCompletion vK w) :
        w.1.Completion) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let eW :=
    localizedCompletionEquivCompletion vK hvK w
  let yW : w.1.Completionˣ :=
    Units.mapEquiv eW.toMulEquiv y
  have hyWMem :
      (yW : w.1.Completion) ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w) := by
    rw [mem_absoluteValueCompletionIntegers_iff]
    change ‖eW (y : LocalizedCompletion vK w)‖ ≤ 1
    change ‖(y : LocalizedCompletion vK w)‖ ≤ 1
    exact hy
  have hyWInvMem :
      ((yW⁻¹ : w.1.Completionˣ) : w.1.Completion) ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w) := by
    rw [mem_absoluteValueCompletionIntegers_iff]
    change
      ‖eW
        (((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
          LocalizedCompletion vK w))‖ ≤ 1
    change
      ‖((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w)‖ ≤ 1
    exact hyInv
  let yO :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          vK hvKna w))ˣ :=
    { val := ⟨yW, hyWMem⟩
      inv := ⟨yW⁻¹, by simpa using hyWInvMem⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  refine ⟨yO, ?_⟩
  rfl

/-- A family of completion-integer units supported at one extension of a
finite place. -/
noncomputable def singleFinitePlaceIntegralUnitFamily
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    ∀ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      (absoluteValueCompletionIntegers u.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          u))ˣ := by
  classical
  exact fun u =>
    dite (w = u)
      (fun h => h ▸ y)
      (fun _ => 1)

/-- The integral local tensor unit represented by a unit in one completion
factor and by one in every other factor. -/
noncomputable def singleRelativeLocalTensorDecompositionIntegralUnit
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) v₀ :=
  (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
    (K := K) (L := L) v₀).symm
      (singleFinitePlaceIntegralUnitFamily
        (K := K) (L := L) v₀ w y)

omit [NumberField L] [IsGalois K L] in
/-- The component of a singly supported integral tensor unit is the
corresponding member of its defining completion-unit family. -/
theorem finitePlaceLocalTensorDecompositionUnitsComponent_single
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (u :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L) :
    finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) v₀ u
        (singleRelativeLocalTensorDecompositionIntegralUnit
          (K := K) (L := L) v₀ w y) =
      Units.map
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K v₀)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
            u)).subtype
        (singleFinitePlaceIntegralUnitFamily
          (K := K) (L := L) v₀ w y u) := by
  have h :=
    congrFun
      ((relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
        (K := K) (L := L) v₀).apply_symm_apply
          (singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y)) u
  apply Units.ext
  exact congrArg Subtype.val
    (congrArg Units.val h)

omit [NumberField L] [IsGalois K L] in
/-- A singly supported integral tensor unit is integral in every completion
factor, together with its inverse. -/
theorem singleRelativeLocalTensorDecompositionIntegralUnit_isIntegral
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) v₀
      (singleRelativeLocalTensorDecompositionIntegralUnit
        (K := K) (L := L) v₀ w y) :=
  (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
    (K := K) (L := L) v₀
    (singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y)).1
    (singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y).property

omit [NumberField L] [IsGalois K L] in
/-- The product of component norms of a singly supported integral tensor
unit is the norm of its supported component. -/
theorem prod_norm_finitePlaceLocalTensorDecompositionUnitsComponent_single_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    [Fintype
      (AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)]
    [∀ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      Module.Finite
        (HeightOneSpectrum.adicAbv K v₀).Completion
        u.1.Completion]
    (hNorm :
      Algebra.norm
          (HeightOneSpectrum.adicAbv K v₀).Completion
          ((Units.map
            (absoluteValueCompletionIntegers w.1
              (absoluteValueExtension_isNonarchimedean
                (HeightOneSpectrum.adicAbv K v₀)
                (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
                w)).subtype y :
              w.1.Completionˣ) :
            w.1.Completion) =
        (x₀ : (HeightOneSpectrum.adicAbv K v₀).Completion)) :
    (∏ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      Algebra.norm
        (HeightOneSpectrum.adicAbv K v₀).Completion
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) v₀ u
          (singleRelativeLocalTensorDecompositionIntegralUnit
            (K := K) (L := L) v₀ w y) :
          u.1.Completion)) =
      (x₀ : (HeightOneSpectrum.adicAbv K v₀).Completion) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let z :
      (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y
  have hComponents :
      ∀ u : AbsoluteValueExtension vK L,
        finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z =
          Units.map
            (absoluteValueCompletionIntegers u.1
              (absoluteValueExtension_isNonarchimedean
                vK hvKna u)).subtype
            (singleFinitePlaceIntegralUnitFamily
              (K := K) (L := L) v₀ w y u) :=
    finitePlaceLocalTensorDecompositionUnitsComponent_single
      (K := K) (L := L) v₀ w y
  rw [Finset.prod_eq_single w]
  · rw [hComponents]
    have hSelf :
        singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y w =
          y := by
      change
        dite (w = w)
            (fun h => h ▸ y)
            (fun _ => 1) =
          y
      rw [dite_eq_left rfl]
    rw [hSelf]
    exact hNorm
  · intro u _ hu
    rw [hComponents]
    have hwu : w ≠ u := Ne.symm hu
    have hAway :
        singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y u =
          1 := by
      change
        dite (w = u)
            (fun h => h ▸ y)
            (fun _ => 1) =
          1
      rw [dite_eq_right hwu]
    rw [hAway]
    simp
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

omit [NumberField L] in
/-- The determinant norm of a singly supported integral tensor unit is the
norm of its unique nontrivial completion component. -/
theorem localTensorDetNorm_singleRelativeLocalTensorDecompositionIntegralUnit_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    (hNorm :
      let vK := HeightOneSpectrum.adicAbv K v₀
      letI hK :=
        AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI : Algebra vK.Completion w.1.Completion :=
        AbsoluteValue.completionAlgebra vK w.1 w.2
      Algebra.norm vK.Completion
        ((Units.map
          (absoluteValueCompletionIntegers w.1
            (absoluteValueExtension_isNonarchimedean
              vK
              (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
              w)).subtype y :
            w.1.Completionˣ) :
          w.1.Completion) =
        (x₀ : vK.Completion)) :
    localTensorDetNorm
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v₀)
        ((finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v₀).symm
          (singleRelativeLocalTensorDecompositionIntegralUnit
            (K := K) (L := L) v₀ w y)) =
      x₀ := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK := RayClass.adicAbv_isNontrivial v₀
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  dsimp only at hNorm
  let :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  let : ∀ u : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion u.1.Completion :=
    fun u =>
      completionModuleFinite vK hvK u
  let z :
      (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y
  let zA :
      (LocalTensorAlgebra (L := L) vK)ˣ :=
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v₀).symm z
  have hNormProduct :=
    RelativeIdeleGroup.localNorm_units_eq_prod
      vK hvK zA
  have hProduct :
      (∏ u : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z :
              u.1.Completion)) =
        (x₀ : vK.Completion) :=
    prod_norm_finitePlaceLocalTensorDecompositionUnitsComponent_single_eq
      (K := K) (L := L) v₀ w y x₀ hNorm
  apply Units.ext
  change
    ((Units.map (Algebra.norm vK.Completion) zA :
        vK.Completionˣ) : vK.Completion) =
      (x₀ : vK.Completion)
  rw [hNormProduct]
  have hComponentEq :
      ∀ u : AbsoluteValueExtension vK L,
        completionTensorDecompositionLeft
              (K := K) (L := L) vK hvK
              (zA : LocalTensorAlgebra (L := L) vK) u =
          (finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z :
              u.1.Completion) := by
    intro u
    rfl
  simpa only [hComponentEq] using hProduct

omit [NumberField L] in
private theorem exists_localizedCompletionNormPreimage_with_norm_bounds
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let E := LocalizedCompletion vK w
    ∃ x₀ : vK.Completionˣ,
      ∃ y : Eˣ,
        LocalFieldTheory.normUnits vK.Completion E y = x₀ ∧
          finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x ∧
            ‖(y : E)‖ ≤ 1 ∧
              ‖((y⁻¹ : Eˣ) : E)‖ ≤ 1 := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v₀)
  let : IsUltrametricDist vK.Completion :=
    completionIsUltrametricDist vK hvKna
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2 inferInstance
  let vB := ValuativeRel.valuation vK.Completion
  let : vB.IsNontrivial := inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : FiniteDimensional vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK w
  let : ContinuousSMul vK.Completion w.1.Completion :=
    continuousSMul_of_algebraMap _ _
      (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
  let : LocallyCompactSpace w.1.Completion :=
    LocallyCompactSpace.of_finiteDimensional_of_complete
      vK.Completion w.1.Completion
  let eE : E ≃ᵢ w.1.Completion :=
    { toEquiv :=
        (localizedCompletionEquivCompletion vK hvK w).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  let : LocallyCompactSpace E :=
    (eE.toHomeomorph.locallyCompactSpace_iff).2 inferInstance
  let : IsUltrametricDist E :=
    localizedCompletionIsUltrametricDist vK w hvKna
  let : Valued E ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel E :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let vENorm : Valuation E ℝ≥0 := Valued.v
  let : vENorm.Compatible :=
    Valuation.Compatible.ofValuation vENorm
  let vE := ValuativeRel.valuation E
  let : Valuation.HasExtension vB vE :=
    localizedCompletionValuationHasExtension vK w hvKna
  let : vE.IsNontrivial :=
    Valuation.IsNontrivial.of_hasExtension vB vE
  let : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vE).2 inferInstance
  let : IsValuativeTopology E :=
    isValuativeTopology_of_valued_ofValuation E ℝ≥0
  let : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : Algebra 𝒪[vK.Completion] E :=
    Algebra.ofSubsemiring 𝒪[vK.Completion]
  let : IsIntegralClosure 𝒪[E] 𝒪[vK.Completion] E :=
    localizedCompletionIsIntegralClosureWithExtension
      vK w hvK hvKna
  let : Module.Finite 𝒪[vK.Completion] 𝒪[E] :=
    integerRing_moduleFinite_of_isIntegralClosure
      vK.Completion E
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  have hxChosen :
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v₀ := by
    rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v₀]
    exact hxNorm
  change
    x ∈ (localNormSubgroup vK.Completion E).map
      e.toMonoidHom at hxChosen
  rcases hxChosen with ⟨x₀, hx₀, hx₀map⟩
  have hx₀' :
      x₀ ∈ localNormSubgroup vK.Completion E :=
    hx₀
  rcases
      MonoidHom.mem_range.mp hx₀' with
    ⟨y, hy⟩
  have hx₀val :
      e x₀ = x :=
    hx₀map
  obtain ⟨x₀O, hx₀O⟩ :=
    exists_finitePlaceCompletionIntegerUnit_of_unitsEquiv_eq
      (K := K) v₀ x₀ x hx₀val hxUnit
  have hyValuation :
      v E (Additive.ofMul y) = 0 := by
    apply
      v_eq_zero_of_normUnits_eq_integerUnitsToFieldUnits
        vK.Completion E x₀O y
    exact hy.trans hx₀O.symm
  have hyValuationMap :
      valuationMap E (Additive.ofMul y) = 0 :=
    hyValuation
  let yO : 𝒪[E]ˣ :=
    integerUnitOfValuationMapZero E y hyValuationMap
  have hyO :
      integerUnitsToFieldUnits E yO = y :=
    integerUnitOfValuationMapZero_spec E y hyValuationMap
  have hyMem : (y : E) ∈ 𝒪[E] := by
    have hval :=
      congrArg (fun q : Eˣ => (q : E)) hyO
    rw [← hval]
    exact yO.val.property
  have hyInvMem :
      ((y⁻¹ : Eˣ) : E) ∈ 𝒪[E] := by
    have hInv :
        integerUnitsToFieldUnits E (yO⁻¹) = y⁻¹ := by
      rw [map_inv, hyO]
    have hval :=
      congrArg (fun q : Eˣ => (q : E)) hInv
    rw [← hval]
    exact (yO⁻¹).val.property
  have hyNorm : ‖(y : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one
      vK w hvKna (y : E)).1 hyMem
  have hyInvNorm : ‖((y⁻¹ : Eˣ) : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one
      vK w hvKna _).1 hyInvMem
  exact ⟨x₀, y, hy, hx₀val, hyNorm, hyInvNorm⟩

omit [NumberField L] in
private theorem exists_singleFinitePlaceIntegralUnit_norm_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    ∃ x₀ : vK.Completionˣ,
      ∃ yO :
          (absoluteValueCompletionIntegers w.1
            (absoluteValueExtension_isNonarchimedean
              vK hvKna w))ˣ,
        Algebra.norm vK.Completion
            ((Units.map
              (absoluteValueCompletionIntegers w.1
                (absoluteValueExtension_isNonarchimedean
                  vK hvKna w)).subtype yO :
                w.1.Completionˣ) :
              w.1.Completion) =
            (x₀ : vK.Completion) ∧
          finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  obtain ⟨x₀, y, hy, hx₀val, hyNorm, hyInvNorm⟩ :=
    exists_localizedCompletionNormPreimage_with_norm_bounds
      (K := K) (L := L) v₀ x hxNorm hxUnit
  obtain ⟨yO, hyO⟩ :=
    exists_absoluteValueCompletionIntegerUnit_of_localizedCompletion_norm_bounds
      (K := K) (L := L) vK hvK hvKna w y hyNorm hyInvNorm
  let eW :=
    localizedCompletionEquivCompletion vK hvK w
  have hNormTransport :
      Algebra.norm vK.Completion
          ((y : E) : w.1.Completion) =
        (x₀ : vK.Completion) := by
    change
      Algebra.norm vK.Completion
          (eW (y : E)) =
        (x₀ : vK.Completion)
    rw [Algebra.norm_eq_of_algEquiv eW]
    exact congrArg Units.val hy
  have hNorm :
      Algebra.norm vK.Completion
          ((Units.map
            (absoluteValueCompletionIntegers w.1
              (absoluteValueExtension_isNonarchimedean
                vK hvKna w)).subtype yO :
              w.1.Completionˣ) :
            w.1.Completion) =
        (x₀ : vK.Completion) := by
    calc
      _ = Algebra.norm vK.Completion
          ((y : E) : w.1.Completion) :=
        congrArg (Algebra.norm vK.Completion) hyO
      _ = (x₀ : vK.Completion) := hNormTransport
  exact ⟨x₀, yO, hNorm, hx₀val⟩

omit [NumberField L] in
/-- A local integer unit in the finite tensor-norm image has a preimage
which is integral, together with its inverse, in every factor of the
canonical local tensor decomposition. -/
theorem exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    ∃ z : (v₀.adicCompletion K ⊗[K] L)ˣ,
      _root_.localTensorNorm
          (K := K) (L := L) v₀ z = x ∧
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) v₀ z := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  obtain ⟨x₀, yWO, hNorm, hx₀val⟩ :=
    exists_singleFinitePlaceIntegralUnit_norm_eq
      (K := K) (L := L) v₀ x hxNorm hxUnit
  let z : (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w yWO
  have hzIntegral :
      RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) v₀ z :=
    singleRelativeLocalTensorDecompositionIntegralUnit_isIntegral
      (K := K) (L := L) v₀ w yWO
  refine ⟨z, ?_, hzIntegral⟩
  let zA :
      (LocalTensorAlgebra (L := L) vK)ˣ :=
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v₀).symm z
  have hTensorNormSingle :
      localTensorDetNorm
          (K := K) (L := L) vK
          ((finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀).symm
            (singleRelativeLocalTensorDecompositionIntegralUnit
              (K := K) (L := L) v₀ w yWO)) =
        x₀ :=
      localTensorDetNorm_singleRelativeLocalTensorDecompositionIntegralUnit_eq
        (K := K) (L := L) v₀ w yWO x₀ hNorm
  have hTensorNorm :
      localTensorDetNorm
          (K := K) (L := L) vK zA = x₀ := by
    simpa only [zA, z] using hTensorNormSingle
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  calc
    _root_.localTensorNorm
        (K := K) (L := L) v₀ z =
      _root_.localTensorNorm
          (K := K) (L := L) v₀
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀ zA) := by
        congr 1
        exact
          ((finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀).apply_symm_apply z).symm
    _ =
      e
        (localTensorDetNorm
          (K := K) (L := L) vK zA) :=
      (finitePlaceLocalTensorNorm_commutes
        (K := K) (L := L) v₀ zA).symm
    _ = e x₀ := congrArg e hTensorNorm
    _ = x := hx₀val
