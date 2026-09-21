/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
/-!
# Integral finite local factors of the relative idele group

For a finite place `w` of the base field, the canonical local tensor decomposition identifies
`K_w ⊗_K L` with the product of the completions of `L` above `w`.
This file packages each projection as an actual ring homomorphism and
defines the subgroup of tensor units whose value and inverse are integral
in every completion factor.  Thus the integrality predicate used for the
restricted product is closed under all group operations for structural,
rather than coordinate-dependent, reasons.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The projection of the finite local tensor algebra to one completion
factor in the canonical local tensor decomposition, as a ring homomorphism. -/
noncomputable def finitePlaceLocalTensorDecompositionComponentRingHom
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L) →+* wL.1.Completion := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Pi.evalRingHom
      (fun u : AbsoluteValueExtension vK L =>
        u.1.Completion) wL).comp
      ((completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toRingEquiv.toRingHom.comp
        (relativeFinitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w).symm.toRingEquiv.toRingHom)

omit [NumberField L] in
/-- The ring-homomorphism packaging evaluates to the original
relative-tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponentRingHom_apply
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponentRingHom
        (K := K) (L := L) w wL x =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Every relative-tensor component map sends zero to zero. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_zero
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL 0 = 0 := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_zero

omit [NumberField L] in
/-- Relative-tensor component maps preserve addition. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_add
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x y : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (x + y) =
      finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL x +
        finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL y := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_add x y

/-- The corresponding component homomorphism on units. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L)ˣ →*
      wL.1.Completionˣ :=
  Units.map
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL)

/-- The canonical local tensor decomposition on the complete group of units of the finite local
tensor algebra. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        wL.1.Completionˣ := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Units.mapEquiv
      (((relativeFinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w).symm.toRingEquiv.trans
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK).toRingEquiv).toMulEquiv)).trans
      MulEquiv.piUnits

omit [NumberField L] in
/-- The product equivalence on units evaluates componentwise through the
corresponding unit homomorphism. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsEquiv_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w x wL =
      finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Coercing a unit component to the completion agrees with applying the
underlying tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsComponent_coe
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    ((finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :
          wL.1.Completionˣ) :
        wL.1.Completion) =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (x : w.adicCompletion K ⊗[K] L) :=
  rfl

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The completion equivalence induced by conjugation preserves the
norm exactly. -/
theorem conjugateExtensionCompletionRingEquiv_norm_eq
    (vK : AbsoluteValue K ℝ)
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    ‖conjugateExtensionCompletionRingEquiv vK wL σ x‖ =
      ‖x‖ := by
  change ‖conjugateCompletionRingEquiv wL.1 σ x‖ = ‖x‖
  let f := (conjugateWithAbsRingEquiv wL.1 σ).toRingHom
  let h := conjugateWithAbsRingEquiv_isometry wL.1 σ
  change
    ‖UniformSpace.Completion.mapRingHom f h.continuous x‖ = ‖x‖
  exact
    (UniformSpace.Completion.isometry_mapRingHom h).norm_map_of_map_zero
      (map_zero (UniformSpace.Completion.mapRingHom f h.continuous)) x

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The conjugate-completion equivalence identifies the two valuation
rings. -/
theorem
    conjugateExtensionCompletionRingEquiv_mem_integers_iff
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    conjugateExtensionCompletionRingEquiv vK wL σ x ∈
        absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            vK hvK wL) ↔
      x ∈
        absoluteValueCompletionIntegers
          (absoluteValueExtensionConjugate
            vK wL σ).1
          (absoluteValueExtension_isNonarchimedean
            vK hvK
            (absoluteValueExtensionConjugate
              vK wL σ)) := by
  rw [mem_absoluteValueCompletionIntegers_iff,
    mem_absoluteValueCompletionIntegers_iff,
    conjugateExtensionCompletionRingEquiv_norm_eq]

omit [NumberField L] in
/-- Galois conjugation sends the component at `wL` to the component at
the conjugate extension, transported by the canonical completion
isometry. -/
theorem finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (σ : L ≃ₐ[K] L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.adicCompletion K) σ x) =
      conjugateExtensionCompletionRingEquiv
        (HeightOneSpectrum.adicAbv K w) wL σ
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w
          (absoluteValueExtensionConjugate
            (HeightOneSpectrum.adicAbv K w) wL σ) x) := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, finitePlaceLocalTensorDecompositionComponent_add,
        finitePlaceLocalTensorDecompositionComponent_add, map_add, hx, hy]
  | tmul a b =>
      rw [scalarTensorConjugation_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        map_mul]
      change
        algebraMap vK.Completion wL.1.Completion
              ((relativeFinitePlaceCompletionAlgEquiv
                (K := K) w).symm a) *
            AbsoluteValue.toCompletion wL.1 (σ b) =
          conjugateExtensionCompletionRingEquiv vK wL σ
                (algebraMap vK.Completion
                  (absoluteValueExtensionConjugate
                    vK wL σ).1.Completion
                  ((relativeFinitePlaceCompletionAlgEquiv
                    (K := K) w).symm a)) *
            conjugateExtensionCompletionRingEquiv vK wL σ
              (AbsoluteValue.toCompletion
                (absoluteValueExtensionConjugate
                  vK wL σ).1 b)
      rw [conjugateExtensionCompletionRingEquiv_algebraMap,
        conjugateExtensionCompletionRingEquiv_toCompletion]

omit [NumberField L] in
/-- Valuation-ring integrality of a tensor element is preserved by
Galois conjugation. -/
theorem relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      (scalarTensorConjugation
        (K := K) (L := L)
        (A := w.adicCompletion K) σ x) := by
  intro wL
  rw [finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation]
  exact
    (conjugateExtensionCompletionRingEquiv_mem_integers_iff
      (K := K) (L := L)
      (vK := HeightOneSpectrum.adicAbv K w)
      (hvK :=
        HeightOneSpectrum.isNonarchimedean_adicAbv K w)
      (wL := wL) (σ := σ) _).2
      (hx
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K w) wL σ))

omit [NumberField L] in
/-- The integral tensor-unit condition is stable under the natural
Galois action. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_smul
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (hx : RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w x) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w (σ • x) := by
  let := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  constructor
  · change
      RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w
        (↑(σ • x) :
          w.adicCompletion K ⊗[K] L)
    rw [scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.1
  · change
      RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w
        (↑((σ • x)⁻¹) :
          w.adicCompletion K ⊗[K] L)
    rw [← smul_inv', scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.2

omit [NumberField L] in
/-- Integrality of a tensor unit is exactly membership of every
relative-tensor component in the unit subgroup of its valuation ring. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x ↔
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) w wL x ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
  constructor
  · rintro ⟨hx, hxinv⟩ wL
    exact ⟨hx wL, by
      change
        finitePlaceLocalTensorDecompositionComponent
            (K := K) (L := L) w wL
            (↑(x⁻¹) :
              w.adicCompletion K ⊗[K] L) ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)
      exact hxinv wL⟩
  · intro hx
    constructor
    · intro wL
      exact (hx wL).1
    · intro wL
      exact (hx wL).2

/-- The actual integral-unit subgroup in a finite local tensor factor. -/
noncomputable def relativeLocalTensorDecompositionIntegralUnitSubgroup
    (w : HeightOneSpectrum (𝓞 K)) :
    Subgroup (w.adicCompletion K ⊗[K] L)ˣ :=
  Subgroup.comap
    (MonoidHom.pi
      (fun wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L =>
        finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w wL))
    (Subgroup.pi Set.univ fun wL =>
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K w)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
          wL)).units)

/-- The product of the actual valuation-ring unit groups in all
completion factors above a finite base place. -/
abbrev FinitePlaceLocalTensorDecompositionIntegralUnitProduct
    (w : HeightOneSpectrum (𝓞 K)) :=
  Subgroup.pi Set.univ fun
      wL : AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K w) L =>
    (absoluteValueCompletionIntegers wL.1
      (absoluteValueExtension_isNonarchimedean
        (HeightOneSpectrum.adicAbv K w)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
        wL)).units

/-- A product subgroup is the product of its component subgroup types. -/
@[implicit_reducible]
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).units where
  toFun x wL :=
    ⟨x.1 wL, x.2 wL (Set.mem_univ wL)⟩
  invFun x :=
    ⟨fun wL => x wL, by
      intro wL hwL
      exact (x wL).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext wL
    apply Subtype.ext
    rfl
  map_mul' x y := by
    funext wL
    apply Subtype.ext
    rfl

/-- Replace each valuation-ring unit subgroup by the intrinsic unit
group of the valuation ring. -/
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (K := K) (L := L) w).trans
      (MulEquiv.piCongrRight fun wL =>
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).unitsEquivUnitsType)

omit [NumberField L] in
/-- Membership in the integral tensor-unit subgroup is exactly the
pointwise valuation-ring integrality condition. -/
@[simp]
theorem mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    x ∈ relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ↔
      RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x := by
  rw [relativeLocalTensorDecompositionIntegralUnitAt_iff]
  simp only [relativeLocalTensorDecompositionIntegralUnitSubgroup,
    Subgroup.mem_comap, MonoidHom.pi_apply, Subgroup.mem_pi,
    Set.mem_univ, forall_const]

/-- The restricted Galois action on the integral tensor-unit
subgroup. -/
@[implicit_reducible]
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
    (w : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w) := by
  letI := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  exact
    { smul := fun σ x =>
        ⟨σ • (x :
            (w.adicCompletion K ⊗[K] L)ˣ),
          by
            rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff]
            have hx :
                RelativeLocalTensorDecompositionIntegralUnitAt
                  (K := K) (L := L) w
                  (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
              (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
                (K := K) (L := L) w x).1 x.property
            exact
              relativeLocalTensorDecompositionIntegralUnitAt_smul
                (K := K) (L := L) w σ x hx⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change
          (1 : L ≃ₐ[K] L) •
              (x : (w.adicCompletion K ⊗[K] L)ˣ) =
            (x : (w.adicCompletion K ⊗[K] L)ˣ)
        exact one_smul (L ≃ₐ[K] L) _
      mul_smul := by
        intro σ τ x
        apply Subtype.ext
        exact mul_smul σ τ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
      smul_one := by
        intro σ
        apply Subtype.ext
        change
          σ • (1 : (w.adicCompletion K ⊗[K] L)ˣ) = 1
        exact smul_one σ
      smul_mul := by
        intro σ x y
        apply Subtype.ext
        exact smul_mul' σ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
          (y : (w.adicCompletion K ⊗[K] L)ˣ) }

omit [NumberField L] in
@[simp]
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w
    ((σ • x :
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w) :
      (w.adicCompletion K ⊗[K] L)ˣ) =
      letI := scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.adicCompletion K)
      σ •
        (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
  rfl

/-- The integral local tensor-unit subgroup is exactly the product of
the valuation-ring unit groups occurring in the canonical local tensor decomposition. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w where
  toFun x := ⟨finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w x, by
    have hx := x.property
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff] at hx
    rw [Subgroup.mem_pi]
    intro wL hwL
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using
      (hx wL)⟩
  invFun y := ⟨(finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w).symm y, by
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff]
    intro wL
    have hy :
        finitePlaceLocalTensorDecompositionUnitsEquiv
            (K := K) (L := L) w
            ((finitePlaceLocalTensorDecompositionUnitsEquiv
              (K := K) (L := L) w).symm y) wL ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
      rw [(finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply]
      exact y.property wL (Set.mem_univ wL)
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using hy⟩
  left_inv x := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).map_mul x y

/-- Final local form: the integral tensor units are the product of the
intrinsic unit groups of all completion valuation rings above `w`. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (K := K) (L := L) w).trans
      (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
        (K := K) (L := L) w)
