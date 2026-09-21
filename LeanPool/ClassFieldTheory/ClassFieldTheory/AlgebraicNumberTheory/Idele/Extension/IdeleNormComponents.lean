/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
/-!
# Local components of the ordinary idele norm

The ordinary idele norm is transported from the determinant norm on the
relative idele group. At each place, the canonical local tensor decomposition identifies that
determinant with the product of the ordinary field norms on the completion
factors above the place.  These are the concrete finite- and infinite-place
forms of the local idele norm formula.
-/

open scoped BigOperators NumberField TensorProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The relative-tensor coordinate form underlying the public finite-place
formula below. -/
private theorem finiteComponent_norm_eq_prod_extensions
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let z :=
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a
    let x :=
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v z
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v w x) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) v z
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v w x)
  rw [← hz, norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.finiteComponent_norm]
  apply Units.ext
  change
    (_root_.relativeFinitePlaceCompletionAlgEquiv
        (K := K) v).symm
        (Algebra.norm (v.adicCompletion K)
          (x : v.adicCompletion K ⊗[K] L)) =
      (((∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
              (K := K) (L := L) v w x)) :
          vK.Completionˣ) : vK.Completion)
  let x' : (vK.Completion ⊗[K] L)ˣ :=
    Units.mapEquiv
      (_root_.relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) v).symm.toMulEquiv x
  calc
    (_root_.relativeFinitePlaceCompletionAlgEquiv
        (K := K) v).symm
        (Algebra.norm (v.adicCompletion K)
          (x : v.adicCompletion K ⊗[K] L)) =
        Algebra.norm vK.Completion
          (x' : vK.Completion ⊗[K] L) := by
      exact
        map_norm_tensorProduct_baseChange
          (K := K) (L := L)
          (_root_.relativeFinitePlaceCompletionAlgEquiv
            (K := K) v).symm.toAlgHom
          (x : v.adicCompletion K ⊗[K] L)
    _ = ∏ w : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK
            (x' : vK.Completion ⊗[K] L) w) := by
      exact
        RelativeIdeleGroup.localNorm_units_eq_prod
          vK hvK x'
    _ =
        (((∏ w : AbsoluteValueExtension vK L,
            Units.map (Algebra.norm vK.Completion)
              (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
                (K := K) (L := L) v w x)) :
            vK.Completionˣ) : vK.Completion) := by
      change _ = Units.coeHom vK.Completion _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro w _
      rfl

/-- The finite-place form of the ordinary idele norm. Each factor
is the mathlib field norm of the actual idele component at the concrete
finite place corresponding to an exact extension of `v`; the existing
completion equivalence is used only to put that component in the canonical
absolute-value completion. -/
private theorem finiteComponent_norm_eq_prod_completion
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) v z
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a))
  calc
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
        ∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
              (K := K) (L := L) v w x) :=
      finiteComponent_norm_eq_prod_extensions
        (K := K) (L := L) v a
    _ = ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)) := by
      apply Finset.prod_congr rfl
      intro w _
      apply congrArg (Units.map (Algebra.norm vK.Completion))
      let W :=
        finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w
      have hcomponent :=
        congrArg (fun b : IdeleGroup L => finiteComponent W.1 b) hz
      change
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z).2 W.1 =
          finiteComponent W.1 a at hcomponent
      rw [relativeIdeleBaseChangeMulEquiv_finite,
        _root_.relativeFiniteIdeleToFiniteIdele_apply,
        _root_.relativeFiniteTensorPiMulEquiv_apply] at hcomponent
      change
        _root_.finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L)
            (_root_.finitePlaceBelow (K := K) W.1)
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L)
              (_root_.finitePlaceBelow (K := K) W.1) z)
            ⟨W.1, rfl⟩ =
          finiteComponent W.1 a at hcomponent
      have hcomponent' :
          _root_.finitePlaceTensorUnitsEquivAboveAdic
              (K := K) (L := L) v x W =
            finiteComponent W.1 a := by
        let W₀ : HeightOneSpectrum (𝓞 L) := W.1
        let P : HeightOneSpectrum (𝓞 K) → Prop := fun q =>
          ∀ hq : _root_.finitePlaceBelow (K := K) W₀ = q,
            _root_.finitePlaceTensorUnitsEquivAboveAdic
                (K := K) (L := L) q
                (RelativeIdeleGroup.finiteComponent
                  (K := K) (L := L) q z)
                ⟨W₀, hq⟩ =
              finiteComponent W₀ a
        have hP :
            P (_root_.finitePlaceBelow (K := K) W₀) := by
          intro hq
          simpa only [P, W₀] using hcomponent
        have hW :
            _root_.finitePlaceBelow (K := K) W₀ = v :=
          W.2
        have hPv : P v :=
          hW ▸ hP
        simpa only [P, W₀, x] using hPv W.2
      dsimp only [W] at hcomponent'
      rw [
        _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension
      ] at hcomponent'
      apply
        (Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toMulEquiv).injective
      rw [hcomponent']
      exact
        ((Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toMulEquiv).apply_symm_apply
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)).symm

/-- The finite-place form of the ordinary idele norm, entirely in
the concrete adic completions.  Thus the component at `v` is the product
of the ordinary field norms of the components at all finite places above
`v`. -/
private theorem finiteComponent_norm_eq_prod_exact_index
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L) :=
      fun w =>
        (finitePlaceAdicCompletionMap K L v
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w)).toAlgebra
    finiteComponent v (norm K L a) =
      ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let eBase :=
    _root_.relativeFinitePlaceCompletionAlgEquiv
      (K := K) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra (v.adicCompletion K)
        ((finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w).1.adicCompletion L) :=
    fun w =>
      (finitePlaceAdicCompletionMap K L v
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w)).toAlgebra
  have hCompatible
      (w : AbsoluteValueExtension vK L) :
      RingHom.comp
          (algebraMap
            (v.adicCompletion K)
            ((finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1.adicCompletion L))
          eBase.toRingEquiv =
        RingHom.comp
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toRingHom
          (algebraMap vK.Completion w.1.Completion) := by
    apply RingHom.ext
    intro x
    change
      finitePlaceAdicCompletionMap K L v
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w)
          (eBase x) =
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (algebraMap vK.Completion w.1.Completion x)
    rw [←
      finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
        K L v w]
    simp [finitePlaceExtensionAdicCompletionMap, eBase, vK]
  have hcompletion :=
    finiteComponent_norm_eq_prod_completion
      (K := K) (L := L) v a
  change
    finiteComponent v (norm K L a) =
      ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)
  calc
    finiteComponent v (norm K L a) =
        Units.mapEquiv eBase.toMulEquiv
          (Units.mapEquiv eBase.symm.toMulEquiv
            (finiteComponent v (norm K L a))) := by
      apply Units.ext
      simp
    _ = Units.mapEquiv eBase.toMulEquiv
        (∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w).symm.toMulEquiv
              (finiteComponent
                (finitePlaceExtensionEquivAbove
                  (K := K) (L := L) v w).1 a))) := by
      exact congrArg (Units.mapEquiv eBase.toMulEquiv) hcompletion
    _ = ∏ w : AbsoluteValueExtension vK L,
        Units.mapEquiv eBase.toMulEquiv
          (Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w).symm.toMulEquiv
              (finiteComponent
                (finitePlaceExtensionEquivAbove
                  (K := K) (L := L) v w).1 a))) := by
      rw [map_prod]
    _ = ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a) := by
      apply Finset.prod_congr rfl
      intro w _
      let W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v} :=
        ⟨finitePlaceExtensionCentre (K := K) (L := L) v w,
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := L) v w⟩
      let : Algebra (v.adicCompletion K)
          ((finitePlaceExtensionCentre
            (K := K) (L := L) v w).adicCompletion L) :=
        (finitePlaceAdicCompletionMap K L v W).toAlgebra
      let eExtension :=
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
      let x : w.1.Completionˣ :=
        Units.mapEquiv eExtension.symm.toMulEquiv
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)
      have hNorm :=
        LocalClassFieldTheory.normUnits_map_ringEquiv
          eBase.toRingEquiv eExtension (hCompatible w) x
      have hx :
          Units.mapEquiv eExtension.toMulEquiv x =
            finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a := by
        exact
          (Units.mapEquiv eExtension.toMulEquiv).apply_symm_apply
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)
      rw [hx] at hNorm
      change
        Units.mapEquiv eBase.toMulEquiv
            (LocalFieldTheory.normUnits
              vK.Completion w.1.Completion x) =
          LocalFieldTheory.normUnits
            (v.adicCompletion K)
            ((finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1.adicCompletion L)
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)
      exact hNorm

/-- The finite-place form of the ordinary idele norm. The
component at `v` is the product of the ordinary field norms of the actual
idele components at the finite places above `v`. -/
theorem finiteComponent_norm_eq_prod
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v},
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K L v W).toAlgebra
    finiteComponent v (norm K L a) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K L v W).toAlgebra
  have hexact :=
    finiteComponent_norm_eq_prod_exact_index
      (K := K) (L := L) v a
  change
    finiteComponent v (norm K L a) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a)
  calc
    finiteComponent v (norm K L a) =
        ∏ w : AbsoluteValueExtension vK L,
          LocalFieldTheory.normUnits
            (v.adicCompletion K)
            ((eAbove w).1.adicCompletion L)
            (finiteComponent (eAbove w).1 a) :=
      by
        simpa only [eAbove, finitePlaceExtensionEquivAbove_coe] using
          hexact
    _ = ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a) := by
      exact
        Fintype.prod_equiv eAbove
          (fun w : AbsoluteValueExtension vK L =>
            LocalFieldTheory.normUnits
              (v.adicCompletion K)
              ((eAbove w).1.adicCompletion L)
              (finiteComponent (eAbove w).1 a))
          (fun W : {W : HeightOneSpectrum (𝓞 L) //
              _root_.finitePlaceBelow (K := K) W = v} =>
            LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L)
              (finiteComponent W.1 a))
          (fun _ => rfl)

/-- The absolute-value-extension-coordinate form underlying the public
archimedean formula below. -/
private theorem infiniteComponent_norm_eq_prod_extensions
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let z :=
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a
    let x :=
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v z
    let x' :=
      _root_.infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v x
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' w) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) v z
  let x' :=
    _root_.infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v x
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' w)
  rw [← hz, norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.infiniteComponent_norm]
  apply Units.ext
  change
    _root_.infinitePlaceCompletionAlgEquiv
        (K := K) v
        (Algebra.norm v.Completion
          (x : v.Completion ⊗[K] L)) =
      (((∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
              vK hvK x' w)) :
          vK.Completionˣ) : vK.Completion)
  calc
    _root_.infinitePlaceCompletionAlgEquiv
        (K := K) v
        (Algebra.norm v.Completion
          (x : v.Completion ⊗[K] L)) =
        Algebra.norm vK.Completion
          (x' : vK.Completion ⊗[K] L) := by
      exact
        map_norm_tensorProduct_baseChange
          (K := K) (L := L)
          (_root_.infinitePlaceCompletionAlgEquiv
            (K := K) v).toAlgHom
          (x : v.Completion ⊗[K] L)
    _ = ∏ w : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK
            (x' : vK.Completion ⊗[K] L) w) := by
      exact
        RelativeIdeleGroup.localNorm_units_eq_prod
          vK hvK x'
    _ =
        (((∏ w : AbsoluteValueExtension vK L,
            Units.map (Algebra.norm vK.Completion)
              (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
                vK hvK x' w)) :
            vK.Completionˣ) : vK.Completion) := by
      change _ = Units.coeHom vK.Completion _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro w _
      rfl

/-- The completion-coordinate form underlying the public archimedean
formula below, already reindexed by concrete infinite places. -/
private theorem infiniteComponent_norm_eq_prod_completion
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let eAbove :=
      _root_.infinitePlaceAboveEquivExtension
        (K := K) (L := L) v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    letI : Fintype {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        W.1.1.LiesOver vK :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        Algebra vK.Completion W.1.1.Completion :=
      fun W =>
        AbsoluteValue.completionAlgebra vK W.1.1
          (eAbove W).2
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        Module.Finite vK.Completion W.1.1.Completion :=
      fun W =>
        completionModuleFinite vK hvK (eAbove W)
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a)) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) v z
  let x' :=
    _root_.infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v x
  let eAbove :=
    _root_.infinitePlaceAboveEquivExtension
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : Fintype {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      W.1.1.LiesOver vK :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Algebra vK.Completion W.1.1.Completion :=
    fun W =>
      AbsoluteValue.completionAlgebra vK W.1.1
        (eAbove W).2
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Module.Finite vK.Completion W.1.1.Completion :=
    fun W =>
      completionModuleFinite vK hvK (eAbove W)
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a))
  calc
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
        ∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
              vK hvK x' w) :=
      infiniteComponent_norm_eq_prod_extensions
        (K := K) (L := L) v a
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' (eAbove W)) := by
      exact
        (eAbove.prod_comp
          (fun w : AbsoluteValueExtension vK L =>
            Units.map (Algebra.norm vK.Completion)
              (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
                vK hvK x' w))).symm
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a)) := by
      apply Finset.prod_congr rfl
      intro W _
      apply congrArg (Units.map (Algebra.norm vK.Completion))
      have hcomponent :=
        congrArg (fun b : IdeleGroup L => infiniteComponent W.1 b) hz
      change
        _root_.infinitePlaceTensorUnitsEquivAbove
            (K := K) (L := L)
            (_root_.infinitePlaceBelow (K := K) W.1)
            ((_root_.relativeIdeleToLocalData
              (K := K) (L := L) z).infinite
              (_root_.infinitePlaceBelow (K := K) W.1))
            ⟨W.1, rfl⟩ =
          infiniteComponent W.1 a at hcomponent
      simp only [_root_.relativeIdeleToLocalData] at hcomponent
      have hcomponentFixed :
          _root_.infinitePlaceTensorUnitsEquivAbove
              (K := K) (L := L) v x W =
            infiniteComponent W.1 a := by
        let W₀ : InfinitePlace L := W.1
        let P : InfinitePlace K → Prop := fun q =>
          ∀ hq : _root_.infinitePlaceBelow (K := K) W₀ = q,
            _root_.infinitePlaceTensorUnitsEquivAbove
                (K := K) (L := L) q
                (RelativeIdeleGroup.infiniteComponent
                  (K := K) (L := L) q z)
                ⟨W₀, hq⟩ =
              infiniteComponent W₀ a
        have hP :
            P (_root_.infinitePlaceBelow (K := K) W₀) := by
          intro hq
          simpa only [P, W₀] using hcomponent
        have hW :
            _root_.infinitePlaceBelow (K := K) W₀ = v :=
          W.2
        have hPv : P v :=
          hW ▸ hP
        simpa only [P, W₀, x] using hPv W.2
      rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
        at hcomponentFixed
      apply
        (Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv).injective
      rw [hcomponentFixed]
      apply Units.ext
      exact
        ((InfinitePlace.Completion.equiv W.1).symm_apply_apply _).symm

/-- The archimedean form of the ordinary idele norm. The component
at `v` is the product of the ordinary field norms of the actual idele
components at the infinite places above `v`. -/
theorem infiniteComponent_norm_eq_prod
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let eAbove :=
      _root_.infinitePlaceAboveEquivExtension
        (K := K) (L := L) v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : Fintype {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv
        (AbsoluteValueExtension vK L) eAbove.symm
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        W.1.1.LiesOver v.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    infiniteComponent v (norm K L a) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let eBase :=
    _root_.infinitePlaceCompletionAlgEquiv
      (K := K) v
  let eAbove :=
    _root_.infinitePlaceAboveEquivExtension
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      W.1.1.LiesOver v.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Algebra vK.Completion W.1.1.Completion :=
    fun W =>
      AbsoluteValue.completionAlgebra vK W.1.1
        (eAbove W).2
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Module.Finite vK.Completion W.1.1.Completion :=
    fun W =>
      completionModuleFinite vK hvK (eAbove W)
  have hcompletion :=
    infiniteComponent_norm_eq_prod_completion
      (K := K) (L := L) v a
  change
    infiniteComponent v (norm K L a) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a)
  calc
    infiniteComponent v (norm K L a) =
        Units.mapEquiv eBase.symm.toMulEquiv
          (Units.mapEquiv eBase.toMulEquiv
            (infiniteComponent v (norm K L a))) := by
      apply Units.ext
      simp
    _ = Units.mapEquiv eBase.symm.toMulEquiv
        (∏ W : {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v},
          Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (InfinitePlace.Completion.equiv W.1).toMulEquiv
              (infiniteComponent W.1 a))) := by
      exact
        congrArg (Units.mapEquiv eBase.symm.toMulEquiv) hcompletion
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.mapEquiv eBase.symm.toMulEquiv
          (Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (InfinitePlace.Completion.equiv W.1).toMulEquiv
              (infiniteComponent W.1 a))) := by
      rw [map_prod]
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a) := by
      apply Finset.prod_congr rfl
      intro W _
      let eExtension :=
        (InfinitePlace.Completion.equiv W.1).symm
      let x : W.1.1.Completionˣ :=
        Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).toMulEquiv
          (infiniteComponent W.1 a)
      have hWrapperCompletion :
          RingHom.comp
              (algebraMap v.1.Completion W.1.1.Completion)
              eBase.toRingEquiv =
            RingHom.comp
              (InfinitePlace.Completion.equiv W.1).toRingHom
              (algebraMap v.Completion W.1.Completion) := by
        have hComparison :=
          _root_.infinitePlaceCompletionAlgEquiv_algebraMap
            (K := K) (L := L) v W.1 W.2
        dsimp only [eBase, infinitePlaceCompletionAlgEquiv] at hComparison ⊢
        exact hComparison
      have hCompatible :=
        LocalClassFieldTheory.ringEquiv_compat_symm
          eBase.toRingEquiv
          (InfinitePlace.Completion.equiv W.1)
          hWrapperCompletion
      have hNorm :=
        LocalClassFieldTheory.normUnits_map_ringEquiv
          eBase.symm.toRingEquiv eExtension hCompatible x
      have hx :
          Units.mapEquiv eExtension.toMulEquiv x =
            infiniteComponent W.1 a := by
        apply Units.ext
        change
          (InfinitePlace.Completion.equiv W.1).symm
              ((InfinitePlace.Completion.equiv W.1)
                (infiniteComponent W.1 a : W.1.Completion)) =
            (infiniteComponent W.1 a : W.1.Completion)
        exact
          (InfinitePlace.Completion.equiv W.1).symm_apply_apply _
      rw [hx] at hNorm
      change
        Units.mapEquiv eBase.symm.toMulEquiv
            (LocalFieldTheory.normUnits
              vK.Completion W.1.1.Completion x) =
          LocalFieldTheory.normUnits
            v.Completion W.1.Completion
            (infiniteComponent W.1 a)
      exact hNorm

end IdeleGroup
