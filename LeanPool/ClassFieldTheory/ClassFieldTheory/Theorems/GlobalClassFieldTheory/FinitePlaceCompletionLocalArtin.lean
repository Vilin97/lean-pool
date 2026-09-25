/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# A local Artin map on the actual extension completion

The finite-place local Artin construction is made on an algebraic
localization inside a completion. In finite degree that localization is the
whole completion. This theorem transports the independent local Artin map
to the actual completion and records its image and kernel in public types.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

open GlobalClassFieldTheory.Reciprocity renaming
  chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm →
    chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm in
/-- At a finite place of an abelian number-field extension, one can choose
an extension absolute value and a surjective local Artin map on its actual
completion. Its kernel is precisely the determinant-norm image of the local
tensor algebra. This map is constructed from local reciprocity, independently
of any ray-class Artin map. -/
theorem exists_finitePlaceCompletionLocalArtin
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    ∃ (w : ExtendingAbsoluteValue vK L)
      (halg : Algebra vK.Completion w.1.Completion),
      letI := halg
      ∃ localArtin : (v.adicCompletion K)ˣ →*
          (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion),
        Continuous localArtin ∧ Function.Surjective localArtin ∧
          localArtin.ker = finitePlaceTensorNormSubgroup K L v := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let w : ExtendingAbsoluteValue vK L :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let halg : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Algebra vK.Completion w.1.Completion := halg
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w
  let eC : E ≃ₐ[vK.Completion] w.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion vK hvK w
  let eAut : (E ≃ₐ[vK.Completion] E) ≃*
      (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) :=
    AlgEquiv.autCongr eC
  let localE : (v.adicCompletion K)ˣ →* (E ≃ₐ[vK.Completion] E) :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinMonoidHom v w
  let localArtin : (v.adicCompletion K)ˣ →*
      (w.1.Completion ≃ₐ[vK.Completion] w.1.Completion) :=
    eAut.toMonoidHom.comp localE
  let eD : HilbertRamification.absoluteValueDecompositionGroup K w.1 ≃*
      (E ≃ₐ[vK.Completion] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  have hfactor (x : (v.adicCompletion K)ˣ) :
      GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x =
        (HilbertRamification.absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localE x)) := by
    change GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x = _
    rw [GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor,
      MonoidHom.comp_apply]
    rfl
  have hLocalESurj : Function.Surjective localE := by
    intro τ
    let δ := eD.symm τ
    have hδ : (δ : L ≃ₐ[K] L) ∈
        (GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range := by
      rw [GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_range]
      exact δ.property
    obtain ⟨x, hx⟩ := hδ
    refine ⟨x, ?_⟩
    have hxD : eD.symm (localE x) = δ := by
      apply Subtype.coe_injective
      calc
        ((eD.symm (localE x) :
            HilbertRamification.absoluteValueDecompositionGroup K w.1) :
          L ≃ₐ[K] L) =
            GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v x := (hfactor x).symm
        _ = (δ : L ≃ₐ[K] L) := hx
    change eD.symm (localE x) = eD.symm τ at hxD
    exact eD.symm.injective hxD
  have hLocalKer : localArtin.ker = finitePlaceTensorNormSubgroup K L v := by
    apply SetLike.ext
    intro x
    change localArtin x = 1 ↔ x ∈ finitePlaceTensorNormSubgroup K L v
    have hTransport : localArtin x = 1 ↔ localE x = 1 := by
      constructor
      · intro hx
        apply eAut.injective
        change eAut (localE x) = 1 at hx
        simpa only [map_one] using hx
      · intro hx
        change eAut (localE x) = 1
        rw [hx, map_one]
    have hGlobal : localE x = 1 ↔
        GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x = 1 := by
      constructor
      · intro hx
        rw [hfactor x, hx, map_one, map_one]
      · intro hx
        rw [hfactor x] at hx
        have hxD : eD.symm (localE x) = 1 := by
          apply Subtype.coe_injective
          exact hx
        apply eD.symm.injective
        simpa only [map_one] using hxD
    calc
      localArtin x = 1 ↔ localE x = 1 := hTransport
      _ ↔ GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v x = 1 := hGlobal
      _ ↔ x ∈ _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v :=
        chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
          v x
      _ ↔ x ∈ finitePlaceTensorNormSubgroup K L v := by
        rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
          (K := K) (L := L) v]
        rfl
  have hLocalKerOpen : IsOpen (localArtin.ker : Set (v.adicCompletion K)ˣ) := by
    rw [hLocalKer]
    change IsOpen ((_root_.localTensorNorm (K := K) (L := L) v).range :
      Set (v.adicCompletion K)ˣ)
    rw [finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v]
    exact _root_.chosenFinitePlaceLocalNormSubgroup_isOpen
      (K := K) (L := L) v
  have hLocalContinuous : Continuous localArtin := by
    apply continuous_of_continuousAt_one localArtin
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hLocalKerOpen.mem_nhds (by simp)] with x hx
    change localArtin x = 1 at hx
    simpa only [map_one] using hx
  exact ⟨w, halg, localArtin, hLocalContinuous,
    eAut.surjective.comp hLocalESurj, hLocalKer⟩

end ClassFieldTheory
