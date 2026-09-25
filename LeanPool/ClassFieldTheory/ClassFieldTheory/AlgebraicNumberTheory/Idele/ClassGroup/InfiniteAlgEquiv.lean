/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv
/-!
# Infinite completions under a number-field equivalence

The completion maps along an isomorphism of number fields are mutually
inverse. This is the archimedean local input for the topology of `adeleCongr`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- The map between the completions at corresponding infinite places. -/
noncomputable def infinitePlaceCompletionCongrHom
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion →+*
      W.Completion := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  exact NumberField.LiesOver.completionMap (v := w) (w := W)

/-- The archimedean completion map is continuous. -/
theorem infinitePlaceCompletionCongrHom_continuous
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    Continuous (infinitePlaceCompletionCongrHom e W) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  change Continuous (NumberField.LiesOver.completionMap (v := w) (w := W))
  exact NumberField.LiesOver.continuous_completionMap

/-- Transport along a field isomorphism is an equivalence of the
corresponding infinite-place completions. -/
noncomputable def infinitePlaceCompletionCongrEquiv
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion ≃+*
      W.Completion := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : Algebra M K := e.symm.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  have hMK : infinitePlaceBelow (K := M) w = W := by
    change (W.comap e.toRingHom).comap e.symm.toRingHom = W
    exact (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).right_inv W
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  let : w.1.LiesOver W.1 :=
    ⟨congrArg (fun v : InfinitePlace M => v.1) hMK⟩
  let f : w.Completion →+* W.Completion :=
    NumberField.LiesOver.completionMap (v := w) (w := W)
  let g : W.Completion →+* w.Completion :=
    NumberField.LiesOver.completionMap (v := W) (w := w)
  exact RingEquiv.ofRingHom f g
    (by
      apply RingHom.ext
      intro x
      change f (g x) = x
      refine InfinitePlace.Completion.induction_on W x ?_ ?_
      · exact isClosed_eq
          (NumberField.LiesOver.continuous_completionMap.comp
            NumberField.LiesOver.continuous_completionMap)
          continuous_id
      · intro y
        dsimp only [f, g]
        rw [NumberField.LiesOver.completionMap_coe
            (v := W) (w := w) y,
          NumberField.LiesOver.completionMap_coe
            (v := w) (w := W)
            (algebraMap (WithAbs W.1) (WithAbs w.1) y)]
        apply congrArg (fun z : WithAbs W.1 => (z : W.Completion))
        apply (WithAbs.equiv W.1).injective
        change e (e.symm (WithAbs.equiv W.1 y)) =
          WithAbs.equiv W.1 y
        exact e.apply_symm_apply _)
    (by
      apply RingHom.ext
      intro x
      change g (f x) = x
      refine InfinitePlace.Completion.induction_on w x ?_ ?_
      · exact isClosed_eq
          (NumberField.LiesOver.continuous_completionMap.comp
            NumberField.LiesOver.continuous_completionMap)
          continuous_id
      · intro y
        dsimp only [f, g]
        rw [NumberField.LiesOver.completionMap_coe
            (v := w) (w := W) y,
          NumberField.LiesOver.completionMap_coe
            (v := W) (w := w)
            (algebraMap (WithAbs w.1) (WithAbs W.1) y)]
        apply congrArg (fun z : WithAbs w.1 => (z : w.Completion))
        apply (WithAbs.equiv w.1).injective
        change e.symm (e (WithAbs.equiv w.1 y)) =
          WithAbs.equiv w.1 y
        exact e.symm_apply_apply _)

/-- The completion map agrees with the number-field equivalence on
elements of the number field. -/
theorem infinitePlaceCompletionCongrHom_algebraMap
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) (x : K) :
    infinitePlaceCompletionCongrHom e W
        (algebraMap K
          ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion x) =
      algebraMap M W.Completion (e x) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  change NumberField.LiesOver.completionMap
      (v := w) (w := W)
      ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion) =
    algebraMap M W.Completion (e x)
  rw [NumberField.LiesOver.completionMap_coe]
  apply InfinitePlace.Completion.ext
  rw [InfinitePlace.Completion.algebraMap_toCompletion,
    UniformSpace.Completion.algebraMap_def]
  simp [WithAbs.algebraMap_left_apply,
    WithAbs.algebraMap_right_apply]
  rfl

/-- On infinite coordinates, `adeleCongr` is the completion map at the
corresponding infinite place. -/
theorem adeleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : InfinitePlace M) :
    (adeleCongr e a).1 W =
      infinitePlaceCompletionCongrHom e W
        (a.1 ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W)) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : IsScalarTower ℚ K M :=
    IsScalarTower.of_algHom e.toAlgHom
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  let componentK : NumberField.AdeleRing (𝓞 K) K →+* w.Completion :=
    (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing K)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  let componentM : NumberField.AdeleRing (𝓞 M) M →+* W.Completion :=
    (Pi.evalRingHom (fun v : InfinitePlace M => v.Completion) W).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing M)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 M) M))
  change componentM (adeleCongr e a) =
    infinitePlaceCompletionCongrHom e W (componentK a)
  have hW : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  have hq : infinitePlaceBelow (K := ℚ) w =
      infinitePlaceBelow (K := ℚ) W := by
    rw [← hW, infinitePlaceBelow_infinitePlaceBelow]
  let z := (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)).symm a
  have ha : relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)).apply_symm_apply a
  rw [← ha]
  have htransport :
      componentM (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z)) =
      componentM (adeleCongr e
        (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K) z)) :=
    congrArg componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr e z)
  rw [← htransport]
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      let v := infinitePlaceBelow (K := ℚ) W
      let : W.1.LiesOver
          (infinitePlaceBelow (K := ℚ) W).1 := ⟨rfl⟩
      let : w.1.LiesOver
          (infinitePlaceBelow (K := ℚ) w).1 := ⟨rfl⟩
      let : W.1.LiesOver w.1 :=
        ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
      have hcomponent
          (v' : InfinitePlace ℚ) (hv' : v' = v)
          [hWv : W.1.LiesOver v.1]
          [hwv' : w.1.LiesOver v'.1]
          [hWw : W.1.LiesOver w.1] :
          NumberField.LiesOver.completionMap
              (v := v) (w := W) (b.1 v) =
            NumberField.LiesOver.completionMap
              (v := w) (w := W)
              (NumberField.LiesOver.completionMap
                (v := v') (w := w) (b.1 v')) := by
        subst v'
        exact (infinitePlaceCompletionMap_comp_apply
          (K := ℚ) (M := K) (L := M) W (b.1 v)).symm
      change
        (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := M)
          (relativeAdeleCongr (K := ℚ) e (b ⊗ₜ[ℚ] x))).1 W =
        infinitePlaceCompletionCongrHom e W
          ((relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)
            (b ⊗ₜ[ℚ] x)).1 w)
      rw [relativeAdeleCongr_tmul,
        relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul,
        relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
      rw [map_mul, infinitePlaceCompletionCongrHom_algebraMap]
      exact congrArg₂ (· * ·)
        (hcomponent (infinitePlaceBelow (K := ℚ) w) hq
          (hWv := ⟨rfl⟩) (hwv' := ⟨rfl⟩)
          (hWw := ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩))
        rfl

end
