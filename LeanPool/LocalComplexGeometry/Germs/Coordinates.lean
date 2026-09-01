/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinates and pullback for holomorphic germs

This module relates the standard model `Fin (n + 1) → ℂ` to the product model
used by the pinned Weierstrass-preparation dependency.  It also constructs
contravariant pullback homomorphisms on holomorphic germs, the inclusion of
lower-dimensional base germs, and the resulting algebra structure.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-! ## The standard successor-coordinate splitting -/

/-- Split the last coordinate of `ℂⁿ⁺¹`, as a complex-linear equivalence. -/
def wptAmbientLinearEquiv (n : ℕ) :
    ComplexEuclidean (n + 1) ≃ₗ[ℂ] ClassicalComplexWPT.Ambient n where
  toFun x := (fun i ↦ x i.castSucc, x (Fin.last n))
  invFun x := Fin.lastCases x.2 x.1
  left_inv x := by
    funext i
    cases i using Fin.lastCases <;> simp
  right_inv x := by
    ext i <;> simp
  map_add' x y := by
    ext i <;> simp
  map_smul' c x := by
    ext i <;> simp

/-- The continuous complex-linear splitting of the last coordinate of `ℂⁿ⁺¹`.

The codomain is definitionally WPT's `(Fin n → ℂ) × ℂ` ambient space.
-/
def wptAmbientEquiv (n : ℕ) :
    ComplexEuclidean (n + 1) ≃L[ℂ] ClassicalComplexWPT.Ambient n :=
  (wptAmbientLinearEquiv n).toContinuousLinearEquiv

@[simp]
theorem wptAmbientEquiv_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    wptAmbientEquiv n x = (fun i ↦ x i.castSucc, x (Fin.last n)) :=
  rfl

@[simp]
theorem wptAmbientEquiv_symm_apply (n : ℕ)
    (x : ClassicalComplexWPT.Ambient n) :
    (wptAmbientEquiv n).symm x = Fin.lastCases x.2 x.1 :=
  rfl

theorem wptAmbientEquiv_zero (n : ℕ) :
    wptAmbientEquiv n (0 : ComplexEuclidean (n + 1)) = 0 :=
  map_zero (wptAmbientEquiv n)

theorem wptAmbientEquiv_symm_zero (n : ℕ) :
    (wptAmbientEquiv n).symm (0 : ClassicalComplexWPT.Ambient n) = 0 :=
  map_zero (wptAmbientEquiv n).symm

/-- Analyticity at the origin is preserved and reflected by the standard/WPT
ambient-coordinate equivalence. -/
theorem analyticAt_comp_wptAmbientEquiv_iff (n : ℕ)
    (f : ClassicalComplexWPT.Ambient n → ℂ) :
    AnalyticAt ℂ (f ∘ wptAmbientEquiv n) 0 ↔ AnalyticAt ℂ f 0 := by
  constructor
  · intro hf
    have hf' : AnalyticAt ℂ (f ∘ wptAmbientEquiv n)
        ((wptAmbientEquiv n).symm 0) := by
      rw [map_zero]
      exact hf
    have hcomp := hf'.compContinuousLinearMap
      (u := (wptAmbientEquiv n).symm.toContinuousLinearMap) (x := 0)
    simpa [Function.comp_def] using hcomp
  · intro hf
    have hf' : AnalyticAt ℂ f (wptAmbientEquiv n 0) := by
      rw [map_zero]
      exact hf
    simpa using hf'.compContinuousLinearMap
      (u := (wptAmbientEquiv n).toContinuousLinearMap) (x := 0)

/-- Neighborhood equality at the origin is preserved and reflected by the
standard/WPT ambient-coordinate equivalence. -/
theorem eventuallyEq_comp_wptAmbientEquiv_iff (n : ℕ)
    (f g : ClassicalComplexWPT.Ambient n → ℂ) :
    (f ∘ wptAmbientEquiv n) =ᶠ[𝓝 0] (g ∘ wptAmbientEquiv n) ↔
      f =ᶠ[𝓝 0] g := by
  constructor
  · intro h
    have ht : Tendsto (wptAmbientEquiv n).symm (𝓝 0) (𝓝 0) := by
      have ht' : Tendsto (wptAmbientEquiv n).symm (𝓝 0)
          (𝓝 ((wptAmbientEquiv n).symm 0)) :=
        (wptAmbientEquiv n).symm.continuousAt
      rw [map_zero] at ht'
      exact ht'
    simpa [Function.comp_def] using h.comp_tendsto ht
  · intro h
    have ht : Tendsto (wptAmbientEquiv n) (𝓝 0) (𝓝 0) := by
      have ht' : Tendsto (wptAmbientEquiv n) (𝓝 0)
          (𝓝 (wptAmbientEquiv n 0)) :=
        (wptAmbientEquiv n).continuousAt
      rw [map_zero] at ht'
      exact ht'
    exact h.comp_tendsto ht

/-! ## Pullback of function germs and holomorphic germs -/

/-- Precomposition of function germs by a continuous linear map fixing the origin. -/
def functionGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    FunctionGerm m →+* FunctionGerm n where
  toFun φ := φ.compTendsto L (by
    have hL : Tendsto L (𝓝 (0 : ComplexEuclidean n)) (𝓝 (L 0)) :=
      L.continuous.continuousAt
    rw [L.map_zero] at hL
    exact hL)
  map_zero' := rfl
  map_one' := rfl
  map_add' φ ψ := by
    refine Filter.Germ.inductionOn φ ?_
    intro f
    refine Filter.Germ.inductionOn ψ ?_
    intro g
    rfl
  map_mul' φ ψ := by
    refine Filter.Germ.inductionOn φ ?_
    intro f
    refine Filter.Germ.inductionOn ψ ?_
    intro g
    rfl

@[simp]
theorem functionGermPullbackHom_coe {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (f : ComplexEuclidean m → ℂ) :
    functionGermPullbackHom L (f : FunctionGerm m) =
      ((f ∘ L : ComplexEuclidean n → ℂ) : FunctionGerm n) :=
  rfl

@[simp]
theorem functionGermPullbackHom_value {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : FunctionGerm m) :
    Filter.Germ.value (functionGermPullbackHom L φ) = Filter.Germ.value φ := by
  refine Filter.Germ.inductionOn φ ?_
  intro f
  change (f ∘ L) 0 = f 0
  simp only [Function.comp_apply, map_zero]

@[simp]
theorem functionGermPullbackHom_id (n : ℕ) :
    functionGermPullbackHom (ContinuousLinearMap.id ℂ (ComplexEuclidean n)) =
      RingHom.id (FunctionGerm n) := by
  ext φ
  refine Filter.Germ.inductionOn φ ?_
  intro f
  rfl

theorem functionGermPullbackHom_comp {n m k : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k) :
    functionGermPullbackHom (M.comp L) =
      (functionGermPullbackHom L).comp (functionGermPullbackHom M) := by
  ext φ
  refine Filter.Germ.inductionOn φ ?_
  intro f
  rfl

theorem functionGermPullbackHom_leftInverse {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    Function.LeftInverse
      (functionGermPullbackHom
        (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))
      (functionGermPullbackHom
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) := by
  intro φ
  change ((functionGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)).comp
    (functionGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m))) φ = φ
  rw [← DFunLike.congr_fun (functionGermPullbackHom_comp
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) φ]
  have hcomp :
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m).comp
          (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n) =
        ContinuousLinearMap.id ℂ (ComplexEuclidean m) := by
    apply ContinuousLinearMap.ext
    intro x
    exact L.apply_symm_apply x
  rw [hcomp, DFunLike.congr_fun (functionGermPullbackHom_id m) φ]
  rfl

theorem functionGermPullbackHom_rightInverse {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    Function.RightInverse
      (functionGermPullbackHom
        (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))
      (functionGermPullbackHom
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) := by
  intro φ
  change ((functionGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).comp
    (functionGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))) φ = φ
  rw [← DFunLike.congr_fun (functionGermPullbackHom_comp
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)) φ]
  have hcomp :
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n).comp
          (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) =
        ContinuousLinearMap.id ℂ (ComplexEuclidean n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact L.symm_apply_apply x
  rw [hcomp, DFunLike.congr_fun (functionGermPullbackHom_id n) φ]
  rfl

/-- Pullback of holomorphic germs by a continuous complex-linear map. -/
def holomorphicGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    HolomorphicGerm m →+* HolomorphicGerm n where
  toFun φ :=
    ⟨functionGermPullbackHom L φ.1, by
      obtain ⟨f, hf, hφ⟩ := φ.property
      refine ⟨f ∘ L, ?_, ?_⟩
      · have hf' : AnalyticAt ℂ f (L 0) := by simpa using hf
        simpa using hf'.compContinuousLinearMap (u := L) (x := 0)
      · rw [← hφ]
        rfl⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (functionGermPullbackHom L)
  map_one' := by
    apply Subtype.ext
    exact map_one (functionGermPullbackHom L)
  map_add' φ ψ := by
    apply Subtype.ext
    exact map_add (functionGermPullbackHom L) φ.1 ψ.1
  map_mul' φ ψ := by
    apply Subtype.ext
    exact map_mul (functionGermPullbackHom L) φ.1 ψ.1

@[simp]
theorem holomorphicGermPullbackHom_coe {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    ((holomorphicGermPullbackHom L φ : HolomorphicGerm n) : FunctionGerm n) =
      functionGermPullbackHom L (φ : FunctionGerm m) :=
  rfl

@[simp]
theorem holomorphicGermPullbackHom_ofFunction {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (f : ComplexEuclidean m → ℂ) (hf : AnalyticAt ℂ f 0) :
    holomorphicGermPullbackHom L (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ L)
        (by
          have hf' : AnalyticAt ℂ f (L 0) := by simpa using hf
          simpa using hf'.compContinuousLinearMap (u := L) (x := 0)) := by
  apply Subtype.ext
  rfl

@[simp]
theorem evalAtOrigin_holomorphicGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    evalAtOrigin (holomorphicGermPullbackHom L φ) = evalAtOrigin φ := by
  exact functionGermPullbackHom_value L (φ : FunctionGerm m)

@[simp]
theorem holomorphicGermPullbackHom_id (n : ℕ) :
    holomorphicGermPullbackHom (ContinuousLinearMap.id ℂ (ComplexEuclidean n)) =
      RingHom.id (HolomorphicGerm n) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_id n) φ.1

theorem holomorphicGermPullbackHom_comp {n m k : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k) :
    holomorphicGermPullbackHom (M.comp L) =
      (holomorphicGermPullbackHom L).comp (holomorphicGermPullbackHom M) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_comp L M) φ.1

/-- Pullback by a continuous complex-linear equivalence, as a ring equivalence.

The direction is contravariant: an equivalence `L : ℂⁿ ≃L[ℂ] ℂᵐ` induces an
equivalence from germs on `ℂᵐ` to germs on `ℂⁿ`.
-/
def coordinatePullback {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    HolomorphicGerm m ≃+* HolomorphicGerm n where
  toFun := holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
  invFun := holomorphicGermPullbackHom
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)
  left_inv φ := by
    apply Subtype.ext
    exact functionGermPullbackHom_leftInverse L (φ : FunctionGerm m)
  right_inv φ := by
    apply Subtype.ext
    exact functionGermPullbackHom_rightInverse L (φ : FunctionGerm n)
  map_add' φ ψ := (holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).map_add φ ψ
  map_mul' φ ψ := (holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).map_mul φ ψ

@[simp]
theorem coordinatePullback_apply {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    coordinatePullback L φ = holomorphicGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) φ :=
  rfl

@[simp]
theorem coordinatePullback_symm_apply {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm n) :
    (coordinatePullback L).symm φ = holomorphicGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n) φ :=
  rfl

theorem evalAtOrigin_coordinatePullback {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    evalAtOrigin (coordinatePullback L φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) φ

@[simp]
theorem coordinatePullback_refl (n : ℕ) :
    coordinatePullback (ContinuousLinearEquiv.refl ℂ (ComplexEuclidean n)) =
      RingEquiv.refl (HolomorphicGerm n) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_id n) φ.1

theorem coordinatePullback_trans {n m k : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m ≃L[ℂ] ComplexEuclidean k) :
    coordinatePullback (L.trans M) =
      (coordinatePullback M).trans (coordinatePullback L) := by
  ext φ
  exact DFunLike.congr_fun
    (functionGermPullbackHom_comp (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
      (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k)) φ.1

@[simp]
theorem coordinatePullback_symm {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    coordinatePullback L.symm = (coordinatePullback L).symm := by
  ext φ
  rfl

/-! ## Base inclusion and the last coordinate -/

/-- Projection from `ℂⁿ⁺¹` to its first `n` coordinates. -/
def baseProjectionCLM (n : ℕ) :
    ComplexEuclidean (n + 1) →L[ℂ] ComplexEuclidean n :=
  (ContinuousLinearMap.fst ℂ (ComplexEuclidean n) ℂ).comp
    (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
      ClassicalComplexWPT.Ambient n)

@[simp]
theorem baseProjectionCLM_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    baseProjectionCLM n x = fun i ↦ x i.castSucc :=
  rfl

/-- The zero-last-coordinate section `z ↦ (z, 0)` in the standard model. -/
def baseSectionCLM (n : ℕ) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean (n + 1) :=
  (wptAmbientEquiv n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexEuclidean n) ℂ)

@[simp]
theorem baseSectionCLM_castSucc (n : ℕ) (z : ComplexEuclidean n) (i : Fin n) :
    baseSectionCLM n z i.castSucc = z i := by
  simp [baseSectionCLM]

@[simp]
theorem baseSectionCLM_last (n : ℕ) (z : ComplexEuclidean n) :
    baseSectionCLM n z (Fin.last n) = 0 := by
  simp [baseSectionCLM]

/-- Extraction of the last coordinate of `ℂⁿ⁺¹`. -/
def lastCoordinateCLM (n : ℕ) : ComplexEuclidean (n + 1) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (ComplexEuclidean n) ℂ).comp
    (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
      ClassicalComplexWPT.Ambient n)

@[simp]
theorem lastCoordinateCLM_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    lastCoordinateCLM n x = x (Fin.last n) :=
  rfl

@[simp]
theorem baseProjectionCLM_comp_baseSectionCLM (n : ℕ) :
    (baseProjectionCLM n).comp (baseSectionCLM n) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean n) := by
  apply ContinuousLinearMap.ext
  intro z
  funext i
  simp

/-- Include a base germ as a germ independent of the last coordinate. -/
def lowerDimensionalInclusion (n : ℕ) :
    HolomorphicGerm n →+* HolomorphicGerm (n + 1) :=
  holomorphicGermPullbackHom (baseProjectionCLM n)

/-- Restrict an ambient germ to the zero-last-coordinate base section. -/
def lowerDimensionalRestriction (n : ℕ) :
    HolomorphicGerm (n + 1) →+* HolomorphicGerm n :=
  holomorphicGermPullbackHom (baseSectionCLM n)

@[simp]
theorem lowerDimensionalInclusion_ofFunction {n : ℕ}
    (f : ComplexEuclidean n → ℂ) (hf : AnalyticAt ℂ f 0) :
    lowerDimensionalInclusion n (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ baseProjectionCLM n)
        (by
          have hf' : AnalyticAt ℂ f (baseProjectionCLM n 0) := by
            rw [map_zero]
            exact hf
          simpa using hf'.compContinuousLinearMap
            (u := baseProjectionCLM n) (x := 0)) :=
  holomorphicGermPullbackHom_ofFunction (baseProjectionCLM n) f hf

@[simp]
theorem lowerDimensionalRestriction_ofFunction {n : ℕ}
    (f : ComplexEuclidean (n + 1) → ℂ) (hf : AnalyticAt ℂ f 0) :
    lowerDimensionalRestriction n (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ baseSectionCLM n)
        (by
          have hf' : AnalyticAt ℂ f (baseSectionCLM n 0) := by
            rw [map_zero]
            exact hf
          simpa using hf'.compContinuousLinearMap
            (u := baseSectionCLM n) (x := 0)) :=
  holomorphicGermPullbackHom_ofFunction (baseSectionCLM n) f hf

@[simp]
theorem evalAtOrigin_lowerDimensionalInclusion {n : ℕ}
    (φ : HolomorphicGerm n) :
    evalAtOrigin (lowerDimensionalInclusion n φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom (baseProjectionCLM n) φ

@[simp]
theorem evalAtOrigin_lowerDimensionalRestriction {n : ℕ}
    (φ : HolomorphicGerm (n + 1)) :
    evalAtOrigin (lowerDimensionalRestriction n φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom (baseSectionCLM n) φ

@[simp]
theorem lowerDimensionalRestriction_comp_inclusion (n : ℕ) :
    (lowerDimensionalRestriction n).comp (lowerDimensionalInclusion n) =
      RingHom.id (HolomorphicGerm n) := by
  unfold lowerDimensionalRestriction lowerDimensionalInclusion
  rw [← holomorphicGermPullbackHom_comp,
    baseProjectionCLM_comp_baseSectionCLM, holomorphicGermPullbackHom_id]

theorem lowerDimensionalInclusion_injective (n : ℕ) :
    Function.Injective (lowerDimensionalInclusion n) := by
  apply Function.LeftInverse.injective (g := lowerDimensionalRestriction n)
  intro φ
  change ((lowerDimensionalRestriction n).comp
    (lowerDimensionalInclusion n)) φ = φ
  rw [lowerDimensionalRestriction_comp_inclusion]
  rfl

/-- The germ of the last coordinate `w` on `ℂⁿ⁺¹`. -/
def lastCoordinateGerm (n : ℕ) : HolomorphicGerm (n + 1) :=
  HolomorphicGerm.ofFunction (lastCoordinateCLM n)
    ((lastCoordinateCLM n).analyticAt 0)

@[simp]
theorem evalAtOrigin_lastCoordinateGerm (n : ℕ) :
    evalAtOrigin (lastCoordinateGerm n) = 0 := by
  simp [lastCoordinateGerm]

@[simp]
theorem lowerDimensionalRestriction_lastCoordinateGerm (n : ℕ) :
    lowerDimensionalRestriction n (lastCoordinateGerm n) = 0 := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp

/-! ## The ambient germ ring as an algebra over the base germ ring -/

/-- The natural algebra structure induced by germs independent of the last coordinate. -/
instance holomorphicGermSuccAlgebra (n : ℕ) :
    Algebra (HolomorphicGerm n) (HolomorphicGerm (n + 1)) :=
  (lowerDimensionalInclusion n).toAlgebra

@[simp]
theorem algebraMap_holomorphicGermSucc (n : ℕ) :
    algebraMap (HolomorphicGerm n) (HolomorphicGerm (n + 1)) =
      lowerDimensionalInclusion n :=
  rfl

@[simp]
theorem algebraMap_holomorphicGermSucc_apply (n : ℕ) (φ : HolomorphicGerm n) :
    algebraMap (HolomorphicGerm n) (HolomorphicGerm (n + 1)) φ =
      lowerDimensionalInclusion n φ :=
  rfl

theorem holomorphicGermSucc_smul_eq_mul (n : ℕ)
    (a : HolomorphicGerm n) (f : HolomorphicGerm (n + 1)) :
    a • f = lowerDimensionalInclusion n a * f :=
  rfl

end

end LocalComplexGeometry
