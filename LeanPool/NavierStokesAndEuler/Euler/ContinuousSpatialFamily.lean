/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffTaylor
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathComposition

@[expose] public section

/-!
# Actual spatial derivatives in the uniform norm on continuous paths

A family of continuous paths whose pointwise spatial derivatives are actual
continuous paths, with uniform bounds, is smooth in the uniform path norm.
The proof uses a quadratic Taylor remainder and loses no derivative-bound
constant. No uniform-path differentiability is assumed.
-/

noncomputable section

namespace EulerContinuousSpatialFamily

open ContinuousLinearMap EulerSmoothLimit Filter
open scoped ContDiff Topology

universe u v

section Bundling

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(K,V) := inferInstance
private local instance : NormedSpace ℝ C(K,V) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] C(K,V)) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] C(K,V)) := inferInstance

def direction (D : C(K,Space →L[ℝ] V)) (a : Space) : C(K,V) :=
  ⟨fun t => D t a, D.continuous.clm_apply continuous_const⟩

theorem direction_norm_le (D : C(K,Space →L[ℝ] V)) (a : Space) :
    ‖direction D a‖ ≤ ‖D‖*‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg a))).2
  intro t
  exact ((D t).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm t) (norm_nonneg a))

def derivativeLinear (D : C(K,Space →L[ℝ] V)) : Space →ₗ[ℝ] C(K,V) where
  toFun := direction D
  map_add' a b := by ext t; exact (D t).map_add a b
  map_smul' c a := by ext t; exact (D t).map_smul c a

def derivativeMap (D : C(K,Space →L[ℝ] V)) : Space →L[ℝ] C(K,V) where
  toLinearMap := derivativeLinear D
  cont := AddMonoidHomClass.continuous_of_bound (derivativeLinear D) ‖D‖
    (direction_norm_le D)

@[simp] theorem derivativeMap_apply (D : C(K,Space →L[ℝ] V)) (a : Space) (t : K) :
    derivativeMap D a t = D t a := rfl

theorem derivativeMap_norm_le (D : C(K,Space →L[ℝ] V)) : ‖derivativeMap D‖ ≤ ‖D‖ :=
  (derivativeMap D).opNorm_le_bound (norm_nonneg D) (direction_norm_le D)

def derivativeBundlingLinear : C(K,Space →L[ℝ] V) →ₗ[ℝ] (Space →L[ℝ] C(K,V)) where
  toFun := derivativeMap
  map_add' D E := by ext a t; rfl
  map_smul' c D := by ext a t; rfl

def derivativeBundling : C(K,Space →L[ℝ] V) →L[ℝ] (Space →L[ℝ] C(K,V)) where
  toLinearMap := derivativeBundlingLinear
  cont := AddMonoidHomClass.continuous_of_bound (derivativeBundlingLinear (K := K) (V := V)) 1
    (fun D => by
      change ‖derivativeMap D‖ ≤ 1*‖D‖
      simpa only [one_mul] using derivativeMap_norm_le D)

theorem derivativeBundling_norm_le_one : ‖derivativeBundling (K := K) (V := V)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro D
  change ‖derivativeMap D‖ ≤ 1*‖D‖
  simpa only [one_mul] using derivativeMap_norm_le D

end Bundling

/-- Actual continuous spatial derivative paths and finite uniform bounds.
The `jet_eq` field identifies every supplied jet with the ordinary derivative. -/
structure SpatialFamily (K : Type u) [TopologicalSpace K] [CompactSpace K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : Space → C(K,V)
  smooth : ∀ t, ContDiff ℝ ∞ (fun a => field a t)
  jet : (n : ℕ) → Space → C(K,Space [×n]→L[ℝ] V)
  jet_eq : ∀ n a t, jet n a t = iteratedFDeriv ℝ n (fun b => field b t) a
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bounded : ∀ n a t, ‖iteratedFDeriv ℝ n (fun b => field b t) a‖ ≤ bound n

namespace SpatialFamily

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(K,V) := inferInstance
private local instance : NormedSpace ℝ C(K,V) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] C(K,V)) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] C(K,V)) := inferInstance

def derivativeField (A : SpatialFamily K V) (a : Space) : C(K,Space →L[ℝ] V) :=
  (continuousMultilinearCurryFin1 ℝ Space
    V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ K
    (A.jet 1 a)

theorem derivativeField_eq (A : SpatialFamily K V) (a : Space) (t : K) :
    A.derivativeField a t = fderiv ℝ (fun b => A.field b t) a := by
  change continuousMultilinearCurryFin1 ℝ Space V (A.jet 1 a t) = _
  rw [A.jet_eq]
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp

def derivativeJet (A : SpatialFamily K V) (n : ℕ) (a : Space) :
    C(K,Space [×n]→L[ℝ] (Space →L[ℝ] V)) :=
  (continuousMultilinearCurryRightEquiv' ℝ n Space
    V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ K
    (A.jet (n+1) a)

theorem derivativeJet_eq (A : SpatialFamily K V) (n : ℕ) (a : Space) (t : K) :
    A.derivativeJet n a t = iteratedFDeriv ℝ n (fderiv ℝ (fun b => A.field b t)) a := by
  change continuousMultilinearCurryRightEquiv' ℝ n Space V (A.jet (n+1) a t) = _
  rw [A.jet_eq, iteratedFDeriv_succ_eq_comp_right]
  exact (continuousMultilinearCurryRightEquiv' ℝ n Space V).apply_symm_apply _

def derivative (A : SpatialFamily K V) : SpatialFamily K (Space →L[ℝ] V) where
  field := A.derivativeField
  smooth t := by
    have he : (fun a => A.derivativeField a t) = fderiv ℝ (fun a => A.field a t) :=
      funext (fun a => A.derivativeField_eq a t)
    rw [he]
    exact (A.smooth t).fderiv_right (m := ∞) (by simp)
  jet := A.derivativeJet
  jet_eq n a t := by
    have he : (fun b => A.derivativeField b t) = fderiv ℝ (fun b => A.field b t) :=
      funext (fun b => A.derivativeField_eq b t)
    rw [he]
    exact A.derivativeJet_eq n a t
  bound n := A.bound (n+1)
  bound_nonneg n := A.bound_nonneg (n+1)
  bounded n a t := by
    have he : (fun b => A.derivativeField b t) = fderiv ℝ (fun b => A.field b t) :=
      funext (fun b => A.derivativeField_eq b t)
    rw [he, norm_iteratedFDeriv_fderiv]
    exact A.bounded (n+1) a t

@[simp] theorem derivative_bound (A : SpatialFamily K V) (n : ℕ) :
    A.derivative.bound n = A.bound (n+1) := rfl

theorem taylor_bound (A : SpatialFamily K V) (a b : Space) :
    ‖A.field b-A.field a-derivativeMap (A.derivative.field a) (b-a)‖ ≤
      A.bound 2*‖b-a‖^2 := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (A.bound_nonneg 2) (sq_nonneg _))).2
  intro t
  change ‖A.field b t-A.field a t-A.derivativeField a t (b-a)‖ ≤ _
  rw [A.derivativeField_eq]
  have hD (x : Space) : ‖fderiv ℝ (fderiv ℝ (fun y => A.field y t)) x‖ ≤ A.bound 2 := by
    simpa only [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] using A.bounded 2 x t
  have h := EulerMeanBoundary.norm_linearization_remainder_le
    (fun x => A.field x t) (A.smooth t) (A.bound 2) (A.bound_nonneg 2) hD a (b-a)
  simpa only [add_sub_cancel] using h

/-- Genuine differentiability in the uniform path norm, from the pointwise Taylor estimate. -/
theorem hasFDerivAt_field (A : SpatialFamily K V) (a : Space) :
    HasFDerivAt A.field (derivativeMap (A.derivative.field a)) a := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun b => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun b : Space => A.bound 2*‖b-a‖)
  · intro b
    calc
      _ ≤ ‖b-a‖⁻¹*(A.bound 2*‖b-a‖^2) := mul_le_mul_of_nonneg_left
        (A.taylor_bound a b) (inv_nonneg.mpr (norm_nonneg _))
      _ = A.bound 2*‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => A.bound 2*‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a

theorem fderiv_field (A : SpatialFamily K V) :
    fderiv ℝ A.field = fun a => derivativeBundling (A.derivative.field a) :=
  funext (fun a => (A.hasFDerivAt_field a).fderiv)

private theorem contDiff_field_aux (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SpatialFamily K V),
      ContDiff ℝ n A.field := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun a => (A.hasFDerivAt_field a).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.hasFDerivAt_field a).differentiableAt, by simp, ?_⟩
    rw [A.fderiv_field]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := C(K,Space →L[ℝ] V)) (F := Space →L[ℝ] C(K,V))
      (derivativeBundling (K := K) (V := V))).comp (ih (Space →L[ℝ] V) A.derivative)

/-- All ordinary pointwise derivatives produce genuine uniform-path smoothness. -/
theorem contDiff_field (A : SpatialFamily K V) : ContDiff ℝ ∞ A.field :=
  contDiff_infty.mpr (fun n => contDiff_field_aux n V A)

private theorem norm_iteratedFDeriv_field_aux (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SpatialFamily K V) (a : Space),
      ‖iteratedFDeriv ℝ n A.field a‖ ≤ A.bound n := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero]
    apply (ContinuousMap.norm_le _ (A.bound_nonneg 0)).2
    intro t
    simpa only [norm_iteratedFDeriv_zero] using A.bounded 0 a t
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.fderiv_field]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := C(K,Space →L[ℝ] V)) (G := Space →L[ℝ] C(K,V))
      (derivativeBundling (K := K) (V := V))
      (A.derivative.contDiff_field.contDiffAt (x := a)) (n := n) (by simp)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (K := K) (V := V)) (norm_nonneg _)).trans
      (by simpa only [one_mul, derivative_bound] using ih (Space →L[ℝ] V) A.derivative a))

/-- The original pointwise uniform derivative bound holds without any additional factor. -/
theorem norm_iteratedFDeriv_field_le (A : SpatialFamily K V) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n A.field a‖ ≤ A.bound n :=
  norm_iteratedFDeriv_field_aux n V A a

end SpatialFamily

end EulerContinuousSpatialFamily
