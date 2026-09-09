/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus

@[expose] public section

/-!
# Smooth substitution of a continuous path into a smooth coefficient field

The derivative is the actual pointwise derivative multiplier.  A uniform
second-derivative remainder proves Fréchet differentiability in the path
sup norm, and iteration gives smoothness at every order.
-/

noncomputable section


open scoped ContDiff BoundedContinuousFunction Topology

namespace SmoothTimeField

open EulerContinuousTimeIntegral EulerContinuousPathCalculus

universe u

variable {K E : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup C(K, E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ C(K, E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

omit [TopologicalSpace K] [CompactSpace K] in
private theorem quadratic_taylor_bound
    (f : E → V) (hf : ContDiff ℝ ∞ f) (M : ℝ) (hM : 0 ≤ M)
    (hD₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (x v : E) :
    ‖f (x+v) - f x - fderiv ℝ f x v‖ ≤ M * ‖v‖ ^ 2 := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hdifference (y : E) : ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * ‖y-x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (s := Set.univ) (fun z _ => hdf z) (fun z _ => hD₂ z)
      (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ y)
  have hbound (y : E) (hy : y ∈ Metric.closedBall x ‖v‖) :
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * ‖v‖ := by
    exact (hdifference y).trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,
      dist_eq_norm] using hy) hM)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (𝕜 := ℝ) (f := f) (s := Metric.closedBall x ‖v‖) (C := M * ‖v‖)
    (φ := fderiv ℝ f x) (x := x) (y := x+v)
    (fun y _ => (hf.differentiable (by simp)) y) hbound (convex_closedBall x ‖v‖)
    (by simp) (by simp [dist_eq_norm])
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using H

def superposition (A : SmoothTimeField K E V) (u : C(K, E)) : C(K,V) where
  toFun t := A.field t (u t)
  continuous_toFun := by fun_prop

@[simp] theorem superposition_apply (A : SmoothTimeField K E V)
    (u : C(K,E)) (t : K) : A.superposition u t = A.field t (u t) := rfl

def superpositionDerivative (A : SmoothTimeField K E V) (u : C(K,E)) :
    C(K,E) →L[ℝ] C(K,V) :=
  EulerContinuousTimeIntegral.multiplier (A.derivative.superposition u)

theorem superpositionDerivative_apply (A : SmoothTimeField K E V)
    (u h : C(K,E)) (t : K) :
    A.superpositionDerivative u h t = fderiv ℝ (A.field t : E → V) (u t) (h t) := by
  change A.derivativeField t (u t) (h t) = _
  rw [A.derivativeField_eq]

theorem superposition_taylor_bound (A : SmoothTimeField K E V)
    (u v : C(K,E)) :
    ‖A.superposition v - A.superposition u - A.superpositionDerivative u (v-u)‖ ≤
      ‖A.jet 2‖ * ‖v-u‖^2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  change ‖A.field t (v t) - A.field t (u t) - A.superpositionDerivative u (v-u) t‖ ≤ _
  rw [A.superpositionDerivative_apply]
  have h₂ (x : E) : ‖fderiv ℝ (fderiv ℝ (A.field t : E → V)) x‖ ≤ ‖A.jet 2‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, ← A.jet_eq]
    exact ((A.jet 2 t).norm_coe_le_norm x).trans ((A.jet 2).norm_coe_le_norm t)
  have h := quadratic_taylor_bound
    (A.field t : E → V) (A.smooth t) ‖A.jet 2‖ (norm_nonneg _) h₂ (u t) (v t-u t)
  have he : u t + (v t-u t) = v t := by abel
  rw [he] at h
  have hv : ‖v t-u t‖ ≤ ‖v-u‖ := (v-u).norm_coe_le_norm t
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hv 2) (norm_nonneg _))

theorem superposition_hasFDerivAt (A : SmoothTimeField K E V) (u : C(K,E)) :
    HasFDerivAt A.superposition (A.superpositionDerivative u) u := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero
    (fun v => mul_nonneg (inv_nonneg.mpr (norm_nonneg (v-u))) (norm_nonneg _))
    (g := fun v : C(K,E) => ‖A.jet 2‖ * ‖v-u‖)
  · intro v
    calc
      _ ≤ ‖v-u‖⁻¹ * (‖A.jet 2‖ * ‖v-u‖^2) :=
        mul_le_mul_of_nonneg_left (A.superposition_taylor_bound u v)
          (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by
        by_cases h : ‖v-u‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun v : C(K,E) => ‖A.jet 2‖ * ‖v-u‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto u

theorem superposition_fderiv (A : SmoothTimeField K E V) :
    fderiv ℝ A.superposition = A.superpositionDerivative :=
  funext (fun u => (A.superposition_hasFDerivAt u).fderiv)

private theorem superposition_contDiff_nat (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (A : SmoothTimeField K E V), ContDiff ℝ n A.superposition := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun u => (A.superposition_hasFDerivAt u).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun u => (A.superposition_hasFDerivAt u).differentiableAt, by simp, ?_⟩
    rw [A.superposition_fderiv]
    exact contDiff_multiplier A.derivative.superposition
      (ih (E →L[ℝ] V) A.derivative)

theorem superposition_contDiff (A : SmoothTimeField K E V) :
    ContDiff ℝ ∞ A.superposition :=
  contDiff_infty.mpr (fun n => superposition_contDiff_nat n V A)

end SmoothTimeField
