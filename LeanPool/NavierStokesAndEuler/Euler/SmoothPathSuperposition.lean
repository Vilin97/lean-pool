/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
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

namespace EulerMeanCoefficients.SmoothCoefficientPath

open EulerSmoothLimit EulerContinuousTimeIntegral EulerContinuousPathCalculus

universe u v

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup C(K, Space →ᵇ (Space [×n]→L[ℝ] V)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ C(K, Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance

def superposition (A : SmoothCoefficientPath K V) (u : C(K, Space)) : C(K,V) where
  toFun t := A.field t (u t)
  continuous_toFun := by fun_prop

@[simp] theorem superposition_apply (A : SmoothCoefficientPath K V)
    (u : C(K,Space)) (t : K) : A.superposition u t = A.field t (u t) := rfl

def superpositionDerivative (A : SmoothCoefficientPath K V) (u : C(K,Space)) :
    C(K,Space) →L[ℝ] C(K,V) :=
  EulerContinuousTimeIntegral.multiplier (A.derivative.superposition u)

theorem superpositionDerivative_apply (A : SmoothCoefficientPath K V)
    (u h : C(K,Space)) (t : K) :
    A.superpositionDerivative u h t = fderiv ℝ (A.field t : Space → V) (u t) (h t) := by
  change A.derivativeField t (u t) (h t) = _
  rw [A.derivativeField_eq]

theorem superposition_taylor_bound (A : SmoothCoefficientPath K V)
    (u v : C(K,Space)) :
    ‖A.superposition v - A.superposition u - A.superpositionDerivative u (v-u)‖ ≤
      ‖A.jet 2‖ * ‖v-u‖^2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  change ‖A.field t (v t) - A.field t (u t) - A.superpositionDerivative u (v-u) t‖ ≤ _
  rw [A.superpositionDerivative_apply]
  have h₂ (x : Space) : ‖fderiv ℝ (fderiv ℝ (A.field t : Space → V)) x‖ ≤ ‖A.jet 2‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, ← A.jet_eq]
    exact ((A.jet 2 t).norm_coe_le_norm x).trans ((A.jet 2).norm_coe_le_norm t)
  have h := EulerMeanBoundary.norm_linearization_remainder_le
    (A.field t : Space → V) (A.smooth t) ‖A.jet 2‖ (norm_nonneg _) h₂ (u t) (v t-u t)
  have he : u t + (v t-u t) = v t := by abel
  rw [he] at h
  have hv : ‖v t-u t‖ ≤ ‖v-u‖ := (v-u).norm_coe_le_norm t
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hv 2) (norm_nonneg _))

theorem superposition_hasFDerivAt (A : SmoothCoefficientPath K V) (u : C(K,Space)) :
    HasFDerivAt A.superposition (A.superpositionDerivative u) u := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero
    (fun v => mul_nonneg (inv_nonneg.mpr (norm_nonneg (v-u))) (norm_nonneg _))
    (g := fun v : C(K,Space) => ‖A.jet 2‖ * ‖v-u‖)
  · intro v
    calc
      _ ≤ ‖v-u‖⁻¹ * (‖A.jet 2‖ * ‖v-u‖^2) :=
        mul_le_mul_of_nonneg_left (A.superposition_taylor_bound u v)
          (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by
        by_cases h : ‖v-u‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun v : C(K,Space) => ‖A.jet 2‖ * ‖v-u‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto u

theorem superposition_fderiv (A : SmoothCoefficientPath K V) :
    fderiv ℝ A.superposition = A.superpositionDerivative :=
  funext (fun u => (A.superposition_hasFDerivAt u).fderiv)

private theorem superposition_contDiff_nat (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (A : SmoothCoefficientPath K V), ContDiff ℝ n A.superposition := by
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
      (ih (Space →L[ℝ] V) A.derivative)

theorem superposition_contDiff (A : SmoothCoefficientPath K V) :
    ContDiff ℝ ∞ A.superposition :=
  contDiff_infty.mpr (fun n => superposition_contDiff_nat n V A)

end EulerMeanCoefficients.SmoothCoefficientPath
