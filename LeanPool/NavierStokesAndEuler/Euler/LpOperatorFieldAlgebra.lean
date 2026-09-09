/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
public import LeanPool.NavierStokesAndEuler.Euler.LpOperatorField
import Mathlib.Algebra.Order.Star.Real

/-!
# Algebra and coercivity of actual full-space L² multipliers

The bounded-field multiplier preserves composition and adjoints. Pointwise
frame lower bounds and Hessian upper bounds hold on the full Bochner L²
space. Measurable spatial cutoffs are self-adjoint and commute with these
rectangular multipliers. Thus support preservation of a variational inverse
can be proved by its actual uniqueness theorem.
-/

@[expose] public section


noncomputable section

namespace EulerLpOperatorField

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpSupportedSubspace
  EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable {α U E F : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α)

section Composition

variable [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication by the actual product field is composition on L². -/
theorem full_comp (A : α →ᵇ E →L[ℝ] F) (B : α →ᵇ U →L[ℝ] E) :
    full μ (compositionMap A B) = (full μ A).comp (full μ B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [full_ae μ (compositionMap A B) u,
    full_ae μ A (full μ B u),full_ae μ B u] with x hab ha hb
  change full μ (compositionMap A B) u x = full μ A (full μ B u) x
  rw [hab,ha,hb]
  rfl

theorem full_neg (A : α →ᵇ E →L[ℝ] F) : full μ (-A) = -full μ A :=
  map_neg (fullMap μ) A

/-- A literal coefficient identity can be lifted without introducing a new
operator hypothesis. -/
theorem full_eq_neg_comp (C : α →ᵇ U →L[ℝ] F)
    (A : α →ᵇ E →L[ℝ] F) (B : α →ᵇ U →L[ℝ] E)
    (hC : ∀ x u, C x u = -(A x (B x u))) :
    full μ C = -(full μ A).comp (full μ B) := by
  have hc : C = -compositionMap A B := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro u
    exact hC x u
  rw [hc,full_neg,full_comp]

end Composition

section Hilbert

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A pointwise lower frame bound is a lower bound on genuine full-space L². -/
theorem full_norm_sq_lower (A : α →ᵇ E →L[ℝ] F) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ‖A x v‖ ^ 2) (u : Lp E 2 μ) :
    c*‖u‖^2 ≤ ‖full μ A u‖^2 := by
  have hroot : (Real.sqrt c)^2 = c := Real.sq_sqrt hc
  have h : ‖Real.sqrt c • u‖ ≤ ‖full μ A u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [full_ae μ A u,Lp.coeFn_smul (Real.sqrt c) u] with x ha hs
    rw [ha,hs,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg c)]
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)) (norm_nonneg _)).1
    rw [mul_pow,hroot]
    exact hA x (u x)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg c)] at h
  have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)) (norm_nonneg _)).2 h
  simpa only [mul_pow,hroot] using hs

/-- The actual L² Hessian inherits its pointwise quadratic upper bound. -/
theorem full_quadratic_upper (A : α →ᵇ E →L[ℝ] E) (C : ℝ)
    (hA : ∀ x v, ⟪A x v, v⟫_ℝ ≤ C * ‖v‖ ^ 2) (u : Lp E 2 μ) :
    ⟪full μ A u,u⟫_ℝ ≤ C*‖u‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae (L2.integrable_inner (full μ A u) u)
    ((L2.integrable_inner u u).const_mul C)
  filter_upwards [full_ae μ A u] with x hx
  rw [hx,real_inner_self_eq_norm_sq]
  exact hA x (u x)

/-- A rectangular coefficient commutes with literal spatial localization. -/
theorem full_cutoff (S : Set α) (hS : MeasurableSet S)
    (A : α →ᵇ E →L[ℝ] F) (u : Lp E 2 μ) :
    full μ A (cutoffOperator μ S hS u) = cutoffOperator μ S hS (full μ A u) := by
  apply Lp.ext
  filter_upwards [full_ae μ A (cutoffOperator μ S hS u),cutoff_ae μ S hS u,
    cutoff_ae μ S hS (full μ A u),full_ae μ A u] with x ha hi ho hu
  change full μ A (cutoffOperator μ S hS u) x = cutoff μ S hS (full μ A u) x
  change cutoffOperator μ S hS u x = _ at hi
  rw [ha,hi,ho]
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx,hu]
  · simp only [indicator_of_notMem hx,map_zero]

variable [CompleteSpace E] [CompleteSpace F]

/-- The L² adjoint is multiplication by the pointwise adjoint field. -/
theorem full_adjoint (A : α →ᵇ E →L[ℝ] F) :
    (full μ A).adjoint = full μ (adjointMap A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [full_ae μ A v,full_ae μ (adjointMap A) u] with x ha hadj
  rw [ha,hadj,adjointMap_apply,adjoint_inner_left]

end Hilbert

end EulerLpOperatorField

namespace EulerLpSupportedSubspace

open Set MeasureTheory ContinuousLinearMap InnerProductSpace

variable {α E : Type*} [MeasurableSpace α] (μ : Measure α)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set α) (hS : MeasurableSet S)

/-- The genuine measurable spatial cutoff is an orthogonal projection. -/
theorem cutoffOperator_adjoint :
    (cutoffOperator (V := E) μ S hS).adjoint = cutoffOperator μ S hS := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoff_ae μ S hS v,cutoff_ae μ S hS u] with x hv hu
  change ⟪u x,cutoff μ S hS v x⟫_ℝ = ⟪cutoff μ S hS u x,v x⟫_ℝ
  rw [hv,hu]
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx,inner_zero_left,inner_zero_right]

end EulerLpSupportedSubspace
