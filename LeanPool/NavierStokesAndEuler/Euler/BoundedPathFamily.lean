/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-! Uniform bounds on a genuine time derivative turn a continuous family
of paths into a continuous path of bounded fields. -/

noncomputable section

open scoped BoundedContinuousFunction

namespace EulerBoundedPathFamily

open Set EulerVolterraConvolution

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : X → C(Icc (0 : ℝ) T,V))
  (hf : Continuous f) (C D : ℝ)
  (hC : ∀ t x, ‖f x t‖ ≤ C)
  (hD : 0 ≤ D) (hq : ∀ t x, ‖q x t‖ ≤ D)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)

def boundedSlice (t : Icc (0 : ℝ) T) : X →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x t)
    ((ContinuousMap.evalCLM ℝ t).continuous.comp hf) C (hC t)

include hq hd in
theorem boundedSlice_lipschitz :
    LipschitzWith ⟨D,hD⟩ (boundedSlice T f hf C hC) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hD dist_nonneg)).2
  intro x
  change ‖f x s - f x t‖ ≤ D * dist s t
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := extendPath T hT (f x)) (f' := extendPath T hT (q x)) (C := D)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hd x ⟨r,hr⟩)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hq ⟨r,hr⟩ x)
    (convex_Icc (0 : ℝ) T) t.property s.property
  simpa only [extendPath,
    projIcc_of_mem hT t.property, projIcc_of_mem hT s.property,
    dist_eq_norm, Subtype.dist_eq] using h

def boundedPath : C(Icc (0 : ℝ) T,X →ᵇ V) where
  toFun := boundedSlice T f hf C hC
  continuous_toFun := (boundedSlice_lipschitz T hT f q hf C D hC hD hq hd).continuous

@[simp] theorem boundedPath_apply (t : Icc (0 : ℝ) T) (x : X) :
    boundedPath T hT f q hf C D hC hD hq hd t x = f x t := rfl

theorem boundedPath_norm (hCnonneg : 0 ≤ C) :
    ‖boundedPath T hT f q hf C D hC hD hq hd‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hCnonneg).2
  intro t
  exact (BoundedContinuousFunction.norm_le hCnonneg).2 (hC t)

end EulerBoundedPathFamily
