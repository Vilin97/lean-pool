/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions
public import LeanPool.QuadraticCarleson.QuadraticCarleson.PrincipalValueDistribution

/-!
# The quadratically modulated principal-value kernel

The kernel in the paper is the product of the smooth phase
`y ↦ e(λ y²)` and the tempered distribution `p.v. (1 / y)`.
-/

@[expose] public section

open scoped SchwartzMap

namespace QuadraticCarleson

theorem quadraticPhase_hasTemperateGrowth (modulation : ℝ) :
    (fun y : ℝ => phase (modulation * y ^ 2)).HasTemperateGrowth := by
  rw [show (fun y : ℝ => phase (modulation * y ^ 2)) =
      (fun u : ℝ => Complex.exp (u * Complex.I)) ∘
        fun y : ℝ => 2 * Real.pi * (modulation * y ^ 2) by
    funext y
    simp only [Function.comp_apply, phase]]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- The distribution `e(λ y²) · p.v. (1 / y)`. -/
noncomputable def quadraticKernelDistribution (modulation : ℝ) : 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ
    (fun y : ℝ => phase (modulation * y ^ 2)) principalValueOneDiv

theorem quadraticKernelDistribution_apply (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) :
    quadraticKernelDistribution modulation f =
      principalValueOneDiv
        (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => phase (modulation * y ^ 2)) f) := by
  rfl

end QuadraticCarleson
