/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PVSymmetricLimit
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticKernelDistribution

/-!
# Symmetric truncations of the quadratic kernel

The distribution `e(λx²) · p.v. (1/x)` is the limit of its ordinary
symmetric truncations on every Schwartz test function.
-/

open Filter
open scoped SchwartzMap Topology

namespace QuadraticCarleson

/-- The ordinary symmetric truncation of the quadratic kernel paired with a
Schwartz test function. -/
noncomputable def quadraticKernelTruncationAction
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) : ℂ :=
  principalValueTruncation ε
    (SchwartzMap.smulLeftCLM ℂ
      (fun y : ℝ ↦ phase (modulation * y ^ 2)) f)

theorem quadraticKernelTruncationAction_eq_integral
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) :
    quadraticKernelTruncationAction modulation ε f =
      ∫ y in {y : ℝ | ε < |y|},
        phase (modulation * y ^ 2) * f y / (y : ℂ) := by
  simp [quadraticKernelTruncationAction, principalValueTruncation,
    SchwartzMap.smulLeftCLM_apply_apply
      (quadraticPhase_hasTemperateGrowth modulation), smul_eq_mul]

/-- The distributional quadratic kernel agrees with the limit of ordinary
symmetric truncations as the deleted radius tends to zero from above. -/
theorem tendsto_quadraticKernelTruncationAction
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ ↦ quadraticKernelTruncationAction modulation ε f)
      (𝓝[>] 0) (𝓝 (quadraticKernelDistribution modulation f)) := by
  simpa only [quadraticKernelTruncationAction, quadraticKernelDistribution_apply,
    principalValueOneDiv_apply] using
      tendsto_principalValueTruncation
        (SchwartzMap.smulLeftCLM ℂ
          (fun y : ℝ ↦ phase (modulation * y ^ 2)) f)

end QuadraticCarleson
