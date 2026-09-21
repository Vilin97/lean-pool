/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Nonnegative multiples of upper semicontinuous functions

Multiplication by a nonnegative real constant preserves upper semicontinuity on a set.

## Main results

* `UpperSemicontinuousOn.const_mul`: Nonnegative multiples of upper semicontinuous functions are
  upper semicontinuous.
-/

public section

open Set

/-- Nonnegative multiples of upper semicontinuous functions are upper semicontinuous. -/
theorem UpperSemicontinuousOn.const_mul {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X}
    {c : ℝ} (hf : UpperSemicontinuousOn f s) (hc : 0 ≤ c) :
    UpperSemicontinuousOn (fun x => c * f x) s := fun z hz =>
  (continuous_const.mul continuous_id).continuousAt.comp_upperSemicontinuousWithinAt
    (hf z hz) (fun _ _ hxy => mul_le_mul_of_nonneg_left hxy hc)

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
