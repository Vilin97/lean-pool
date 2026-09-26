/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# API checks for functions at `0⁻`

A function that vanishes near zero represents `0` in `Fun_{0⁻}(ℚ)` even when it is globally
nonzero. A second fixture is eventually valued in a proper coordinate subspace but leaves it
away from zero. These distinguish eventual equality and membership from their global versions.
A nonzero constant function remains nonzero, and the tensor check evaluates the pointwise
representative formula on a nonconstant real-valued function at `0⁻`.
-/

open Filter Topology
open scoped TensorProduct

namespace Tests

public noncomputable section

/-- A rational-valued function that vanishes throughout `(-1, 0)` but not globally. -/
def tailZero (γ : ℝ) : ℚ :=
  if γ < -1 then 1 else 0

/-- The test function is globally nonzero. -/
theorem tailZero_neg_two : tailZero (-2) = 1 := by
  norm_num [tailZero]

/-- Agreement near `0`, rather than global equality, makes the test function `0` in
`Fun_{0⁻}(ℚ)`. -/
theorem tailZero_funAtZeroMinus_eq_zero :
    (tailZero : FunAtZeroMinus ℚ) = 0 := by
  change (tailZero : FunAtZeroMinus ℚ) = ((fun _ : ℝ ↦ (0 : ℚ)) : FunAtZeroMinus ℚ)
  rw [funAtZeroMinus_coe_eq_iff_exists]
  refine ⟨1, by norm_num, fun γ hγ _ ↦ ?_⟩
  rw [tailZero, ite_eq_right]
  linarith

/-- Constant functions remain distinct in `Fun_{0⁻}(ℚ)`. -/
theorem funAtZeroMinus_one_ne_zero :
    (1 : FunAtZeroMinus ℚ) ≠ 0 := by
  change ((1 : ℚ) : FunAtZeroMinus ℚ) ≠ ((0 : ℚ) : FunAtZeroMinus ℚ)
  intro h
  exact one_ne_zero (Filter.Germ.const_inj.mp h)

/-- The first coordinate axis in `ℚ × ℚ`. -/
def firstAxis : Submodule ℚ (ℚ × ℚ) where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x.2 = 0 at hx
    change y.2 = 0 at hy
    change x.2 + y.2 = 0
    rw [hx, hy, add_zero]
  smul_mem' c x hx := by
    change x.2 = 0 at hx
    change c * x.2 = 0
    rw [hx, mul_zero]

/-- Membership in the first coordinate axis is vanishing of the second coordinate. -/
@[simp]
theorem mem_firstAxis_iff (x : ℚ × ℚ) :
    x ∈ firstAxis ↔ x.2 = 0 := by
  change x.2 = 0 ↔ x.2 = 0
  rfl

/-- A function that enters the first coordinate axis on `(-1, 0)`. -/
def eventuallyFirstAxis (γ : ℝ) : ℚ × ℚ :=
  if γ < -1 then (0, 1) else (1, 0)

/-- The subspace-valued test function does not lie in the first axis globally. -/
theorem eventuallyFirstAxis_neg_two_not_mem :
    eventuallyFirstAxis (-2) ∉ firstAxis := by
  simp [eventuallyFirstAxis]

/-- Taking values in the subspace near `0` suffices for membership of the function at `0⁻` in
`Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)`. -/
theorem eventuallyFirstAxis_funAtZeroMinus_mem :
    (eventuallyFirstAxis : FunAtZeroMinus (ℚ × ℚ)) ∈ funAtZeroMinusSubmodule firstAxis := by
  rw [coe_mem_funAtZeroMinusSubmodule_iff_exists]
  refine ⟨1, by norm_num, fun γ hγ _ ↦ ?_⟩
  rw [eventuallyFirstAxis, ite_eq_right]
  · simp
  · linarith

/-- Tensor extension is represented by pointwise pure tensors on a nonconstant function at
`0⁻`. -/
theorem funAtZeroMinusTensorId_identity_tmul :
    funAtZeroMinusTensorId (E := ℝ)
        (LinearMap.id : FunAtZeroMinus ℝ →ₗ[ℝ] FunAtZeroMinus ℝ)
        (((fun γ : ℝ ↦ γ) : FunAtZeroMinus ℝ) ⊗ₜ[ℝ] (2 : ℝ)) =
      ((fun γ : ℝ ↦ γ ⊗ₜ[ℝ] (2 : ℝ)) : FunAtZeroMinus (ℝ ⊗[ℝ] ℝ)) := by
  apply funAtZeroMinusTensorId_tmul_of_eq_coe
  rfl

end

end Tests
