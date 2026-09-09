/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive

@[expose] public section

/-! The normalized periodic angular primitive commutes with actual angular translation. -/

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem primitive_translate (P : ℝ) (hP : P ≠ 0) (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f P) (hmean : ∫ θ in 0..P, f θ=0) (a : ℝ) :
    primitive P (fun θ => f (θ+a))=fun θ => primitive P f (θ+a) := by
  symm
  apply primitive_unique P hP (fun θ => f (θ+a)) (hf.comp (continuous_id.add continuous_const))
  · intro θ
    simpa only [one_smul, Function.comp_def, id_eq] using
      (primitive_hasDerivAt P f hf (θ+a)).scomp θ ((hasDerivAt_id θ).add_const a)
  · rw [intervalIntegral.integral_comp_add_right]
    have h := (primitive_periodic P f hf hper hmean).intervalIntegral_add_eq a 0
    rw [zero_add] at h
    rw [zero_add, add_comm P a, h, primitive_mean_zero P hP f hf]

end EulerAngleMeanZeroPrimitive
