/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The normalized angular primitive reverses joint reflection parity. -/

@[expose] public section


noncomputable section

namespace EulerAngleMeanZeroPrimitive

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem primitive_neg (P : ℝ) (f : ℝ → E) :
    primitive P (fun θ => -f θ)=fun θ => -primitive P f θ := by
  funext θ
  simp only [primitive, rawPrimitive, intervalIntegral.integral_neg, smul_neg]
  abel

/-- Reflection of the argument contributes one minus sign to a primitive. -/
theorem primitive_reflection (P : ℝ) (hP : P ≠ 0) (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f P) (hmean : ∫ θ in 0..P, f θ = 0) :
    primitive P (fun θ => -f (-θ))=fun θ => primitive P f (-θ) := by
  symm
  apply primitive_unique P hP (fun θ => -f (-θ)) (hf.comp continuous_neg).neg
  · intro θ
    simpa only [Function.comp_def, id_eq, neg_smul, one_smul] using
      (primitive_hasDerivAt P f hf (-θ)).scomp θ ((hasDerivAt_id θ).neg)
  · rw [intervalIntegral.integral_comp_neg, neg_zero]
    have h := (primitive_periodic P f hf hper hmean).intervalIntegral_add_eq (-P) 0
    simp only [neg_add_cancel, zero_add] at h
    exact h.trans (primitive_mean_zero P hP f hf)

end EulerAngleMeanZeroPrimitive
