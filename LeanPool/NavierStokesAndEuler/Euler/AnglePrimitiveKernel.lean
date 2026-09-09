/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveTranslation

@[expose] public section

/-! A translation-kernel formula for the literal normalized periodic primitive. -/

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- This formula realizes the angular primitive as an integral of translations. -/
theorem primitive_eq_translation_kernel (P : ℝ) (hP : P ≠ 0) (f : ℝ → E)
    (hf : Continuous f) (hper : Function.Periodic f P)
    (hmean : (∫ s in (0 : ℝ)..P, f s)=0) (θ : ℝ) :
    primitive P f θ = P⁻¹ • (∫ s in (0 : ℝ)..P, s • f (θ+s)) := by
  let q := primitive P f
  have hq : Continuous q := primitive_continuous P f hf
  have hqp : Function.Periodic q P := primitive_periodic P f hf hper hmean
  have hd (s : ℝ) : HasDerivAt (fun r => r • q (θ+r))
      (q (θ+s)+s • f (θ+s)) s := by
    have hq' := (primitive_hasDerivAt P f hf (θ+s)).scomp s ((hasDerivAt_id s).const_add θ)
    simpa only [Function.comp_def, id_eq, one_smul, Pi.smul_def', q, add_comm] using
      (hasDerivAt_id s).smul hq'
  have hqc : Continuous (fun s => q (θ+s)) := hq.comp (continuous_const.add continuous_id)
  have hfc : Continuous (fun s => s • f (θ+s)) :=
    continuous_id.smul (hf.comp (continuous_const.add continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((hqc.add hfc).intervalIntegrable 0 P)
  rw [intervalIntegral.integral_add (hqc.intervalIntegrable 0 P) (hfc.intervalIntegrable 0 P)] at hi
  have hzero : (∫ s in (0 : ℝ)..P, q (θ+s))=0 := by
    rw [intervalIntegral.integral_comp_add_left]
    have hp := hqp.intervalIntegral_add_eq θ 0
    rw [zero_add] at hp
    rw [add_zero, hp]
    exact primitive_mean_zero P hP f hf
  rw [hzero, zero_add, hqp θ, zero_smul, sub_zero] at hi
  change q θ = _
  rw [hi, smul_smul, inv_mul_cancel₀ hP, one_smul]

end EulerAngleMeanZeroPrimitive
