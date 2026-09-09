/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive

@[expose] public section

/-! Uniform bounds for the actual mean-zero angular primitive. -/

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem rawPrimitive_bound (P M : ℝ) (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ θ ∈ Icc 0 P, ‖f θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖rawPrimitive f θ‖ ≤ M*P := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := θ) (f := f) (C := M) (fun x hx => hf x (by
      rw [uIoc_of_le hθ.1] at hx
      exact ⟨hx.1.le, hx.2.trans hθ.2⟩))
  simp only [sub_zero, abs_of_nonneg hθ.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left hθ.2 hM)

omit [CompleteSpace E] in
theorem primitive_bound (P M : ℝ) (hP : 0 < P) (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ θ ∈ Icc 0 P, ‖f θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖primitive P f θ‖ ≤ 2*P*M := by
  have hraw := rawPrimitive_bound P M hM f hf
  have hint : ‖∫ s in 0..P, rawPrimitive f s‖ ≤ (M*P)*P := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := P) (f := rawPrimitive f) (C := M*P) (fun x hx => hraw x (by
        rw [uIoc_of_le hP.le] at hx
        exact ⟨hx.1.le, hx.2⟩))
    simpa only [sub_zero, abs_of_pos hP] using h
  have hmean : ‖P⁻¹ • (∫ s in 0..P, rawPrimitive f s)‖ ≤ M*P := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)]
    calc
      _ ≤ P⁻¹*((M*P)*P) := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hP.le)
      _ = M*P := by field_simp
  exact (norm_sub_le _ _).trans (by linarith [hraw θ hθ, hmean])

end EulerAngleMeanZeroPrimitive
