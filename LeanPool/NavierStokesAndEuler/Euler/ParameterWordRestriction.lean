/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

@[expose] public section

/-! Exact parameter restriction and injective subalphabet bounds for genuine derivative words. -/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P Q E ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]

/-- Restricting an alphabet only discards nonnegative summands. -/
theorem wordSum_subalphabet_le (directions : κ → P) (e : ι → κ) (he : Function.Injective e)
    (f : P → E) (n : ℕ) (x : P) :
    wordSum (directions ∘ e) f n x ≤ wordSum directions f n x := by
  classical
  have hinj : Function.Injective (fun w : Fin n → ι => e ∘ w) := by
    intro u v h
    exact funext (fun j => he (congrFun h j))
  calc
    _ = ∑ w ∈ univ.image (fun w : Fin n → ι => e ∘ w), ‖wordDerivative directions f w x‖ := by
      rw [sum_image hinj.injOn]
      rfl
    _ ≤ ∑ w : Fin n → κ, ‖wordDerivative directions f w x‖ :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => norm_nonneg _)

/-- The same literal subalphabet restriction is contractive on every fixed Sobolev block. -/
theorem block_subalphabet_le (directions : κ → P) (e : ι → κ) (he : Function.Injective e)
    (q : ℕ) (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block (directions ∘ e) q f n x ≤ block directions q f n x := by
  rw [block_eq_sum_levels _ q f hf,block_eq_sum_levels _ q f hf]
  exact sum_le_sum (fun k _ => wordSum_subalphabet_le directions e he f (n+k) x)

omit [Fintype ι] in
/-- A linear parameter map transports the actual directions exactly. -/
theorem wordDerivative_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f ∘ A) w x = wordDerivative (A ∘ directions) f w (A x) := by
  have h := congrArg (fun D : P[×n]→L[ℝ] E => D (fun j => directions (w j)))
    (A.iteratedFDeriv_comp_right hf x (i := n) (by simp))
  exact h

theorem wordSum_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (f ∘ A) n x = wordSum (A ∘ directions) f n (A x) := by
  unfold wordSum
  exact sum_congr rfl (fun w _ => congrArg norm (wordDerivative_comp_right directions A f hf w x))

/-- Restricting parameters does not change a fixed block when the directions are transported. -/
theorem block_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (q : ℕ) (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q (f ∘ A) n x = block (A ∘ directions) q f n (A x) := by
  rw [block_eq_sum_levels _ q _ (hf.comp A.contDiff),block_eq_sum_levels _ q _ hf]
  exact sum_congr rfl (fun k _ => wordSum_comp_right directions A f hf (n+k) x)

end EulerParameterWordGevrey
