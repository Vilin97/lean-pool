/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher

/-! Fixed bounded maps preserve the actual fixed-Sobolev external word sums. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E F ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

theorem baseSize_comp_clm_le (directions : ι → P) (q : ℕ) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (x : P) :
    baseSize directions q (L ∘ f) x ≤ ‖L‖*baseSize directions q f x := by
  unfold baseSize
  rw [mul_sum]
  exact sum_le_sum (fun k _ => wordSum_comp_clm_le directions L f hf k x)

/-- The exact same external radius and fixed Sobolev order pass through
every fixed continuous linear map, with just its operator norm. -/
theorem block_comp_clm_le (directions : ι → P) (q : ℕ) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q (L ∘ f) n x ≤ ‖L‖*block directions q f n x := by
  unfold block
  rw [mul_sum]
  apply sum_le_sum
  intro w _
  have he : wordDerivative directions (L ∘ f) w = L ∘ wordDerivative directions f w :=
    funext (wordDerivative_comp_clm directions L f hf w)
  rw [he]
  exact baseSize_comp_clm_le directions q L _ (wordDerivative_contDiff directions f hf w) x

theorem coefficientBlock_comp_clm_le (directions : ι → P) (q : ℕ) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    coefficientBlock directions q (L ∘ f) n x ≤ ‖L‖*coefficientBlock directions q f n x :=
  (mul_le_mul_of_nonneg_left (block_comp_clm_le directions q L f hf n x) (by positivity)).trans_eq
    (by unfold coefficientBlock; ring)

theorem block_sub_le (directions : ι → P) (q : ℕ) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    block directions q (f-g) n x ≤ block directions q f n x+block directions q g n x := by
  unfold block
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  have he : wordDerivative directions (f-g) w =
      wordDerivative directions f w-wordDerivative directions g w :=
    funext (wordDerivative_sub directions f g hf hg w)
  rw [he]
  exact baseSize_sub_le directions q _ _ (wordDerivative_contDiff directions f hf w)
    (wordDerivative_contDiff directions g hg w) x

end EulerParameterWordGevrey
