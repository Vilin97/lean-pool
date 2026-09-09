/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks

@[expose] public section

/-! Direct two-input linear bounds for genuine fixed Sobolev word blocks. -/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E F G ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem wordDerivative_pair (directions : ι → P) (f : P → E) (g : P → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (fun y => (f y,g y)) w x =
      (wordDerivative directions f w x,wordDerivative directions g w x) := by
  apply Prod.ext
  · exact (wordDerivative_comp_clm directions (fst ℝ E F)
      (fun y => (f y,g y)) (hf.prodMk hg) w x).symm
  · exact (wordDerivative_comp_clm directions (snd ℝ E F)
      (fun y => (f y,g y)) (hf.prodMk hg) w x).symm

theorem wordDerivative_linear_pair (directions : ι → P) (L : (E × F) →L[ℝ] G)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (fun y => L (f y,g y)) w x =
      L (wordDerivative directions f w x,wordDerivative directions g w x) :=
  (wordDerivative_comp_clm directions L (fun y => (f y,g y)) (hf.prodMk hg) w x).trans
    (congrArg L (wordDerivative_pair directions f g hf hg w x))

variable [Fintype ι]

theorem wordSum_linear_pair_le (directions : ι → P) (L : (E × F) →L[ℝ] G)
    (a b : ℝ) (hL : ∀ p q, ‖L (p,q)‖ ≤ a*‖p‖+b*‖q‖)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : P) :
    wordSum directions (fun y => L (f y,g y)) n x ≤
      a*wordSum directions f n x+b*wordSum directions g n x := by
  unfold wordSum
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_linear_pair directions L f g hf hg w x]
  exact hL _ _

theorem baseSize_linear_pair_le (directions : ι → P) (q : ℕ) (L : (E × F) →L[ℝ] G)
    (a b : ℝ) (hL : ∀ p r, ‖L (p,r)‖ ≤ a*‖p‖+b*‖r‖)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : P) :
    baseSize directions q (fun y => L (f y,g y)) x ≤
      a*baseSize directions q f x+b*baseSize directions q g x := by
  unfold baseSize
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum (fun k _ => wordSum_linear_pair_le directions L a b hL f g hf hg k x)

theorem block_linear_pair_le (directions : ι → P) (q : ℕ) (L : (E × F) →L[ℝ] G)
    (a b : ℝ) (hL : ∀ p r, ‖L (p,r)‖ ≤ a*‖p‖+b*‖r‖)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : P) :
    block directions q (fun y => L (f y,g y)) n x ≤
      a*block directions q f n x+b*block directions q g n x := by
  unfold block
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro w _
  have he : wordDerivative directions (fun y => L (f y,g y)) w =
      fun y => L (wordDerivative directions f w y,wordDerivative directions g w y) :=
    funext (wordDerivative_linear_pair directions L f g hf hg w)
  rw [he]
  exact baseSize_linear_pair_le directions q L a b hL
    (wordDerivative directions f w) (wordDerivative directions g w)
    (wordDerivative_contDiff directions f hf w) (wordDerivative_contDiff directions g hg w) x

end EulerParameterWordGevrey
