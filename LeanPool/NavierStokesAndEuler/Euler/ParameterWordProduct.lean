/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordCalculus

@[expose] public section

/-!
# Genuine word-sum product estimates

The binomial convolution is proved directly for the sum over ordered
directional words. The forcing and solution word sums stay unchanged;
there is no dimension factor or enlargement of their radius.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds
open scoped ContDiff

variable {P E F G ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The ordinary product rule in a fixed direction, as an equality of actual functions. -/
theorem directional_bilinear (directions : ι → P) (B : E →L[ℝ] F →L[ℝ] G)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : ι) :
    directional directions (fun x => B (f x) (g x)) i =
      (fun x => B (f x) (directional directions g i x))+
      (fun x => B (directional directions f i x) (g x)) := by
  funext x
  dsimp only [directional]
  rw [B.fderiv_of_bilinear (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

variable [Fintype ι]

theorem sum_convolution_right (A : ℕ → ℝ) (B : ι → ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution A (B i) n) = leibnizConvolution A (fun k => ∑ i, B i k) n := by
  simp only [leibnizConvolution]
  rw [sum_comm]
  exact sum_congr rfl (fun k _ => (mul_sum ..).symm)

theorem sum_convolution_left (A : ι → ℕ → ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution (A i) B n) = leibnizConvolution (fun k => ∑ i, A i k) B n := by
  simp only [leibnizConvolution]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← sum_mul, ← mul_sum]

/-- Sharp binomial convolution of the actual directional word sums. -/
theorem wordSum_bilinear_le (directions : ι → P) (B : E →L[ℝ] F →L[ℝ] G)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : P) :
    wordSum directions (fun y => B (f y) (g y)) n x ≤
      ‖B‖*leibnizConvolution (fun k => wordSum directions f k x)
        (fun k => wordSum directions g k x) n := by
  induction n generalizing f g with
  | zero =>
    simp only [wordSum_zero, leibnizConvolution, Nat.zero_add, sum_range_one,
      Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    exact ((B (f x)).le_opNorm (g x)).trans
      ((mul_le_mul_of_nonneg_right (B.le_opNorm (f x)) (norm_nonneg (g x))).trans_eq (mul_assoc _ _
        _))
  | succ n ih =>
    have hp : ContDiff ℝ ∞ (fun y => B (f y) (g y)) := (B.contDiff.comp hf).clm_apply hg
    rw [wordSum_succ directions _ hp n x]
    have ht (i : ι) :
        wordSum directions (directional directions (fun y => B (f y) (g y)) i) n x ≤
          ‖B‖ * (leibnizConvolution (fun k => wordSum directions f k x)
            (fun k => wordSum directions (directional directions g i) k x) n +
          leibnizConvolution (fun k => wordSum directions (directional directions f i) k x)
            (fun k => wordSum directions g k x) n) := by
      rw [directional_bilinear directions B f g hf hg i]
      apply (wordSum_add_le directions _ _
        ((B.contDiff.comp hf).clm_apply (directional_contDiff directions g hg i))
        ((B.contDiff.comp (directional_contDiff directions f hf i)).clm_apply hg) n x).trans
      exact (add_le_add (ih f (directional directions g i) hf (directional_contDiff directions g hg
        i))
        (ih (directional directions f i) g (directional_contDiff directions f hf i) hg)).trans_eq
          (mul_add _ _ _).symm
    apply (sum_le_sum (fun i _ => ht i)).trans_eq
    rw [← mul_sum, sum_add_distrib, sum_convolution_right, sum_convolution_left]
    simp_rw [← wordSum_succ directions g hg, ← wordSum_succ directions f hf]
    rw [leibnizConvolution_succ]

/-- Operator application has product constant one in the actual word-sum norm. -/
theorem wordSum_clm_apply_le (directions : ι → P) (A : P → E →L[ℝ] F)
    (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (fun y => A y (f y)) n x ≤
      leibnizConvolution (fun k => wordSum directions A k x)
        (fun k => wordSum directions f k x) n := by
  let B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := (ContinuousLinearMap.apply ℝ F).flip
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, opNorm_flip, ContinuousLinearMap.apply]
    apply opNorm_le_bound _ zero_le_one
    intro z
    simp only [coe_id', id_eq, one_mul]
    rfl
  have h := wordSum_bilinear_le directions B A f hA hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right hB
    (sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wordSum_nonneg directions A k x)) (wordSum_nonneg directions f (n-k) x)))).trans_eq (one_mul
        _))

end EulerParameterWordGevrey
