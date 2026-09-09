/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks

@[expose] public section

/-!
# Positive external-order commutators in actual fixed Sobolev blocks

The commutator is an explicit difference of genuine derivatives and the
undifferentiated coefficient action. Its direct word recurrence places at
least one external derivative on the coefficient in every term.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds
open scoped ContDiff

variable {P E F ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- The actual external word commutator of operator multiplication. -/
def wordCommutator (directions : ι → P) (A : P → E →L[ℝ] F) (f : P → E)
    {n : ℕ} (w : Fin n → ι) : P → F :=
  wordDerivative directions (fun y => A y (f y)) w-
    fun y => A y (wordDerivative directions f w y)

omit [Fintype ι] in
theorem wordCommutator_contDiff (directions : ι → P) (A : P → E →L[ℝ] F) (f : P → E)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) :
    ContDiff ℝ ∞ (wordCommutator directions A f w) :=
  (wordDerivative_contDiff directions _ (hA.clm_apply hf) w).sub
    (hA.clm_apply (wordDerivative_contDiff directions f hf w))

omit [Fintype ι] in
theorem wordCommutator_snoc (directions : ι → P) (A : P → E →L[ℝ] F) (f : P → E)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (i : ι) :
    wordCommutator directions A f (Fin.snoc w i) =
      wordCommutator directions A (directional directions f i) w+
        wordDerivative directions (fun y => directional directions A i y (f y)) w := by
  have hprod := directional_bilinear directions ((ContinuousLinearMap.apply ℝ F).flip) A f hA hf i
  change directional directions (fun y => A y (f y)) i =
    (fun y => A y (directional directions f i y))+
    (fun y => directional directions A i y (f y)) at hprod
  funext x
  change wordDerivative directions (fun y => A y (f y)) (Fin.snoc w i) x-
      A x (wordDerivative directions f (Fin.snoc w i) x) =
    (wordDerivative directions (fun y => A y (directional directions f i y)) w x-
      A x (wordDerivative directions (directional directions f i) w x))+
    wordDerivative directions (fun y => directional directions A i y (f y)) w x
  rw [wordDerivative_snoc directions _ (hA.clm_apply hf), wordDerivative_snoc directions f hf,
    hprod, wordDerivative_add directions _ _
      (hA.clm_apply (directional_contDiff directions f hf i))
      ((directional_contDiff directions A hA i).clm_apply hf)]
  abel

def commutatorBlock (directions : ι → P) (q : ℕ) (A : P → E →L[ℝ] F) (f : P → E)
    (n : ℕ) (x : P) : ℝ :=
  ∑ w : Fin n → ι, baseSize directions q (wordCommutator directions A f w) x

theorem baseSize_zero_function (directions : ι → P) (q : ℕ) (x : P) :
    baseSize directions q (fun _ : P => (0 : E)) x = 0 := by
  unfold baseSize
  apply sum_eq_zero
  intro n _
  cases n with
  | zero => simp only [wordSum_zero, norm_zero]
  | succ n => simp only [wordSum, wordDerivative, iteratedFDeriv_succ_const,
      Pi.zero_apply, zero_apply, norm_zero, sum_const_zero]

theorem commutatorBlock_zero (directions : ι → P) (q : ℕ) (A : P → E →L[ℝ] F) (f : P → E)
    (x : P) : commutatorBlock directions q A f 0 x = 0 := by
  have he (w : Fin 0 → ι) : wordCommutator directions A f w = fun _ => 0 := by
    funext y
    simp only [wordCommutator, Pi.sub_apply, wordDerivative_zero, sub_self]
  simp only [commutatorBlock, he, baseSize_zero_function, sum_const_zero]

theorem commutatorBlock_nonneg (directions : ι → P) (q : ℕ) (A : P → E →L[ℝ] F) (f : P → E)
    (n : ℕ) (x : P) : 0 ≤ commutatorBlock directions q A f n x :=
  sum_nonneg (fun _ _ => baseSize_nonneg directions q _ x)

theorem commutatorBlock_succ_le (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    commutatorBlock directions q A f (n+1) x ≤
      ∑ i, (commutatorBlock directions q A (directional directions f i) n x+
        block directions q (fun y => directional directions A i y (f y)) n x) := by
  unfold commutatorBlock block
  rw [sum_words_snoc]
  apply sum_le_sum
  intro i _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordCommutator_snoc directions A f hA hf w i]
  exact baseSize_add_le directions q _ _
    (wordCommutator_contDiff directions A (directional directions f i) hA
      (directional_contDiff directions f hf i) w)
    (wordDerivative_contDiff directions _ ((directional_contDiff directions A hA i).clm_apply hf)
      w) x

theorem sum_commutator_convolution_right (A : ℕ → ℝ) (B : ι → ℕ → ℝ) (n : ℕ) :
    (∑ i, commutatorConvolution A (B i) n) =
      commutatorConvolution A (fun k => ∑ i, B i k) n := by
  simp only [commutatorConvolution]
  rw [sum_sub_distrib, sum_convolution_right, mul_sum]

/-- Every external commutator term contains a positive external derivative
of the coefficient, with no enlargement of solution or forcing radii. -/
theorem commutatorBlock_bound (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    commutatorBlock directions q A f n x ≤
      commutatorConvolution (fun k => coefficientBlock directions q A k x)
        (fun k => block directions q f k x) n := by
  induction n generalizing A f with
  | zero => simp only [commutatorBlock_zero, commutatorConvolution_eq_sum, range_zero, sum_empty,
    le_refl]
  | succ n ih =>
    apply (commutatorBlock_succ_le directions q A f hA hf n x).trans
    have ht (i : ι) := add_le_add
      (ih A (directional directions f i) hA (directional_contDiff directions f hf i))
      (block_clm_apply_le directions q (directional directions A i) f
        (directional_contDiff directions A hA i) hf n x)
    apply (sum_le_sum (fun i _ => ht i)).trans_eq
    rw [sum_add_distrib, sum_commutator_convolution_right, sum_convolution_left]
    simp_rw [← block_succ directions q f hf, ← coefficientBlock_succ directions q A hA]
    rw [commutatorConvolution_succ]

end EulerParameterWordGevrey
