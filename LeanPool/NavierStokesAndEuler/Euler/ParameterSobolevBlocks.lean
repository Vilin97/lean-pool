/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.JetProductBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordCalculus
import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordProduct
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Fixed Sobolev blocks of genuine external parameter words

The fixed base order is kept inside each actual external word. Product
bounds place its finite cost on coefficient blocks, preserving the input
and output external radius and factorial shift.
-/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds
open scoped ContDiff

variable {P E F ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- The fixed-order sum of the actual spatial derivative norms. -/
def baseSize (directions : ι → P) (q : ℕ) (f : P → E) (x : P) : ℝ :=
  ∑ k ∈ range (q+1), wordSum directions f k x

/-- A fixed Sobolev base norm inside the sum of actual external words. -/
def block (directions : ι → P) (q : ℕ) (f : P → E) (n : ℕ) (x : P) : ℝ :=
  ∑ w : Fin n → ι, baseSize directions q (wordDerivative directions f w) x

/-- The finite base-order Leibniz constant belongs only to the coefficient block. -/
def coefficientBlock (directions : ι → P) (q : ℕ) (f : P → E) (n : ℕ) (x : P) : ℝ :=
  (2 : ℝ)^q*block directions q f n x

theorem baseSize_nonneg (directions : ι → P) (q : ℕ) (f : P → E) (x : P) :
    0 ≤ baseSize directions q f x := sum_nonneg (fun k _ => wordSum_nonneg directions f k x)

theorem block_nonneg (directions : ι → P) (q : ℕ) (f : P → E) (n : ℕ) (x : P) :
    0 ≤ block directions q f n x := sum_nonneg (fun _w _ => baseSize_nonneg directions q _ x)

theorem coefficientBlock_nonneg (directions : ι → P) (q : ℕ) (f : P → E) (n : ℕ) (x : P) :
    0 ≤ coefficientBlock directions q f n x :=
  mul_nonneg (by positivity) (block_nonneg directions q f n x)

theorem baseSize_zero (directions : ι → P) (f : P → E) (x : P) :
    baseSize directions 0 f x = ‖f x‖ := by
  simp only [baseSize, Nat.zero_add, sum_range_one, wordSum_zero]

theorem baseSize_succ (directions : ι → P) (q : ℕ) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (x : P) :
    baseSize directions (q+1) f x = ‖f x‖+∑ i, baseSize directions q (directional directions f i) x
        := by
  unfold baseSize
  rw [sum_range_succ']
  simp only [wordSum_zero, wordSum_succ directions f hf]
  rw [sum_comm, add_comm]

theorem baseSize_mono (directions : ι → P) (f : P → E) (x : P) {p q : ℕ} (hpq : p ≤ q) :
    baseSize directions p f x ≤ baseSize directions q f x :=
  sum_le_sum_of_subset_of_nonneg (range_mono (Nat.add_le_add_right hpq 1))
    (fun k _ _ => wordSum_nonneg directions f k x)

theorem norm_le_baseSize (directions : ι → P) (q : ℕ) (f : P → E) (x : P) :
    ‖f x‖ ≤ baseSize directions q f x :=
  (baseSize_zero directions f x).symm.trans_le (baseSize_mono directions f x (Nat.zero_le q))

theorem baseSize_add_le (directions : ι → P) (q : ℕ) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : P) :
    baseSize directions q (f+g) x ≤ baseSize directions q f x+baseSize directions q g x := by
  unfold baseSize
  rw [← sum_add_distrib]
  exact sum_le_sum (fun k _ => wordSum_add_le directions f g hf hg k x)

theorem baseSize_sub_le (directions : ι → P) (q : ℕ) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : P) :
    baseSize directions q (f-g) x ≤ baseSize directions q f x+baseSize directions q g x := by
  unfold baseSize
  rw [← sum_add_distrib]
  exact sum_le_sum (fun k _ => wordSum_sub_le directions f g hf hg k x)

theorem baseSize_clm_apply_le (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (x : P) :
    baseSize directions q (fun y => A y (f y)) x ≤
      (2 : ℝ)^q*baseSize directions q A x*baseSize directions q f x := by
  apply (sum_le_sum (fun k _ => wordSum_clm_apply_le directions A f hA hf k x)).trans
  exact EulerH6Pressure.base_convolution_bound q (fun k => wordSum directions A k x)
    (fun k => wordSum directions f k x)
    (fun k => wordSum_nonneg directions A k x) (fun k => wordSum_nonneg directions f k x)

theorem block_zero (directions : ι → P) (q : ℕ) (f : P → E) (x : P) :
    block directions q f 0 x = baseSize directions q f x := by
  have he (w : Fin 0 → ι) : wordDerivative directions f w = f :=
    funext (wordDerivative_zero directions f w)
  simp only [block, he, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
      one_smul]

theorem block_succ (directions : ι → P) (q : ℕ) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    block directions q f (n+1) x = ∑ i, block directions q (directional directions f i) n x := by
  unfold block
  rw [sum_words_snoc]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro w _
  exact congrArg (fun g : P → E => baseSize directions q g x)
    (funext (wordDerivative_snoc directions f hf w i))

theorem coefficientBlock_succ (directions : ι → P) (q : ℕ) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    coefficientBlock directions q f (n+1) x =
      ∑ i, coefficientBlock directions q (directional directions f i) n x := by
  simp only [coefficientBlock, block_succ directions q f hf, mul_sum]

theorem block_add_le (directions : ι → P) (q : ℕ) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    block directions q (f+g) n x ≤ block directions q f n x+block directions q g n x := by
  unfold block
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  have he : wordDerivative directions (f+g) w =
      wordDerivative directions f w+wordDerivative directions g w :=
    funext (wordDerivative_add directions f g hf hg w)
  rw [he]
  exact baseSize_add_le directions q _ _ (wordDerivative_contDiff directions f hf w)
    (wordDerivative_contDiff directions g hg w) x

/-- Direct Leibniz in external words with fixed Sobolev blocks. -/
theorem block_clm_apply_le (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    block directions q (fun y => A y (f y)) n x ≤
      leibnizConvolution (fun k => coefficientBlock directions q A k x)
        (fun k => block directions q f k x) n := by
  let B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := (ContinuousLinearMap.apply ℝ F).flip
  induction n generalizing A f with
  | zero =>
    simpa only [leibnizConvolution, Nat.zero_add, sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.sub_zero, block_zero, coefficientBlock] using
      baseSize_clm_apply_le directions q A f hA hf x
  | succ n ih =>
    have hp : ContDiff ℝ ∞ (fun y => A y (f y)) := hA.clm_apply hf
    rw [block_succ directions q _ hp n x]
    have ht (i : ι) :
        block directions q (directional directions (fun y => A y (f y)) i) n x ≤
          leibnizConvolution (fun k => coefficientBlock directions q A k x)
            (fun k => block directions q (directional directions f i) k x) n +
          leibnizConvolution (fun k => coefficientBlock directions q (directional directions A i) k
              x)
            (fun k => block directions q f k x) n := by
      have he := directional_bilinear directions B A f hA hf i
      change directional directions (fun y => A y (f y)) i =
        (fun y => A y (directional directions f i y)) +
        (fun y => directional directions A i y (f y)) at he
      rw [he]
      exact (block_add_le directions q _ _ (hA.clm_apply (directional_contDiff directions f hf i))
        ((directional_contDiff directions A hA i).clm_apply hf) n x).trans
        (add_le_add (ih A (directional directions f i) hA (directional_contDiff directions f hf i))
          (ih (directional directions A i) f (directional_contDiff directions A hA i) hf))
    apply (sum_le_sum (fun i _ => ht i)).trans_eq
    rw [sum_add_distrib, sum_convolution_right, sum_convolution_left]
    simp_rw [← block_succ directions q f hf, ← coefficientBlock_succ directions q A hA]
    rw [leibnizConvolution_succ]

end EulerParameterWordGevrey
