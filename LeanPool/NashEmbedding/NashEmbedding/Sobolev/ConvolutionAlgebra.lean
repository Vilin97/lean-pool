/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.FourierSynthesis
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationSharp
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Resolvent

/-!
# Algebra of coefficient convolution, and conjugate reflection

`seqConv a b m = ∑' i, a i * b (m - i)` is the multiplication of periodic functions on
the momentum side. This file records:

* **bilinearity and commutativity** of `seqConv`, under the summability guaranteed by
  `a, b ∈ H^s` with `2s > n` (`seqConv_summable`); commutativity and the zero laws are
  unconditional (`tsum` reindexing along `i ↦ m - i`);
* the **conjugate reflection** `conjReflect a m = conj (a (-m))`, which fixes exactly the
  coefficient sequences of real-valued functions. It commutes with `seqConv`,
  `partialCoeff`, `resolventCoeff`, preserves `H^s` and its norm, and the Fourier synthesis
  of a `conjReflect`-fixed absolutely summable sequence is real-valued.

The Günther operator is built from these operations, so it preserves `conjReflect`-fixed
sequences; this is how the fixed point of Theorem B is seen to be real (`ℝᴺ`-valued).
-/

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Unconditional identities -/

lemma seqConv_comm (a b : (Fin n → ℤ) → ℂ) : seqConv a b = seqConv b a := by
  funext m
  unfold seqConv
  rw [← (Equiv.subLeft m).tsum_eq (fun i => b i * a (m - i))]
  refine tsum_congr fun i => ?_
  simp [Equiv.subLeft_apply, mul_comm]

lemma seqConv_zero_left (b : (Fin n → ℤ) → ℂ) : seqConv (fun _ => (0 : ℂ)) b = fun _ => 0 := by
  funext m; simp [seqConv]

lemma seqConv_zero_right (a : (Fin n → ℤ) → ℂ) : seqConv a (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext m; simp [seqConv]

lemma seqConv_smul_left (c : ℂ) (a b : (Fin n → ℤ) → ℂ) :
    seqConv (fun m => c * a m) b = fun m => c * seqConv a b m := by
  funext m
  simp only [seqConv, mul_assoc]
  exact tsum_mul_left

lemma seqConv_smul_right (c : ℂ) (a b : (Fin n → ℤ) → ℂ) :
    seqConv a (fun m => c * b m) = fun m => c * seqConv a b m := by
  funext m
  simp only [seqConv, mul_left_comm]
  exact tsum_mul_left

lemma seqConv_neg_left (a b : (Fin n → ℤ) → ℂ) :
    seqConv (fun m => -a m) b = fun m => -seqConv a b m := by
  funext m
  simp only [seqConv, neg_mul]
  exact tsum_neg

/-! ## Additivity under summability -/

lemma seqConv_add_left {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a a' b : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (ha' : MemSobolev n s a')
    (hb : MemSobolev n s b) :
    seqConv (fun m => a m + a' m) b = fun m => seqConv a b m + seqConv a' b m := by
  funext m
  simp only [seqConv, add_mul]
  exact (seqConv_summable hn hs ha hb m).tsum_add (seqConv_summable hn hs ha' hb m)

lemma seqConv_add_right {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b b' : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (hb' : MemSobolev n s b') :
    seqConv a (fun m => b m + b' m) = fun m => seqConv a b m + seqConv a b' m := by
  funext m
  simp only [seqConv, mul_add]
  exact (seqConv_summable hn hs ha hb m).tsum_add (seqConv_summable hn hs ha hb' m)

lemma seqConv_sub_left {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a a' b : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (ha' : MemSobolev n s a')
    (hb : MemSobolev n s b) :
    seqConv (fun m => a m - a' m) b = fun m => seqConv a b m - seqConv a' b m := by
  funext m
  simp only [seqConv, sub_mul]
  exact (seqConv_summable hn hs ha hb m).tsum_sub (seqConv_summable hn hs ha' hb m)

lemma seqConv_sub_right {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b b' : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (hb' : MemSobolev n s b') :
    seqConv a (fun m => b m - b' m) = fun m => seqConv a b m - seqConv a b' m := by
  funext m
  simp only [seqConv, mul_sub]
  exact (seqConv_summable hn hs ha hb m).tsum_sub (seqConv_summable hn hs ha hb' m)

lemma seqConv_finset_sum_left {ι : Type*} {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ} {b : (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, MemSobolev n s (a i)) (hb : MemSobolev n s b) :
    seqConv (fun m => ∑ i ∈ S, a i m) b = fun m => ∑ i ∈ S, seqConv (a i) b m := by
  funext m
  simp only [seqConv, Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun i hi => seqConv_summable hn hs (ha i hi) hb m)

/-! ## Conjugate reflection -/

/-- `conjReflect a m = conj (a (-m))`. The coefficient sequence of a function `f` is
`conjReflect`-fixed iff `f` is real-valued. -/
def conjReflect (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ := conj (a (-m))

lemma conjReflect_conjReflect (a : (Fin n → ℤ) → ℂ) : conjReflect (conjReflect a) = a := by
  funext m; simp [conjReflect]

lemma norm_conjReflect (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    ‖conjReflect a m‖ = ‖a (-m)‖ := by
  simp [conjReflect]

lemma MemSobolev.conjReflect {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    MemSobolev n s (NashEmbedding.Sobolev.conjReflect a) := by
  have h : (fun m : Fin n → ℤ => weight n s m * ‖NashEmbedding.Sobolev.conjReflect a m‖ ^ 2)
      = (fun m : Fin n → ℤ => weight n s m * ‖a m‖ ^ 2) ∘ (Equiv.neg (Fin n → ℤ)) := by
    funext m
    simp [NashEmbedding.Sobolev.conjReflect, weight_neg]
  unfold MemSobolev
  rw [h]
  exact (Equiv.neg (Fin n → ℤ)).summable_iff.mpr ha

lemma sobolevNormSq_conjReflect (s : ℝ) (a : (Fin n → ℤ) → ℂ) :
    sobolevNormSq n s (conjReflect a) = sobolevNormSq n s a := by
  unfold sobolevNormSq
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun m => weight n s m * ‖a m‖ ^ 2)]
  refine tsum_congr fun m => ?_
  simp [conjReflect, weight_neg]

lemma conjReflect_add (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => a m + b m) = fun m => conjReflect a m + conjReflect b m := by
  funext m; simp [conjReflect]

lemma conjReflect_sub (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => a m - b m) = fun m => conjReflect a m - conjReflect b m := by
  funext m; simp [conjReflect]

lemma conjReflect_real_smul (c : ℝ) (a : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => (c : ℂ) * a m) = fun m => (c : ℂ) * conjReflect a m := by
  funext m; simp [conjReflect]

lemma conjReflect_finset_sum {ι : Type*} (S : Finset ι) (a : ι → (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => ∑ i ∈ S, a i m) = fun m => ∑ i ∈ S, conjReflect (a i) m := by
  funext m; simp [conjReflect, map_sum]

lemma conjReflect_seqConv (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (seqConv a b) = seqConv (conjReflect a) (conjReflect b) := by
  funext m
  simp only [conjReflect, seqConv]
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun i => conj (a i * b (-m - i)))]
  refine tsum_congr fun i => ?_
  simp only [Equiv.neg_apply, map_mul, neg_sub_neg, neg_sub]

lemma conjReflect_partialCoeff (j : Fin n) (a : (Fin n → ℤ) → ℂ) :
    conjReflect (partialCoeff j a) = partialCoeff j (conjReflect a) := by
  funext m
  simp [conjReflect, partialCoeff, Complex.conj_I]

lemma conjReflect_resolventCoeff (a : (Fin n → ℤ) → ℂ) :
    conjReflect (resolventCoeff a) = resolventCoeff (conjReflect a) := by
  funext m
  simp [conjReflect, resolventCoeff, map_div₀]

lemma conjReflect_laplacianCoeff (a : (Fin n → ℤ) → ℂ) :
    conjReflect (laplacianCoeff a) = laplacianCoeff (conjReflect a) := by
  funext m
  simp [conjReflect, laplacianCoeff]

/-- The Fourier synthesis of a `conjReflect`-fixed sequence is real-valued (no summability
is needed: `conj` commutes with `tsum` unconditionally). -/
theorem fourierSynthesis_im_eq_zero {a : (Fin n → ℤ) → ℂ}
    (hfix : conjReflect a = a) (θ : Fin n → ℝ) : (fourierSynthesis n a θ).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold fourierSynthesis
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun m => a m * fourierExp n m θ)]
  refine tsum_congr fun m => ?_
  have hm : conj (a m) = a (-m) := by
    have := congrFun hfix (-m)
    simpa [conjReflect] using this
  have he : conj (fourierExp n m θ) = fourierExp n (-m) θ := by
    unfold fourierExp
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I, Finset.sum_neg_distrib]
  simp only [Equiv.neg_apply, map_mul, hm, he]

end NashEmbedding.Sobolev

end
