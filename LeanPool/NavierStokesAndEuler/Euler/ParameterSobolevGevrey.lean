/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordProduct

/-!
# A single-radius inverse estimate in genuine fixed Sobolev blocks

The fixed Sobolev inverse bound is applied to each actual external word.
Its commutator contains only positive external coefficient derivatives.
Consequently the original factorial radius is preserved at every grade.
-/

section

/-!
# Positive external-order commutators in actual fixed Sobolev blocks

The commutator is an explicit difference of genuine derivatives and the
undifferentiated coefficient action. Its direct word recurrence places at
least one external derivative on the coefficient in every term.
-/

@[expose] public section

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
  wordDerivative directions (fun y => A y (f y)) w -
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
      wordCommutator directions A (directional directions f i) w +
        wordDerivative directions (fun y => directional directions A i y (f y)) w := by
  have hprod := directional_bilinear directions ((ContinuousLinearMap.apply ℝ F).flip) A f hA hf i
  change directional directions (fun y => A y (f y)) i =
    (fun y => A y (directional directions f i y)) +
    (fun y => directional directions A i y (f y)) at hprod
  funext x
  change wordDerivative directions (fun y => A y (f y)) (Fin.snoc w i) x -
      A x (wordDerivative directions f (Fin.snoc w i) x) =
    (wordDerivative directions (fun y => A y (directional directions f i y)) w x -
      A x (wordDerivative directions (directional directions f i) w x)) +
    wordDerivative directions (fun y => directional directions A i y (f y)) w x
  rw [wordDerivative_snoc directions _ (hA.clm_apply hf), wordDerivative_snoc directions f hf,
    hprod, wordDerivative_add directions _ _
      (hA.clm_apply (directional_contDiff directions f hf i))
      ((directional_contDiff directions A hA i).clm_apply hf)]
  abel

/-- Commutator block, given by `∑ w : Fin n → ι, baseSize directions q (wordCommutator
directions A f w) x`. -/
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
      ∑ i, (commutatorBlock directions q A (directional directions f i) n x +
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
  | zero =>
      simp only [commutatorBlock_zero, commutatorConvolution_eq_sum, range_zero, sum_empty, le_refl]
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem block_inverse_bound (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (inverse : E →L[ℝ] E) (hleft : ∀ v, inverse (A x v) = v)
    (I B : ℝ) (hinv : ‖inverse‖ ≤ I) (hbase : baseSize directions q A x ≤ B)
    (n : ℕ) :
    block directions q u n x ≤ sobolevInverseCost I B q *
      (block directions q f n x+commutatorBlock directions q A u n x) := by
  have hI : 0 ≤ I := (norm_nonneg inverse).trans hinv
  have hB : 0 ≤ B := (baseSize_nonneg directions q A x).trans hbase
  have hcost : 0 ≤ sobolevInverseCost I B q := sobolevInverseCost_nonneg I B hI hB q
  have hfun : (fun y => A y (u y)) = f := funext heq
  have hw (w : Fin n → ι) : baseSize directions q (wordDerivative directions u w) x ≤
      sobolevInverseCost I B q*(baseSize directions q (wordDerivative directions f w) x +
        baseSize directions q (wordCommutator directions A u w) x) := by
    let g := wordDerivative directions f w-wordCommutator directions A u w
    have hg : ContDiff ℝ ∞ g := (wordDerivative_contDiff directions f hf w).sub
      (wordCommutator_contDiff directions A u hA hu w)
    have he (y : P) : A y (wordDerivative directions u w y) = g y := by
      change A y (wordDerivative directions u w y) = wordDerivative directions f w y -
        (wordDerivative directions (fun z => A z (u z)) w y-A y (wordDerivative directions u w y))
      rw [hfun]
      abel
    exact (baseSize_inverse_bound directions A hA x inverse hleft I B hinv q
      (wordDerivative directions u w) g (wordDerivative_contDiff directions u hu w) hg he
          hbase).trans
      (mul_le_mul_of_nonneg_left (baseSize_sub_le directions q _ _
        (wordDerivative_contDiff directions f hf w) (wordCommutator_contDiff directions A u hA hu
            w) x) hcost)
  calc
    _ ≤ ∑ w : Fin n → ι, sobolevInverseCost I B q *
        (baseSize directions q (wordDerivative directions f w) x +
          baseSize directions q (wordCommutator directions A u w) x) :=
      sum_le_sum (fun w _ => hw w)
    _ = _ := by rw [← mul_sum, sum_add_distrib]; rfl

/-- Genuine fixed-Sobolev external-word recurrence with the computed base inverse constant. -/
theorem block_inverse_recurrence (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (inverse : E →L[ℝ] E) (hleft : ∀ v, inverse (A x v) = v)
    (I B : ℝ) (hinv : ‖inverse‖ ≤ I) (hbase : baseSize directions q A x ≤ B)
    (n : ℕ) :
    block directions q u n x ≤ sobolevInverseCost I B q *
      (block directions q f n x+∑ j ∈ range n,
        (n.choose (j+1) : ℝ)*coefficientBlock directions q A (j+1) x *
          block directions q u (n-(j+1)) x) := by
  have hI : 0 ≤ I := (norm_nonneg inverse).trans hinv
  have hB : 0 ≤ B := (baseSize_nonneg directions q A x).trans hbase
  have h := (block_inverse_bound directions q A u f hA hu hf heq x inverse hleft I B hinv hbase
      n).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (commutatorBlock_bound directions q A u hA hu n
        x))
      (sobolevInverseCost_nonneg I B hI hB q))
  simpa only [commutatorConvolution_eq_sum] using h

/-- One factorial shift in fixed Hq, using the identical input and output
radius and constants independent of the input shift and external order. -/
theorem block_inverse_gevrey (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y)
    (inverse : P → E →L[ℝ] E) (hleft : ∀ x v, inverse x (A x v) = v)
    (I B C D M Rc R : ℝ) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : sobolevInverseCost I B q * C ≤ M)
    (hMD : sobolevInverseCost I B q * D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2 * M * (Rc + 1) ≤ R)
    (hinv : ∀ x, ‖inverse x‖ ≤ I) (hbase : ∀ x, baseSize directions q A x ≤ B)
    (hcoeff : ∀ j x, coefficientBlock directions q A (j + 1) x ≤ C * (Rc ^ (j + 1) * ((j +
        1).factorial : ℝ) ^ 2))
    (d : ℕ) (hforce : ∀ n x, block directions q f n x ≤ D * majorant R d n)
    (n : ℕ) (x : P) : block directions q u n x ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := by nlinarith
  have hI : 0 ≤ I := (norm_nonneg (inverse x)).trans (hinv x)
  have hB : 0 ≤ B := (baseSize_nonneg directions q A x).trans (hbase x)
  have hcost := sobolevInverseCost_nonneg I B hI hB q
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => block directions q u k x) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ)*Rc^(j+1) *
    ((j+1).factorial : ℝ)^2*block directions q u (k-(j+1)) x
  have hS : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hRc _)) (sq_nonneg _))
    (block_nonneg directions q u _ x))
  have hsum : (∑ j ∈ range k, (k.choose (j+1) : ℝ)*coefficientBlock directions q A (j+1) x *
      block directions q u (k-(j+1)) x) ≤ C*S := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j x) (Nat.cast_nonneg (k.choose (j+1))))
      (block_nonneg directions q u (k-(j+1)) x)
    convert h using 1
    ring
  have hrec := block_inverse_recurrence directions q A u f hA hu hf heq x
    (inverse x) (hleft x) I B (hinv x) (hbase x) k
  have hb : block directions q u k x ≤ sobolevInverseCost I B q*(D*majorant R d k+C*S) :=
    hrec.trans (mul_le_mul_of_nonneg_left (add_le_add (hforce k x) hsum) hcost)
  have h₁ := mul_le_mul_of_nonneg_right hMC hS
  have h₂ := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change block directions q u k x ≤ M*(majorant R d k+S)
  nlinarith

end EulerParameterWordGevrey
