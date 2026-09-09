/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordProduct
public import LeanPool.NavierStokesAndEuler.Euler.BoundedInverseGevrey

@[expose] public section

/-!
# A genuine inverse recurrence for the unchanged word sums

Freeze the actual left inverse at a parameter value. The coefficient
difference vanishes there, so the direct word-product estimate removes the
top unknown term. The same factorial radius is used for input and output.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Freezing the actual inverse yields the sharp recurrence for actual ordered word sums. -/
theorem inverse_word_recurrence (directions : ι → P)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (I : E →L[ℝ] E) (hI : ∀ v, I (A x v) = v) (n : ℕ) :
    wordSum directions u n x ≤ ‖I‖ *
      (wordSum directions f n x + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * wordSum directions A (j+1) x *
          wordSum directions u (n-(j+1)) x) := by
  let B : P → E →L[ℝ] E := A-fun _ => A x
  have hB : ContDiff ℝ ∞ B := hA.sub contDiff_const
  have hBu : ContDiff ℝ ∞ (fun y => B y (u y)) := hB.clm_apply hu
  have hfreeze : u = I ∘ (f-fun y => B y (u y)) := by
    funext y
    dsimp [B]
    rw [sub_apply, ← heq y, sub_sub_cancel]
    exact (hI (u y)).symm
  have hzero : wordSum directions B 0 x = 0 := by
    rw [wordSum_zero]
    simp only [B, Pi.sub_apply, sub_self, norm_zero]
  have hpos (j : ℕ) : wordSum directions B (j+1) x = wordSum directions A (j+1) x :=
    wordSum_sub_const_succ directions A hA (A x) j x
  have hprod := wordSum_clm_apply_le directions B u hB hu n x
  unfold leibnizConvolution at hprod
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpos] at hprod
  have hbound := wordSum_comp_clm_le directions I (f-fun y => B y (u y)) (hf.sub hBu) n x
  rw [← hfreeze] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    ((wordSum_sub_le directions f (fun y => B y (u y)) hf hBu n x).trans
      (add_le_add le_rfl hprod)) (norm_nonneg I))

/-- The actual inverse maps a word-sum majorant to one higher factorial
shift at the identical radius. All constants are independent of the shift. -/
theorem inverse_word_gevrey (directions : ι → P)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y)
    (inverse : P → E →L[ℝ] E) (hleft : ∀ x v, inverse x (A x v) = v)
    (I C D M Rc R : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : I*C ≤ M) (hMD : I*D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2*M*(Rc+1) ≤ R)
    (hinv : ∀ x, ‖inverse x‖ ≤ I)
    (hcoeff : ∀ j x, wordSum directions A (j+1) x ≤ C*(Rc^(j+1)*((j+1).factorial : ℝ)^2))
    (d : ℕ) (hforce : ∀ n x, wordSum directions f n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) : wordSum directions u n x ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => wordSum directions u k x) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ)*Rc^(j+1)*
    ((j+1).factorial : ℝ)^2*wordSum directions u (k-(j+1)) x
  have hS : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hRc _)) (sq_nonneg _))
    (wordSum_nonneg directions u _ x))
  have hsum : (∑ j ∈ range k, (k.choose (j+1) : ℝ)*wordSum directions A (j+1) x*
      wordSum directions u (k-(j+1)) x) ≤ C*S := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j x) (Nat.cast_nonneg (k.choose (j+1))))
      (wordSum_nonneg directions u (k-(j+1)) x)
    convert h using 1
    ring
  have hrec := inverse_word_recurrence directions A u f hA hu hf heq x (inverse x) (hleft x) k
  have hb : wordSum directions u k x ≤ I*(D*majorant R d k+C*S) := by
    apply hrec.trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (hforce k x) hsum) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hinv x)
        (add_nonneg (mul_nonneg hD (majorant_nonneg R hR0 d k)) (mul_nonneg hC hS)))
  have h₁ := mul_le_mul_of_nonneg_right hMC hS
  have h₂ := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change wordSum directions u k x ≤ M*(majorant R d k+S)
  nlinarith

end EulerParameterWordGevrey
