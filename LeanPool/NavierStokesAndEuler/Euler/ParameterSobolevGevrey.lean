/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevInverse
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCommutator
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A single-radius inverse estimate in genuine fixed Sobolev blocks

The fixed Sobolev inverse bound is applied to each actual external word.
Its commutator contains only positive external coefficient derivatives.
Consequently the original factorial radius is preserved at every grade.
-/

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
