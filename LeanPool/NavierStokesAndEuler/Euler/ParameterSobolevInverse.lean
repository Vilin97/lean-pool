/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks

@[expose] public section

/-!
# The actual inverse estimate at a fixed Sobolev order

Differentiate the genuine equation once at each of finitely many base
indices. The resulting constant is a fixed polynomial recursion in the
ordinary inverse norm and the finite coefficient-jet bound. It does not
depend on any external derivative order or factorial shift.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

/-- A fixed finite recursion of polynomial base-order inverse constants. -/
def sobolevInverseCost (I B : ℝ) : ℕ → ℝ
  | 0 => I
  | q+1 => I+sobolevInverseCost I B q+(2 : ℝ)^q*B*(sobolevInverseCost I B q)^2

theorem sobolevInverseCost_nonneg (I B : ℝ) (hI : 0 ≤ I) (hB : 0 ≤ B) (q : ℕ) :
    0 ≤ sobolevInverseCost I B q := by
  induction q with
  | zero => exact hI
  | succ q ih => simp only [sobolevInverseCost]; positivity

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Fixed-order Sobolev boundedness of an actual inverse equation.
Every derivative is an ordinary derivative of the original smooth functions. -/
theorem baseSize_inverse_bound (directions : ι → P)
    (A : P → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (x : P)
    (inverse : E →L[ℝ] E) (hleft : ∀ v, inverse (A x v) = v)
    (I B : ℝ) (hinv : ‖inverse‖ ≤ I) :
    ∀ (q : ℕ) (u f : P → E), ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      (∀ y, A y (u y) = f y) → baseSize directions q A x ≤ B →
      baseSize directions q u x ≤ sobolevInverseCost I B q*baseSize directions q f x := by
  have hI : 0 ≤ I := (norm_nonneg inverse).trans hinv
  intro q
  induction q with
  | zero =>
    intro u f _ _ heq _
    rw [baseSize_zero, baseSize_zero, sobolevInverseCost]
    have he : u x = inverse (f x) := by rw [← heq x, hleft]
    rw [he]
    exact (inverse.le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  | succ q ih =>
    intro u f hu hf heq hAb
    have hB : 0 ≤ B := (baseSize_nonneg directions (q+1) A x).trans hAb
    let C := sobolevInverseCost I B q
    let N := baseSize directions (q+1) f x
    have hC : 0 ≤ C := sobolevInverseCost_nonneg I B hI hB q
    have hN : 0 ≤ N := baseSize_nonneg directions (q+1) f x
    have hAbq : baseSize directions q A x ≤ B :=
      (baseSize_mono directions A x (Nat.le_succ q)).trans hAb
    have huq : baseSize directions q u x ≤ C*N :=
      (ih u f hu hf heq hAbq).trans
        (mul_le_mul_of_nonneg_left (baseSize_mono directions f x (Nat.le_succ q)) hC)
    have hzero : ‖u x‖ ≤ I*N := by
      have he : u x = inverse (f x) := by rw [← heq x, hleft]
      rw [he]
      exact (inverse.le_opNorm (f x)).trans
        (mul_le_mul hinv (norm_le_baseSize directions (q+1) f x) (norm_nonneg _) hI)
    have hdf : (∑ i, baseSize directions q (directional directions f i) x) ≤ N := by
      have h := baseSize_succ directions q f hf x
      change baseSize directions (q+1) f x = _ at h
      dsimp only [N]
      linarith [norm_nonneg (f x)]
    have hdA : (∑ i, baseSize directions q (directional directions A i) x) ≤ B := by
      have h := baseSize_succ directions q A hA x
      linarith [norm_nonneg (A x)]
    have hdi (i : ι) : baseSize directions q (directional directions u i) x ≤
        C*(baseSize directions q (directional directions f i) x+
          (2 : ℝ)^q*baseSize directions q (directional directions A i) x*baseSize directions q u x)
            := by
      let fᵢ := directional directions f i-fun y => directional directions A i y (u y)
      have hfᵢ : ContDiff ℝ ∞ fᵢ := (directional_contDiff directions f hf i).sub
        ((directional_contDiff directions A hA i).clm_apply hu)
      have heqᵢ (y : P) : A y (directional directions u i y) = fᵢ y := by
        change A y (directional directions u i y) =
          directional directions f i y-directional directions A i y (u y)
        apply eq_sub_iff_add_eq.mpr
        have hd := congrFun (directional_bilinear directions
          ((ContinuousLinearMap.apply ℝ E).flip) A u hA hu i) y
        have he := congrArg (fun g : P → E => directional directions g i y) (funext heq)
        exact hd.symm.trans he
      have h := ih (directional directions u i) fᵢ (directional_contDiff directions u hu i) hfᵢ
        heqᵢ hAbq
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact (baseSize_sub_le directions q (directional directions f i)
        (fun y => directional directions A i y (u y)) (directional_contDiff directions f hf i)
        ((directional_contDiff directions A hA i).clm_apply hu) x).trans
        (add_le_add le_rfl (baseSize_clm_apply_le directions q (directional directions A i) u
          (directional_contDiff directions A hA i) hu x))
    have hsum : (∑ i, baseSize directions q (directional directions u i) x) ≤
        C*(N+(2 : ℝ)^q*B*(C*N)) := by
      calc
        _ ≤ ∑ i, C*(baseSize directions q (directional directions f i) x+
            (2 : ℝ)^q*baseSize directions q (directional directions A i) x*baseSize directions q u
              x) :=
          sum_le_sum (fun i _ => hdi i)
        _ = C*((∑ i, baseSize directions q (directional directions f i) x)+
            (2 : ℝ)^q*(∑ i, baseSize directions q (directional directions A i) x)*baseSize
              directions q u x) := by
          simp only [← mul_sum, sum_add_distrib, ← sum_mul]
        _ ≤ C*(N+(2 : ℝ)^q*B*(C*N)) := by
          gcongr
          exact baseSize_nonneg directions q u x
    rw [baseSize_succ directions q u hu x]
    calc
      _ ≤ I*N+C*(N+(2 : ℝ)^q*B*(C*N)) := add_le_add hzero hsum
      _ = sobolevInverseCost I B (q+1)*baseSize directions (q+1) f x := by
        simp only [sobolevInverseCost, C, N]
        ring

end EulerParameterWordGevrey
