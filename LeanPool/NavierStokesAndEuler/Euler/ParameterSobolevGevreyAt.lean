/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevrey

@[expose] public section

/-!
# The fixed-Sobolev inverse estimate needs bounds only at its base point

In particular a frozen Duhamel equation has identity as its base operator.
The actual equation and smoothness hold as functions; every quantitative
hypothesis, including invertibility, is needed only at the evaluation point.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem block_inverse_gevrey_at (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y)
    (x : P) (inverse : E →L[ℝ] E) (hleft : ∀ v, inverse (A x v) = v)
    (I B C D M Rc R : ℝ) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : sobolevInverseCost I B q*C ≤ M)
    (hMD : sobolevInverseCost I B q*D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2*M*(Rc+1) ≤ R)
    (hinv : ‖inverse‖ ≤ I) (hbase : baseSize directions q A x ≤ B)
    (hcoeff : ∀ j, coefficientBlock directions q A (j+1) x ≤ C*(Rc^(j+1)*((j+1).factorial : ℝ)^2))
    (d : ℕ) (hforce : ∀ n, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) : block directions q u n x ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := by nlinarith
  have hI : 0 ≤ I := (norm_nonneg inverse).trans hinv
  have hB : 0 ≤ B := (baseSize_nonneg directions q A x).trans hbase
  have hcost := sobolevInverseCost_nonneg I B hI hB q
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => block directions q u k x) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ)*Rc^(j+1)*
    ((j+1).factorial : ℝ)^2*block directions q u (k-(j+1)) x
  have hS : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hRc _)) (sq_nonneg _))
    (block_nonneg directions q u _ x))
  have hsum : (∑ j ∈ range k, (k.choose (j+1) : ℝ)*coefficientBlock directions q A (j+1) x*
      block directions q u (k-(j+1)) x) ≤ C*S := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j) (Nat.cast_nonneg (k.choose (j+1))))
      (block_nonneg directions q u (k-(j+1)) x)
    convert h using 1
    ring
  have hrec := block_inverse_recurrence directions q A u f hA hu hf heq x
    inverse hleft I B hinv hbase k
  have hb : block directions q u k x ≤ sobolevInverseCost I B q*(D*majorant R d k+C*S) :=
    hrec.trans (mul_le_mul_of_nonneg_left (add_le_add (hforce k) hsum) hcost)
  have h₁ := mul_le_mul_of_nonneg_right hMC hS
  have h₂ := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change block directions q u k x ≤ M*(majorant R d k+S)
  nlinarith

end EulerParameterWordGevrey
