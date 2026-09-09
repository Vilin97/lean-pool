/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveGevrey
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Measurability.Init

/-!
# Genuine derivative estimates for bounded inverses on normed spaces

The triangular derivative estimate only needs an actual bounded left inverse
of the frozen operator. This form applies to continuous path spaces as well
as Hilbert spaces, without assigning a Hilbert structure to a uniform norm.
-/

@[expose] public section


noncomputable section

namespace EulerBoundedInverseGevrey

open ContinuousLinearMap Finset EulerGevrey EulerHilbertCoerciveGevrey
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual smooth solutions of an invertible operator family satisfy the same
factorial estimate, using the genuine frozen inverse bound. -/
theorem solution_gevrey
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ x, A x (u x) = f x)
    (inverse : P → E →L[ℝ] E) (hleft : ∀ x v, inverse x (A x v) = v)
    (I C D M Rc R : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : I * C ≤ M) (hMD : I * D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2 * M * (Rc + 1) ≤ R)
    (hinverse : ∀ x, ‖inverse x‖ ≤ I)
    (hcoeff : ∀ j x, ‖iteratedFDeriv ℝ (j + 1) A x‖ ≤
      C * (Rc ^ (j + 1) * ((j + 1).factorial : ℝ) ^ 2))
    (d : ℕ) (hforce : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => ‖iteratedFDeriv ℝ k u x‖) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ)*Rc^(j+1) *
    ((j+1).factorial : ℝ)^2*‖iteratedFDeriv ℝ (k-(j+1)) u x‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsum : (∑ j ∈ range k,
      (k.choose (j+1) : ℝ)*‖iteratedFDeriv ℝ (j+1) A x‖*
        ‖iteratedFDeriv ℝ (k-(j+1)) u x‖) ≤ C*S := by
    dsimp [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j x) (by positivity : (0 : ℝ) ≤ k.choose (j+1)))
      (norm_nonneg (iteratedFDeriv ℝ (k-(j+1)) u x))
    convert h using 1
    ring
  have hrec := derivative_recurrence A u f hA hu hf heq x (inverse x) (hleft x) k
  have hb : ‖iteratedFDeriv ℝ k u x‖ ≤ I*(D*majorant R d k+C*S) := by
    apply hrec.trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (hforce k x) hsum) (norm_nonneg (inverse x))).trans
      (mul_le_mul_of_nonneg_right (hinverse x)
        (add_nonneg (mul_nonneg hD (majorant_nonneg R hR0 d k)) (mul_nonneg hC hS)))
  have ha := mul_le_mul_of_nonneg_right hMC hS
  have hf' := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change ‖iteratedFDeriv ℝ k u x‖ ≤ M*(majorant R d k+S)
  nlinarith

end EulerBoundedInverseGevrey
