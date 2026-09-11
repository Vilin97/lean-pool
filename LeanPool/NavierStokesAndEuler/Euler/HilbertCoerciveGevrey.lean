/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoerciveProjection
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual all-order estimates for a coercive inverse

At a parameter value `x`, freeze the inverse of `A x` and write
`u y = (A x)⁻¹ (f y - (A y - A x) (u y))`. The coefficient difference
vanishes at `x`, so differentiating gives a triangular estimate with no
highest-order solution term on the right. The factorial estimate below is
therefore derived from genuine derivatives of the constructed inverse.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerHilbertCoerciveGevrey

open ContinuousLinearMap Finset InnerProductSpace EulerGevrey
  EulerCoerciveProjection EulerHilbertCoerciveParameter

section Normed

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Freezing the coefficient gives the actual triangular derivative bound. -/
theorem derivative_recurrence
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (I : E →L[ℝ] E) (hI : ∀ v, I (A x v) = v) (n : ℕ) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ ‖I‖ *
      (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) A x‖ *
          ‖iteratedFDeriv ℝ (n-(j+1)) u x‖) := by
  let B : P → E →L[ℝ] E := fun y => A y - A x
  have hB : ContDiff ℝ ∞ B := hA.sub contDiff_const
  have hBu : ContDiff ℝ ∞ (fun y => B y (u y)) := hB.clm_apply hu
  have hfreeze : u = I ∘ (fun y => f y - B y (u y)) := by
    funext y
    dsimp [B]
    rw [sub_apply, ← heq y, sub_sub_cancel]
    exact (hI (u y)).symm
  have hzero : ‖iteratedFDeriv ℝ 0 B x‖ = 0 := by
    rw [norm_iteratedFDeriv_zero]
    simp [B]
  have hpositive (j : ℕ) :
      iteratedFDeriv ℝ (j+1) B x = iteratedFDeriv ℝ (j+1) A x := by
    change iteratedFDeriv ℝ (j+1) (A - fun _ => A x) x = _
    rw [iteratedFDeriv_sub_apply (hA.contDiffAt.of_le (by simp)) contDiffAt_const]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
  have hprod := norm_iteratedFDeriv_clm_apply hB hu x (n := n) (by simp)
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpositive] at hprod
  have hsub : ‖iteratedFDeriv ℝ n (fun y => f y - B y (u y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n (fun y => B y (u y)) x‖ := by
    change ‖iteratedFDeriv ℝ n (f - fun y => B y (u y)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp))
      (hBu.contDiffAt.of_le (by simp))]
    exact norm_sub_le _ _
  have hbound := I.norm_iteratedFDeriv_comp_left (x := x)
    ((hf.sub hBu).contDiffAt) (n := n) (by simp)
  rw [← hfreeze] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (hsub.trans (add_le_add (le_refl ‖iteratedFDeriv ℝ n f x‖) hprod)) (norm_nonneg I))

end Normed

section Hilbert

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The recurrence for the actual Lax--Milgram inverse, with its coercivity bound. -/
theorem coerciveSolution_derivative_recurrence
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hcoercive : ∀ x v, c x * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (x : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ n
      (fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)) x‖ ≤
    (c x)⁻¹ * (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
      (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) A x‖ *
        ‖iteratedFDeriv ℝ (n-(j+1))
          (fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)) x‖) := by
  let u := fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)
  have hu : ContDiff ℝ ∞ u := contDiff_coerciveSolution_variable A c hc hcoercive f hA hf
  have hrec := derivative_recurrence A u f hA hu hf
    (fun y => operator_inverse_apply (A y) (c y) (hc y) (hcoercive y) (f y)) x
    (coerciveInverse (A x) (c x) (hc x) (hcoercive x))
    (inverse_operator_apply (A x) (c x) (hc x) (hcoercive x)) n
  exact hrec.trans (mul_le_mul_of_nonneg_right
    (coerciveInverse_norm_le (A x) (c x) (hc x) (hcoercive x)) (by positivity))

/-- A single factorial shift controls every actual derivative of the inverse solve. -/
theorem coerciveSolution_gevrey
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hcoercive : ∀ x v, c x * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hRc : 0 ≤ Rc) (hR : 2 * M * (Rc + 1) ≤ R)
    (hinv : ∀ x, (c x)⁻¹ ≤ M)
    (hcoeff : ∀ j x, ‖iteratedFDeriv ℝ (j + 1) A x‖ ≤
      Rc ^ (j + 1) * ((j + 1).factorial : ℝ) ^ 2)
    (d : ℕ) (hforce : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n
      (fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)) x‖ ≤
        majorant R (d+1) n := by
  let u := fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => ‖iteratedFDeriv ℝ k f x‖)
    (fun k => ‖iteratedFDeriv ℝ k u x‖) (fun k => hforce k x) _ n
  intro k
  have hrec := coerciveSolution_derivative_recurrence A c hc hcoercive f hA hf x k
  have hsum : (∑ j ∈ range k,
      (k.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) A x‖ *
        ‖iteratedFDeriv ℝ (k-(j+1)) u x‖) ≤
      ∑ j ∈ range k, (k.choose (j+1) : ℝ) * Rc^(j+1) *
        ((j+1).factorial : ℝ)^2 * ‖iteratedFDeriv ℝ (k-(j+1)) u x‖ := by
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j x) (by positivity : (0 : ℝ) ≤ k.choose (j+1)))
      (norm_nonneg (iteratedFDeriv ℝ (k-(j+1)) u x))
    simpa only [mul_assoc] using h
  exact hrec.trans ((mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ‖iteratedFDeriv ℝ k f x‖) hsum)
    (inv_nonneg.mpr (hc x).le)).trans
      (mul_le_mul_of_nonneg_right (hinv x) (by positivity)))

/-- Polynomial coefficient and forcing amplitudes enter only the fixed top
constant, not the derivative-order radius. -/
theorem coerciveSolution_gevrey_amplitudes
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hcoercive : ∀ x v, c x * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f : P → E) (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (I C D M Rc R : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : I * C ≤ M) (hMD : I * D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2 * M * (Rc + 1) ≤ R)
    (hinv : ∀ x, (c x)⁻¹ ≤ I)
    (hcoeff : ∀ j x, ‖iteratedFDeriv ℝ (j + 1) A x‖ ≤
      C * (Rc ^ (j + 1) * ((j + 1).factorial : ℝ) ^ 2))
    (d : ℕ) (hforce : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n
      (fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)) x‖ ≤
        majorant R (d+1) n := by
  let u := fun y => coerciveInverse (A y) (c y) (hc y) (hcoercive y) (f y)
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => ‖iteratedFDeriv ℝ k u x‖) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ) * Rc^(j+1) *
    ((j+1).factorial : ℝ)^2 * ‖iteratedFDeriv ℝ (k-(j+1)) u x‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsum : (∑ j ∈ range k,
      (k.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) A x‖ *
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
  have hrec := coerciveSolution_derivative_recurrence A c hc hcoercive f hA hf x k
  have hb : ‖iteratedFDeriv ℝ k u x‖ ≤ I * (D * majorant R d k + C*S) := by
    apply hrec.trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (hforce k x) hsum)
      (inv_nonneg.mpr (hc x).le)).trans
      (mul_le_mul_of_nonneg_right (hinv x)
        (add_nonneg (mul_nonneg hD (majorant_nonneg R hR0 d k)) (mul_nonneg hC hS)))
  have ha := mul_le_mul_of_nonneg_right hMC hS
  have hf' := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change ‖iteratedFDeriv ℝ k u x‖ ≤ M * (majorant R d k + S)
  nlinarith

end Hilbert

end EulerHilbertCoerciveGevrey
