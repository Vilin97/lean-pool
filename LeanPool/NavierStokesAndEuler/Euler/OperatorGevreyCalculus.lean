/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Factorial bounds for genuine operator-valued derivatives

These estimates use actual iterated Fréchet derivatives and bounded linear or
bilinear maps. They transfer coefficient bounds to the time multipliers,
transported variational forms, and right sides of the constructed inverses.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerOperatorGevreyCalculus

open ContinuousLinearMap EulerGevrey EulerTransverseGramInverse

/-- Enlarging the radius enlarges the factorial majorant. -/
theorem majorant_radius_mono (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) (d n : ℕ) :
    majorant R d n ≤ majorant S d n := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRS (n+d)) (sq_nonneg _)

section Normed

variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A constant field satisfies the order-zero multiplier bound. -/
theorem const_bound (v : E) (R C : ℝ) (hR : 0 ≤ R) (hv : ‖v‖ ≤ C)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun _ : P => v) x‖ ≤ C * majorant R 0 n := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero,
      pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hv
  | succ n =>
    rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact mul_nonneg ((norm_nonneg v).trans hv) (majorant_nonneg R hR 0 (n+1))

/-- Bounded linear maps preserve every factorial shift. -/
theorem linear_bound (L : E →L[ℝ] F) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (R A : ℝ) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => L (f y)) x‖ ≤ (‖L‖*A) * majorant R d n := by
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n x) (norm_nonneg L))

/-- A linear contraction does not enlarge a factorial multiplier constant. -/
theorem contraction_bound (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (f : P → E) (hf : ContDiff ℝ ∞ f)
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => L (f y)) x‖ ≤ A * majorant R d n := by
  apply (linear_bound L f hf R A d hb n x).trans
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hA)
    (majorant_nonneg R hR d n)

/-- The shifted product bound for any bilinear contraction. -/
theorem bilinear_bound (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (f : P → E) (g : P → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (d e : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R d n)
    (hc : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ C * majorant R e n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      (3*A*C) * majorant R (d+e) n := by
  have hp := sequence_product_majorant R A C hR hA hC d e
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb k x)
    (fun k => by simpa only [abs_norm] using hc k x) n
  exact (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x (by simp) hB).trans
    ((le_abs_self _).trans (by simpa using hp))

/-- Actual operator application has the shifted factorial product bound. -/
theorem clm_apply_bound (A : P → E →L[ℝ] F) (u : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d e : ℕ)
    (hcoeff : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (hfield : ∀ n x, ‖iteratedFDeriv ℝ n u x‖ ≤ D * majorant R e n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => A y (u y)) x‖ ≤
      (3*C*D) * majorant R (d+e) n :=
  bilinear_bound (ContinuousLinearMap.id ℝ (E →L[ℝ] F)) norm_id_le
    A u hA hu R C D hR hC hD d e hcoeff hfield n x

/-- Composition of actual parameterized operators has the same product bound. -/
theorem clm_comp_bound (A : P → F →L[ℝ] G) (B : P → E →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d e : ℕ)
    (hcoeff : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (hfield : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ D * majorant R e n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => (A y).comp (B y)) x‖ ≤
      (3*C*D) * majorant R (d+e) n :=
  bilinear_bound (ContinuousLinearMap.compL ℝ E F G) (norm_compL_le ℝ E F G)
    A B hA hB R C D hR hC hD d e hcoeff hfield n x

/-- Adding actual jets adds the multiplier constants. -/
theorem add_bound (f g : P → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (d : ℕ)
    (ha : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R d n)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤ (A+B) * majorant R d n := by
  rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (ha n x) (hb n x))

/-- Subtracting actual jets adds the multiplier constants. -/
theorem sub_bound (f g : P → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (d : ℕ)
    (ha : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R d n)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => f y - g y) x‖ ≤ (A+B) * majorant R d n := by
  change ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  exact (norm_sub_le _ _).trans (by simpa only [add_mul] using add_le_add (ha n x) (hb n x))

/-- Composition with a fixed operator on the right costs its operator norm. -/
theorem clm_comp_const_right_bound (A : P → F →L[ℝ] G) (B : E →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => (A y).comp B) x‖ ≤ (‖B‖*C) * majorant R d n := by
  let L : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) := (compL ℝ E F G).flip B
  have hL : ‖L‖ ≤ ‖B‖ := by
    apply opNorm_le_bound _ (norm_nonneg B)
    intro a
    exact (opNorm_comp_le a B).trans_eq (mul_comm _ _)
  exact (linear_bound L A hA R C d hb n x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hC) (majorant_nonneg R hR d n))

/-- Composition with a fixed operator on the left costs its operator norm. -/
theorem clm_comp_const_left_bound (A : F →L[ℝ] G) (B : P → E →L[ℝ] F)
    (hB : ContDiff ℝ ∞ B) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => A.comp (B y)) x‖ ≤ (‖A‖*C) * majorant R d n := by
  let L : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] G) := compL ℝ E F G A
  have hL : ‖L‖ ≤ ‖A‖ := by
    apply opNorm_le_bound _ (norm_nonneg A)
    intro b
    exact opNorm_comp_le A b
  exact (linear_bound L B hB R C d hb n x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hC) (majorant_nonneg R hR d n))

/-- Negating a field leaves all factorial bounds unchanged. -/
theorem neg_bound (f : P → E) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => -f y) x‖ ≤ C * majorant R d n := by
  change ‖iteratedFDeriv ℝ n (-f) x‖ ≤ _
  simpa only [iteratedFDeriv_neg_apply, norm_neg] using hb n x

end Normed

section Hilbert

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking the actual Hilbert adjoint preserves the multiplier constant. -/
theorem adjoint_bound (A : P → U →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => (A y).adjoint) x‖ ≤ C * majorant R d n := by
  have hL : ‖realAdjoint (U := U) (E := E)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro a
    change ‖a.adjoint‖ ≤ 1 * ‖a‖
    simp only [LinearIsometryEquiv.norm_map, one_mul, le_refl]
  exact contraction_bound (P := P) (E := U →L[ℝ] E) (F := E →L[ℝ] U)
    (realAdjoint (U := U) (E := E)) hL A hA R C hR hC d hb n x

end Hilbert

end EulerOperatorGevreyCalculus
