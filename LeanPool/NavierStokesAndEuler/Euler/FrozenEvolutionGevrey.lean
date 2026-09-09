/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Differentiating a genuine frozen-evolution identity

This calculus lemma applies to actual bounded initial-data and Green operators.
The coefficient difference vanishes at the base point, so the resulting
binomial recurrence contains only lower solution derivatives on the right.
-/

@[expose] public section


noncomputable section

namespace EulerFrozenEvolutionGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The triangular recurrence is derived from actual Fréchet derivatives of
the frozen equation; it is not an assumed sequence estimate. -/
theorem derivative_recurrence
    (B : P → X →L[ℝ] X) (u f : P → X) (a : P → E)
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (ha : ContDiff ℝ ∞ a)
    (x : P) (H : E →L[ℝ] X) (K : X →L[ℝ] X)
    (heq : ∀ y, u y = H (a y) + K (f y + (B y - B x) (u y))) (n : ℕ) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ ‖H‖*‖iteratedFDeriv ℝ n a x‖ + ‖K‖*
      (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) B x‖ *
          ‖iteratedFDeriv ℝ (n-(j+1)) u x‖) := by
  let C : P → X →L[ℝ] X := fun y => B y-B x
  let p : P → X := fun y => C y (u y)
  let q : P → X := f+p
  have hC : ContDiff ℝ ∞ C := hB.sub contDiff_const
  have hp : ContDiff ℝ ∞ p := hC.clm_apply hu
  have hq : ContDiff ℝ ∞ q := hf.add hp
  have hfreeze : u = (H ∘ a) + (K ∘ q) := funext heq
  have hzero : ‖iteratedFDeriv ℝ 0 C x‖ = 0 := by
    rw [norm_iteratedFDeriv_zero]
    simp [C]
  have hpositive (j : ℕ) : iteratedFDeriv ℝ (j+1) C x = iteratedFDeriv ℝ (j+1) B x := by
    change iteratedFDeriv ℝ (j+1) (B - fun _ => B x) x = _
    rw [iteratedFDeriv_sub_apply (hB.contDiffAt.of_le (by simp)) contDiffAt_const]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
  have hprod := norm_iteratedFDeriv_clm_apply hC hu x (n := n) (by simp)
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpositive] at hprod
  have hqnorm : ‖iteratedFDeriv ℝ n q x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n p x‖ := by
    change ‖iteratedFDeriv ℝ n (f+p) x‖ ≤ _
    rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by simp)) (hp.contDiffAt.of_le (by simp))]
    exact norm_add_le _ _
  have hH := H.norm_iteratedFDeriv_comp_left (x := x) ha.contDiffAt (n := n) (by simp)
  have hK := K.norm_iteratedFDeriv_comp_left (x := x) hq.contDiffAt (n := n) (by simp)
  have hsum : ‖iteratedFDeriv ℝ n u x‖ ≤
      ‖iteratedFDeriv ℝ n (H ∘ a) x‖ + ‖iteratedFDeriv ℝ n (K ∘ q) x‖ := by
    conv_lhs => rw [hfreeze]
    rw [iteratedFDeriv_add_apply ((H.contDiff.comp ha).contDiffAt.of_le (by simp))
      ((K.contDiff.comp hq).contDiffAt.of_le (by simp))]
    exact norm_add_le _ _
  exact hsum.trans (add_le_add hH (hK.trans (mul_le_mul_of_nonneg_left
    (hqnorm.trans (add_le_add le_rfl hprod)) (norm_nonneg K))))

end EulerFrozenEvolutionGevrey
