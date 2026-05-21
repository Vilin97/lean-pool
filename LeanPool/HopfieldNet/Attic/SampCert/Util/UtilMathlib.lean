/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
/-!
# Mathlib Util

This file contains a lemma which was in Mathlib at one point, but was removed.
-/


open Complex Real Asymptotics Filter Topology

open scoped Real BigOperators UpperHalfPlane

theorem exists_summable_bound_exp_mul_sq {R : ℝ} (hR : 0 < R) :
    ∃ bd : ℤ → ℝ, Summable bd ∧ ∀ {τ : ℂ} (_ : R ≤ τ.im) (n : ℤ),
      ‖cexp (π * I * (n : ℂ) ^ 2 * τ)‖ ≤ bd n := by
  let y := rexp (-π * R)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR)
  refine' ⟨fun n => y ^ n.natAbs, Summable.of_nat_of_neg _ _, fun hτ n => _⟩; pick_goal 3
  · refine' (norm_exp_mul_sq_le (hR.trans_le hτ) n).trans _
    dsimp
    have Y : y = rexp (-π * R) := rfl
    rw [Y]
    gcongr rexp ?_ ^ _
    rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos)]
  all_goals
    simpa only [Int.natAbs_neg, Int.natAbs_ofNat] using
      summable_geometric_of_lt_one (Real.exp_pos _).le h

theorem summable_exp_mul_sq {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * τ) :=
  let ⟨_, h, h'⟩ := exists_summable_bound_exp_mul_sq hτ
  .of_norm_bounded _ h (h' <| le_refl _)
