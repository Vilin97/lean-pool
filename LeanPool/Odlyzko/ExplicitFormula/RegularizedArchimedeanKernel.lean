/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.ArchimedeanKernel
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPrimePowerSeriesIntegral

/-!
# Regularized Archimedean Kernel

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Real

namespace NumberField.Odlyzko

theorem exp_sub_poitouKernel_mul_exp_neg_half_div_eq_inverseGaussKernel
    (f : ℝ → ℝ) {x : ℝ} (_hx : 0 < x) :
    (Real.exp (-x) -
        poitouKernel f x * Real.exp (-x / 2)) /
        (1 - Real.exp (-x)) =
      inverseGaussKernel f x := by
  have hexphalf : Real.exp (x / 2) ≠ 0 := Real.exp_ne_zero _
  have hcosh :
      Real.cosh (x / 2) =
        (Real.exp x + 1) / (2 * Real.exp (x / 2)) := by
    rw [Real.cosh_eq, Real.exp_neg]
    have hsquare : Real.exp (x / 2) ^ 2 = Real.exp x := by
      calc
        Real.exp (x / 2) ^ 2 =
            Real.exp (x / 2) * Real.exp (x / 2) := pow_two _
        _ = Real.exp (x / 2 + x / 2) := (Real.exp_add _ _).symm
        _ = Real.exp x := by simp
    grind
  unfold poitouKernel inverseGaussKernel
  rw [hcosh]
  have hexpneghalf :
      Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
    rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  grind

theorem exp_sub_regularizedPoitouKernel_mul_exp_neg_half_div
    (y δ : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) -
        poitouKernel (regularizedScaledTartar y δ) x *
          Real.exp (-x / 2)) /
        (1 - Real.exp (-x)) =
      inverseGaussKernel (regularizedScaledTartar y δ) x :=
  exp_sub_poitouKernel_mul_exp_neg_half_div_eq_inverseGaussKernel
    (regularizedScaledTartar y δ) hx

end NumberField.Odlyzko
