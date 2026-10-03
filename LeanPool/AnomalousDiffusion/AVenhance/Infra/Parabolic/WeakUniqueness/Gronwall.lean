/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Gronwall

/-!
# Scalar Grönwall closure for weak energy estimates

The parabolic uniqueness argument reduces the squared norm of the difference to a homogeneous
integral Grönwall inequality. This lemma packages that final implication.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- A nonnegative continuous function satisfying a homogeneous integral Grönwall bound vanishes
on the whole interval. -/
theorem continuous_nonneg_eq_zero_of_integral_gronwall
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hf_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f t ≤ C * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  have hc : IntervalIntegrable (fun _ : ℝ => C) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hcf : IntervalIntegrable (fun s : ℝ => C * f s) volume 0 1 :=
    (continuous_const.mul hf).intervalIntegrable 0 1
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f t ≤ 0 + ∫ s in (0 : ℝ)..t, C * f s := by
    intro t ht
    rw [intervalIntegral.integral_const_mul]
    simpa using hineq t ht
  have hgronwall := AVenhance.Infra.ODE.integral_gronwall_bound
    (a := 0) (b := 1) (C := 0) (c := fun _ => C) (z := f)
    (by norm_num) hc hcf (fun _ _ => hC) hbound
  intro t ht
  exact le_antisymm (by simpa using hgronwall t ht) (hf_nonneg t ht)

end AVenhance.Infra.Parabolic.WeakUniqueness
