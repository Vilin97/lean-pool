/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import Mathlib.Order.LiminfLimsup
public import LeanPool.LiCriterion.Hadamard.Basic

/-!
Order bounds from max-modulus bounds.

This file isolates a general lemma that converts an eventual max-modulus bound

`maxModulus f r ≤ exp (r ^ ρ)`

into an order bound `order f ≤ ρ`, where `order` is the `limsup` definition from
`LZC/HadamardFactorization/Basic.lean`.

It is used in the order-`≤ 1` Hadamard factorization proof to show the quotient
`Q := f / P` has `order Q < 2`, hence is an exponential of a linear function.
-/

@[expose] public section

namespace Hadamard

open Complex Real Filter

/-! ### A coboundedness helper for the `order` auxiliary function -/

/-- A cheap eventual lower bound for the auxiliary function used in `order`.

This is purely a `Filter`/`limsup` technicality: `Filter.limsup_le_of_le` requires an
`IsCoboundedUnder` hypothesis, which we obtain from this lemma. -/
private lemma orderAux_eventually_ge_neg_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ∀ᶠ r : ℝ in atTop,
      (-1 : ℝ) ≤
        (if r > 0 ∧ maxModulus f r > 1 then
            Real.log (Real.log (maxModulus f r)) / Real.log r
          else 0) := by
  classical
  -- Either the max modulus ever exceeds 1, or it never does.
  by_cases hex : ∃ r0 : ℝ, maxModulus f r0 > 1
  · rcases hex with ⟨r0, hr0⟩
    have hr0_nonneg : 0 ≤ r0 := by
      by_contra h
      have hr0_neg : r0 < 0 := lt_of_not_ge h
      have hset_empty : {y : ℝ | ∃ z : ℂ, ‖z‖ = r0 ∧ y = ‖f z‖} = ∅ := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
          linarith [hz, hr0_neg]
        · intro hy; cases hy
      have : maxModulus f r0 = 0 := by
        simp [maxModulus, hset_empty]
      have : ¬ maxModulus f r0 > 1 := by
        simp [this]
      exact this hr0
    -- `M0` is a fixed value `> 1`.
    let M0 : ℝ := maxModulus f r0
    have hM0 : 1 < M0 := hr0
    have hlogM0_pos : 0 < Real.log M0 := Real.log_pos hM0
    let L : ℝ := Real.log (Real.log M0)
    -- Threshold making `log r ≥ -L`, and ensuring `r ≥ r0` and `r ≥ 2`.
    let R1 : ℝ := max (max r0 2) (Real.exp (-L))
    have hR1_ge2 : (2 : ℝ) ≤ R1 := le_trans (le_max_right r0 2) (le_max_left _ _)
    have hR1_ge_r0 : r0 ≤ R1 := le_trans (le_max_left r0 2) (le_max_left _ _)
    have hR1_ge_exp : Real.exp (-L) ≤ R1 := le_max_right _ _
    refine Filter.eventually_atTop.2 ⟨R1, ?_⟩
    intro r hr
    have hr_ge2 : (2 : ℝ) ≤ r := le_trans hR1_ge2 hr
    have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr_ge2
    have hr_gt1 : 1 < r := by linarith
    have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
    have hM0_le : M0 ≤ maxModulus f r := by
      have hr0_le : r0 ≤ r := le_trans hR1_ge_r0 hr
      exact maxModulus_mono_of_differentiable f hf (hR := hr_pos) (hr := hr0_nonneg) hr0_le
    have hMr_gt1 : 1 < maxModulus f r := lt_of_lt_of_le hM0 hM0_le
    have hloglog_ge : L ≤ Real.log (Real.log (maxModulus f r)) := by
      have hlogMr_ge : Real.log M0 ≤ Real.log (maxModulus f r) :=
        Real.log_le_log (by linarith [hM0]) hM0_le
      have : Real.log (Real.log M0) ≤ Real.log (Real.log (maxModulus f r)) :=
        Real.log_le_log hlogM0_pos (le_trans (le_rfl) hlogMr_ge)
      simpa [L] using this
    have hlogr_ge : -L ≤ Real.log r := by
      have : Real.exp (-L) ≤ r := le_trans hR1_ge_exp hr
      have hlog_exp : Real.log (Real.exp (-L)) ≤ Real.log r :=
        Real.log_le_log (by positivity) this
      simpa [Real.log_exp] using hlog_exp
    -- Now `-log r ≤ loglogM`.
    have hneglogr_le : -Real.log r ≤ Real.log (Real.log (maxModulus f r)) := by
      have : -Real.log r ≤ L := by linarith [hlogr_ge]
      exact le_trans this hloglog_ge
    -- Convert to `(-1) ≤ loglogM / log r`.
    have : (-1 : ℝ) ≤ Real.log (Real.log (maxModulus f r)) / Real.log r := by
      have : (-1 : ℝ) * Real.log r ≤ Real.log (Real.log (maxModulus f r)) := by
        simpa using hneglogr_le
      exact (le_div_iff₀ hlogr_pos).2 this
    have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hMr_gt1⟩
    simpa [hcond] using this
  · -- If the max modulus never exceeds 1, the expression is always 0.
    refine Filter.Eventually.of_forall ?_
    intro r
    have hnot : ¬ maxModulus f r > 1 := by
      intro hr'
      exact hex ⟨r, hr'⟩
    by_cases hr0 : r > 0
    · simp [hr0, hnot]
    · simp [hr0]

/-! ### Order bound from an eventual max-modulus bound -/

theorem order_le_of_eventually_maxModulus_le_exp_rpow
    (f : ℂ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f)
    (h : ∀ᶠ r : ℝ in atTop, maxModulus f r ≤ Real.exp (r ^ ρ)) :
    order f ≤ ρ := by
  let u : ℝ → ℝ := fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0
  have hu_upper : ∀ᶠ r : ℝ in atTop, u r ≤ ρ := by
    filter_upwards [h, (eventually_gt_atTop (1 : ℝ))] with r hr hr_gt1
    by_cases hcond : r > 0 ∧ maxModulus f r > 1
    · have hr_pos : 0 < r := hcond.1
      have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
      have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hcond.2
      have hlogM_le : Real.log (maxModulus f r) ≤ r ^ ρ := by
        have := Real.log_le_log hM_pos hr
        simpa [Real.log_exp] using this
      have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hcond.2
      have hloglog_le : Real.log (Real.log (maxModulus f r)) ≤ Real.log (r ^ ρ) :=
        Real.log_le_log hlogM_pos hlogM_le
      have hlogrpow : Real.log (r ^ ρ) = ρ * Real.log r := Real.log_rpow hr_pos ρ
      have : Real.log (Real.log (maxModulus f r)) ≤ ρ * Real.log r :=
        le_trans hloglog_le (by rw [hlogrpow])
      have : Real.log (Real.log (maxModulus f r)) / Real.log r ≤ ρ :=
        (div_le_iff₀ hlogr_pos).2 this
      simpa [u, hcond] using this
    · simp [u, hcond, hρ]
  have hu_lower : ∀ᶠ r : ℝ in atTop, (-1 : ℝ) ≤ u r := orderAux_eventually_ge_neg_one f hf
  have hu_cobdd : IsCoboundedUnder (· ≤ ·) atTop u :=
    Filter.isCoboundedUnder_le_of_eventually_le atTop hu_lower
  have hlimsup : Filter.limsup u atTop ≤ ρ :=
    Filter.limsup_le_of_le (f := (atTop : Filter ℝ)) (u := u) (a := ρ) hu_cobdd hu_upper
  simpa [Hadamard.order, u] using hlimsup

/-! ### Order bounds from a `ρ + ε` max-modulus family -/

/-!
If we can bound `maxModulus f r` by `exp(r^(ρ+ε))` for every `ε > 0`, then `order f ≤ ρ`.

This packages the exact “max-modulus form” pipeline used for order-`≤ 1` goals:
prove the family of bounds, then apply `order_le_of_eventually_maxModulus_le_exp_rpow`
at exponent `ρ+ε`, and finally let `ε → 0` using `le_of_forall_pos_le_add`.
-/
theorem order_le_of_forall_pos_eventually_maxModulus_le_exp_rpow_add
    (f : ℂ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r : ℝ in atTop, maxModulus f r ≤ Real.exp (r ^ (ρ + ε))) :
    order f ≤ ρ := by
  refine _root_.le_of_forall_pos_le_add ?_
  intro ε hε
  have hρ' : 0 ≤ ρ + ε := add_nonneg hρ (le_of_lt hε)
  exact
    order_le_of_eventually_maxModulus_le_exp_rpow (f := f) (ρ := ρ + ε) (hρ := hρ') (hf := hf)
      (h := h ε hε)

/-! A convenient specialization for order-`≤ 1` (the β use-case). -/
theorem order_le_one_of_forall_pos_eventually_maxModulus_le_exp_rpow_one_add
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, maxModulus f r ≤ Real.exp (r ^ (1 + ε))) :
    order f ≤ 1 := by
  simpa using
    (order_le_of_forall_pos_eventually_maxModulus_le_exp_rpow_add (f := f) (ρ := 1) (hρ := by
      norm_num) (hf := hf) (h := h))

end Hadamard
