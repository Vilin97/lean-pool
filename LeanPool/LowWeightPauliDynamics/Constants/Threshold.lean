/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Constants.Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Norm-level cutoff existence

This file proves the existence form of `apd:thm:truncation_threshold_entangled` at norm level:
for a decay base `0 ≤ q < 1`, the majorant `q^(m+1) (e(m+1))^c M` supplied by
`total_truncation_error_product_bound` tends to zero in the rung `m`, so every sufficiently large
rung `m ≥ 1` brings it below any tolerance `ε > 0`.

## Main results

* `norm_majorant_tendsto_zero`: `q^(m+1) (e(m+1))^c M → 0` as `m → ∞`, for `0 ≤ q < 1`.
* `exists_eventual_norm_threshold`, `exists_norm_threshold`: a rung `m ≥ 1` meeting the tolerance
  exists, and so does every larger rung.
* `exists_uniform_norm_threshold`, `exists_uniform_weight_cutoff`: one rung, respectively one
  weight cutoff `w = k_o + (k_h − 1)m`, for a whole family sharing the same `q, c, M`.
* `exists_model_norm_threshold`: the case `q = decayBase G kh α t` with `t < tZeroModel G kh α`.
* `exists_admissible_step_count`: a step count `r` can be chosen after the rung.

## Scope

`apd:thm:truncation_threshold_entangled` and `eq:truncation_weight_bound` use exponential decay
to dominate the polynomial factor. Here the norm-level majorant `q^(m+1) (e(m+1))^c M` tends to
zero when `0 ≤ q < 1`; for `c ≥ 0` its factor `(e(m+1))^c` is smaller than the factor
`(m*+2)(e(m*+2))^c` of `apd:eq:total_truncation_error`. The analytic limit permits any real
`c, M`; physical applications use the nonnegative constants supplied by the norm bound. Mathlib's
real-power/exponential asymptotic is reused directly.

The conclusions are cutoff existence, a conservative form of the paper's corollary: the explicit
logarithmic/log-log estimate of `m*`, the runtime statement (`apd:thm:runtime`) and the
conversion to an error in expectation are not formalized here. The uniform-family corollary
requires one common `q,c,M` bound for the entire family; dimension independence is not inferred
when those parameters, especially the observable norm bound, grow with dimension.
Converting a uniform rung to a uniform weight also requires fixed `k_o,k_h`; the weight
corollary keeps these outside the family quantifier explicitly.

Choosing a larger numerical step count is separate from constructing the corresponding gate
angles. Nothing here assumes a fixed angle family still satisfies `a ≤ αt/r` after `r` changes.
-/

@[expose] public section

namespace Lean4LPD

open Filter
open scoped Topology

/-- The analytic decay behind `apd:thm:truncation_threshold_entangled`, applied to the norm-level
majorant of `total_truncation_error_product_bound`: for `0 ≤ q < 1` and all real `c, M`,
`q^(m+1) (e(m+1))^c M → 0` as `m → ∞`. The exponential decay of `q^(m+1)` dominates the
polynomial factor. -/
theorem norm_majorant_tendsto_zero {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ) :
    Tendsto (fun m : ℕ => q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
      atTop (𝓝 0) := by
  rcases hq0.eq_or_lt with hzero | hqpos
  · simp [hzero.symm]
  · have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hqpos hq1)
    have hn : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hreal := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c (-Real.log q) hlog).comp hn
    have hscaled : Tendsto (fun m : ℕ =>
        ((m : ℝ) + 1) ^ c * Real.exp (Real.log q * ((m : ℝ) + 1)) * (Real.exp c * M))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_neg, zero_mul] using hreal.mul_const (Real.exp c * M)
    apply hscaled.congr'
    apply Filter.Eventually.of_forall
    intro m
    dsimp only
    have hp : q ^ (m + 1) = Real.exp (Real.log q * (((m + 1 : ℕ) : ℝ))) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hqpos]
    rw [hp, Real.mul_rpow (by positivity) (by positivity), Real.exp_one_rpow]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Every sufficiently large natural rung meets the norm tolerance, the existence part of
`apd:thm:truncation_threshold_entangled`. No explicit logarithmic formula for the rung is
asserted, and no hypothesis on the input state is involved. -/
theorem exists_eventual_norm_threshold {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m →
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by
  have hevent : ∀ᶠ m : ℕ in atTop,
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M < ε :=
    (tendsto_order.mp (norm_majorant_tendsto_zero hq0 hq1 c M)).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 1 N, le_max_left _ _, fun m hm => ?_⟩
  exact (hN m (le_trans (le_max_right _ _) hm)).le

/-- A natural cutoff rung satisfying the requested absolute norm tolerance, from
`apd:thm:truncation_threshold_entangled` at norm level only. -/
theorem exists_norm_threshold {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by
  obtain ⟨m, hm, hbound⟩ := exists_eventual_norm_threshold hq0 hq1 c M hε
  exact ⟨m, hm, hbound m le_rfl⟩

/-- The cutoff can be chosen independently of the family index **when the same `q,c,M`
majorizes the whole family**. This is the qualified dimension-independent interpretation of
`apd:thm:truncation_threshold_entangled`, for absolute norm tolerance. -/
theorem exists_uniform_norm_threshold {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ i m, 1 ≤ m → error i m ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ i, error i m ≤ ε := by
  obtain ⟨m₀, hm₀, hsmall⟩ := exists_eventual_norm_threshold hq0 hq1 c M hε
  exact ⟨m₀, hm₀, fun m hm i =>
    (hbound i m (le_trans hm₀ hm)).trans (hsmall m hm)⟩

/-- A single weight cutoff works for the whole family when `k_o,k_h,q,c,M` are all fixed
uniform data. This is the norm-level, absolute-tolerance form of
`eq:truncation_weight_bound`, not a runtime or expectation theorem. -/
theorem exists_uniform_weight_cutoff {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ko kh : ℕ)
    (hbound : ∀ i m, 1 ≤ m → error i (ko + (kh - 1) * m) ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w m : ℕ, 1 ≤ m ∧ w = ko + (kh - 1) * m ∧ ∀ i, error i w ≤ ε := by
  obtain ⟨m, hm, hsmall⟩ := exists_norm_threshold hq0 hq1 c M hε
  exact ⟨ko + (kh - 1) * m, m, hm, rfl, fun i => (hbound i m hm).trans hsmall⟩

/-- The model-only short-time condition `t < tZeroModel G kh α` supplies `0≤q<1` for
`q = decayBase G kh α t`, so the norm-level cutoff exists. This is the model-threshold
counterpart of `apd:thm:truncation_threshold_entangled`; it concerns the norm-level majorant
only, so no hypothesis on the input state is involved. -/
theorem exists_model_norm_threshold {G kh α t c M ε : ℝ}
    (hG : 0 < G) (hkh : 1 < kh) (hα : 0 < α) (ht : 0 ≤ t)
    (htime : t < tZeroModel G kh α) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ decayBase G kh α t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε :=
  exists_norm_threshold (decayBase_nonneg hG hkh hα ht)
    (decayBase_lt_one hG hkh hα htime) c M hε

/-- Numerical step counts can be chosen after the rung: an Archimedean helper for the conditions
of `apd:eq:multijump_factor`. The two real lower bounds `B₁`, `B₂` may encode the paper's
finite-step conditions `r ≥ 8(m*+1)²/Γ` and `r ≥ 8e²·w₂·αt`; satisfying them does not construct
or update any gate-angle family. -/
theorem exists_admissible_step_count (m : ℕ) (B₁ B₂ : ℝ) :
    ∃ r : ℕ, 5 ≤ r ∧ m ≤ r ∧ B₁ ≤ (r : ℝ) ∧ B₂ ≤ (r : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max B₁ B₂)
  have hkR : (k : ℝ) ≤ (max 5 (max m k) : ℕ) := by
    exact_mod_cast le_trans (le_max_right m k) (le_max_right 5 (max m k))
  exact ⟨max 5 (max m k), le_max_left _ _,
    le_trans (le_max_left m k) (le_max_right 5 (max m k)),
    (le_max_left B₁ B₂).trans (hk.trans hkR),
    (le_max_right B₁ B₂).trans (hk.trans hkR)⟩

end Lean4LPD
