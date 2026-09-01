/-
Copyright (c) 2025 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A product limit for a triangular array

This file determines the limit of the product  `∏ₖ (1 + a_{n,k})` for a triangular array `a_{n,k}`
satisfying `∑ₖ a_{n,k} → L`and `∑ₖ ‖a_{n,k}‖² → 0` as `n → ∞`.

The main result is the following:

· `tendsto_finset_prod_one_add_of_sum_of_sq` — if `∑ₖ a_{n,k} → L` and
  `∑ₖ, ‖a_{n,k}‖² → 0`, then `∏ₖ (1 + a_{n,k}) → exp L`.

-/

namespace LeanPool.LinearModel

noncomputable section

open Filter Complex Finset
open scoped Topology

variable {a : (n : ℕ) → Fin n → ℂ}


section IntermediateResults

/-- For `‖z‖ ≤ 1/2`, we have `‖log(1+z) - z‖ ≤ ‖z‖²`. -/
private lemma norm_log_one_add_sub_self_le_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
  calc ‖log (1 + z) - z‖
      ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := norm_log_one_add_sub_self_le (lt_of_le_of_lt hz (by norm_num))
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        gcongr; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    _ = ‖z‖ ^ 2 := by ring

/-- `max ‖a n k‖² ≤ ∑ ‖a n k‖²`, so if `∑ₖ ‖a_{n,k}‖² → 0`, eventually all `‖a n k‖` are small. -/
private lemma eventually_norm_le_of_sum_sq_tendsto
    (hsq : Tendsto (fun n ↦ ∑ k : Fin n, ‖a n k‖ ^ 2) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ k : Fin n, ‖a n k‖ ≤ 1 / 2 := by
  rw [Metric.tendsto_nhds] at hsq
  have hsq_14 := hsq (1 / 4) (by positivity)
  simp only [Real.dist_eq, sub_zero] at hsq_14
  filter_upwards [hsq_14] with n hn k
  have hle : ‖a n k‖ ^ 2 ≤ ∑ j : Fin n, ‖a n j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ ‖a n j‖ ^ 2) (fun _ _ ↦ by positivity) (mem_univ k)
  have habs : |∑ j : Fin n, ‖a n j‖ ^ 2| = ∑ j : Fin n, ‖a n j‖ ^ 2 :=
    abs_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)
  have hsq_small : ‖a n k‖ ^ 2 < 1 / 4 := lt_of_le_of_lt hle (habs ▸ hn)
  nlinarith [sq_nonneg ‖a n k‖, norm_nonneg (a n k)]

/-- If `‖a_{n,k}‖ ≤ 1/2` then `‖∑ₖ log (1 + a_{n,k}) - ∑ₖ a_{n,k}‖` is bounded
above by `∑_k ‖a_{n,k}‖ ^ 2`. -/
private lemma norm_sum_log_sub_sum_le
    {n : ℕ} (ha : ∀ k : Fin n, ‖a n k‖ ≤ 1 / 2) :
    ‖∑ k : Fin n, log (1 + a n k) - ∑ k : Fin n, a n k‖
      ≤ ∑ k : Fin n, ‖a n k‖ ^ 2 := by
  rw [← sum_sub_distrib]
  calc ‖∑ k, (log (1 + a n k) - a n k)‖
      ≤ ∑ k, ‖log (1 + a n k) - a n k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖a n k‖ ^ 2 := sum_le_sum fun k _ ↦ norm_log_one_add_sub_self_le_sq (ha k)

/-- If `‖a_{n,k}‖ ≤ 1` then `exp(∑ₖ log (1 + a_{n,k})) = ∏ₖ (1 + a_{n,k})`. -/
private lemma exp_sum_log_eq_prod
    {n : ℕ} (ha : ∀ k : Fin n, ‖a n k‖ < 1) :
    exp (∑ k : Fin n, log (1 + a n k)) = ∏ k : Fin n, (1 + a n k) := by
  rw [exp_sum]
  congr 1 with k
  apply exp_log
  have hk : ‖a n k‖ < 1 := ha k
  have : ‖(1 : ℂ) + a n k‖ ≥ 1 - ‖a n k‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(a n k))
    simp [norm_neg] at this
    linarith
  intro h0
  simp [h0] at this
  linarith

end IntermediateResults


section MainResults

/-- If `∑ₖ a_{n,k} → L` and `∑ₖ ‖a_{n,k}‖² → 0`, then `∏ₖ (1 + a_{n,k}) → exp L`. -/
lemma tendsto_finset_prod_one_add_of_sum_of_sq
    {L : ℂ}
    (hsum : Tendsto (fun n ↦ ∑ k : Fin n, a n k) atTop (𝓝 L))
    (hsq : Tendsto (fun n ↦ ∑ k : Fin n, ‖a n k‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∏ k : Fin n, (1 + a n k)) atTop (𝓝 (exp L)) := by
  -- Step 1: ∑ log(1 + a n k) → L
  have hlog : Tendsto (fun n ↦ ∑ k : Fin n, log (1 + a n k)) atTop (𝓝 L) := by
    have hdiff : Tendsto (fun n ↦ ∑ k : Fin n, log (1 + a n k) - ∑ k : Fin n, a n k)
        atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hev := eventually_norm_le_of_sum_sq_tendsto hsq
      rw [Metric.tendsto_nhds] at hsq
      have hsq_eps := hsq ε hε
      simp only [Real.dist_eq, sub_zero] at hsq_eps
      filter_upwards [hev, hsq_eps] with n hn1 hn2
      rw [dist_eq_norm, sub_zero]
      calc ‖∑ k, log (1 + a n k) - ∑ k, a n k‖
          ≤ ∑ k, ‖a n k‖ ^ 2 := norm_sum_log_sub_sum_le hn1
        _ ≤ |∑ k : Fin n, ‖a n k‖ ^ 2| := le_abs_self _
        _ < ε := hn2
    have := hdiff.add hsum
    simp only [zero_add] at this
    exact this.congr (fun n ↦ by ring)
  -- Step 2: exp(∑ log(1 + a n k)) → exp L by continuity
  have hexp : Tendsto (fun n ↦ cexp (∑ k : Fin n, log (1 + a n k))) atTop (𝓝 (cexp L)) :=
    (continuous_exp.tendsto _).comp hlog
  -- Step 3: exp(∑ log(1 + a n k)) = ∏ (1 + a n k) eventually
  refine hexp.congr' ?_
  have hev := eventually_norm_le_of_sum_sq_tendsto hsq
  filter_upwards [hev] with n hn
  exact exp_sum_log_eq_prod (fun k ↦ lt_of_le_of_lt (hn k) (by norm_num))


end MainResults

end
end LinearModel
end LeanPool
