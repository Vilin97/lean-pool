/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). Planar analytic k-th root.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Local analytic k-th root

`RS.AnalyticAt.exists_pow_eq`: a non-vanishing analytic germ `u` at `z₀ : ℂ` has an analytic
`k`-th root `r` near `z₀` (`r ^ k = u` eventually, `r z₀ ≠ 0`), for any `k ≠ 0`.

Route (design §5.1): with `a := u z₀ ≠ 0`, set `r z := exp (log a / k) * exp (log (u z / a) / k)`.
Only `log (u z / a)` (value near `1`, inside `slitPlane`) needs *analyticity* of `log`;
`exp (log a) = a` holds for every nonzero constant, so no case split on `arg (u z₀)` is needed.
-/

open Filter Complex
open scoped Topology

namespace RS

/-- Local analytic k-th root of a non-vanishing analytic function. -/
theorem AnalyticAt.exists_pow_eq {u : ℂ → ℂ} {z₀ : ℂ} (hu : AnalyticAt ℂ u z₀)
    (hu₀ : u z₀ ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, r z ^ k = u z := by
  set a : ℂ := u z₀ with ha
  have hka : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  -- `exp (w / k) ^ k = exp w`
  have hpow : ∀ w : ℂ, exp (w / k) ^ k = exp w := by
    intro w
    rw [← exp_nat_mul]
    congr 1
    field_simp
  refine ⟨fun z ↦ exp (log a / k) * exp (log (u z / a) / k), ?_, ?_, ?_⟩
  · -- analyticity at `z₀`
    have hdiv : AnalyticAt ℂ (fun z ↦ u z / a) z₀ := hu.div analyticAt_const hu₀
    have hmem : u z₀ / a ∈ slitPlane := by
      rw [← ha, div_self hu₀]; exact one_mem_slitPlane
    have hlog : AnalyticAt ℂ (fun z ↦ log (u z / a)) z₀ := hdiv.clog hmem
    have hlogk : AnalyticAt ℂ (fun z ↦ log (u z / a) / k) z₀ := hlog.div analyticAt_const hka
    exact analyticAt_const.mul (analyticAt_cexp.comp hlogk)
  · exact mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  · -- eventual equality `r ^ k = u`
    filter_upwards [hu.continuousAt.eventually_ne hu₀] with z hz
    have hza : u z / a ≠ 0 := div_ne_zero hz hu₀
    rw [mul_pow, hpow, hpow, exp_log hu₀, exp_log hza]
    field_simp

end RS
