/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Bridge: Project `residueAt` and Mathlib `MeromorphicAt`

As of Mathlib v4.29, there is no `MeromorphicAt.residue` definition in Mathlib.
Mathlib provides:
- `MeromorphicAt f z₀` -- existence of a meromorphic decomposition
- `meromorphicOrderAt f z₀` -- the order (pole/zero multiplicity) as `WithTop ℤ`
- `meromorphicOrderAt_eq_int_iff` -- factorization: `f =ᶠ (z - z₀)^n • g` with `g` analytic,
  `g(z₀) ≠ 0`

This file bridges the project's residue definitions to Mathlib's meromorphic API:

## Main Results

* `residueAt_eq_zero_of_analyticAt` -- `residueAt f z₀ = 0` when `f` is analytic at `z₀`
* `residueSimplePole_eq_zero_of_nonneg_order` -- `residueSimplePole f z₀ = 0` when the order
  is non-negative

For higher-order poles, the project's `residueAt_eq_laurent_head_coeff` (in
`FlatnessTransfer/PerTermVanishing.lean`) provides the general connection to the `a₋₁`
Laurent coefficient.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ### Analytic / non-negative order bridge -/

/-- If `f` is analytic at `z₀`, then `residueAt f z₀ = 0`.
The contour integral of an analytic function on a small circle vanishes by Cauchy's theorem. -/
theorem residueAt_eq_zero_of_analyticAt (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : AnalyticAt ℂ f z₀) :
    residueAt f z₀ = 0 := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨r, hr_pos, hf_ball⟩ := hf.exists_ball_analyticOnNhd
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr_pos] with ρ hρ_lt hρ_pos
  simp only [Set.mem_Ioi] at hρ_pos
  simp only [Set.mem_Iio] at hρ_lt
  have h_cont : ContinuousOn f (Metric.closedBall z₀ ρ) :=
    hf_ball.continuousOn.mono (Metric.closedBall_subset_ball hρ_lt)
  have h_int_zero : (∮ z in C(z₀, ρ), f z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hρ_pos.le
      Set.countable_empty h_cont
      (fun z ⟨hz, _⟩ => (hf_ball z (Metric.ball_subset_ball hρ_lt.le hz)).differentiableAt)
  rw [h_int_zero, mul_zero]

/-- If `f` is meromorphic at `z₀` with non-negative order (i.e., analytic or removable
singularity), then `residueSimplePole f z₀ = 0`. -/
theorem residueSimplePole_eq_zero_of_nonneg_order (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : MeromorphicAt f z₀) (hord : 0 ≤ meromorphicOrderAt f z₀) :
    residueSimplePole f z₀ = 0 := by
  -- Non-negative order means f =ᶠ (z-z₀)^n • g with n ≥ 0 and g analytic
  -- So (z-z₀) * f(z) → 0 as z → z₀
  unfold residueSimplePole
  apply Filter.Tendsto.limUnder_eq
  by_cases htop : meromorphicOrderAt f z₀ = ⊤
  · -- f =ᶠ 0 near z₀, so (z-z₀) * f(z) =ᶠ 0
    rw [meromorphicOrderAt_eq_top_iff] at htop
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [htop] with z hz
    rw [hz, mul_zero]
  · -- f has finite order n ≥ 0
    obtain ⟨g, hg_an, _hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).mp htop
    set n := (meromorphicOrderAt f z₀).untop₀
    have hord_val : (0 : ℤ) ≤ n := by
      have h_fin := WithTop.coe_untop₀_of_ne_top htop
      rw [← h_fin] at hord
      exact_mod_cast hord
    -- (z - z₀) * f(z) =ᶠ (z-z₀)^(n+1) • g(z) with n+1 ≥ 1, tends to 0
    have hexp_pos : 0 < n + 1 := by omega
    -- First show the eventual equality
    have h_ev : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * f z =
        (z - z₀) ^ (1 + n) * g z := by
      filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hne
      have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
      rw [hz, smul_eq_mul, ← mul_assoc, ← zpow_one_add₀ hzsub]
    -- The zpow factor tends to 0 since exponent ≥ 1
    have h_zpow_tend : Tendsto (fun z => (z - z₀) ^ (1 + n)) (𝓝[≠] z₀) (𝓝 0) := by
      have h_sub_tend : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
        rw [show (0 : ℂ) = z₀ - z₀ from (sub_self z₀).symm]
        exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      rw [show (0 : ℂ) = 0 ^ (1 + n) from (zero_zpow _ (by omega)).symm]
      exact h_sub_tend.zpow₀ (1 + n) (Or.inr (by omega))
    have h_g_tend : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
      hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h_prod_tend : Tendsto (fun z => (z - z₀) ^ (1 + n) * g z) (𝓝[≠] z₀) (𝓝 0) := by
      have := h_zpow_tend.mul h_g_tend
      rwa [zero_mul] at this
    exact h_prod_tend.congr' (h_ev.mono fun z hz => hz.symm)

end GeneralizedResidueTheory
