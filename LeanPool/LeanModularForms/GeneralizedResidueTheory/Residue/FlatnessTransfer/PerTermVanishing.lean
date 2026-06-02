/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.BoundaryVanishing
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.CutoffInfrastructure
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase

/-!
# Per-Term PV Vanishing and CPV Helpers

Per-term PV vanishing for higher-order polar terms (L4), Laurent circle
integrals, multi-point CPV, holomorphic CPV vanishing, and assembly helpers.

## Main results

* `pv_higher_order_term_tendsto_zero`: single-crossing higher-order PV → 0
* `multipoint_pv_zpow_tendsto_zero`: multi-point CPV of zpow → 0
* `holomorphic_cpv_tendsto_zero_on_convex`: holomorphic CPV → 0 on convex domains
* `tendsto_cpv_of_continuousOn_zero_integral`: CPV → 0 for continuous functions with zero integral
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ## L4: Per-term PV vanishing for higher-order polar terms

The cutoff integral of `a/(γ(t)-s)^{m}·γ'(t)` (with m ≥ 2) tends to 0 under
the angle condition + flatness, using FTC + boundary vanishing (L3).

The FTC reduces the cutoff integral to boundary terms `(γ(t_exit)-s)^{1-m}/(1-m)`
at the exit points of the ε-ball. These boundary terms are exactly the `w^k`
from L3 with `k = 1-m ≤ -1`, and flatness of order `m` gives
`n + k = m + (1-m) = 1 ≥ 1`. -/

/-- For a single crossing at `t₀` with angle `α`, exponent `m ≥ 2`, and
flatness of order `m`: if `(m-1) · α ∈ 2πℤ`, then the PV cutoff integral
of `(γ-s)^{-m} · γ'` tends to 0.

This combines FTC telescoping (L1) with boundary vanishing (L3). The flatness
hypothesis is essential: without it, the boundary terms `(γ-s)^{1-m}` at the
ε-cutoff points grow as `ε^{1-m} → ∞` and the angle condition alone cannot
compensate. With flatness of order `m`, the direction convergence rate is
`o(ε^{m-1})`, which exactly cancels the `ε^{1-m}` divergence. -/
theorem pv_higher_order_term_tendsto_zero
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (h_angle : ∃ k : ℤ, ((m - 1 : ℕ) : ℝ) * _root_.angleAtCrossing γ t₀ ht₀ =
      ↑k * (2 * Real.pi)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε
         then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0))
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨wR, wL, uR, uL, h_nR, h_nL, h_neR, h_neL, huR, huL,
    h_arg, h_rate_R, h_rate_L, h_eq⟩ :=
    cutoff_zpow_infrastructure γ s m hm t₀ ht₀ hcross h_unique hγ_closed h_flat
  have h_zpow : uR ^ (1 - (m : ℤ)) = uL ^ (1 - (m : ℤ)) := by
    apply unit_zpow_eq_of_angle_multiple _ _ _ huR huL
    obtain ⟨n_a, h_n_a⟩ := h_arg
    obtain ⟨j, hj⟩ := h_angle
    have h1m : 1 ≤ m := by omega
    refine ⟨-j + (1 - (m : ℤ)) * n_a, ?_⟩
    push_cast [Nat.cast_sub h1m] at hj h_n_a ⊢
    have h_expand : (1 - (m : ℝ)) * (arg uR - arg uL) =
        (1 - (m : ℝ)) * _root_.angleAtCrossing γ t₀ ht₀ +
        (1 - (m : ℝ)) * ((n_a : ℝ) * (2 * Real.pi)) := by
      rw [h_n_a]; ring
    linarith
  have h_L3 : Tendsto (fun ε => wR ε ^ (1 - (m : ℤ)) - wL ε ^ (1 - (m : ℤ)))
      (𝓝[>] 0) (𝓝 0) :=
    zpow_boundary_diff_tendsto_zero (1 - (m : ℤ)) (by omega) wR wL
      h_nR h_nL h_neR h_neL uR uL huR huL h_zpow m (by omega) h_rate_R h_rate_L
  have h_bdy : Tendsto
      (fun ε => (wL ε ^ (1 - (m : ℤ)) - wR ε ^ (1 - (m : ℤ))) /
        ((1 : ℂ) - ↑(m : ℤ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := h_L3.neg.div_const ((1 : ℂ) - ↑(m : ℤ))
    simp only [neg_zero, zero_div] at h1
    exact Tendsto.congr (fun ε => by ring) h1
  exact Tendsto.congr' (h_eq.mono fun ε h => h.symm) h_bdy

/-- The CPV integrand of any function is pointwise bounded by
`‖g(γ(t))‖ * ‖γ'(t)‖` (since it's either 0 or `g(γ(t)) * γ'(t)`). -/
private lemma norm_cpvIntegrandOn_le (S0 : Finset ℂ) (g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    ‖cauchyPrincipalValueIntegrandOn S0 g γ ε t‖ ≤
      ‖g (γ t)‖ * ‖deriv γ t‖ := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs with h
  · simp only [norm_zero]; positivity
  · exact norm_mul_le _ _

/-- CPV integrand of `f` minus CPV integrand of `g` equals CPV integrand of `f - g`,
pointwise, because both use the same indicator set `{t : ∃ s ∈ S0, ‖γ t - s‖ ≤ ε}`. -/
lemma cpvIntegrandOn_sub (S0 : Finset ℂ) (f g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 f γ ε t -
    cauchyPrincipalValueIntegrandOn S0 g γ ε t =
    cauchyPrincipalValueIntegrandOn S0 (fun z => f z - g z) γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-! ### Sublemma 1: Residue equals leading Laurent coefficient -/

/-- Helper: circle integral of a single Laurent term `a / (z - s)^{k+1}`. -/
private theorem circleIntegral_laurent_term
    (s : ℂ) (r : ℝ) (hr_pos : 0 < r) (c : ℂ) (k : ℕ) :
    (∮ z in C(s, r), c / (z - s) ^ (k + 1)) =
      if k = 0 then c * (2 * ↑Real.pi * I) else 0 := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by
    simp [hr_ne.symm]
  have h_eq : Set.EqOn (fun z => c / (z - s) ^ (k + 1))
      (fun z => c * (z - s) ^ (-(↑(k + 1) : ℤ))) (Metric.sphere s r) := by
    intro z _
    simp only [div_eq_mul_inv, zpow_neg, zpow_natCast]
  rw [circleIntegral.integral_congr hr_pos.le h_eq,
    circleIntegral.integral_const_mul]
  by_cases hk : k = 0
  · simp only [hk, zero_add, Nat.cast_one, if_true]
    congr 1
    have h_eq' : Set.EqOn (fun z => (z - s) ^ (-(1 : ℤ)))
        (fun z => (z - s)⁻¹) (Metric.sphere s r) := by
      intro z _; simp only [zpow_neg_one]
    rw [circleIntegral.integral_congr hr_pos.le h_eq',
      circleIntegral.integral_sub_center_inv s hr_ne]
  · simp only [hk, if_false]
    rw [circleIntegral.integral_sub_zpow_of_ne, mul_zero]
    intro h_neg_eq
    apply hk
    omega

/-- Helper: circle integral of the Laurent sum equals `a₀ * 2πi`. -/
private theorem circleIntegral_laurent_sum (s : ℂ) (r : ℝ) (hr_pos : 0 < r)
    (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ) :
    (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      a ⟨0, hN⟩ * (2 * ↑Real.pi * I) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by
    simp [hr_ne.symm]
  have h_ci_term : ∀ k : Fin N,
      CircleIntegrable (fun z => a k / (z - s) ^ (k.val + 1)) s r := by
    intro k
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const).pow _
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))
  have h_push : (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      ∑ k : Fin N, (∮ z in C(s, r), a k / (z - s) ^ (k.val + 1)) := by
    unfold circleIntegral
    have h_smul : ∀ θ : ℝ,
        deriv (circleMap s r) θ •
          (∑ k : Fin N, a k / (circleMap s r θ - s) ^ (k.val + 1)) =
        ∑ k : Fin N,
          deriv (circleMap s r) θ • (a k / (circleMap s r θ - s) ^ (k.val + 1)) :=
      fun θ => Finset.smul_sum
    rw [show (fun θ => deriv (circleMap s r) θ •
          (∑ k : Fin N, a k / (circleMap s r θ - s) ^ (k.val + 1))) =
          fun θ => ∑ k : Fin N,
            deriv (circleMap s r) θ • (a k / (circleMap s r θ - s) ^ (k.val + 1))
      from funext h_smul]
    rw [intervalIntegral.integral_finsetSum]
    intro i _
    exact (h_ci_term i).out
  rw [h_push]
  rw [show (∑ k : Fin N, (∮ z in C(s, r), a k / (z - s) ^ (k.val + 1))) =
      ∑ k : Fin N, if k.val = 0 then a k * (2 * ↑Real.pi * I) else 0
    from Finset.sum_congr rfl (fun k _ => circleIntegral_laurent_term s r hr_pos (a k) k.val)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have h_filter : Finset.filter (fun k : Fin N => k.val = 0) Finset.univ = {⟨0, hN⟩} := by
    ext ⟨j, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => congr_arg Fin.val h⟩
  rw [h_filter, Finset.sum_singleton]

/-- **Sublemma 1**: The residue of `f` at `s` equals the leading Laurent coefficient `a₀`.

Given the Laurent expansion `f(z) = g(z) + Σ_{k=0}^{N-1} aₖ/(z-s)^{k+1}` near `s`,
with `g` analytic at `s`, the circle integral definition of `residueAt` gives
`residueAt f s = a₀`.

Proof strategy: On a small circle of radius `r` around `s`:
- `∮ g = 0` by Cauchy (g analytic → differentiable on disk)
- `∮ (z-s)^{-(k+1)} = 0` for `k ≥ 1` (by `integral_sub_zpow_of_ne`, exponent ≠ -1)
- `∮ (z-s)⁻¹ = 2πi` (by `integral_sub_center_inv`)
- So `∮ f = a₀ · 2πi`, hence `residueAt f s = (2πi)⁻¹ · a₀ · 2πi = a₀`. -/
theorem residueAt_eq_laurent_head_coeff (f : ℂ → ℂ) (s : ℂ) (N : ℕ)
    (hN : 0 < N) (a : Fin N → ℂ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g s)
    (hf_eq : ∀ᶠ z in 𝓝[≠] s,
      f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) :
    residueAt f s = a ⟨0, hN⟩ := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
  simp only [Set.mem_Ioi] at hr_pos
  simp only [Set.mem_Iio] at hr_lt
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h_eq_on : Set.EqOn f
      (fun z => g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) (Metric.sphere s r) := by
    intro z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have h_in : dist z s < rf := by
      rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf
    exact hrf_eq ⟨Metric.mem_ball.mpr h_in, Set.mem_compl_singleton_iff.mpr h_ne⟩
  have h_g_cont : ContinuousOn g (Metric.closedBall s r) :=
    hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
  have h_ci_g : CircleIntegrable g s r :=
    (h_g_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  have h_ci_sum : CircleIntegrable
      (fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finsetSum
    intro k _
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const).pow _
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))
  have h_int_eq : (∮ z in C(s, r), f z) =
      (∮ z in C(s, r), g z) +
      (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) := by
    rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
      circleIntegral.integral_add h_ci_g h_ci_sum]
  have h_g_zero : (∮ z in C(s, r), g z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
      Set.countable_empty h_g_cont
      (fun z ⟨hz, _⟩ => (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)).differentiableAt)
  rw [h_int_eq, h_g_zero, zero_add, circleIntegral_laurent_sum s r hr_pos N hN a]
  have h2pi_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [mul_comm (a ⟨0, hN⟩) _, ← mul_assoc, inv_mul_cancel₀ h2pi_ne, one_mul]

/-- Helper 1: The difference between single-point and multi-point CPV integrands
equals an indicator function a.e. on `Ι γ.a γ.b`. -/
private lemma ae_eq_indicator_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hs : s ∈ S0)
    (f_zpow : ℂ → ℂ) (hf_zpow : f_zpow = fun z => (z - s) ^ (-(m : ℤ)))
    (ε : ℝ) :
    (fun t => (if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0) -
      cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t) =ᵐ[volume.restrict (Ι γ.a γ.b)]
      (({t | ε < ‖γ.toFun t - s‖} \ {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b).indicator
        (fun t => f_zpow (γ.toFun t) * deriv γ.toFun t) := by
  have hIoc_sub : Ι γ.a γ.b ⊆ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le (le_of_lt γ.hab)]; exact Set.Ioc_subset_Icc_self
  filter_upwards [ae_restrict_mem (measurableSet_uIoc)] with t ht
  have ht_Icc : t ∈ Icc γ.a γ.b := hIoc_sub ht
  simp only [cauchyPrincipalValueIntegrandOn, Set.indicator, hf_zpow]
  by_cases h1 : ε < ‖γ.toFun t - s‖ <;>
    by_cases h2 : ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖
  · have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨_, h_nG⟩, _⟩ => h_nG h2
    simp only [h_not_mem, ite_false, if_pos h1,
      if_neg (show ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε from by push Not; exact h2)]
    ring
  · push Not at h2
    obtain ⟨s', hs', hs'_le⟩ := h2
    have h_mem : t ∈ ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b :=
      ⟨⟨h1, fun h_all =>
        absurd (h_all s' hs') (not_lt.mpr hs'_le)⟩, ht_Icc⟩
    simp only [h_mem, ite_true, if_pos h1,
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε from ⟨s', hs', hs'_le⟩)]
    ring
  · push Not at h1
    have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨h_far, _⟩, _⟩ => absurd h_far (not_lt.mpr h1)
    simp only [h_not_mem, ite_false,
      if_neg (show ¬‖γ.toFun t - s‖ > ε from not_lt.mpr h1),
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
        from ⟨s, hs, h1⟩)]
    ring
  · push Not at h1 h2
    have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨h_far, _⟩, _⟩ => absurd h_far (not_lt.mpr h1)
    obtain ⟨s', hs', hs'_le⟩ := h2
    simp only [h_not_mem, ite_false,
      if_neg (show ¬‖γ.toFun t - s‖ > ε from not_lt.mpr h1),
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
        from ⟨s', hs', hs'_le⟩)]
    ring

/-- Helper 2a: The multi-point "good set"
`{t | ∀ s' ∈ S0, ε < ‖γ(t)-s'‖} ∩ Icc` is measurable. -/
lemma measurableSet_goodSet_Icc
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (ε : ℝ) :
    MeasurableSet ({t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) := by
  have h_eq : {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b =
      Icc γ.a γ.b \ ({t | ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b) := by
    ext t; constructor
    · intro ⟨h_good, ht⟩; exact ⟨ht, fun ⟨⟨s', hs', h_le⟩, _⟩ =>
        absurd (h_good s' hs') (not_lt.mpr h_le)⟩
    · intro ⟨ht, h_not⟩; exact ⟨fun s' hs' => by
        by_contra h_le; push Not at h_le; exact h_not ⟨⟨s', hs', h_le⟩, ht⟩, ht⟩
  rw [h_eq]; apply MeasurableSet.diff isClosed_Icc.measurableSet
  have h_eq2 : {t | ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b =
      ⋃ s' ∈ S0, ({t | ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b) := by
    ext t; simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, exists_prop]
    exact ⟨fun ⟨⟨s', hs', h⟩, ht⟩ => ⟨s', hs', h, ht⟩,
           fun ⟨s', hs', h, ht⟩ => ⟨⟨s', hs', h⟩, ht⟩⟩
  rw [h_eq2]; apply Finset.measurableSet_biUnion; intro s' _
  have : {t | ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b =
      Icc γ.a γ.b \ ({t | ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) := by
    ext t; simp only [mem_inter_iff, mem_setOf_eq, mem_diff, not_and]; constructor
    · intro ⟨h_le, ht⟩; exact ⟨ht, fun h_gt => absurd h_gt (not_lt.mpr h_le)⟩
    · intro ⟨ht, h_not⟩; exact ⟨le_of_not_gt (fun h => (h_not h) ht), ht⟩
  rw [this]; exact isClosed_Icc.measurableSet.diff
    (measurableSet_norm_gt_Icc ε
      (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const))

/-- The derivative `deriv γ.toFun` is AEStronglyMeasurable on `Icc γ.a γ.b` for
any `PiecewiseC1Immersion γ`, because it is continuous off the finite partition set. -/
lemma aesm_deriv_on_Icc (γ : PiecewiseC1Immersion) :
    AEStronglyMeasurable (deriv γ.toFun) (volume.restrict (Icc γ.a γ.b)) :=
  aEStronglyMeasurable_of_continuousOn_off_finite (P := γ.partition) (by
    intro t ⟨ht_Icc, ht_nP⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b :=
      ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm fun h =>
        ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)),
       lt_of_le_of_ne ht_Icc.2 fun h =>
        ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2)⟩
    exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
      t ht_Ioo ht_nP).continuousWithinAt)

/-- Helper 2b: `(z-s)^{-m} ∘ γ · γ'` is AEStronglyMeasurable on the "single far" set. -/
private lemma aesm_zpow_on_singleFar
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t)
      (volume.restrict ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b)) := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  have hSF_meas : MeasurableSet ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) :=
    measurableSet_norm_gt_Icc ε (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
  have hf_cont : ContinuousOn (fun t => f_zpow (γ.toFun t))
      ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) := by
    have hf_zpow_cont : ContinuousOn f_zpow {z : ℂ | z - s ≠ 0} :=
      ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) (-(m : ℤ))
        (fun z hz => Or.inl hz)
    have h_maps : Set.MapsTo γ.toFun
        ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) {z | z - s ≠ 0} := by
      intro t ⟨ht_far, _⟩
      change γ.toFun t - s ≠ 0
      exact sub_ne_zero.mpr (fun heq => by
        have : ε < ‖γ.toFun t - s‖ := ht_far
        rw [heq, sub_self, norm_zero] at this; linarith)
    exact hf_zpow_cont.comp
      (γ.toPiecewiseC1Curve.continuous_toFun.mono Set.inter_subset_right) h_maps
  exact (hf_cont.aestronglyMeasurable hSF_meas).mul
    ((aesm_deriv_on_Icc γ).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

/-- Helper 2: The difference between single-point and multi-point CPV integrands
of `(z-s)^{-m}` is AEStronglyMeasurable on `Ι γ.a γ.b`. Assembled from
`ae_eq_indicator_diff_cpv_zpow`, `aesm_zpow_on_singleFar`, and
`measurableSet_goodSet_Icc`. -/
private lemma aesm_diff_single_multi_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0 (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      (volume.restrict (Ι γ.a γ.b)) := by
  have h_diff_ae := ae_eq_indicator_diff_cpv_zpow S0 γ s m hs
    (fun z => (z - s) ^ (-(m : ℤ))) rfl ε
  apply AEStronglyMeasurable.congr _ h_diff_ae.symm
  have hSF_meas : MeasurableSet ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) :=
    measurableSet_norm_gt_Icc ε (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
  have hSG_sub :
      ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b ⊆
      {t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b :=
    Set.inter_subset_inter_left _ Set.diff_subset
  have hSG_meas : MeasurableSet (({t | ε < ‖γ.toFun t - s‖} \
      {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩ Icc γ.a γ.b) := by
    rw [show ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩ Icc γ.a γ.b =
      ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) \
        ({t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) from by
        ext x; simp only [mem_inter_iff, mem_diff]; tauto]
    exact hSF_meas.diff (measurableSet_goodSet_Icc S0 γ ε)
  apply ((AEStronglyMeasurable.piecewise hSG_meas
    ((aesm_zpow_on_singleFar γ s m ε hε).mono_measure (Measure.restrict_mono hSG_sub le_rfl))
    (aestronglyMeasurable_const (β := ℂ) (b := 0))).mono_measure
      Measure.restrict_le_self).congr
  filter_upwards with t
  simp only [Set.piecewise, Set.indicator]

/-- A.e. `t` in the integration interval `Ι γ.a γ.b` does not land on any
point of `S0` under `γ`, because each crossing set is finite (hence null). -/
lemma ae_forall_ne_of_finite_crossings
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b → ∀ s ∈ S0, γ.toFun t ≠ s := by
  have h_preimage_finite : (⋃ s ∈ S0, {t ∈ Icc γ.a γ.b | γ.toFun t = s}).Finite :=
    Set.Finite.biUnion S0.finite_toSet (fun s _ => finite_crossings γ s)
  rw [Filter.eventually_iff, mem_ae_iff]
  refine le_antisymm ?_ zero_le
  calc volume {t | ¬(t ∈ Ι γ.a γ.b → ∀ s ∈ S0, γ.toFun t ≠ s)}
      ≤ volume (⋃ s ∈ S0, {t ∈ Icc γ.a γ.b | γ.toFun t = s}) := by
        apply measure_mono; intro t ht; push Not at ht
        obtain ⟨ht_in, s, hs, hts⟩ := ht
        exact Set.mem_biUnion hs
          ⟨Ioc_subset_Icc_self (Set.uIoc_of_le γ.hab.le ▸ ht_in), hts⟩
    _ = 0 := h_preimage_finite.measure_zero _

/-! ### Sublemma 2: Multi-point CPV of higher-order pole term → 0 -/

/-- Norm bound for the zpow integrand: if `‖γ(t) - s‖ > ε` then
`‖(γ(t)-s)^{-m} · γ'(t)‖ ≤ ε⁻¹^m · (|Mγ'| + 1)`. -/
private lemma zpow_deriv_norm_bound
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc γ.a γ.b)
    (h_far : ‖γ.toFun t - s‖ > ε) :
    ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t‖ ≤
      ε⁻¹ ^ m * (|Mγ'| + 1) := by
  calc ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t‖
      ≤ ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t)‖ * ‖deriv γ.toFun t‖ :=
        norm_mul_le _ _
    _ ≤ ε⁻¹ ^ m * (|Mγ'| + 1) := by
        apply mul_le_mul
        · simp only []
          rw [norm_zpow, zpow_neg, zpow_natCast, inv_pow]
          exact inv_anti₀ (by positivity)
            (pow_le_pow_left₀ hε.le h_far.le m)
        · exact le_trans
            ((hMγ' t ht).trans (le_abs_self _))
            (le_add_of_nonneg_right one_pos.le)
        · exact norm_nonneg _
        · positivity

/-- The single-point cutoff integrand of `(z-s)^{-m} · γ'` is interval integrable. -/
private lemma single_cutoff_zpow_intervalIntegrable
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then
        (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0)
      volume γ.a γ.b := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  have h_eq_cpv : (fun t => if ‖γ.toFun t - s‖ > ε then
      f_zpow (γ.toFun t) * deriv γ.toFun t else 0) =
    (fun t =>
      cauchyPrincipalValueIntegrandOn {s} f_zpow γ.toFun ε t) :=
    funext fun t => by rw [cauchyPrincipalValueIntegrandOn_singleton]
  rw [h_eq_cpv]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt γ.hab)]
  refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
  refine integrableOn_of_bounded_aeMeasurable (M := ε⁻¹ ^ m * (|Mγ'| + 1)) ?_ ?_
  · have h_aesm_if : AEStronglyMeasurable
        (fun t => if ε < ‖γ.toFun t - s‖ then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)
        (volume.restrict (Icc γ.a γ.b)) := by
      apply aEStronglyMeasurable_pv_integrand_piecewiseC1
        (P := γ.partition) (z₀ := s)
      · intro z ⟨_, hz_not_ball⟩
        have hz_ne : z ≠ s := by
          intro heq; exact hz_not_ball (by rw [Metric.mem_ball, heq, dist_self]; exact hε)
        exact ((continuousAt_id.sub continuousAt_const).zpow₀ (-(m : ℤ))
          (Or.inl (sub_ne_zero.mpr hz_ne))).continuousWithinAt
      · exact γ.toPiecewiseC1Curve.continuous_toFun
      · intro t ⟨ht_Icc, ht_nP⟩
        have ht_Ioo : t ∈ Ioo γ.a γ.b := by
          refine ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm fun h =>
            ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)), ?_⟩
          exact lt_of_le_of_ne ht_Icc.2 fun h =>
            ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2)
        exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
          t ht_Ioo ht_nP).continuousWithinAt
    exact h_aesm_if.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t _
      exact (cauchyPrincipalValueIntegrandOn_singleton f_zpow γ.toFun s ε t).symm)
  · intro t ht
    rw [cauchyPrincipalValueIntegrandOn_singleton]
    split_ifs with h
    · exact zpow_deriv_norm_bound γ s m Mγ' hMγ' ε hε t ht h
    · simp only [norm_zero]; positivity

/-- The multi-point cutoff integrand of `(z-s)^{-m} · γ'` is interval integrable. -/
private lemma multi_cutoff_zpow_intervalIntegrable
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      volume γ.a γ.b := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt γ.hab)]
  refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
  refine integrableOn_of_bounded_aeMeasurable (M := ε⁻¹ ^ m * (|Mγ'| + 1)) ?_ ?_
  · let GoodSet := {t : ℝ | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}
    have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc γ.a γ.b) :=
      measurableSet_goodSet_Icc S0 γ ε
    have hfγ_cont_good : ContinuousOn (fun t => f_zpow (γ.toFun t))
        (GoodSet ∩ Icc γ.a γ.b) := by
      have hf_cont : ContinuousOn f_zpow {z : ℂ | z - s ≠ 0} :=
        ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) (-(m : ℤ))
          (fun z hz => Or.inl hz)
      have h_maps : Set.MapsTo γ.toFun (GoodSet ∩ Icc γ.a γ.b) {z | z - s ≠ 0} := by
        intro t ⟨ht_good, _⟩
        exact sub_ne_zero.mpr (fun heq => by
          have := ht_good s hs; rw [heq, sub_self, norm_zero] at this; linarith)
      exact hf_cont.comp
        (γ.toPiecewiseC1Curve.continuous_toFun.mono Set.inter_subset_right) h_maps
    have hγ'_meas := aesm_deriv_on_Icc γ
    have h_prod_meas : AEStronglyMeasurable (fun t => f_zpow (γ.toFun t) * deriv γ.toFun t)
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)) :=
      (hfγ_cont_good.aestronglyMeasurable hGoodSet_meas).mul
        (hγ'_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)ᶜ) := aestronglyMeasurable_const
    have h_pw := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas h_zero_meas
    exact (h_pw.mono_measure Measure.restrict_le_self).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [cauchyPrincipalValueIntegrandOn]
      by_cases ht_good : t ∈ GoodSet ∩ Icc γ.a γ.b
      · rw [Set.piecewise_eq_of_mem _ _ _ ht_good]
        have : ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by push Not; exact ht_good.1
        rw [if_neg this]
      · rw [Set.piecewise_eq_of_notMem _ _ _ ht_good]
        have : ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by
          by_contra h; push Not at h; exact ht_good ⟨h, ht⟩
        rw [if_pos this])
  · intro t ht
    simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h
    · simp only [norm_zero]; positivity
    · push Not at h; exact zpow_deriv_norm_bound γ s m Mγ' hMγ' ε hε t ht (h s hs)

/-- DCT bound for the difference between single-point and multi-point CPV
integrands: when `ε < δ_sep / 2`, the difference is bounded by
`(δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1)`. -/
private lemma dct_bound_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0) (_hS0_single : S0 ≠ {s})
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (δ_sep : ℝ) (hδ_pos : 0 < δ_sep)
    (hδ_sep_le : ∀ s' ∈ S0.erase s, δ_sep ≤ ‖s - s'‖)
    (ε : ℝ) (hε : ε ∈ Ioo 0 (δ_sep / 2)) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖(if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t‖ ≤
      (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1) := by
  have hε2 := hε.2
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  apply ae_of_all; intro t ht
  simp only [cauchyPrincipalValueIntegrandOn]
  by_cases h_multi_cut : ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
  · rw [if_pos h_multi_cut]
    by_cases h_single_cut : ‖γ.toFun t - s‖ > ε
    · rw [if_pos h_single_cut]; simp only [sub_zero]
      obtain ⟨s', hs', hs'_close⟩ := h_multi_cut
      have hs'_ne : s' ≠ s := by intro heq; rw [heq] at hs'_close; linarith
      have h_sep_s' : δ_sep ≤ ‖s - s'‖ :=
        hδ_sep_le s' (Finset.mem_erase.mpr ⟨hs'_ne, hs'⟩)
      have h_far : ‖γ.toFun t - s‖ ≥ δ_sep / 2 := by
        have h1 : ‖s - s'‖ ≤ ‖γ.toFun t - s‖ + ‖γ.toFun t - s'‖ := by
          calc ‖s - s'‖ = ‖(s - γ.toFun t) + (γ.toFun t - s')‖ := by ring_nf
            _ ≤ ‖s - γ.toFun t‖ + ‖γ.toFun t - s'‖ := norm_add_le _ _
            _ = ‖γ.toFun t - s‖ + ‖γ.toFun t - s'‖ := by rw [norm_sub_rev]
        linarith [hε2]
      have ht_Icc : t ∈ Icc γ.a γ.b :=
        Ioc_subset_Icc_self (Set.uIoc_of_le γ.hab.le ▸ ht)
      calc ‖f_zpow (γ.toFun t) * deriv γ.toFun t‖
          ≤ ‖f_zpow (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
        _ ≤ (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1) := by
            apply mul_le_mul
            · change ‖f_zpow (γ.toFun t)‖ ≤ (δ_sep / 2)⁻¹ ^ m
              simp only [f_zpow]
              rw [norm_zpow, zpow_neg, zpow_natCast, inv_pow]
              exact inv_anti₀ (by positivity)
                (pow_le_pow_left₀ (by linarith) h_far m)
            · exact le_trans ((hMγ' t ht_Icc).trans (le_abs_self _))
                (le_add_of_nonneg_right one_pos.le)
            · exact norm_nonneg _
            · positivity
    · push Not at h_single_cut; rw [if_neg (not_lt.mpr h_single_cut)]
      norm_num; positivity
  · rw [if_neg h_multi_cut]
    by_cases h_single_cut : ‖γ.toFun t - s‖ > ε
    · rw [if_pos h_single_cut]; norm_num; positivity
    · push Not at h_single_cut h_multi_cut
      exact absurd (h_multi_cut s hs) (not_lt.mpr h_single_cut)

/-- A.e. pointwise limit of the single-multi CPV difference is 0 when `t` does
not land on any point of `S0`. -/
private lemma ae_limit_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0) (hS0_ne : S0.Nonempty) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε =>
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_forall_ne_of_finite_crossings S0 γ] with t h_not_cross ht_in
  have h_nc := h_not_cross ht_in
  apply tendsto_const_nhds.congr'
  let δ_t := S0.inf' hS0_ne (fun s' => ‖γ.toFun t - s'‖)
  have hδ_t_pos : 0 < δ_t := by
    apply (Finset.lt_inf'_iff _).mpr
    intro s' hs'; exact norm_pos_iff.mpr (sub_ne_zero.mpr (h_nc s' hs'))
  filter_upwards [Ioo_mem_nhdsGT hδ_t_pos] with ε hε
  simp only [cauchyPrincipalValueIntegrandOn]
  have h_no_near : ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by
    push Not; intro s' hs'
    exact lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs')
  rw [if_neg h_no_near]
  have h_far_s : ‖γ.toFun t - s‖ > ε :=
    lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs)
  rw [if_pos h_far_s]; ring

/-- Reduce the multi-point CPV goal to showing the single-multi difference
tends to 0, using `Tendsto.sub` and `integral_sub`. -/
private lemma reduce_to_diff_tendsto_zero
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (h_single : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0))
      (𝓝[>] 0) (𝓝 0))
    (h_diff : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        ((if ‖γ.toFun t - s‖ > ε then
            (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
         cauchyPrincipalValueIntegrandOn S0
           (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  have h_single_int : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable
        (fun t => if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)
        volume γ.a γ.b :=
    fun ε hε => single_cutoff_zpow_intervalIntegrable γ s m Mγ' hMγ' ε hε
  have h_multi_int : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable
        (fun t => cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t)
        volume γ.a γ.b :=
    fun ε hε => multi_cutoff_zpow_intervalIntegrable S0 γ s m hs Mγ' hMγ' ε hε
  have h_eventually_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t =
      (∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)) -
      ∫ t in γ.a..γ.b,
        ((if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0) -
         cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    rw [← intervalIntegral.integral_sub (h_single_int ε hε)
      ((h_single_int ε hε).sub (h_multi_int ε hε))]
    congr 1; ext t; ring
  have h_sub := h_single.sub h_diff
  simp only [sub_self] at h_sub
  exact h_sub.congr' (h_eventually_eq.mono fun ε h => h.symm)

/-- **Sublemma 2**: The multi-point CPV integral of `(z-s)^{-m}` tends to 0
for `m ≥ 2`, given flatness of order `m` and the angle condition.

This extends `pv_higher_order_term_tendsto_zero` from single-point to
multi-point cutoff. The difference between multi-point and single-point
cutoffs is supported on a set where `(z-s)^{-m}` is bounded (far from `s`,
near some other `s' ∈ S0`) and whose measure tends to 0. -/
theorem multipoint_pv_zpow_tendsto_zero (S0 : Finset ℂ)
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m) (hs : s ∈ S0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (h_angle : ∃ k : ℤ, ((m - 1 : ℕ) : ℝ) * _root_.angleAtCrossing γ t₀ ht₀ =
      ↑k * (2 * Real.pi)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have h_single : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0))
      (𝓝[>] 0) (𝓝 0) :=
    pv_higher_order_term_tendsto_zero γ s m hm t₀ ht₀ hcross h_unique
      hγ_closed h_flat h_angle
  apply reduce_to_diff_tendsto_zero S0 γ s m hs Mγ' hMγ' h_single
  by_cases hS0_single : S0 = {s}
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    show 0 = _
    rw [show (∫ t in γ.a..γ.b,
          ((if ‖γ.toFun t - s‖ > ε then
              (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
           cauchyPrincipalValueIntegrandOn S0
             (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)) =
        ∫ t in γ.a..γ.b, (0 : ℂ) from by
      congr 1; ext t
      rw [hS0_single, cauchyPrincipalValueIntegrandOn_singleton]; ring_nf]
    simp only [intervalIntegral.integral_zero]
  · have hS0_ne : S0.Nonempty := ⟨s, hs⟩
    let δ_sep := (S0.erase s).inf' (by
      exact (Finset.erase_nonempty hs).mpr
        ((Finset.nontrivial_iff_ne_singleton hs).mpr hS0_single))
      (fun s' => ‖s - s'‖)
    have hδ_pos : 0 < δ_sep := by
      apply (Finset.lt_inf'_iff _).mpr
      intro s' hs'
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_erase hs').symm)
    have hδ_sep_le : ∀ s' ∈ S0.erase s, δ_sep ≤ ‖s - s'‖ :=
      fun s' hs' => Finset.inf'_le _ hs'
    have h_dct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1))
      (by filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
          exact aesm_diff_single_multi_cpv_zpow S0 γ s m hs ε hε)
      (by filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ_sep / 2 by linarith)]
            with ε hε
          exact dct_bound_diff_cpv_zpow S0 γ s m hs hS0_single Mγ' hMγ'
            δ_sep hδ_pos hδ_sep_le ε hε)
      intervalIntegrable_const
      (ae_limit_diff_cpv_zpow S0 γ s m hs hS0_ne)
    simp only [intervalIntegral.integral_zero] at h_dct
    exact h_dct

end GeneralizedResidueTheory
