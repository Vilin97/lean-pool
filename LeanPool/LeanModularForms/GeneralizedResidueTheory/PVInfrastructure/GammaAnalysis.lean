/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# PV Infrastructure: Gamma Analysis

Derivative-based bounds on curves near crossing points. These are
used in the dyadic PV limit proof for principal value convergence.

## Main Results

* `gamma_lower_bound_of_hasDerivAt` — lower bound
    ‖γ - γ₀‖ ≥ (‖L‖/2)|t - t₀|
* `gamma_upper_bound_of_hasDerivAt` — upper bound
    ‖γ - γ₀‖ ≤ 2‖L‖|t - t₀|
* `no_return_of_inj_continuous` — γ bounded away from γ(t₀)
    outside nbhd
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

private lemma hasDerivAt_remainder_bound
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ε * |t - t₀| := by
  intro ε hε
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hγ
  obtain ⟨s, hs_mem, hs⟩ := (hγ hε).exists_mem
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hs_mem
  refine ⟨δ, hδ_pos, fun t _ ht_lt => ?_⟩
  have h_bound := hs t (hδ_ball (by simp [Metric.mem_ball, Real.dist_eq, ht_lt]))
  simpa only [Real.norm_eq_abs] using h_bound

private lemma norm_real_smul (x : ℝ) (L : ℂ) :
    ‖x • L‖ = |x| * ‖L‖ := by
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  rw [norm_smul, Real.norm_eq_abs]

private lemma norm_add_lower_bound (a b : ℂ) :
    ‖a + b‖ ≥ ‖a‖ - ‖b‖ := by
  have h := norm_sub_norm_le a (-b)
  simp only [sub_neg_eq_add, norm_neg] at h
  linarith

private lemma farSet_isCompact
    (a b t₀ δ : ℝ) (_hab : a < b) (_hδ : 0 < δ) :
    IsCompact {t | t ∈ Set.Icc a b ∧ δ ≤ |t - t₀|} := by
  apply IsCompact.inter_right isCompact_Icc
  have : IsClosed {t : ℝ | δ ≤ |t - t₀|} :=
    isClosed_le continuous_const
      (continuous_abs.comp (continuous_sub_right t₀))
  exact this

private lemma norm_sub_pos_on_farSet
    (γ : ℝ → ℂ) (a b t₀ δ : ℝ)
    (hab : a < b) (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj_far : ∀ t ∈ Set.Icc a b,
      δ ≤ |t - t₀| → γ t ≠ γ t₀) :
    ∃ m > 0, ∀ t ∈ Set.Icc a b,
      δ ≤ |t - t₀| → m ≤ ‖γ t - γ t₀‖ := by
  let farSet := {t | t ∈ Set.Icc a b ∧ δ ≤ |t - t₀|}
  have h_compact : IsCompact farSet :=
    farSet_isCompact a b t₀ δ hab hδ
  have h_cont_norm :
      ContinuousOn (fun t => ‖γ t - γ t₀‖) (Set.Icc a b) := by
    apply Continuous.comp_continuousOn continuous_norm
    exact hγ_cont.sub continuousOn_const
  by_cases h_nonempty : farSet.Nonempty
  · have h_cont_on_far :
        ContinuousOn (fun t => ‖γ t - γ t₀‖) farSet :=
      h_cont_norm.mono (fun t ht => ht.1)
    obtain ⟨t_min', ht_min'_mem, ht_min'_min⟩ :=
      h_compact.exists_isMinOn h_nonempty h_cont_on_far
    have h_min_pos : 0 < ‖γ t_min' - γ t₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr
        (h_inj_far t_min' ht_min'_mem.1 ht_min'_mem.2))
    exact ⟨‖γ t_min' - γ t₀‖, h_min_pos,
      fun t ht1 ht2 => ht_min'_min ⟨ht1, ht2⟩⟩
  · exact ⟨1, one_pos, fun t ht1 ht2 => by
      exfalso; exact h_nonempty ⟨t, ht1, ht2⟩⟩

/-- The integrand times (t-t₀) tends to 1.
This is the key estimate:
(t-t₀) * (γ-γ₀)⁻¹ * γ' → 1 as t → t₀. -/
lemma integrand_times_t_tendsto_one
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀)
    (hγ_cont_at : ContinuousAt (deriv γ) t₀) :
    Tendsto
      (fun t => (↑(t - t₀) : ℂ) *
        (γ t - γ t₀)⁻¹ * deriv γ t)
      (𝓝[≠] t₀) (𝓝 1) := by
  have h_deriv_eq : deriv γ t₀ = L := hγ_hasderiv.deriv
  have h_deriv_tendsto : Tendsto (deriv γ) (𝓝 t₀) (𝓝 L) :=
    by rw [← h_deriv_eq]; exact hγ_cont_at
  have h_ratio_tendsto :
      Tendsto (fun t => (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹)
        (𝓝[≠] t₀) (𝓝 L⁻¹) := by
    have h_slope :
        Tendsto (fun t => (t - t₀)⁻¹ • (γ t - γ t₀))
          (𝓝[≠] t₀) (𝓝 L) := by
      rw [hasDerivAt_iff_tendsto_slope_zero] at hγ_hasderiv
      have h_comp :
          (fun t => (t - t₀)⁻¹ • (γ t - γ t₀)) =
          (fun s => s⁻¹ • (γ (t₀ + s) - γ t₀)) ∘
            (fun t => t - t₀) := by
        ext t; simp [add_sub_cancel]
      rw [h_comp]
      apply Tendsto.comp hγ_hasderiv
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h1 : Tendsto (fun t => t - t₀)
            (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
          tendsto_id.sub_const t₀
        simp only [sub_self] at h1; exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_compl_iff,
          Set.mem_singleton_iff, sub_ne_zero]
        exact ht
    have h_smul_eq :
        ∀ t : ℝ, (t - t₀)⁻¹ • (γ t - γ t₀) =
          (γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹ := by
      intro t; rw [Algebra.smul_def]; simp [mul_comm]
    have h_slope' :
        Tendsto
          (fun t => (γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹)
          (𝓝[≠] t₀) (𝓝 L) := by
      simp only [← h_smul_eq]; exact h_slope
    have h_recip :
        Tendsto
          (fun t =>
            ((γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹)⁻¹)
          (𝓝[≠] t₀) (𝓝 L⁻¹) :=
      h_slope'.inv₀ hL
    have h_inv_eq : ∀ t : ℝ,
        ((γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹)⁻¹ =
          (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ := by
      intro t
      by_cases h : γ t - γ t₀ = 0
      · simp [h]
      · by_cases ht : (t : ℂ) - t₀ = 0
        · simp [ht]
        · field_simp
    simp only [h_inv_eq] at h_recip; exact h_recip
  have h_prod :
      Tendsto
        (fun t => (↑(t - t₀) : ℂ) *
          (γ t - γ t₀)⁻¹ * deriv γ t)
        (𝓝[≠] t₀) (𝓝 (L⁻¹ * L)) :=
    Tendsto.mul h_ratio_tendsto
      (h_deriv_tendsto.mono_left nhdsWithin_le_nhds)
  simp only [inv_mul_cancel₀ hL] at h_prod
  exact h_prod

/-- Asymptotic control:
‖(γ-γ₀)⁻¹ * γ' - (t-t₀)⁻¹‖ ≤ ε / |t-t₀|. -/
lemma integrand_asymptotic
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ)
    (_hL : L ≠ 0)
    (_hγ_hasderiv : HasDerivAt γ L t₀)
    (_hγ_cont_at : ContinuousAt (deriv γ) t₀)
    (h_tendsto :
      Tendsto
        (fun t => (↑(t - t₀) : ℂ) *
          (γ t - γ t₀)⁻¹ * deriv γ t)
        (𝓝[≠] t₀) (𝓝 1)) :
    ∀ ε > 0, ∃ δ > 0, ∀ t,
      0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t -
        (↑(t - t₀))⁻¹‖ ≤ ε / |t - t₀| := by
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h_tendsto
  obtain ⟨δ, hδ_pos, hδ⟩ := h_tendsto ε hε
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_ne : t ≠ t₀ := fun h => by simp [h] at ht_pos
  have h_bound := hδ h_ne (by rwa [Real.dist_eq])
  rw [Complex.dist_eq] at h_bound
  have h_ne_c : (↑(t - t₀) : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero, sub_eq_zero]
    exact h_ne
  have h_key :
      (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹ =
      ((↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ *
        deriv γ t - 1) * (↑(t - t₀))⁻¹ := by
    field_simp
  rw [h_key]
  calc ‖((↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ *
        deriv γ t - 1) * (↑(t - t₀))⁻¹‖
      = ‖(↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ *
          deriv γ t - 1‖ *
        ‖(↑(t - t₀) : ℂ)⁻¹‖ := norm_mul _ _
    _ ≤ ε * ‖(↑(t - t₀) : ℂ)⁻¹‖ := by
        apply mul_le_mul_of_nonneg_right
          (le_of_lt h_bound) (norm_nonneg _)
    _ = ε / |t - t₀| := by
        rw [norm_inv, Complex.norm_real,
          Real.norm_eq_abs, div_eq_mul_inv]

/-- Lower bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses `hasDerivAt_remainder_bound` + reverse triangle
inequality. -/
lemma gamma_lower_bound_of_hasDerivAt
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀| := by
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    hasDerivAt_remainder_bound hγ_hasderiv
      (‖L‖ / 2) (half_pos hLnorm_pos)
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_rem :
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        (‖L‖ / 2) * |t - t₀| :=
    hδ_bound t ht_pos ht_lt
  have h_decomp :
      (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) =
        γ t - γ t₀ := by ring
  have h_tri :
      ‖γ t - γ t₀‖ ≥
        ‖(t - t₀) • L‖ -
          ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    have h1 :
        ‖γ t - γ t₀‖ =
          ‖(t - t₀) • L +
            (γ t - γ t₀ - (t - t₀) • L)‖ := by
      congr 1; ring
    rw [h1]
    exact norm_add_lower_bound _ _
  have h_smul : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ :=
    norm_real_smul (t - t₀) L
  calc ‖γ t - γ t₀‖
      ≥ ‖(t - t₀) • L‖ -
          ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≥ |t - t₀| * ‖L‖ -
          (‖L‖ / 2) * |t - t₀| := by
        rw [h_smul]; linarith
    _ = (‖L‖ / 2) * |t - t₀| := by ring

/-- Upper bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses `hasDerivAt_remainder_bound` + triangle inequality. -/
lemma gamma_upper_bound_of_hasDerivAt
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ →
      ‖γ t - γ t₀‖ ≤ 2 * ‖L‖ * |t - t₀| := by
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    hasDerivAt_remainder_bound hγ_hasderiv ‖L‖ hLnorm_pos
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_rem :
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        ‖L‖ * |t - t₀| :=
    hδ_bound t ht_pos ht_lt
  have h_tri :
      ‖γ t - γ t₀‖ ≤
        ‖(t - t₀) • L‖ +
          ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    have h1 :
        ‖γ t - γ t₀‖ =
          ‖(t - t₀) • L +
            (γ t - γ t₀ - (t - t₀) • L)‖ := by
      congr 1; ring
    rw [h1]
    exact norm_add_le _ _
  have h_smul : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ :=
    norm_real_smul (t - t₀) L
  calc ‖γ t - γ t₀‖
      ≤ ‖(t - t₀) • L‖ +
          ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≤ |t - t₀| * ‖L‖ +
          ‖L‖ * |t - t₀| := by
        rw [h_smul]; linarith
    _ = 2 * ‖L‖ * |t - t₀| := by ring

/-- If γ is continuous on [a,b] and injective at γ(t₀),
then γ stays bounded away from γ(t₀) outside any
neighborhood of t₀. -/
lemma no_return_of_inj_continuous
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b,
      γ t = γ t₀ → t = t₀) :
    ∃ ρ > 0, ∀ t ∈ Set.Icc a b,
      c ≤ |t - t₀| → ρ ≤ ‖γ t - γ t₀‖ := by
  let S := Set.Icc a b ∩ {t | c ≤ |t - t₀|}
  have hS_compact : IsCompact S :=
    isCompact_Icc.inter_right
      (isClosed_le continuous_const
        (continuous_abs.comp
          (continuous_id.sub continuous_const)))
  have hf_cont :
      ContinuousOn (fun t => ‖γ t - γ t₀‖) S :=
    ((hγ_cont.mono Set.inter_subset_left).sub
      continuousOn_const).norm
  have hf_pos :
      ∀ t ∈ S, (0 : ℝ) < ‖γ t - γ t₀‖ := by
    intro t ⟨ht_Icc, ht_dist⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro h_eq
    have h_t_eq := h_inj t ht_Icc h_eq
    subst h_t_eq; simp only [Set.mem_setOf_eq, sub_self, abs_zero] at ht_dist; linarith
  obtain ⟨ρ, hρ_pos, hρ_le⟩ :=
    hS_compact.exists_forall_le' hf_cont hf_pos
  exact ⟨ρ, hρ_pos,
    fun t ht h_dist => hρ_le t ⟨ht, h_dist⟩⟩

/-- From γ-space upper bound to t-space upper bound:
If ‖γ t - γ t₀‖ ≤ εC and we have the lower bound,
then |t - t₀| ≤ 2*εC/‖L‖. -/
lemma t_bound_from_gamma_bound
    {γ : ℝ → ℂ} {t₀ t : ℝ} {L : ℂ} {εC δ : ℝ}
    (hL : L ≠ 0) (_hδ_pos : 0 < δ)
    (ht_pos : 0 < |t - t₀|)
    (ht_lt : |t - t₀| < δ)
    (h_lower : ∀ s, 0 < |s - t₀| →
      |s - t₀| < δ →
      ‖γ s - γ t₀‖ ≥ (‖L‖ / 2) * |s - t₀|)
    (h_gamma_bound : ‖γ t - γ t₀‖ ≤ εC) :
    |t - t₀| ≤ 2 * εC / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h1 : (‖L‖ / 2) * |t - t₀| ≤ εC := le_trans (h_lower t ht_pos ht_lt) h_gamma_bound
  calc |t - t₀|
      = (‖L‖ / 2 * |t - t₀|) / (‖L‖ / 2) := by field_simp
    _ ≤ εC / (‖L‖ / 2) := div_le_div_of_nonneg_right h1 (half_pos hL_norm_pos).le
    _ = 2 * εC / ‖L‖ := by field_simp

/-- From γ-space lower bound to t-space lower bound:
If ‖γ t - γ t₀‖ > εC and we have the upper bound,
then |t - t₀| > εC/(2*‖L‖). -/
lemma t_lower_from_gamma_lower
    {γ : ℝ → ℂ} {t₀ t : ℝ} {L : ℂ} {εC δ : ℝ}
    (hL : L ≠ 0) (_hδ_pos : 0 < δ)
    (ht_pos : 0 < |t - t₀|)
    (ht_lt : |t - t₀| < δ)
    (h_upper : ∀ s, 0 < |s - t₀| →
      |s - t₀| < δ →
      ‖γ s - γ t₀‖ ≤ 2 * ‖L‖ * |s - t₀|)
    (h_gamma_lower : εC < ‖γ t - γ t₀‖) :
    εC / (2 * ‖L‖) < |t - t₀| := by
  have h1 : εC < 2 * ‖L‖ * |t - t₀| := lt_of_lt_of_le h_gamma_lower (h_upper t ht_pos ht_lt)
  calc εC / (2 * ‖L‖)
      < (2 * ‖L‖ * |t - t₀|) / (2 * ‖L‖) :=
        div_lt_div_of_pos_right h1 (by linarith [norm_pos_iff.mpr hL])
    _ = |t - t₀| := by field_simp

/-- If γ is C² at t₀, then deriv γ is continuous at t₀. -/
lemma contAt_deriv_of_contDiffAt_two
    {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) :
    ContinuousAt (deriv γ) t₀ := by
  obtain ⟨u, hu_mem, hγ_on⟩ :=
    hγ_C2.contDiffOn (m := 2) le_rfl
      (by norm_cast)
  obtain ⟨ε, hε_pos, hball_sub⟩ :=
    Metric.mem_nhds_iff.mp hu_mem
  have hγ_ball :
      ContDiffOn ℝ 2 γ (Metric.ball t₀ ε) :=
    hγ_on.mono hball_sub
  have h_fderiv_cont :
      ContinuousOn (fderiv ℝ γ) (Metric.ball t₀ ε) :=
    hγ_ball.continuousOn_fderiv_of_isOpen
      Metric.isOpen_ball (by norm_cast)
  have h_mem_ball : t₀ ∈ Metric.ball t₀ ε :=
    Metric.mem_ball_self hε_pos
  have h_cont_at_fderiv :
      ContinuousAt (fderiv ℝ γ) t₀ :=
    h_fderiv_cont.continuousAt
      (Metric.isOpen_ball.mem_nhds h_mem_ball)
  have h_deriv_eq :
      deriv γ = (fun t => fderiv ℝ γ t 1) := by
    ext t
    by_cases h : DifferentiableAt ℝ γ t
    · rw [fderiv_apply_one_eq_deriv]
    · simp [deriv_zero_of_not_differentiableAt h,
        fderiv_zero_of_not_differentiableAt h]
  rw [h_deriv_eq]
  exact h_cont_at_fderiv.clm_apply continuousAt_const

end
