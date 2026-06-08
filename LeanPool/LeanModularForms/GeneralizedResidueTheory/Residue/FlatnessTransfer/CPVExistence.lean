/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.HigherOrderAssembly

/-!
# CPV Existence for Inverse along Piecewise C¹ Immersions

CPV existence for `(z-z₀)⁻¹` along closed piecewise C¹ immersions with a unique
crossing point. This is infrastructure needed by both the convex and
null-homologous residue theorems.

## Main results

* `cpv_exists_inv_sub_of_closed_unique`: CPV of `(z-z₀)⁻¹` exists for closed curves
  with a unique crossing through `z₀`.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

private lemma continuousOn_cutoff_integral
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (_ht₀ : t₀ ∈ Set.Ioo γ.a γ.b)
    (_hcross : γ.toFun t₀ = z₀)
    (_honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (δ : ℝ) (_hδ : δ > 0)
    (hbnd : ∀ ε ∈ Set.Ioo 0 δ, ∃ σ₁ σ₂,
      γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧
      ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧
      (∀ t ∈ Set.Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧
      (∀ t ∈ Set.Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧
      ∀ t ∈ Set.Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε)
    (l r : ℝ) (hl_lt : l < t₀) (hr_gt : t₀ < r)
    (_hl_ge_a : γ.a ≤ l) (_hr_le_b : r ≤ γ.b)
    (hg_anti : StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Set.Icc l t₀))
    (hg_mono : StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Set.Icc t₀ r))
    (hδ_le_l : δ ≤ ‖γ.toFun l - z₀‖) (hδ_le_r : δ ≤ ‖γ.toFun r - z₀‖) :
    ContinuousOn (fun ε => ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)
      (Set.Ioo 0 δ) := by
  intro ε₀ hε₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM γ.a (left_mem_Icc.mpr γ.hab.le))
  have hε₀_pos : (0 : ℝ) < ε₀ := hε₀.1
  have hε₀_half : (0 : ℝ) < ε₀ / 2 := by linarith
  have h_level_null : volume {t ∈ Icc γ.a γ.b | ‖γ.toFun t - z₀‖ = ε₀} = 0 := by
    obtain ⟨σ₁, σ₂, hσ₁_ge, hσ₁_lt, hσ₂_gt, hσ₂_le,
      hσ₁_val, hσ₂_val, h_left, h_right, h_mid⟩ := hbnd ε₀ hε₀
    have hσ₁_ge_l : l ≤ σ₁ := by
      by_contra h_lt; push Not at h_lt
      have hl_in : l ∈ Icc σ₁ σ₂ := ⟨h_lt.le, le_trans hl_lt.le hσ₂_gt.le⟩
      exact absurd (h_mid l hl_in) (not_le.mpr (by linarith [hδ_le_l, hε₀.2]))
    have hσ₂_le_r : σ₂ ≤ r := by
      by_contra h_gt; push Not at h_gt
      have hr_in : r ∈ Icc σ₁ σ₂ :=
        ⟨le_trans hσ₁_lt.le (le_trans (le_of_lt hr_gt) (le_refl r)), h_gt.le⟩
      exact absurd (h_mid r hr_in) (not_le.mpr (by linarith [hδ_le_r, hε₀.2]))
    apply measure_mono_null (t := ({σ₁, σ₂} : Set ℝ))
    · intro t ⟨ht_Icc, ht_eq⟩
      have ht_σ : t ∈ Icc σ₁ σ₂ := by
        refine ⟨?_, ?_⟩
        · by_contra h; push Not at h; linarith [h_left t ⟨ht_Icc.1, h⟩]
        · by_contra h; push Not at h; linarith [h_right t ⟨h, ht_Icc.2⟩]
      rcases le_or_gt t t₀ with htt₀ | ht₀t
      · left; exact hg_anti.injOn ⟨le_trans hσ₁_ge_l ht_σ.1, htt₀⟩
          ⟨hσ₁_ge_l, hσ₁_lt.le⟩ (ht_eq ▸ hσ₁_val.symm)
      · right; exact hg_mono.injOn ⟨ht₀t.le, le_trans ht_σ.2 hσ₂_le_r⟩
          ⟨hσ₂_gt.le, hσ₂_le_r⟩ (ht_eq ▸ hσ₂_val.symm)
    · exact (Set.toFinite {σ₁, σ₂}).measure_zero _
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => (ε₀ / 2)⁻¹ * M)
  · have hε₀_lt_δ := hε₀.2
    filter_upwards [Ioo_mem_nhds (by linarith : ε₀ / 2 < ε₀)
      (show ε₀ < min (ε₀ + 1) δ from lt_min (by linarith) hε₀_lt_δ)] with ε hε
    have hε_pos : 0 < ε := lt_trans (by linarith : (0 : ℝ) < ε₀ / 2) hε.1
    have hε_lt_δ : ε < δ := lt_of_lt_of_le hε.2 (min_le_right _ _)
    obtain ⟨σ₁, σ₂, hσ₁_ge, hσ₁_lt, hσ₂_gt, hσ₂_le,
      hσ₁_val, hσ₂_val, h_left, h_right, h_mid⟩ := hbnd ε ⟨hε_pos, hε_lt_δ⟩
    set Q : Finset ℝ := γ.partition ∪ {σ₁, σ₂}
    have h_cont_off : ContinuousOn
        (fun t => if ‖γ.toFun t - z₀‖ > ε then
          (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) (Icc γ.a γ.b \ ↑Q) := by
      intro t ⟨ht_Icc, ht_nQ⟩
      have ht_nP : t ∉ (↑γ.partition : Set ℝ) := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp h)))
      have ht_ne_σ₁ : t ≠ σ₁ := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_insert_self σ₁ {σ₂}) |> (h ▸ ·)))
      have ht_ne_σ₂ : t ≠ σ₂ := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self σ₂)) |> (h ▸ ·)))
      have ht_Ioo : t ∈ Ioo γ.a γ.b :=
        ⟨lt_of_le_of_ne ht_Icc.1 (fun h =>
          ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)),
         lt_of_le_of_ne ht_Icc.2 (fun h =>
          ht_nP (h.symm ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2))⟩
      by_cases h₁ : t < σ₁
      · have h_gt : ε < ‖γ.toFun t - z₀‖ := h_left t ⟨ht_Icc.1, h₁⟩
        have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
        exact (ContinuousAt.mul
          ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
            continuousAt_const).inv₀ hne)
          (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t ht_Ioo ht_nP)
          ).congr (by
            filter_upwards [(continuous_norm.continuousAt.comp
              (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
                continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt)]
              with s hs; exact (if_pos hs).symm) |>.continuousWithinAt
      · by_cases h₂ : σ₂ < t
        · have h_gt : ε < ‖γ.toFun t - z₀‖ := h_right t ⟨h₂, ht_Icc.2⟩
          have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
          exact (ContinuousAt.mul
            ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
              continuousAt_const).inv₀ hne)
            (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t ht_Ioo ht_nP)
            ).congr (by
              filter_upwards [(continuous_norm.continuousAt.comp
                (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
                  continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt)]
                with s hs; exact (if_pos hs).symm) |>.continuousWithinAt
        · have ht_mid : t ∈ Ioo σ₁ σ₂ :=
            ⟨lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm ht_ne_σ₁),
             lt_of_le_of_ne (not_lt.mp h₂) ht_ne_σ₂⟩
          exact continuousAt_const.congr (by
            filter_upwards [Ioo_mem_nhds ht_mid.1 ht_mid.2] with s hs
            exact (if_neg (not_lt.mpr (h_mid s ⟨hs.1.le, hs.2.le⟩))).symm
            ) |>.continuousWithinAt
    exact (intervalIntegrable_of_piecewise_continuousOn_bounded
      ((ε₀ / 2)⁻¹ * M) γ.hab.le h_cont_off
      (fun t ht => by
        split_ifs with h
        · rw [norm_mul, norm_inv]
          exact mul_le_mul (inv_anti₀ hε₀_half (le_of_lt (lt_trans hε.1 h)))
            (hM t ht) (norm_nonneg _) (inv_nonneg.mpr hε₀_half.le)
        · simp only [norm_zero]
          exact mul_nonneg (inv_nonneg.mpr hε₀_half.le) hM_nn)
      ).aestronglyMeasurable.mono_measure (by
        rw [Set.uIoc_of_le γ.hab.le])
  · filter_upwards [Ioo_mem_nhds (by linarith : ε₀ / 2 < ε₀)
      (by linarith [hε₀.2] : ε₀ < ε₀ + 1)] with ε hε
    filter_upwards with t ht
    split_ifs with h
    · rw [Set.uIoc_of_le γ.hab.le] at ht
      rw [norm_mul, norm_inv]
      exact mul_le_mul (inv_anti₀ hε₀_half (le_of_lt (lt_trans hε.1 h)))
        (hM t (Ioc_subset_Icc_self ht)) (norm_nonneg _) (inv_nonneg.mpr hε₀_half.le)
    · simp only [norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hε₀_half.le) hM_nn
  · exact intervalIntegrable_const
  · rw [Set.uIoc_of_le γ.hab.le]
    have h_ae : ∀ᵐ t ∂volume,
        ¬(t ∈ Icc γ.a γ.b ∧ ‖γ.toFun t - z₀‖ = ε₀) :=
      compl_mem_ae_iff.mpr h_level_null
    filter_upwards [h_ae] with t ht_not_level ht_Ioc
    have ht_Icc := Ioc_subset_Icc_self ht_Ioc
    have h_ne : ‖γ.toFun t - z₀‖ ≠ ε₀ := fun h => ht_not_level ⟨ht_Icc, h⟩
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · have h_ev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 ε₀]
          (fun ε => if ‖γ.toFun t - z₀‖ > ε then
            (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) := by
        filter_upwards [Ioi_mem_nhds h_lt] with ε hε
        exact (if_neg (not_lt.mpr (mem_Ioi.mp hε).le)).symm
      exact continuousAt_const.congr h_ev
    · have h_ev : (fun _ : ℝ => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t) =ᶠ[𝓝 ε₀]
          (fun ε => if ‖γ.toFun t - z₀‖ > ε then
            (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) := by
        filter_upwards [Iio_mem_nhds h_gt] with ε hε
        exact (if_pos (mem_Iio.mp hε)).symm
      exact continuousAt_const.congr h_ev

/-- PV of `(z-z₀)⁻¹` exists along a closed PiecewiseC1Immersion with unique crossing.
This is the C²-free version of `cpv_exists_inv_sub`: it uses the exp-convergence
from `tendsto_exp_cutoff_integral_crossing` (which doesn't need C²) together with
a Cauchy transfer argument to extract convergence of the integral itself. -/
lemma cpv_exists_inv_sub_of_closed_unique
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed)
    (_h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  set R : ℝ → ℂ := fun ε => ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0
  have h_exp := tendsto_exp_cutoff_integral_crossing γ hclosed z₀ t₀ ht₀ hcross honly
  obtain ⟨δ, hδ, l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, hg_mono,
    hδ_le_l, hδ_le_r, hbnd⟩ :=
    exists_cutoff_boundary_times_with_mono γ z₀ t₀ ht₀ hcross honly
  set L₀ : ℂ := Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀)))
  have hL₀_ne : L₀ ≠ 0 := Complex.exp_ne_zero _
  have hR_cont : ContinuousOn R (Ioo 0 δ) :=
    continuousOn_cutoff_integral γ z₀ t₀ ht₀ hcross honly δ hδ hbnd
      l r hl_lt hr_gt hl_ge_a hr_le_b hg_anti hg_mono hδ_le_l hδ_le_r
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hL₀_ne with hsp | hsp
  · exact cpv_of_exp_tendsto_slitPlane R L₀ δ hδ hsp h_exp hR_cont
  · exact cpv_of_exp_tendsto_neg_slitPlane R L₀ δ hδ hsp h_exp hR_cont
  where
  cpv_of_exp_tendsto_slitPlane (R : ℝ → ℂ) (L₀ : ℂ) (δ : ℝ) (hδ : 0 < δ)
      (hsp : L₀ ∈ Complex.slitPlane)
      (h_exp : Tendsto (fun ε => Complex.exp (R ε)) (𝓝[>] 0) (𝓝 L₀))
      (hR_cont : ContinuousOn R (Ioo 0 δ)) :
      ∃ L, Tendsto R (𝓝[>] 0) (𝓝 L) := by
    have h_log : Tendsto (fun ε => Complex.log (Complex.exp (R ε))) (𝓝[>] 0)
        (𝓝 (Complex.log L₀)) := h_exp.clog hsp
    have h_sp_ev := h_exp.eventually (Complex.isOpen_slitPlane.mem_nhds hsp)
    obtain ⟨η, hη, hη_le_δ, hη_sp⟩ : ∃ η > 0, η ≤ δ ∧ ∀ ε ∈ Ioo (0 : ℝ) η,
        Complex.exp (R ε) ∈ Complex.slitPlane := by
      rw [Filter.Eventually, mem_nhdsWithin] at h_sp_ev
      obtain ⟨U, hU_open, h0_mem, hU_sub⟩ := h_sp_ev
      obtain ⟨r, hr, hr_ball⟩ := Metric.isOpen_iff.mp hU_open 0 h0_mem
      exact ⟨min r δ, by positivity, min_le_right _ _, fun ε hε => hU_sub ⟨hr_ball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [sub_zero, abs_of_pos hε.1]
        exact lt_of_lt_of_le hε.2 (min_le_left _ _)), hε.1⟩⟩
    have h_logexp_cont : ContinuousOn (fun ε => Complex.log (Complex.exp (R ε))) (Ioo 0 η) :=
      (Complex.continuous_exp.comp_continuousOn
        (hR_cont.mono fun ε hε => ⟨(Set.mem_Ioo.mp hε).1,
          lt_of_lt_of_le (Set.mem_Ioo.mp hε).2 hη_le_δ⟩)).clog fun ε hε => hη_sp ε hε
    have h_phi_cont : ContinuousOn (fun ε => R ε - Complex.log (Complex.exp (R ε))) (Ioo 0 η) :=
      (hR_cont.mono fun ε hε => ⟨(Set.mem_Ioo.mp hε).1,
        lt_of_lt_of_le (Set.mem_Ioo.mp hε).2 hη_le_δ⟩).sub h_logexp_cont
    have h_phi_const : ∀ ε₁ ∈ Ioo (0 : ℝ) η, ∀ ε₂ ∈ Ioo (0 : ℝ) η,
        R ε₁ - Complex.log (Complex.exp (R ε₁)) =
        R ε₂ - Complex.log (Complex.exp (R ε₂)) := by
      set T : Set ℂ := Set.range (fun n : ℤ => ↑n * (2 * ↑Real.pi * I)) with hT_def
      have h_maps : Set.MapsTo
          (fun ε => R ε - Complex.log (Complex.exp (R ε))) (Ioo 0 η) T := by
        intro ε hε
        have h_exp_eq : Complex.exp (R ε - Complex.log (Complex.exp (R ε))) = 1 := by
          rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _), div_self
            (Complex.exp_ne_zero _)]
        rw [Complex.exp_eq_one_iff] at h_exp_eq
        obtain ⟨n, hn⟩ := h_exp_eq
        exact ⟨n, hn.symm⟩
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hT_disc : DiscreteTopology T := by
        rw [discreteTopology_subtype_iff']
        intro y hy
        refine ⟨Metric.ball y (2 * Real.pi), Metric.isOpen_ball, ?_⟩
        ext z
        simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hz_ball, hz_mem⟩
          obtain ⟨m, rfl⟩ := hy
          obtain ⟨n, rfl⟩ := hz_mem
          by_contra h_ne
          have hmn : m ≠ n := by intro heq; exact h_ne (by rw [heq])
          have h_sub : (↑n : ℂ) * (2 * ↑Real.pi * I) - ↑m * (2 * ↑Real.pi * I) =
              ↑(n - m) * (2 * ↑Real.pi * I) := by push_cast; ring
          have h_norm_2piI : ‖(2 * ↑Real.pi * I : ℂ)‖ = 2 * Real.pi := by
            simp only [norm_mul, Complex.norm_ofNat,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
              Complex.norm_I, mul_one]
          have h_dist : dist (↑n * (2 * ↑Real.pi * I)) (↑m * (2 * ↑Real.pi * I)) =
              ‖(↑(n - m) : ℂ)‖ * (2 * Real.pi) := by
            rw [dist_eq_norm, h_sub, norm_mul, h_norm_2piI]
          rw [h_dist, Complex.norm_intCast] at hz_ball
          have h_int_pos : (1 : ℝ) ≤ |(↑(n - m) : ℝ)| := by
            have h1 := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmn))
            rw [← Int.cast_abs] at hz_ball ⊢
            exact_mod_cast h1
          linarith [mul_le_mul_of_nonneg_right h_int_pos (le_of_lt h2pi_pos)]
        · intro heq
          exact ⟨by rw [heq]; exact Metric.mem_ball_self h2pi_pos,
            by rw [heq]; exact hy⟩
      intro ε₁ hε₁ ε₂ hε₂
      exact isPreconnected_Ioo.constant_of_mapsTo ⟨hT_disc⟩ h_phi_cont h_maps hε₁ hε₂
    have hη2 : η / 2 ∈ Ioo (0 : ℝ) η := ⟨by linarith, by linarith⟩
    set k := R (η / 2) - Complex.log (Complex.exp (R (η / 2)))
    have hR_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), R ε = Complex.log (Complex.exp (R ε)) + k := by
      filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
      have := h_phi_const ε hε (η / 2) hη2; linear_combination this
    exact ⟨Complex.log L₀ + k, Filter.Tendsto.congr'
      (by filter_upwards [hR_eq] with ε hε; exact hε.symm)
      (h_log.add tendsto_const_nhds)⟩
  cpv_of_exp_tendsto_neg_slitPlane (R : ℝ → ℂ) (L₀ : ℂ) (δ : ℝ) (hδ : 0 < δ)
      (hsp : -L₀ ∈ Complex.slitPlane)
      (h_exp : Tendsto (fun ε => Complex.exp (R ε)) (𝓝[>] 0) (𝓝 L₀))
      (hR_cont : ContinuousOn R (Ioo 0 δ)) :
      ∃ L, Tendsto R (𝓝[>] 0) (𝓝 L) := by
    have h_shift : Tendsto (fun ε => Complex.exp (R ε + ↑Real.pi * I))
        (𝓝[>] 0) (𝓝 (-L₀)) :=
      (show (fun ε => Complex.exp (R ε + ↑Real.pi * I)) =
          fun ε => -(Complex.exp (R ε)) from
        funext fun ε => by rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring) ▸ h_exp.neg
    obtain ⟨L', hL'⟩ := cpv_of_exp_tendsto_slitPlane _ (-L₀) δ hδ hsp h_shift
      (hR_cont.add continuousOn_const)
    exact ⟨L' - ↑Real.pi * I,
      (show R = fun ε => (R ε + ↑Real.pi * I) - ↑Real.pi * I from funext fun _ => by ring)
        ▸ hL'.sub tendsto_const_nhds⟩

end GeneralizedResidueTheory
