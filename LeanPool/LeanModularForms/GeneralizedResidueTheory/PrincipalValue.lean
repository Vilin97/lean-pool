/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Cauchy Principal Value Theory

Theory of Cauchy principal value integrals for piecewise C¹ contour integration.
The principal value approach allows contours to pass through singularities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

theorem cauchyPrincipalValueIntegrand_bounded
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (_hε : 0 < ε)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M : ℝ, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
  by_cases h_empty :
      (γ '' Icc a b \ Metric.ball z₀ ε).Nonempty
  · have hcompact_domain : IsCompact (γ '' Icc a b \ Metric.ball z₀ ε) :=
      (isCompact_Icc.image_of_continuousOn hγ_cont).inter_right
        Metric.isOpen_ball.isClosed_compl
    obtain ⟨Mf, hMf⟩ := hcompact_domain.exists_bound_of_continuousOn hf_cont.norm
    obtain ⟨Mγ, hMγ⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ'_cont.norm
    have hMf' : ∀ x ∈ γ '' Icc a b \ Metric.ball z₀ ε, ‖f x‖ ≤ Mf := fun x hx => by
      simpa [Real.norm_eq_abs, abs_norm] using hMf x hx
    have hMγ' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ := fun t ht => by
      simpa [Real.norm_eq_abs, abs_norm] using hMγ t ht
    refine ⟨Mf * Mγ + 1, fun t ht => ?_⟩
    unfold cauchyPrincipalValueIntegrand'; split_ifs with h
    · calc ‖f (γ t) * deriv γ t‖ = ‖f (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ Mf * Mγ := by
            apply mul_le_mul (hMf' _ ⟨⟨t, ht, rfl⟩, by
                simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact h.le⟩)
              (hMγ' t ht) (norm_nonneg _)
              (le_trans (norm_nonneg _) (hMf' _ ⟨⟨t, ht, rfl⟩, by
                simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact h.le⟩))
        _ ≤ Mf * Mγ + 1 := le_add_of_nonneg_right one_pos.le
    · simp only [norm_zero]
      exact add_nonneg (mul_nonneg
        (le_trans (norm_nonneg _) (hMf' _ h_empty.some_mem))
        (by obtain ⟨_, ⟨t', ht', _⟩, _⟩ := h_empty
            exact le_trans (norm_nonneg _) (hMγ' _ ht'))) (by norm_num)
  · exact ⟨0, fun t ht => by
      unfold cauchyPrincipalValueIntegrand'
      split_ifs with h
      · exact absurd ⟨γ t, ⟨t, ht, rfl⟩, by
          simp only [Metric.mem_ball, not_lt, dist_eq_norm]
          exact le_of_lt h⟩ h_empty
      · simp only [norm_zero, le_refl]⟩

lemma measurableSet_pv_support (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (hγ_cont : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_norm_cont : ContinuousOn (fun t => ‖γ t - z₀‖) (Icc a b) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_open_sub :
      IsOpen ((Icc a b).restrict (fun t => ‖γ t - z₀‖) ⁻¹' Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖γ t - z₀‖} ∩ Icc a b = U ∩ Icc a b := by
    ext x; constructor
    · intro ⟨hx_far, hx_Icc⟩
      exact ⟨by
        have : (⟨x, hx_Icc⟩ : ↑(Icc a b)) ∈
            (Icc a b).restrict (fun t => ‖γ t - z₀‖) ⁻¹' Ioi ε := by
          simp only [mem_preimage, restrict_apply, mem_Ioi]; exact hx_far
        rwa [← hU_eq] at this, hx_Icc⟩
    · intro ⟨hx_U, hx_Icc⟩
      exact ⟨by
        have : (⟨x, hx_Icc⟩ : ↑(Icc a b)) ∈ Subtype.val ⁻¹' U := hx_U
        rw [hU_eq] at this
        simp only [mem_preimage, restrict_apply, mem_Ioi] at this
        exact this, hx_Icc⟩
  rw [h_eq]
  exact hU_open.measurableSet.inter isClosed_Icc.measurableSet

lemma continuousOn_pv_base (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hf_cont : ContinuousOn f
      (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ContinuousOn (fun t => f (γ t) * deriv γ t)
      ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  intro t ⟨ht_far, ht_Icc⟩
  have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
    ⟨mem_image_of_mem γ ht_Icc, by
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact le_of_lt ht_far⟩
  have h_maps :
      MapsTo γ ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)
        (γ '' Icc a b \ Metric.ball z₀ ε) := by
    intro s ⟨hs_far, hs_Icc⟩
    exact ⟨mem_image_of_mem γ hs_Icc, by
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact le_of_lt hs_far⟩
  have hfγ_at : ContinuousWithinAt (f ∘ γ)
      ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) t :=
    ContinuousWithinAt.comp (hf_cont _ hγt_in)
      ((hγ_cont t ht_Icc).mono inter_subset_right) h_maps
  exact hfγ_at.mul ((hγ'_cont t ht_Icc).mono inter_subset_right)

/-- If `f =ᶠ g` along a filter, their `limUnder` values agree. -/
theorem limUnder_eventually_eq {α : Type*} [TopologicalSpace α] [Nonempty α]
    {f g : ℝ → α} {l : Filter ℝ} [l.NeBot] (h : ∀ᶠ x in l, f x = g x) :
    limUnder l f = limUnder l g := by
  simp only [limUnder, Filter.map_congr h]

private theorem aEStronglyMeasurable_pv_integrand
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    AEStronglyMeasurable
      (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t
        else 0) (volume.restrict (Icc a b)) := by
  let S := {t | ε < ‖γ t - z₀‖}
  have hS_meas : MeasurableSet (S ∩ Icc a b) :=
    measurableSet_pv_support γ a b z₀ ε hγ
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t)
      (S ∩ Icc a b) :=
    continuousOn_pv_base f γ a b z₀ ε hf hγ hγ'
  have h_base_meas : AEStronglyMeasurable
      (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) :=
    h_cont.aestronglyMeasurable hS_meas
  have h_piecewise := AEStronglyMeasurable.piecewise
    hS_meas h_base_meas
    (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (S ∩ Icc a b)ᶜ))
  have h_eq : (fun t => if ε < ‖γ t - z₀‖
      then f (γ t) * deriv γ t else 0) =ᵐ[
        volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise
        (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem
      isClosed_Icc.measurableSet] with t ht
    simp only [piecewise]
    by_cases ht_S : t ∈ S
    · simp only [show t ∈ S ∩ Icc a b from ⟨ht_S, ht⟩,
        ↓reduceIte, show ε < ‖γ t - z₀‖ from ht_S, ↓reduceIte]
    · simp only [show t ∉ S ∩ Icc a b from fun h => ht_S h.1,
        ↓reduceIte, show ¬(ε < ‖γ t - z₀‖) from ht_S,
        ↓reduceIte]
  exact (h_piecewise.mono_measure
    Measure.restrict_le_self).congr h_eq.symm

theorem cauchyPrincipalValueIntegrand_integrable
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (hε : 0 < ε) (hab : a < b)
    (hf_cont : ContinuousOn f
      (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    IntervalIntegrable
      (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b := by
  obtain ⟨M, hM⟩ := cauchyPrincipalValueIntegrand_bounded
    f γ a b z₀ ε hε hf_cont hγ_cont hγ'_cont
  have h_eq : cauchyPrincipalValueIntegrand' f γ z₀ ε =
      fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t
        else 0 := by ext t; rfl
  rw [h_eq, intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt hab)]
  apply IntegrableOn.mono_set
  · apply IntegrableOn.of_bound measure_Icc_lt_top
      (aEStronglyMeasurable_pv_integrand hf_cont hγ_cont
        hγ'_cont)
      (max M 0)
    filter_upwards [ae_restrict_mem
      isClosed_Icc.measurableSet] with x hx
    calc ‖if ε < ‖γ x - z₀‖ then f (γ x) * deriv γ x
        else 0‖
        ≤ M := by
          simp only [cauchyPrincipalValueIntegrand'] at hM
          exact hM x hx
      _ ≤ max M 0 := le_max_left M 0
  · exact Ioc_subset_Icc_self

/-- Dominated convergence for principal value integrals. -/
theorem cauchyPrincipalValue_of_dominated
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b) (M : ℝ) (_hM : 0 < M)
    (h_bound : ∀ ε > 0, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M)
    (h_ae_limit : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L))
    (hF_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (cauchyPrincipalValueIntegrand' f γ z₀ ε)
        (volume.restrict (uIoc a b))) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  have hab' := le_of_lt hab
  have h_bound_ae : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂volume,
      t ∈ uIoc a b →
        ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Eventually.of_forall
    intro t ht
    exact h_bound ε hε t
      (Ioc_subset_Icc_self (uIoc_of_le hab' ▸ ht))
  have h_ae_unr : ∀ᵐ t ∂volume, t ∈ Icc a b →
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L) := by
    rwa [ae_restrict_iff' isClosed_Icc.measurableSet]
      at h_ae_limit
  have h_limit_ae : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L) := by
    filter_upwards [h_ae_unr] with t ht ht_mem
    exact ht (Ioc_subset_Icc_self (uIoc_of_le hab' ▸ ht_mem))
  let g : ℝ → ℂ := fun t => Filter.limUnder (𝓝[>] (0 : ℝ))
    (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
  have h_lim_conv : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 (g t)) := by
    filter_upwards [h_limit_ae] with t ht ht_mem
    obtain ⟨L, hL⟩ := ht ht_mem
    rwa [show g t = L from hL.limUnder_eq]
  exact ⟨∫ t in a..b, g t,
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) hF_meas h_bound_ae
      intervalIntegrable_const h_lim_conv⟩

private theorem pv_uniform_bound_of_continuous_aux
    (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M > 0, ∀ ε > 0, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' g γ z₀ ε t‖ ≤ M := by
  obtain ⟨Mg, hMg⟩ :=
    (isCompact_Icc.image_of_continuousOn hγ).exists_bound_of_continuousOn hg.norm
  obtain ⟨Mγ', hMγ'⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hγ'.norm
  have hMg' : ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg := fun z hz => by
    have := hMg z hz; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
  have hMγ'' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ' := fun t ht => by
    have := hMγ' t ht; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
  have hMg_nn : (0 : ℝ) ≤ Mg :=
    le_trans (norm_nonneg _) (hMg' _ ⟨a, left_mem_Icc.mpr hab.le, rfl⟩)
  have hMγ_nn : (0 : ℝ) ≤ Mγ' :=
    le_trans (norm_nonneg _) (hMγ'' a (left_mem_Icc.mpr hab.le))
  refine ⟨Mg * Mγ' + 1, by linarith [mul_nonneg hMg_nn hMγ_nn],
    fun ε _ t ht => ?_⟩
  unfold cauchyPrincipalValueIntegrand'; split_ifs with h
  · calc ‖g (γ t) * deriv γ t‖
        = ‖g (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
      _ ≤ Mg * Mγ' := mul_le_mul (hMg' _ ⟨t, ht, rfl⟩) (hMγ'' t ht)
          (norm_nonneg _) hMg_nn
      _ ≤ Mg * Mγ' + 1 := by linarith
  · simp only [norm_zero]; linarith [mul_nonneg hMg_nn hMγ_nn]

/-- PV exists for continuous integrands on C¹ curves. -/
theorem cauchyPrincipalValueExists_of_continuous
    (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    CauchyPrincipalValueExists' g γ a b z₀ := by
  obtain ⟨M, hM_pos, h_bound⟩ :=
    pv_uniform_bound_of_continuous_aux g γ a b z₀ hab hg hγ hγ'
  refine cauchyPrincipalValue_of_dominated g γ a b z₀ hab M hM_pos
    h_bound ?_ ?_
  · apply Eventually.of_forall; intro t
    by_cases h : γ t = z₀
    · exact ⟨0, Tendsto.congr' (by
        rw [EventuallyEq, eventually_iff_exists_mem]
        exact ⟨Ioi 0, self_mem_nhdsWithin, fun ε hε => by
          simp only [cauchyPrincipalValueIntegrand', h, sub_self,
            norm_zero, not_lt.mpr (le_of_lt (mem_Ioi.mp hε)),
            ite_false]⟩) tendsto_const_nhds⟩
    · exact ⟨g (γ t) * deriv γ t, Tendsto.congr' (by
        rw [EventuallyEq, eventually_iff_exists_mem]
        exact ⟨Ioo 0 ‖γ t - z₀‖,
          Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr h)),
          fun ε hε => by
            simp only [cauchyPrincipalValueIntegrand',
              hε.2, ite_true]⟩) tendsto_const_nhds⟩
  · filter_upwards [self_mem_nhdsWithin] with ε _
    have h_eq : cauchyPrincipalValueIntegrand' g γ z₀ ε =
        fun t => if ε < ‖γ t - z₀‖ then g (γ t) * deriv γ t
          else 0 := funext fun _ => rfl
    rw [h_eq]
    exact (aEStronglyMeasurable_pv_integrand
      (hg.mono diff_subset) hγ hγ').mono_measure
      (Measure.restrict_mono
        (by rw [uIoc_of_le hab.le]; exact Ioc_subset_Icc_self)
        le_rfl)

/-- PV exists for singular 1/(z-z₀) integrands on C¹ immersions. -/
theorem cauchyPrincipalValueExists_of_singular_inv
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (h_crossing_cauchy :
      (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in γ.a..γ.b,
            if ε < ‖γ.toFun t - z₀‖
            then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
            else 0) (𝓝[>] 0))) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹)
      γ.toFun γ.a γ.b z₀ := by
  by_cases h_cross : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀
  · exact CompleteSpace.complete (h_crossing_cauchy h_cross)
  · push Not at h_cross
    have h_cont : ContinuousOn
        (fun t => ‖γ.toFun t - z₀‖) (Icc γ.a γ.b) :=
      (γ.continuous_toFun.sub continuousOn_const).norm
    obtain ⟨t₀, ht₀, ht₀_min⟩ :=
      IsCompact.exists_isMinOn isCompact_Icc
        ⟨γ.a, left_mem_Icc.mpr γ.hab.le⟩ h_cont
    have hδ : 0 < ‖γ.toFun t₀ - z₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_cross t₀ ht₀))
    have hδ_le : ∀ t ∈ Icc γ.a γ.b,
        ‖γ.toFun t₀ - z₀‖ ≤ ‖γ.toFun t - z₀‖ :=
      Filter.eventually_principal.mp ht₀_min
    refine ⟨∫ t in γ.a..γ.b,
        (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      symm
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le γ.hab.le] at ht
      simp only [gt_iff_lt, show ε < ‖γ.toFun t - z₀‖ from
        lt_of_lt_of_le hε.2 (hδ_le t ht), ite_true])

/-- Uniform avoidance on compact sets. -/
theorem uniform_avoidance_on_compact
    (γ : ℝ → ℂ) (K : Set ℝ) (z₀ : ℂ)
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hγ_cont : ContinuousOn γ K)
    (h_avoid : ∀ t ∈ K, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ K, δ ≤ ‖γ t - z₀‖ := by
  obtain ⟨t₀, ht₀, h_min⟩ := hK_compact.exists_isMinOn
    hK_nonempty (hγ_cont.sub continuousOn_const).norm
  exact ⟨‖γ t₀ - z₀‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀)),
    Filter.eventually_principal.mp h_min⟩

private theorem pv_piecewise_measurable
    (g : ℂ → ℂ) (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (h_integrable : IntervalIntegrable
      (fun t => g (γ.toFun t) * deriv γ.toFun t)
      volume γ.a γ.b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)
      (volume.restrict (Ι γ.a γ.b)) := by
  filter_upwards [self_mem_nhdsWithin] with ε _
  rw [show Ι γ.a γ.b = Ioc γ.a γ.b from uIoc_of_le γ.hab.le]
  exact (h_integrable.aestronglyMeasurable.indicator
    (measurableSet_pv_support γ.toFun γ.a γ.b z₀ ε
      γ.continuous_toFun)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases h : ε < ‖γ.toFun t - z₀‖
    · rw [indicator_of_mem (show t ∈ {t | ε < ‖γ.toFun t - z₀‖} ∩
        Icc γ.a γ.b from ⟨h, Ioc_subset_Icc_self ht⟩), if_pos h]
    · rw [indicator_of_notMem (fun hmem => h hmem.1), if_neg h])

private theorem pv_piecewise_bound (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (g : ℂ → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖(if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)‖ ≤
      ‖g (γ.toFun t) * deriv γ.toFun t‖ := by
  filter_upwards [self_mem_nhdsWithin] with ε _
  exact Eventually.of_forall fun t _ => by
    split_ifs with h
    · exact le_refl _
    · simp only [norm_zero]; exact norm_nonneg _

private theorem pv_piecewise_pointwise
    (γ : PiecewiseC1Curve) (z₀ : ℂ) (g : ℂ → ℂ)
    (h_finite_preimage :
      Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε => if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 (g (γ.toFun t) * deriv γ.toFun t)) := by
  filter_upwards [h_finite_preimage.countable.ae_notMem _]
      with t ht ht_uIoc
  have h_ne : γ.toFun t ≠ z₀ := fun heq =>
    ht ⟨Ioc_subset_Icc_self (uIoc_of_le γ.hab.le ▸ ht_uIoc), heq⟩
  exact tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsGT
      (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne))] with ε hε
    simp only [hε.2, ite_true])

private theorem pv_simple_pole_integrand_split
    (γ_fun : ℝ → ℂ) (z₀ c : ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    (if ε < ‖γ_fun t - z₀‖
    then (c / (γ_fun t - z₀) + g (γ_fun t)) *
      deriv γ_fun t else 0) =
    (if ε < ‖γ_fun t - z₀‖
    then c / (γ_fun t - z₀) * deriv γ_fun t else 0) +
    (if ε < ‖γ_fun t - z₀‖
    then g (γ_fun t) * deriv γ_fun t else 0) := by
  split_ifs <;> ring

private theorem pv_simple_pole_tendsto
    (γ : PiecewiseC1Immersion) (z₀ c : ℂ) (g : ℂ → ℂ)
    (Ls Lg : ℂ)
    (hLs : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then c / (γ.toFun t - z₀) * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 Ls))
    (hLg : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then g (γ.toFun t) * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 Lg))
    (h_int : ∀ ε > 0,
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then c / (γ.toFun t - z₀) * deriv γ.toFun t
        else 0) volume γ.a γ.b ∧
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t
        else 0) volume γ.a γ.b) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      (if ε < ‖γ.toFun t - z₀‖
      then c / (γ.toFun t - z₀) * deriv γ.toFun t
      else 0) + (if ε < ‖γ.toFun t - z₀‖
      then g (γ.toFun t) * deriv γ.toFun t
      else 0)) (𝓝[>] 0) (𝓝 (Ls + Lg)) := by
  refine Tendsto.congr' ?_ (Tendsto.add hLs hLg)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  exact intervalIntegral.integral_add
    (h_int ε (mem_Ioi.mp hε)).1 (h_int ε (mem_Ioi.mp hε)).2

end
