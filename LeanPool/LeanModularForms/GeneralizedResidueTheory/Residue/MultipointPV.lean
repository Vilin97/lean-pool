/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.MeasureHelpers
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# Multi-point Principal Value Infrastructure

Lemmas for multi-point Cauchy principal values: minimum separation,
disjoint balls, boundedness, integrability, measurability, and the
dominated convergence argument for decomposing multi-point PVs into
sums of single-point PVs.

## Main Results

* `finset_discrete_min_sep` — positive minimum separation in a
  finite set
* `disjoint_balls_of_small_epsilon` — disjoint balls for small ε
* `dominated_convergence_multipoint_helper` — dominated convergence
  for multi-point PV decomposition
* `multipointPV_diff_tendsto` — difference integrand converges
* `multipointPV_eq_sum_of_integral_zero` — multi-point PV equals
  sum of single-point PVs when regular integral vanishes
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-- The derivative of a piecewise C¹ immersion is continuous off its partition. -/
private lemma piecewiseC1Immersion_continuousOn_deriv_off_partition (γ : PiecewiseC1Immersion) :
    ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b \ γ.partition) := by
  intro t ⟨ht_Icc, ht_notP⟩
  by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
  · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
        t ht_Ioo ht_notP).continuousWithinAt
  · have ha_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.1
    have hb_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.2
    have ht_endpoint : t = γ.a ∨ t = γ.b := by
      simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
      rcases ht_Icc.1.lt_or_eq with h | h
      · right; exact le_antisymm ht_Icc.2 (ht_Ioo h)
      · left; exact h.symm
    rcases ht_endpoint with rfl | rfl
    <;> exact (ht_notP (by assumption)).elim

/-! ## Measurability Infrastructure -/

private lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ)
    (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  have h_norm_cont : ContinuousOn (fun t => ‖f t‖) s := hf.norm
  have h_open_sub : IsOpen ((s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x; constructor
    · intro ⟨hx_far, hx_s⟩; refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈
          (s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε := by
        simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi]; exact hx_far
      rw [← hU_eq] at h1; exact h1
    · intro ⟨hx_U, hx_s⟩; refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := hx_U
      rw [hU_eq] at h1
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi] at h1; exact h1
  rw [h_eq]; exact hU_open.measurableSet.inter hs

private lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ} (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

theorem aEStronglyMeasurable_of_continuousOn_off_finite {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f (Icc a b \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  have hP_finite : (↑P ∩ Icc a b : Set ℝ).Finite := P.finite_toSet.inter_of_left (Icc a b)
  have hP_meas_zero : volume (↑P ∩ Icc a b) = 0 := hP_finite.measure_zero volume
  have h_diff_meas : MeasurableSet (Icc a b \ P) :=
    isClosed_Icc.measurableSet.diff P.finite_toSet.measurableSet
  have h_cont_meas : AEStronglyMeasurable f (volume.restrict (Icc a b \ P)) :=
    hf_cont.aestronglyMeasurable h_diff_meas
  have hP_inter_meas : MeasurableSet (↑P ∩ Icc a b) :=
    P.finite_toSet.measurableSet.inter isClosed_Icc.measurableSet
  have h_disj : Disjoint (Icc a b \ P) (↑P ∩ Icc a b) := by
    rw [Set.disjoint_left]; intro x ⟨_, hx_nP⟩ ⟨hx_P, _⟩; exact hx_nP hx_P
  have h_eq : volume.restrict (Icc a b) =
      volume.restrict (Icc a b \ P) + volume.restrict (↑P ∩ Icc a b) := by
    rw [← Measure.restrict_union h_disj hP_inter_meas]; congr 1; ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [h_eq]; apply AEStronglyMeasurable.add_measure h_cont_meas
  simpa only [Measure.restrict_eq_zero.mpr hP_meas_zero] using aestronglyMeasurable_zero_measure f

private lemma measurableSet_multipoint_condition {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
  have h_eq : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      ⋃ s ∈ S, ({t | ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨s, hs, h_norm⟩, ht_Icc⟩; exact ⟨s, hs, h_norm, ht_Icc⟩
    · intro ⟨s, hs, h_norm, ht_Icc⟩; exact ⟨⟨s, hs, h_norm⟩, ht_Icc⟩
  rw [h_eq]; apply Finset.measurableSet_biUnion; intro s _
  have h_compl_meas : MeasurableSet ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  have h_eq' : {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      Icc a b \ ({t | ε < ‖γ t - s‖} ∩ Icc a b) := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff, not_and]
    constructor
    · intro ⟨h_le, ht_Icc⟩; exact ⟨ht_Icc, fun h_gt => absurd h_gt (not_lt.mpr h_le)⟩
    · intro ⟨ht_Icc, h_not⟩; refine ⟨?_, ht_Icc⟩
      by_contra h_gt; push Not at h_gt; exact (h_not h_gt) ht_Icc
  rw [h_eq']; exact isClosed_Icc.measurableSet.diff h_compl_meas

private lemma measurableSet_multipoint_goodset {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b) := by
  have h_eq : {t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b =
      Icc a b \ ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t; constructor
    · intro ⟨h_good, ht_Icc⟩; refine ⟨ht_Icc, ?_⟩
      intro ⟨⟨s, hs, h_le⟩, _⟩; linarith [h_good s hs]
    · intro ⟨ht_Icc, h_not⟩; refine ⟨?_, ht_Icc⟩; intro s hs
      by_contra h_le; push Not at h_le; exact h_not ⟨⟨s, hs, h_le⟩, ht_Icc⟩
  rw [h_eq]; exact isClosed_Icc.measurableSet.diff (measurableSet_multipoint_condition S hγ)

private lemma goodset_piecewise_ae_eq_multipoint {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) :
    (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℂ) else g (γ t) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
    ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise
      (fun t => g (γ t) * deriv γ t) (fun _ => 0) := by
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · rw [if_pos ht_good]
    have : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by push Not; exact ht_good.1
    simp only [this, ↓reduceIte]
  · rw [if_neg ht_good]
    have : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      by_contra h_not; push Not at h_not; exact ht_good ⟨h_not, ht⟩
    simp only [this, ↓reduceIte]

private theorem aEStronglyMeasurable_pv_integrand_multipoint {g : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else g (γ t) * deriv γ t) (volume.restrict (Icc a b)) := by
  have h_base_meas : AEStronglyMeasurable (fun t => g (γ t) * deriv γ t)
      (volume.restrict (Icc a b)) :=
    ((hg.comp hγ fun t ht => Set.mem_image_of_mem _ ht).aestronglyMeasurable
      isClosed_Icc.measurableSet).mul
      (aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P)
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)ᶜ) :=
    aestronglyMeasurable_const
  exact ((AEStronglyMeasurable.piecewise (measurableSet_multipoint_goodset S hγ)
    (h_base_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    h_zero_meas).mono_measure Measure.restrict_le_self).congr
    (goodset_piecewise_ae_eq_multipoint S).symm

private lemma aEStronglyMeasurable_residueProd_on_goodset {γ : ℝ → ℂ} {a b ε : ℝ}
    {P : Finset ℝ} {s c : ℂ} (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => (c / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have h_ratio : AEStronglyMeasurable (fun t => c / (γ t - s))
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) := by
    apply ContinuousOn.aestronglyMeasurable _
      (measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const))
    apply ContinuousOn.div continuousOn_const
    · exact (hγ.mono Set.inter_subset_right).sub continuousOn_const
    · intro t ⟨ht_good, _⟩; exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hε ht_good))
  exact h_ratio.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private theorem
    aEStronglyMeasurable_pv_integrand_residue
    {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ}
    {s c : ℂ}
    (_hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε
        then (c / (γ t - s)) * deriv γ t
        else 0)
      (volume.restrict (Icc a b)) := by
  have hGoodSet_meas :
      MeasurableSet
        ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε
      (hγ.sub continuousOn_const)
  have h_zero_meas :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict
          ({t : ℝ | ε < ‖γ t - s‖} ∩
            Icc a b)ᶜ) :=
    aestronglyMeasurable_const
  have h_prod_meas :
      AEStronglyMeasurable
        (fun t => (c / (γ t - s)) * deriv γ t)
        (volume.restrict
          ({t | ε < ‖γ t - s‖} ∩ Icc a b)) :=
    aEStronglyMeasurable_residueProd_on_goodset
      _hε hγ hγ'_off_P
  have h_piecewise :=
    AEStronglyMeasurable.piecewise hGoodSet_meas
      h_prod_meas h_zero_meas
  refine (h_piecewise.mono_measure
    Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem
    isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff,
    Set.mem_setOf_eq, gt_iff_lt]
  by_cases h1 : ε < ‖γ t - s‖
  · simp only [h1, ht, and_self, ↓reduceIte]
  · push Not at h1
    simp only [not_lt.mpr h1, ht, and_true,
      ↓reduceIte]

private lemma aEStronglyMeasurable_singularSum_on_goodset
    {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ)
    (hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b)) :
    AEStronglyMeasurable
      (fun t => ∑ s ∈ S, coeffs s / (γ t - s))
      (volume.restrict
        ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩
          Icc a b)) := by
  apply Finset.aestronglyMeasurable_fun_sum S
  intro s hs
  apply ContinuousOn.aestronglyMeasurable _
    (measurableSet_multipoint_goodset S hγ)
  apply ContinuousOn.div continuousOn_const
  · exact (hγ.mono Set.inter_subset_right).sub
      continuousOn_const
  · intro t ⟨ht_good, _⟩
    exact norm_ne_zero_iff.mp
      (ne_of_gt (lt_trans hε (ht_good s hs)))

private lemma aEStronglyMeasurable_decomposed_on_goodset {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have hgγ_cont : ContinuousOn (fun t => g_reg (γ t)) (Icc a b) :=
    hg.comp hγ fun t ht => Set.mem_image_of_mem _ ht
  have hgγ_meas : AEStronglyMeasurable (fun t => g_reg (γ t))
      (volume.restrict (Icc a b)) :=
    hgγ_cont.aestronglyMeasurable isClosed_Icc.measurableSet
  have h_f_meas := (hgγ_meas.mono_measure
    (Measure.restrict_mono Set.inter_subset_right le_rfl)).add
    (aEStronglyMeasurable_singularSum_on_goodset S coeffs hε hγ)
  exact h_f_meas.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private lemma goodset_piecewise_ae_eq_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ) :
    (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
    ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise
      (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (fun _ => 0) := by
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · rw [if_pos ht_good]
    have : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by push Not; exact ht_good.1
    simp only [this, if_false]
  · rw [if_neg ht_good]
    have : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      by_contra h_not; push Not at h_not; exact ht_good ⟨h_not, ht⟩
    simp only [this, if_true]

theorem aEStronglyMeasurable_pv_integrand_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict (Icc a b)) := by
  exact ((AEStronglyMeasurable.piecewise
    (measurableSet_multipoint_goodset S hγ)
    (aEStronglyMeasurable_decomposed_on_goodset S coeffs hε hg hγ hγ'_off_P)
    aestronglyMeasurable_const).mono_measure
    Measure.restrict_le_self).congr
    (goodset_piecewise_ae_eq_decomposed
      S coeffs).symm

theorem integrableOn_of_bounded_aeMeasurable
    {f : ℝ → ℂ} {a b : ℝ} (M : ℝ)
    (hf_meas : AEStronglyMeasurable f
      (volume.restrict (Icc a b)))
    (hf_bound : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntegrableOn f (Icc a b) volume := by
  apply IntegrableOn.of_bound measure_Icc_lt_top
    hf_meas (max M 0)
  filter_upwards [ae_restrict_mem
    isClosed_Icc.measurableSet] with x hx
  exact (hf_bound x hx).trans (le_max_left M 0)

theorem tendsto_integral_of_dominated' {a b : ℝ} {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ}
    {g : ℝ → ℝ} (hF_meas : ∀ ε > 0,
      AEStronglyMeasurable (F ε) (volume.restrict (Ι a b)))
    (hF_le : ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F ε t‖ ≤ g t)
    (hg_int : IntervalIntegrable g volume a b)
    (hF_lim : ∀ᵐ t ∂volume, t ∈ Ι a b →
      Tendsto (fun ε => F ε t) (𝓝[>] 0) (𝓝 (f t))) :
    Tendsto (fun ε => ∫ t in a..b, F ε t) (𝓝[>] 0) (𝓝 (∫ t in a..b, f t)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence g
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_meas ε hε)
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_le ε hε)
    hg_int hF_lim

/-! ## Finite Set Separation -/

/-- Positive minimum separation in a finite set. -/
lemma finset_discrete_min_sep (S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty)
    (hS0_discrete : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → 0 < ‖s' - s‖) :
    ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_singleton : S0.card ≤ 1
  · refine ⟨1, one_pos, fun s hs s' hs' hne => ?_⟩
    have h_card_eq : S0.card = 1 := by have := hS0_nonempty.card_pos; omega
    obtain ⟨x, hS0_eq⟩ := Finset.card_eq_one.mp h_card_eq
    have hs_eq : s = x := by rw [hS0_eq] at hs; exact Finset.mem_singleton.mp hs
    have hs'_eq : s' = x := by rw [hS0_eq] at hs'; exact Finset.mem_singleton.mp hs'
    exact (hne (hs_eq.trans hs'_eq.symm)).elim
  · push Not at h_singleton
    classical
    let dists : Finset ℝ := S0.biUnion (fun s =>
      S0.filter (· ≠ s) |>.image (fun s' => ‖s' - s‖))
    have h_nonempty : dists.Nonempty := by
      obtain ⟨x, hx⟩ := hS0_nonempty
      have h_exists_y : ∃ y ∈ S0, y ≠ x := by
        by_contra h_all; push Not at h_all
        have : S0.card ≤ 1 := (Finset.card_le_card
          (fun z hz => Finset.mem_singleton.mpr (h_all z hz))).trans
          (by simp only [Finset.card_singleton, le_refl])
        omega
      obtain ⟨y, hy, hne⟩ := h_exists_y; refine ⟨‖y - x‖, ?_⟩
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨x, hx, y, ⟨hy, hne⟩, rfl⟩
    let δ := dists.min' h_nonempty
    have hδ_pos : 0 < δ := by
      have h_mem := Finset.min'_mem dists h_nonempty
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at h_mem
      obtain ⟨s, hs, s', ⟨hs', hne⟩, heq⟩ := h_mem
      have h_pos : 0 < ‖s' - s‖ := hS0_discrete s hs s' hs' hne.symm
      calc δ = ‖s' - s‖ := heq.symm
        _ > 0 := h_pos
    refine ⟨δ, hδ_pos, fun s hs s' hs' hne => ?_⟩
    have h_in : ‖s' - s‖ ∈ dists := by
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨s, hs, s', ⟨hs', hne.symm⟩, rfl⟩
    exact Finset.min'_le dists _ h_in

/-- Disjoint balls for small epsilon. -/
lemma disjoint_balls_of_small_epsilon (S0 : Finset ℂ) (ε : ℝ) (_hε : 0 < ε) (δ : ℝ)
    (_hδ : 0 < δ) (hε_small : ε < δ / 2)
    (h_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' →
      Disjoint (Metric.ball s ε) (Metric.ball s' ε) := by
  intro s hs s' hs' hne; apply Metric.ball_disjoint_ball
  have h2 : δ ≤ dist s s' := by
    rw [dist_eq_norm, norm_sub_rev]; exact h_sep s hs s' hs' hne
  linarith

/-! ## Boundedness Lemmas -/

/-- Continuous functions on a compact image are bounded. -/
lemma continuousOn_image_bounded {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b)) (hg_cont : ContinuousOn g (γ '' Icc a b)) :
    ∃ Mg : ℝ, ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg :=
  (isCompact_Icc.image_of_continuousOn hγ_cont).exists_bound_of_continuousOn hg_cont

/-- Piecewise if-then-else is bounded when the active branch is bounded. -/
lemma piecewise_if_bounded {f : ℝ → ℂ} {a b M : ℝ} {cond : ℝ → Prop} [DecidablePred cond]
    (hf_bound : ∀ t ∈ Icc a b, cond t → ‖f t‖ ≤ M) (hM : 0 ≤ M) :
    ∀ t ∈ Icc a b, ‖if cond t then f t else 0‖ ≤ M := by
  intro t ht; by_cases hcond : cond t
  · simp only [hcond, ↓reduceIte]; exact hf_bound t ht hcond
  · simp only [hcond, ↓reduceIte, norm_zero]; exact hM

/-- Residue term is bounded when separated from the singularity. -/
lemma residue_term_bounded_when_separated {γ : ℝ → ℂ} {s c : ℂ} {a b ε : ℝ}
    (hε : 0 < ε) (h_sep : ∀ t ∈ Icc a b, ε < ‖γ t - s‖) :
    ∀ t ∈ Icc a b, ‖c / (γ t - s)‖ ≤ ‖c‖ / ε := by
  intro t ht
  rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg c) hε (le_of_lt (h_sep t ht))

/-- The sum of the norms of the simple-pole residues of `f` over a finite set `S`. -/
def residueNormSum (f : ℂ → ℂ) (S : Finset ℂ) : ℝ := ∑ s ∈ S, ‖residueSimplePole f s‖

lemma A_int_bound_good_set {S0 : Finset ℂ} {f g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε Mg Mγ : ℝ} (hε : 0 < ε) (hMg : 0 ≤ Mg) (_hMγ : 0 ≤ Mγ)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_bound : ∀ t ∈ Icc a b, ‖g_reg (γ t)‖ ≤ Mg)
    (hγ'_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ)
    (h_all_far : ∀ t ∈ Icc a b, ∀ s ∈ S0, ε < ‖γ t - s‖) :
    ∀ t ∈ Icc a b,
      ‖(cauchyPrincipalValueIntegrandOn S0 f γ ε t -
        ∑ s ∈ S0, if ‖γ t - s‖ > ε then residueSimplePole f s / (γ t - s) * deriv γ t
          else 0)‖ ≤ Mg * Mγ := by
  intro t ht
  have h_no_excl : ¬∃ s ∈ S0, ‖γ t - s‖ ≤ ε := by push Not; exact fun s hs => h_all_far t ht s hs
  simp only [cauchyPrincipalValueIntegrandOn, h_no_excl, ↓reduceIte]
  have h_sum_active : ∑ s ∈ S0, (if ε < ‖γ t - s‖
      then residueSimplePole f s / (γ t - s) * deriv γ t else 0) =
      (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl
    intro s hs; simp only [h_all_far t ht s hs, ↓reduceIte]
  rw [h_sum_active]
  have h_factor : f (γ t) * deriv γ t -
      (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t =
      (f (γ t) - ∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by ring
  rw [h_factor]
  have h_not_in_S0 : γ t ∉ (S0 : Set ℂ) := by
    intro h_in; simp only [Finset.mem_coe] at h_in
    have := h_all_far t ht (γ t) h_in; simp only [sub_self, norm_zero] at this; linarith
  rw [show f (γ t) - ∑ s ∈ S0, residueSimplePole f s / (γ t - s) = g_reg (γ t) from by
    rw [hg_decomp (γ t) h_not_in_S0]; ring]
  calc ‖g_reg (γ t) * deriv γ t‖ = ‖g_reg (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
    _ ≤ Mg * Mγ := mul_le_mul (hg_bound t ht) (hγ'_bound t ht) (norm_nonneg _) hMg

/-! ## Integrability Lemmas -/

/-- Multi-point PV integrand is interval integrable. -/
lemma intervalIntegrable_cauchyPrincipalValueIntegrandOn {S0 : Finset ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Immersion} {ε : ℝ} (_hε : 0 < ε)
    (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b)) :
    IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  obtain ⟨Mf, hMf⟩ := continuousOn_image_bounded hγ_cont hf_cont
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have _h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t‖ ≤ |Mf| * |Mγ'| + 1 := by
    intro t ht; simp only [cauchyPrincipalValueIntegrandOn]; split_ifs with h
    · simp only [norm_zero]; positivity
    · calc ‖f (γ.toFun t) * deriv γ.toFun t‖
          = ‖f (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ |Mf| * |Mγ'| := by
            apply mul_le_mul
            · exact le_trans (hMf _ (Set.mem_image_of_mem _ ht)) (le_abs_self _)
            · exact le_trans (hMγ' t ht) (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ |Mf| * |Mγ'| + 1 := by linarith
  let M := |Mf| * |Mγ'| + 1
  have h_meas :
      AEStronglyMeasurable
        (cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε)
        (volume.restrict (Icc γ.a γ.b)) :=
    aEStronglyMeasurable_pv_integrand_multipoint
      S0 hf_cont hγ_cont (piecewiseC1Immersion_continuousOn_deriv_off_partition γ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt γ.hab)]
  apply IntegrableOn.mono_set
  · exact integrableOn_of_bounded_aeMeasurable M
      h_meas _h_bound
  · exact Ioc_subset_Icc_self

/-- Residue term integrand is interval integrable. -/
lemma intervalIntegrable_residueTerm
    {γ : PiecewiseC1Immersion} {s c : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε
        then (c / (γ.toFun t - s)) *
          deriv γ.toFun t
        else 0)
      volume γ.a γ.b := by
  have h_γ'_bound :=
    piecewiseC1Immersion_deriv_bounded γ
  obtain ⟨Mγ', hMγ'⟩ := h_γ'_bound
  let M := ‖c‖ / ε * |Mγ'| + 1
  have _h_bound :
      ∀ t ∈ Icc γ.a γ.b,
        ‖if ‖γ.toFun t - s‖ > ε
          then (c / (γ.toFun t - s)) *
            deriv γ.toFun t
          else 0‖ ≤ M := by
    intro t ht
    split_ifs with h
    · calc ‖(c / (γ.toFun t - s)) *
            deriv γ.toFun t‖
          = ‖c / (γ.toFun t - s)‖ *
            ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ (‖c‖ / ε) * |Mγ'| := by
            apply mul_le_mul
            · rw [norm_div]
              apply div_le_div_of_nonneg_left
                (norm_nonneg c) hε
              exact le_of_lt h
            · exact le_trans (hMγ' t ht)
                (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ M := by simp only [M]; linarith
    · simp only [norm_zero, M]; positivity
  have hγ_cont :=
    γ.toPiecewiseC1Curve.continuous_toFun
  have h_meas :
      AEStronglyMeasurable
        (fun t => if ‖γ.toFun t - s‖ > ε
          then (c / (γ.toFun t - s)) *
            deriv γ.toFun t
          else 0)
        (volume.restrict (Icc γ.a γ.b)) :=
    aEStronglyMeasurable_pv_integrand_residue
      hε hγ_cont (piecewiseC1Immersion_continuousOn_deriv_off_partition γ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt γ.hab)]
  apply IntegrableOn.mono_set
  · exact integrableOn_of_bounded_aeMeasurable M
      h_meas _h_bound
  · exact Ioc_subset_Icc_self

/-! ## Measurability Lemmas -/

lemma aEStronglyMeasurable_pv_sum_residue
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ)
    {P : Finset ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => ∑ s ∈ S,
        if ‖γ t - s‖ > ε
        then residueSimplePole f s / (γ t - s) *
          deriv γ t
        else 0)
      (volume.restrict (Icc a b)) := by
  induction S using Finset.induction_on with
  | empty => exact aestronglyMeasurable_const
  | @insert x S' hx ih =>
    have hterm :=
      aEStronglyMeasurable_pv_integrand_residue
        (s := x)
        (c := residueSimplePole f x)
        hε hγ_cont hγ'_off_P
    refine AEStronglyMeasurable.add hterm ih
      |>.congr ?_
    refine ae_of_all _ (fun t => ?_)
    simp only [Pi.add_apply, Finset.sum_insert hx]

lemma aEStronglyMeasurable_multipointPV_diff
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ)
    {P : Finset ℝ}
    (hf_cont : ContinuousOn f
      (γ '' Set.uIcc a b))
    (hγ_cont : ContinuousOn γ
      (Set.uIcc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Set.uIcc a b \ P)) :
    AEStronglyMeasurable
      (fun t =>
        cauchyPrincipalValueIntegrandOn S0 f γ ε t -
          ∑ s ∈ S0,
            if ‖γ t - s‖ > ε
            then residueSimplePole f s / (γ t - s) *
              deriv γ t
            else 0)
      (volume.restrict (Ι a b)) := by
  rcases le_or_gt a b with hab | hab
  case inl =>
    have huIcc : Set.uIcc a b = Icc a b :=
      Set.uIcc_of_le hab
    rw [huIcc] at hf_cont hγ_cont hγ'_off_P
    have h1 :=
      aEStronglyMeasurable_pv_integrand_multipoint
        (ε := ε) S0 hf_cont hγ_cont hγ'_off_P
    have h3 :=
      aEStronglyMeasurable_pv_sum_residue S0 f γ ε
        hε a b hγ_cont hγ'_off_P
    have h_subset : Ι a b ⊆ Icc a b :=
      Set.uIoc_of_le hab ▸ Set.Ioc_subset_Icc_self
    exact (h1.sub h3).mono_measure
      (Measure.restrict_mono h_subset le_rfl)
  case inr =>
    have hba : b ≤ a := hab.le
    have huIcc : Set.uIcc a b = Icc b a :=
      Set.uIcc_of_ge hba
    rw [huIcc] at hf_cont hγ_cont hγ'_off_P
    have h1 :=
      aEStronglyMeasurable_pv_integrand_multipoint
        (ε := ε) S0 hf_cont hγ_cont hγ'_off_P
    have h3 :=
      aEStronglyMeasurable_pv_sum_residue S0 f γ ε
        hε b a hγ_cont hγ'_off_P
    have h_subset : Ι a b ⊆ Icc b a :=
      Set.uIoc_comm a b ▸
        Set.uIoc_of_le hba ▸
          Set.Ioc_subset_Icc_self
    exact (h1.sub h3).mono_measure
      (Measure.restrict_mono h_subset le_rfl)


end
