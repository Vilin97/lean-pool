/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts


/-!
# Holomorphic Primitives on Convex Sets

Construction of a primitive F for a holomorphic function f on a convex
open set S via the segment integral F(z) = ∫₀¹ f(c + t(z-c))·(z-c) dt.

## Main Results

* `holomorphic_convex_primitive` — holomorphic on convex open ⇒ has primitive
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

-- Needed in mathlib v4.29 where these instances are no longer synthesized automatically
attribute [local instance] IsScalarTower.complexToReal

private instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ :=
  NormedSpace.toNormSMulClass

private instance instIsBoundedSMulRealComplex : IsBoundedSMul ℝ ℂ :=
  NormSMulClass.toIsBoundedSMul

private instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ :=
  IsBoundedSMul.continuousSMul

private lemma segment_subset_convex {S : Set ℂ} (hS : Convex ℝ S)
    {c z : ℂ} (hc : c ∈ S) (hz : z ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, c + t • (z - c) ∈ S := fun t ht => by
  rw [show c + t • (z - c) = (1 - t) • c + t • z from by module]
  exact hS hc hz (by linarith [ht.2]) ht.1 (by linarith [ht.1])

private lemma integral_t_mul_deriv_eq {f : ℂ → ℂ} {S : Set ℂ}
    {c z : ℂ} (hS_open : IsOpen S)
    (hf : DifferentiableOn ℂ f S)
    (h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (z - c) ∈ S) :
    ∫ t in (0 : ℝ)..1,
        t * (deriv f (c + t • (z - c)) * (z - c)) =
      f z - ∫ t in (0 : ℝ)..1, f (c + t • (z - c)) := by
  let u : ℝ → ℂ := fun t => t
  let v : ℝ → ℂ := fun t => f (c + t • (z - c))
  let u' : ℝ → ℂ := fun _ => 1
  let v' : ℝ → ℂ := fun t => deriv f (c + t • (z - c)) * (z - c)
  let γ : ℝ → ℂ := fun t => c + t • (z - c)
  have hγ_cont : Continuous γ :=
    continuous_const.add (continuous_ofReal.smul continuous_const)
  have hu_cont : ContinuousOn u (Set.uIcc 0 1) :=
    continuous_ofReal.continuousOn
  have hv_cont : ContinuousOn v (Set.uIcc 0 1) := by
    apply ContinuousOn.comp hf.continuousOn hγ_cont.continuousOn
    intro t ht
    exact h_seg t (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ ht)
  have hu_deriv : ∀ x ∈ Set.Ioo (min 0 1) (max 0 1),
      HasDerivAt u (u' x) x := by
    intro x _
    simp only [u, u']
    exact ofRealCLM.hasDerivAt
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (z - c) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t :=
      ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) • (z - c))
        ((1 : ℂ) • (z - c)) t := h1.smul_const (z - c)
    simp only [one_smul] at h2
    have h3 : HasDerivAt (fun _ : ℝ => c) 0 t :=
      hasDerivAt_const t c
    convert h3.add h2 using 1
    · rfl
    · rfl
    · ring
  have hv_deriv : ∀ x ∈ Set.Ioo (min 0 1) (max 0 1),
      HasDerivAt v (v' x) x := by
    intro t ht
    simp only [v, v']
    simp only [min_eq_left, max_eq_right, (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h_in_S : γ t ∈ S := h_seg t (Ioo_subset_Icc_self ht)
    have h_chain := (hf.differentiableAt (hS_open.mem_nhds h_in_S)).hasDerivAt.scomp
      t (hγ_deriv t)
    simp only [smul_eq_mul] at h_chain
    convert h_chain using 1
    · rfl
    · rfl
    · ring
  have hu'_int : IntervalIntegrable u' MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable continuousOn_const
  have hv'_int : IntervalIntegrable v' MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hf.contDiffOn hS_open).continuousOn_deriv_of_isOpen hS_open le_rfl).mul_const _
      |>.comp hγ_cont.continuousOn (fun t ht => h_seg t ht)
  have h_parts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont hv_cont hu_deriv hv_deriv hu'_int hv'_int
  simp only [u, v, u', v'] at h_parts
  simp only [ofReal_one, ofReal_zero, one_mul, zero_mul,
    sub_zero] at h_parts
  rwa [show f (c + (1 : ℝ) • (z - c)) = f z by simp] at h_parts

private lemma continuous_segmentMap (c w : ℂ) :
    Continuous (fun t : ℝ => c + t • (w - c)) :=
  continuous_const.add (continuous_ofReal.smul continuous_const)

private lemma segmentIntegrand_aestronglyMeasurable
    {f : ℂ → ℂ} {S : Set ℂ} {c w : ℂ}
    (hf : ContinuousOn f S)
    (h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ S) :
    AEStronglyMeasurable (fun t : ℝ => f (c + t • (w - c)))
      (volume.restrict (Ioc 0 1)) := by
  have hcontOn : ContinuousOn
      (fun t : ℝ => f (c + t • (w - c))) (Icc 0 1) :=
    hf.comp (continuous_segmentMap c w).continuousOn
      (fun t ht => h_seg t ht)
  exact (hcontOn.mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc

private lemma segmentDerivIntegrand_aestronglyMeasurable
    {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S)
    (h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (z - c) ∈ S) :
    AEStronglyMeasurable
      (fun t : ℝ => t • deriv f (c + t • (z - c)))
      (volume.restrict (Ioc 0 1)) := by
  have hf'_cont : ContinuousOn (deriv f) S :=
    (hf.contDiffOn hS_open).continuousOn_deriv_of_isOpen
      hS_open le_rfl
  have hcontOn : ContinuousOn
      (fun t : ℝ => (t : ℂ) • deriv f (c + t • (z - c)))
      (Icc 0 1) :=
    continuous_ofReal.continuousOn.smul
      (hf'_cont.comp (continuous_segmentMap c z).continuousOn
        (fun t ht => h_seg t ht))
  exact (hcontOn.mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc

private lemma segmentIntegrand_intervalIntegrable
    {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hf : ContinuousOn f S)
    (h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (z - c) ∈ S) :
    IntervalIntegrable (fun t => f (c + t • (z - c)))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hf.comp (continuous_segmentMap c z).continuousOn
    (fun t ht => h_seg t ht)

private lemma hasDerivAt_segmentIntegrand {f : ℂ → ℂ}
    {S : Set ℂ} {c z : ℂ} {t : ℝ}
    (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S)
    (hpt : c + t • (z - c) ∈ S) :
    HasDerivAt (fun w => f (c + t • (w - c)))
      (t • deriv f (c + t • (z - c))) z := by
  have hg : HasDerivAt (fun w => c + t • (w - c)) t z := by
    have h1 : HasDerivAt (fun w : ℂ => t • (w - c)) (t • (1 : ℂ)) z :=
      ((hasDerivAt_id z).sub_const c).const_smul (t : ℝ)
    simpa [Complex.real_smul] using h1.const_add c
  have hf_at :=
    (hf.differentiableAt (hS_open.mem_nhds hpt)).hasDerivAt
  have hcomp := hf_at.comp z hg
  refine hcomp.congr_deriv ?_
  rw [RCLike.real_smul_eq_coe_mul]
  exact mul_comm _ _

private lemma segmentIntegrand_lipschitzOnWith {f : ℂ → ℂ}
    {S : Set ℂ} {c z : ℂ} {t : ℝ} {ε M : ℝ}
    (_hε_pos : 0 < ε) (_hM_pos : 0 < M)
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℂ f S) (hc : c ∈ S)
    (hε_ball : Metric.ball z ε ⊆ S)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hM_bound : ∀ w ∈ Metric.ball z ε,
      ‖deriv f (c + t • (w - c))‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (|t| * M))
      (fun w => f (c + t • (w - c)))
      (Metric.ball z ε) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hgx : c + t • (x - c) ∈ S :=
    segment_subset_convex hS_convex hc (hε_ball hx) t ht
  have hgy : c + t • (y - c) ∈ S :=
    segment_subset_convex hS_convex hc (hε_ball hy) t ht
  have h_diff :
      (c + t • (x - c)) - (c + t • (y - c)) = t • (x - y) := by module
  have hconv_seg : Convex ℝ
      (segment ℝ (c + t • (x - c)) (c + t • (y - c))) :=
    convex_segment _ _
  have h_seg_in_S :
      segment ℝ (c + t • (x - c)) (c + t • (y - c)) ⊆ S :=
    hS_convex.segment_subset hgx hgy
  have h_bound :
      ‖f (c + t • (x - c)) - f (c + t • (y - c))‖ ≤
        M * ‖(c + t • (x - c)) - (c + t • (y - c))‖ := by
    have h_diff_at : ∀ p ∈
        segment ℝ (c + t • (x - c)) (c + t • (y - c)),
        DifferentiableAt ℂ f p :=
      fun p hp =>
        hf.differentiableAt (hS_open.mem_nhds (h_seg_in_S hp))
    have h_deriv_bound : ∀ p ∈
        segment ℝ (c + t • (x - c)) (c + t • (y - c)),
        ‖deriv f p‖ ≤ M := by
      intro p hp
      obtain ⟨s, hs, hp_eq⟩ :=
        segment_eq_image' ℝ
          (c + t • (x - c)) (c + t • (y - c)) ▸ hp
      have hw' : x + s • (y - x) ∈ Metric.ball z ε :=
        (convex_ball z ε).add_smul_sub_mem hx hy hs
      have hp_form :
          p = c + t • ((x + s • (y - x)) - c) := by
        rw [← hp_eq]; simp only [smul_sub, smul_add]
        simp only [smul_comm s t]; module
      rw [hp_form]; exact hM_bound _ hw'
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      h_diff_at h_deriv_bound hconv_seg
      (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
  calc dist (f (c + t • (x - c))) (f (c + t • (y - c)))
      = ‖f (c + t • (x - c)) - f (c + t • (y - c))‖ :=
        dist_eq_norm _ _
    _ ≤ M * ‖(c + t • (x - c)) - (c + t • (y - c))‖ :=
        h_bound
    _ = M * ‖t • (x - y)‖ := by rw [h_diff]
    _ = M * (|t| * ‖x - y‖) := by rw [norm_smul]; simp only [Real.norm_eq_abs]
    _ = |t| * M * ‖x - y‖ := by ring
    _ = |t| * M * dist x y := by rw [dist_eq_norm]
    _ ≤ Real.toNNReal (|t| * M) * dist x y := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        exact Real.le_coe_toNNReal _

private lemma hasDerivAt_segmentIntegral_aux {f : ℂ → ℂ}
    {S : Set ℂ} {c z : ℂ} {ε : ℝ}
    (hε_pos : 0 < ε)
    (hS_convex : Convex ℝ S) (hS_open : IsOpen S)
    (hc : c ∈ S) (hz : z ∈ S)
    (hf : DifferentiableOn ℂ f S)
    (hε_ball : Metric.ball z ε ⊆ S) :
    HasDerivAt
      (fun w => ∫ t in (0 : ℝ)..1, f (c + t • (w - c)))
      (∫ t in (0 : ℝ)..1, t • deriv f (c + t • (z - c)))
      z := by
  let F : ℂ → ℝ → ℂ := fun w t => f (c + t • (w - c))
  let F' : ℝ → ℂ := fun t => t • deriv f (c + t • (z - c))
  have h_seg : ∀ w ∈ Metric.ball z ε,
      ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ S :=
    fun w hw t ht =>
      segment_subset_convex hS_convex hc (hε_ball hw) t ht
  have h_seg_z : ∀ t ∈ Icc (0 : ℝ) 1,
      c + t • (z - c) ∈ S :=
    fun t ht => segment_subset_convex hS_convex hc hz t ht
  let ε' := ε / 2
  have hε'_pos : 0 < ε' := by positivity
  have hε'_lt_ε : ε' < ε := by change ε / 2 < ε; linarith
  have hε'_ball : Metric.ball z ε' ⊆ Metric.ball z ε :=
    Metric.ball_subset_ball (le_of_lt hε'_lt_ε)
  have hf'_cont : ContinuousOn (deriv f) S :=
    (hf.contDiffOn hS_open).continuousOn_deriv_of_isOpen
      hS_open le_rfl
  obtain ⟨M, hM_pos, hM_bound⟩ :
      ∃ M > 0, ∀ w ∈ Metric.ball z ε',
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖deriv f (c + t • (w - c))‖ ≤ M := by
    let segmentMap : ℂ × ℝ → ℂ :=
      fun ⟨w, t⟩ => c + t • (w - c)
    have hcont : Continuous segmentMap := by
      apply Continuous.add continuous_const
      exact continuous_snd.smul
        (continuous_fst.sub continuous_const)
    let K := segmentMap ''
      (Metric.closedBall z ε' ×ˢ Icc (0 : ℝ) 1)
    have hK_compact : IsCompact K :=
      (IsCompact.prod (isCompact_closedBall z ε')
        isCompact_Icc).image hcont
    have hclosedBall_in_S :
        Metric.closedBall z ε' ⊆ S :=
      (Metric.closedBall_subset_ball hε'_lt_ε).trans hε_ball
    have hK_in_S : K ⊆ S := by
      intro p hp
      obtain ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩ := hp
      exact segment_subset_convex hS_convex hc
        (hclosedBall_in_S hw) t ht
    obtain ⟨M', hM'⟩ :=
      hK_compact.bddAbove_image (hf'_cont.norm.mono hK_in_S)
    exact ⟨max M' 1, by positivity, fun w hw t ht =>
      (hM' ⟨c + t • (w - c),
        ⟨⟨w, t⟩, ⟨Metric.ball_subset_closedBall hw, ht⟩,
          rfl⟩, rfl⟩).trans (le_max_left _ _)⟩
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w)
        (volume.restrict (Set.uIoc 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds z hε'_pos] with w hw
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact segmentIntegrand_aestronglyMeasurable
      hf.continuousOn (fun t ht => h_seg w (hε'_ball hw) t ht)
  have hF_int : IntervalIntegrable (F z) volume 0 1 :=
    segmentIntegrand_intervalIntegrable hf.continuousOn h_seg_z
  have hF'_meas : AEStronglyMeasurable F'
      (volume.restrict (Set.uIoc 0 1)) := by
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact segmentDerivIntegrand_aestronglyMeasurable
      hS_open hf h_seg_z
  have h_lip : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 →
      LipschitzOnWith (Real.nnabs (|t| * M))
        (fun w => F w t) (Metric.ball z ε') := by
    apply MeasureTheory.ae_of_all
    intro t ht_mem
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      at ht_mem
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt ht_mem.1, ht_mem.2⟩
    have h_nonneg : 0 ≤ |t| * M :=
      mul_nonneg (abs_nonneg t) (le_of_lt hM_pos)
    rw [Real.nnabs_of_nonneg h_nonneg]
    exact segmentIntegrand_lipschitzOnWith hε'_pos hM_pos
      hS_open hS_convex hf hc
      (fun w hw => hε_ball (hε'_ball hw)) ht
      (fun w hw => hM_bound w hw t ht)
  have bound_int :
      IntervalIntegrable (fun t => |t| * M) volume 0 1 :=
    (continuous_abs.intervalIntegrable 0 1).mul_const M
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 →
      HasDerivAt (fun w => F w t) (F' t) z := by
    apply MeasureTheory.ae_of_all
    intro t ht_mem
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      at ht_mem
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt ht_mem.1, ht_mem.2⟩
    exact hasDerivAt_segmentIntegrand hS_open hf (h_seg_z t ht)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (Metric.ball_mem_nhds z hε'_pos) hF_meas hF_int hF'_meas h_lip bound_int h_diff).2

private lemma hasDerivAt_segmentIntegral {f : ℂ → ℂ}
    {S : Set ℂ} {c z : ℂ}
    (hS_convex : Convex ℝ S) (hS_open : IsOpen S)
    (hc : c ∈ S) (hz : z ∈ S)
    (hf : DifferentiableOn ℂ f S) :
    HasDerivAt
      (fun w => ∫ t in (0 : ℝ)..1,
        f (c + t • (w - c)) * (w - c))
      (f z) z := by
  have h_seg_z : ∀ t ∈ Icc (0 : ℝ) 1,
      c + t • (z - c) ∈ S :=
    fun t ht => segment_subset_convex hS_convex hc hz t ht
  obtain ⟨ε, hε_pos, hε_ball⟩ :=
    Metric.isOpen_iff.mp hS_open z hz
  let H : ℂ → ℂ := fun w =>
    ∫ t in (0 : ℝ)..1, f (c + t • (w - c))
  have hF_eq : ∀ w,
      (∫ t in (0 : ℝ)..1,
        f (c + t • (w - c)) * (w - c)) =
      H w * (w - c) := by
    intro w
    simpa only [H] using intervalIntegral.integral_mul_const (𝕜 := ℂ) _ _
  suffices HasDerivAt (fun w => H w * (w - c)) (f z) z by
    convert this using 1
    ext w; exact hF_eq w
  have h1 : HasDerivAt (fun w => w - c) 1 z :=
    ((hasDerivAt_id z).sub (hasDerivAt_const z c)).congr_deriv (by ring)
  let H' : ℂ → ℂ := fun w =>
    ∫ t in (0 : ℝ)..1, t * deriv f (c + t • (w - c))
  have h_key : H' z * (z - c) = f z - H z := by
    simp only [H, H']
    have h_ibp :=
      integral_t_mul_deriv_eq hS_open hf h_seg_z
    rw [show (∫ (t : ℝ) in (0 : ℝ)..1, ↑t * deriv f (c + t • (z - c))) * (z - c) =
      ∫ (t : ℝ) in (0 : ℝ)..1, ↑t * deriv f (c + t • (z - c)) * (z - c) from
      (intervalIntegral.integral_mul_const (𝕜 := ℂ) _ _).symm]
    convert h_ibp using 2
    ext t; ring
  suffices hH : HasDerivAt H (H' z) z by
    have h_prod := hH.mul h1
    refine h_prod.congr_deriv ?_
    calc H' z * (z - c) + H z * 1 = H' z * (z - c) + H z := by ring
      _ = (f z - H z) + H z := by rw [h_key]
      _ = f z := by ring
  exact hasDerivAt_segmentIntegral_aux hε_pos hS_convex
    hS_open hc hz hf hε_ball

/-- For a convex open set, holomorphic functions have primitives.

**Construction**: For f holomorphic on convex open S and c ∈ S,
F(z) = ∫₀¹ f(c + t(z-c))·(z-c) dt is a primitive with F'(z) = f(z).
-/
theorem holomorphic_convex_primitive
    {f : ℂ → ℂ} {S : Set ℂ} (hS_convex : Convex ℝ S)
    (hS_open : IsOpen S) (hS_ne : S.Nonempty)
    (hf : DifferentiableOn ℂ f S) :
    ∃ F : ℂ → ℂ, ∀ z ∈ S, HasDerivAt F (f z) z := by
  obtain ⟨c, hc⟩ := hS_ne
  exact ⟨fun z => ∫ t in (0 : ℝ)..1,
    f (c + t • (z - c)) * (z - c),
    fun z hz => hasDerivAt_segmentIntegral hS_convex
      hS_open hc hz hf⟩

end
