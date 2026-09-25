/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.SupportThickening

/-!
# Global and local `Lᵖ` approximation by mollification

The three results below separate translation continuity, the normalized-kernel
estimate, and the compact-localization step used for interior convergence.
-/

@[expose] public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section

private theorem tendsto_eLpNorm_sub_zero_mollify_of_continuous
    {d : ℕ} {f : Vec d → ℝ} {p : ENNReal}
    (hp_top : p ≠ ∞) (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume)
      atTop (nhds 0) := by
  let K : Set (Vec d) := Metric.closedBall 0 1 + tsupport f
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : Vec d) 1).add hf_supp.isCompact
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hK_ne_top : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
  have hpow_ne_top : volume K ^ (1 / p.toReal) ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK_ne_top).ne
  let cK : ℝ := (volume K ^ (1 / p.toReal)).toReal
  have hcK_nonneg : 0 ≤ cK := ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cK = volume K ^ (1 / p.toReal) := by
    dsimp [cK]
    exact ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  let δ : ℝ := η.toReal / (cK + 1)
  have hη_real : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont) δ hδ_pos
  have hε_small : ∀ᶠ n in atTop, ε n < γ / 2 :=
    (tendsto_order.1 hε).2 _ (by positivity)
  have hε_le_one : ∀ᶠ n in atTop, ε n ≤ 1 :=
    ((tendsto_order.1 hε).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [hε_small, hε_le_one] with n hn_small hn_one
  have hkernel_support :
      support (mollifier (d := d) (ε n) (hε_pos n)) ⊆ Metric.ball 0 (2 * ε n) := by
    apply (subset_tsupport _).trans
    rw [CKN.mollifier_tsupp_eq_closedBall (hε_pos n)]
    exact Metric.closedBall_subset_ball (by linarith only [hε_pos n])
  have hdist : ∀ x,
      dist (mollify f (ε n) (hε_pos n) x) (f x) ≤ δ := by
    intro x
    apply MeasureTheory.dist_convolution_le (le_of_lt hδ_pos)
    · exact hkernel_support
    · exact mollifier_nonneg (hε_pos n)
    · exact mollifier_integral_one (hε_pos n)
    · exact hf_cont.aestronglyMeasurable
    · intro y hy
      rw [Metric.mem_ball, dist_eq_norm_sub] at hy
      apply (hγ ?_).le
      rw [dist_eq_norm_sub]
      exact hy.trans (by linarith only [hn_small])
  have hconv_support :
      support (mollify f (ε n) (hε_pos n)) ⊆ K := by
    calc
      support (mollify f (ε n) (hε_pos n)) ⊆
          support (mollifier (d := d) (ε n) (hε_pos n)) + support f := by
        simpa [mollify] using
          (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
            (f := mollifier (d := d) (ε n) (hε_pos n)) (g := f))
      _ ⊆ Metric.closedBall 0 1 + tsupport f := by
        exact add_subset_add
          ((subset_tsupport _).trans (by
            rw [CKN.mollifier_tsupp_eq_closedBall (hε_pos n)]
            exact Metric.closedBall_subset_closedBall hn_one))
          (subset_tsupport _)
  have hf_support : support f ⊆ K := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hbound :
      eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := by
    have hmeas : AEStronglyMeasurable
        (fun x => mollify f (ε n) (hε_pos n) x - f x) volume :=
      ((mollify_continuous (hε_pos n)
        (hf_cont.integrable_of_hasCompactSupport hf_supp).locallyIntegrable).sub hf_cont)
        |>.aestronglyMeasurable
    exact eLpNorm_sub_le_of_dist_bdd volume hp_top hK_meas.nullMeasurableSet hδ_pos.le
      hmeas hdist
      hconv_support hf_support
  have hδmul : δ * cK ≤ η.toReal := by
    have hfrac_le : cK / (cK + 1) ≤ 1 := by
      exact div_le_one_of_le₀ (by linarith only [hcK_nonneg]) (by linarith only [hcK_nonneg])
    calc
      δ * cK = η.toReal * (cK / (cK + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη_real.le
      _ = η.toReal := mul_one _
  calc
    eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := hbound
    _ = ENNReal.ofReal (δ * cK) := by
      rw [← hpow_eq, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hη_top]
      exact ENNReal.ofReal_le_ofReal hδmul

theorem tendsto_eLpNorm_sub_zero_mollify
    {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {g : Vec 3 → ℝ} (hg : MemLp g p volume)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm (fun x => mollify g (ε n) (hε_pos n) x - g x) p volume)
      atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec 3))) (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec 3))) (ε := ℝ) (p := p) hη₁_pos.ne'
  let δ : ℝ≥0∞ := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f', hf'_supp, happrox', hf'_cont, hf'_mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp_top hδ_pos.ne'
  have hthird_mem' : MemLp (fun x => f' x - g x) p volume := hf'_mem.sub hg
  have hthird_norm' : eLpNorm (fun x => f' x - g x) p volume ≤ η₁ := by
    have hneg : (fun x => f' x - g x) = -(fun x => g x - f' x) := by
      ext x
      change f' x - g x = -(g x - f' x)
      abel_nf
    rw [hneg, eLpNorm_neg]
    exact happrox'.trans (min_le_left _ _)
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm (fun x => mollify f' (ε n) (hε_pos n) x - f' x) p volume ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_sub_zero_mollify_of_continuous hp_top hf'_cont hf'_supp hε hε_pos)
      η₂ hη₂_pos
  filter_upwards [hmid_eventually] with n hmid
  let k : Vec 3 → ℝ := mollifier (d := 3) (ε n) (hε_pos n)
  have hk_compact : HasCompactSupport k := mollifier_hasCompactSupport (hε_pos n)
  have hk_cont : Continuous k := (mollifier_contDiff (hε_pos n) (n := 0)).continuous
  have hg_loc : LocallyIntegrable g volume := hg.locallyIntegrable hp
  have hf'_loc : LocallyIntegrable f' volume := hf'_mem.locallyIntegrable hp
  have hdiff_loc : LocallyIntegrable (fun x => g x - f' x) volume := hg_loc.sub hf'_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hconv_f : ConvolutionExists k f' (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hf'_loc
  have hconv_diff : ConvolutionExists k (fun x => g x - f' x)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hdiff_loc
  have hsplit : g = (fun x => g x - f' x) + f' := by
    ext x
    change g x = (g x - f' x) + f' x
    abel_nf
  have hconv_split :
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := by
    calc
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => g x - f' x) + f') := by
            exact congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' :=
            hconv_diff.distrib_add hconv_f
  have hfirst_norm :
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
        p volume ≤ η₂ := by
    calc
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
          p volume ≤ eLpNorm (fun x => g x - f' x) p volume :=
        young_convolution_nonneg_integral_one_of_aemeasurable hp hp_top
          (mollifier_nonneg (hε_pos n)) (integrable_of_integral_eq_one
            (mollifier_integral_one (hε_pos n))) (mollifier_integral_one (hε_pos n))
          hk_cont.measurable (hg.sub hf'_mem).aestronglyMeasurable.aemeasurable
      _ ≤ η₂ := happrox'.trans (min_le_right _ _)
  have hfirst_meas : AEStronglyMeasurable
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) volume := by
    exact (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hk_cont hdiff_loc).aestronglyMeasurable
  have hmiddle_meas : AEStronglyMeasurable
      (fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) volume := by
    exact (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hk_cont hf'_loc).sub hf'_cont |>.aestronglyMeasurable
  have hfirst_middle :
      eLpNorm
        ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x)
        p volume < η₁ := by
    exact hη₂ _ _ hfirst_norm (by simpa only [k, mollify] using hmid)
  have hsum :
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p volume < η := by
    exact hη₁ _ _ hfirst_middle.le hthird_norm'
  have hdecomp :
      eLpNorm (fun x => mollify g (ε n) (hε_pos n) x - g x) p volume =
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p volume := by
    rw [show mollify g (ε n) (hε_pos n) =
        k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g by rfl, hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    abel_nf
  exact hdecomp ▸ hsum.le

theorem mollify_eq_on_compact_of_eq_on_thickening
    {d : ℕ} {K : Set (Vec d)} {u g : Vec d → ℝ} {ε₀ ε : ℝ}
    (hε : 0 < ε) (hεlt : ε ≤ ε₀)
    (h_eq : ∀ y ∈ K + Metric.closedBall 0 ε₀, u y = g y) {x : Vec d} (hx : x ∈ K) :
    mollify u ε hε x = mollify g ε hε x := by
  rw [mollify, mollify]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Metric.closedBall 0 ε
  · have hty : x - t ∈ K + Metric.closedBall 0 ε₀ := by
      refine ⟨x, hx, -t, ?_, by abel_nf⟩
      have ht' : ‖t‖ ≤ ε := by
        simpa [Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using ht
      simpa [norm_neg] using le_trans ht' hεlt
    rw [h_eq (x - t) hty]
  · have hzero : mollifier (d := d) ε hε t = 0 := by
      apply notMem_support.mp
      intro ht_support
      exact ht (CKN.mollifier_tsupp_eq_closedBall hε ▸ subset_tsupport _ ht_support)
    simp [hzero]

theorem tendsto_eLpNorm_restrict_mollify_sub_zero
    {U K : Set (Vec 3)} (hK : IsCompact K) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hKε₀ : ∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U)
    {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : Vec 3 → ℝ} (hu : MemLp u p (volume.restrict U))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm
        (fun x => mollify ((K + Metric.closedBall 0 ε₀).indicator u) (ε n) (hε_pos n) x - u x)
        p (volume.restrict K))
      atTop (nhds 0) := by
  let S : Set (Vec 3) := K + Metric.closedBall 0 ε₀
  have hS_compact : IsCompact S := hK.add (isCompact_closedBall (0 : Vec 3) ε₀)
  have hS_meas : MeasurableSet S := hS_compact.measurableSet
  have hS_sub_U : S ⊆ U := by
    rintro y ⟨x, hx, t, ht, rfl⟩
    apply hKε₀ x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have ht' : ‖t‖ ≤ ε₀ := by
      simpa [Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using ht
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht'
  have huS : MemLp u p (volume.restrict S) :=
    hu.mono_measure (Measure.restrict_mono hS_sub_U (le_refl volume))
  have hg : MemLp (S.indicator u) p volume :=
    (memLp_indicator_iff_restrict hS_meas).2 huS
  have hglobal := tendsto_eLpNorm_sub_zero_mollify hp hp_top hg hε hε_pos
  have h_eq : ∀ y ∈ S, u y = S.indicator u y := by
    intro y hy
    simp only [Set.indicator_of_mem hy]
  have h_eq_on_K : ∀ᵐ x ∂volume.restrict K, x ∈ K :=
    ae_restrict_mem (μ := volume) hK.measurableSet
  have hle : ∀ᶠ n in atTop,
      eLpNorm
          (fun x => mollify (S.indicator u) (ε n) (hε_pos n) x - u x) p
            (volume.restrict K) ≤
        eLpNorm
          (fun x => mollify (S.indicator u) (ε n) (hε_pos n) x - S.indicator u x) p volume := by
    filter_upwards [] with n
    apply (eLpNorm_congr_ae ?_).trans_le
    · exact eLpNorm_mono_measure _ Measure.restrict_le_self
    filter_upwards [h_eq_on_K] with x hx
    have hxS : x ∈ S := by
      refine ⟨x, hx, 0, ?_, by simp only [add_zero]⟩
      simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      exact hε₀.le
    rw [h_eq x hxS]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hglobal
    (Eventually.of_forall fun _ => zero_le) hle

end

end CKN
