/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvolutionLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Global `L^p` convergence of the scaled mollifier

This file proves the global approximate-identity statement for the convex
kernel family.  It is deliberately independent of the affine inward
mollification and of bounded-domain Sobolev theory.
-/

namespace Homogenization

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

noncomputable section

private theorem tsupport_scaledConvexApproxKernel_subset_closedBall
    {d : ℕ} {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    tsupport (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall 0 a := by
  apply closure_minimal
  · intro t ht
    have hρ_ne : ρ (a⁻¹ • t) ≠ 0 := by
      intro hzero
      apply ht
      simp only [scaledConvexApproxKernel, hzero, mul_zero]
    have hρ_ball : a⁻¹ • t ∈ Metric.closedBall (0 : Vec d) 1 :=
      hρ.support_subset_closedBall (subset_tsupport ρ hρ_ne)
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball ⊢
    calc
      ‖t‖ = a * (a⁻¹ * ‖t‖) := by field_simp [ha.ne']
      _ = a * ‖a⁻¹ • t‖ := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hρ_ball ha.le
      _ = a := mul_one _
  · exact Metric.isClosed_closedBall

private theorem eLpNorm_convolution_scaledConvexApproxKernel_le
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (hg : AEMeasurable g volume) :
    eLpNorm
        (scaledConvexApproxKernel ρ a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
        p volume ≤ eLpNorm g p volume := by
  exact young_convolution_nonneg_integral_one_of_aemeasurable hp1 hp
    (scaledConvexApproxKernel_nonneg hρ ha)
    (integrable_scaledConvexApproxKernel hρ ha)
    (integral_scaledConvexApproxKernel hρ ha)
    (measurable_scaledConvexApproxKernel hρ.continuous a) hg

private theorem tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel_of_continuous
    {d : ℕ} {ρ f : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp : p ≠ ⊤)
    (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (nhds 0))
    (ha_pos : ∀ᶠ n in atTop, 0 < a n) :
    Tendsto
      (fun n => eLpNorm
        (fun x =>
          (scaledConvexApproxKernel ρ (a n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x)
        p volume)
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
  have ha_small : ∀ᶠ n in atTop, a n < γ / 2 :=
    (tendsto_order.1 ha).2 _ (by linarith)
  have ha_le_one : ∀ᶠ n in atTop, a n ≤ 1 :=
    ((tendsto_order.1 ha).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [ha_pos, ha_small, ha_le_one] with n han_pos han_small han_one
  have hkernel_support :
      support (scaledConvexApproxKernel ρ (a n)) ⊆ Metric.ball 0 (2 * a n) := by
    exact (subset_tsupport _).trans
      ((tsupport_scaledConvexApproxKernel_subset_closedBall hρ han_pos).trans
        (Metric.closedBall_subset_ball (by linarith)))
  have hdist : ∀ x,
      dist
        ((scaledConvexApproxKernel ρ (a n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)
        (f x) ≤ δ := by
    intro x
    apply MeasureTheory.dist_convolution_le (le_of_lt hδ_pos)
    · exact hkernel_support
    · exact scaledConvexApproxKernel_nonneg hρ han_pos
    · exact integral_scaledConvexApproxKernel hρ han_pos
    · exact hf_cont.aestronglyMeasurable
    · intro y hy
      rw [Metric.mem_ball, dist_eq_norm_sub] at hy
      apply (hγ ?_).le
      rw [dist_eq_norm_sub]
      exact hy.trans (by linarith)
  have hconv_support :
      support (scaledConvexApproxKernel ρ (a n) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ⊆ K := by
    calc
      support (scaledConvexApproxKernel ρ (a n) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
          ⊆ support (scaledConvexApproxKernel ρ (a n)) + support f :=
            support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
      _ ⊆ Metric.closedBall 0 1 + tsupport f := by
        exact add_subset_add
          ((subset_tsupport _).trans
            ((tsupport_scaledConvexApproxKernel_subset_closedBall hρ han_pos).trans
              (Metric.closedBall_subset_closedBall han_one)))
          (subset_tsupport _)
  have hf_support : support f ⊆ K := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hbound :
      eLpNorm
        (fun x =>
          (scaledConvexApproxKernel ρ (a n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x)
        p volume ≤ ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := by
    exact eLpNorm_sub_le_of_dist_bdd volume hp hK_meas.nullMeasurableSet hδ_pos.le
      (by
        exact (MeasureTheory.AEStronglyMeasurable.convolution
          (ContinuousLinearMap.lsmul ℝ ℝ)
          (continuous_scaledConvexApproxKernel hρ.continuous (a n)).aestronglyMeasurable
          hf_cont.aestronglyMeasurable).sub hf_cont.aestronglyMeasurable)
      hdist hconv_support hf_support
  have hδmul : δ * cK ≤ η.toReal := by
    have hfrac_le : cK / (cK + 1) ≤ 1 := by
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    calc
      δ * cK = η.toReal * (cK / (cK + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη_real.le
      _ = η.toReal := mul_one _
  calc
    eLpNorm
        (fun x =>
          (scaledConvexApproxKernel ρ (a n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x)
        p volume ≤ ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := hbound
    _ = ENNReal.ofReal (δ * cK) := by
      rw [← hpow_eq, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hη_top]
      exact ENNReal.ofReal_le_ofReal hδmul

/-- Convolution by the scaled convex kernel is a global approximate identity
in every finite `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hg : MemLp g p volume)
    {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ᶠ n in atTop, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm
        (fun x =>
          (scaledConvexApproxKernel ρ (ε n * r) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x)
        p volume)
      atTop (nhds 0) := by
  have hscale : Tendsto (fun n => ε n * r) atTop (nhds 0) := by
    simpa only [zero_mul] using hε.mul_const r
  have hscale_pos : ∀ᶠ n in atTop, 0 < ε n * r :=
    hε_pos.mono (fun _ hn => mul_pos hn hr)
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec d))) (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec d))) (ε := ℝ) (p := p) hη₁_pos.ne'
  let δ : ENNReal := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f, hf_supp, happrox, hf_cont, hf_mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp hδ_pos.ne'
  have hthird_mem : MemLp (fun x => f x - g x) p volume := hf_mem.sub hg
  have hthird_norm : eLpNorm (fun x => f x - g x) p volume ≤ η₁ := by
    have hneg : (fun x => f x - g x) = -(fun x => g x - f x) := by
      ext x
      change f x - g x = -(g x - f x)
      ring
    rw [hneg, eLpNorm_neg]
    exact happrox.trans (min_le_left _ _)
  have hmid_tendsto :=
    tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel_of_continuous
      hρ hp hf_cont hf_supp hscale hscale_pos
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm
        (fun x =>
          (scaledConvexApproxKernel ρ (ε n * r) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
        p volume ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1 hmid_tendsto η₂ hη₂_pos
  filter_upwards [hscale_pos, hmid_eventually] with n hn_scale hmid
  let k : Vec d → ℝ := scaledConvexApproxKernel ρ (ε n * r)
  have hk_compact : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hn_scale
  have hk_cont : Continuous k :=
    (contDiff_scaledConvexApproxKernel hρ (ε n * r)).continuous
  have hg_loc : LocallyIntegrable g volume := hg.locallyIntegrable hp1
  have hf_loc : LocallyIntegrable f volume := hf_mem.locallyIntegrable hp1
  have hdiff_loc : LocallyIntegrable (fun x => g x - f x) volume := hg_loc.sub hf_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hconv_f : ConvolutionExists k f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hf_loc
  have hconv_diff : ConvolutionExists k (fun x => g x - f x)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hdiff_loc
  have hsplit : g = (fun x => g x - f x) + f := by
    ext x
    change g x = (g x - f x) + f x
    ring
  have hconv_split :
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
    calc
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => g x - f x) + f) := by
            exact congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f :=
            hconv_diff.distrib_add hconv_f
  have hfirst_norm :
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x)
        p volume ≤ η₂ := by
    calc
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x)
          p volume
          ≤ eLpNorm (fun x => g x - f x) p volume :=
            eLpNorm_convolution_scaledConvexApproxKernel_le hρ hp1 hp hn_scale
              (hg.sub hf_mem).aemeasurable
      _ ≤ η₂ := happrox.trans (min_le_right _ _)
  have hfirst_meas : AEStronglyMeasurable
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) volume := by
    exact
      (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hk_cont hdiff_loc).aestronglyMeasurable
  have hmiddle_meas : AEStronglyMeasurable
      (fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) volume := by
    exact
      (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hk_cont hf_loc).sub hf_cont |>.aestronglyMeasurable
  have hfirst_middle :
      eLpNorm
        ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
        p volume < η₁ := by
    exact hη₂ _ _ hfirst_norm (by simpa only [k] using hmid)
  have hsum :
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) +
          fun x => f x - g x)
        p volume < η := by
    exact hη₁ _ _ hfirst_middle.le hthird_norm
  have hdecomp :
      eLpNorm
        (fun x =>
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x)
        p volume =
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) +
          fun x => f x - g x)
        p volume := by
    rw [hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    ring
  simpa only [k] using hdecomp.trans_le hsum.le

end

end Homogenization
