/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusPrimitive

/-!
# Weighted radial representation

This module upgrades the simple-function radial Radon-Nikodym representation
to the measurable, essentially bounded radius weights used by the weak
monotonicity argument.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- An a.e. identity on the radius interval pulls back through the radius map
to an a.e. identity on the Euclidean ball. -/
theorem ae_eq_comp_norm_on_ball_of_ae_eq_radius
    {n : ℕ} [NeZero n] {R0 : ℝ} {c d : ℝ → ℝ}
    (hcd : c =ᵐ[radiusIntervalMeasure R0] d) :
    (fun x : Domain n => c ‖x‖)
      =ᵐ[volume.restrict (Metric.ball (0 : Domain n) R0)]
    (fun x : Domain n => d ‖x‖) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  have hmap :
      c =ᵐ[μ.map (fun x : Domain n => ‖x‖)] d := by
    exact (radiusPushforward_absolutelyContinuous_euclidean
      (n := n) (R0 := R0)).ae_le hcd
  exact ae_of_ae_map continuous_norm.aemeasurable hmap

/-- The radial Radon-Nikodym density represents integration against every
a.e. measurable and a.e. bounded radius weight. -/
theorem radialRNDensity_radiusWeight_integral_eq {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {c : ℝ → ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hc : RadiusWeightOn R0 c) :
    (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
      =
    ∫ rho in Ioo (0 : ℝ) R0,
      c rho * radialRNDensity (n := n) f R0 rho := by
  classical
  let μ : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  let ν : Measure ℝ := radiusIntervalMeasure R0
  let D : ℝ → ℝ := radialRNDensity (n := n) f R0
  have hfμ : Integrable f μ := hf
  have hDν : Integrable D ν :=
    SignedMeasure.integrable_rnDeriv
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => ‖x‖))
      (radiusIntervalMeasure R0)
  let c₀ : ℝ → ℝ := hc.aestronglyMeasurable.mk c
  have hc₀_meas : Measurable c₀ := by
    simpa [c₀] using hc.aestronglyMeasurable.measurable_mk
  have hc_ae : c =ᵐ[ν] c₀ := by
    simpa [ν, c₀] using hc.aestronglyMeasurable.ae_eq_mk
  rcases hc.exists_ae_bound with ⟨C, hC_nonneg, hC_bound⟩
  have hc₀_bound : ∀ᵐ rho ∂ν, ‖c₀ rho‖ ≤ C := by
    filter_upwards [hc_ae, show ∀ᵐ rho ∂ν, |c rho| ≤ C from hC_bound] with rho hmk hbound
    simpa [hmk] using hbound
  have hpush : μ.map (fun x : Domain n => ‖x‖) ≪ ν := by
    simpa [μ, ν] using
      (radiusPushforward_absolutelyContinuous_euclidean (n := n) (R0 := R0))
  have hc₀_bound_ball :
      ∀ᵐ x ∂μ, ‖c₀ ‖x‖‖ ≤ C := by
    have hmap : ∀ᵐ rho ∂μ.map (fun x : Domain n => ‖x‖), ‖c₀ rho‖ ≤ C :=
      hpush.ae_le hc₀_bound
    exact ae_of_ae_map continuous_norm.aemeasurable hmap
  let cSeq : ℕ → SimpleFunc ℝ ℝ := fun N =>
    SimpleFunc.approxOn c₀ hc₀_meas (Set.univ : Set ℝ) 0 (Set.mem_univ 0) N
  have hleft_meas : ∀ N : ℕ,
      AEStronglyMeasurable
        (fun x : Domain n => cSeq N ‖x‖ * f x) μ := by
    intro N
    let gr : SimpleFunc (Domain n) ℝ :=
      (cSeq N).comp (fun x : Domain n => ‖x‖) continuous_norm.measurable
    exact (hfμ.simpleFunc_mul gr).aestronglyMeasurable
  have hright_meas : ∀ N : ℕ,
      AEStronglyMeasurable
        (fun rho : ℝ => cSeq N rho * D rho) ν := by
    intro N
    exact (hDν.simpleFunc_mul (cSeq N)).aestronglyMeasurable
  have hleft_bound_int :
      Integrable (fun x : Domain n => (C + C) * ‖f x‖) μ := by
    simpa using hfμ.norm.const_mul (C + C)
  have hright_bound_int :
      Integrable (fun rho : ℝ => (C + C) * ‖D rho‖) ν := by
    simpa using hDν.norm.const_mul (C + C)
  have hleft_bound : ∀ N : ℕ,
      ∀ᵐ x ∂μ, ‖cSeq N ‖x‖ * f x‖ ≤ (C + C) * ‖f x‖ := by
    intro N
    filter_upwards [hc₀_bound_ball] with x hx
    have happrox :
        ‖cSeq N ‖x‖‖ ≤ ‖c₀ ‖x‖‖ + ‖c₀ ‖x‖‖ := by
      simpa [cSeq] using
        (SimpleFunc.norm_approxOn_zero_le
          (f := c₀) hc₀_meas (s := Set.univ) (Set.mem_univ 0) ‖x‖ N)
    have hcoeff : ‖cSeq N ‖x‖‖ ≤ C + C :=
      happrox.trans (add_le_add hx hx)
    calc
      ‖cSeq N ‖x‖ * f x‖
          = ‖cSeq N ‖x‖‖ * ‖f x‖ := norm_mul (cSeq N ‖x‖) (f x)
      _ ≤ (C + C) * ‖f x‖ := by
        exact mul_le_mul hcoeff le_rfl (norm_nonneg (f x))
          (add_nonneg hC_nonneg hC_nonneg)
  have hright_bound : ∀ N : ℕ,
      ∀ᵐ rho ∂ν, ‖cSeq N rho * D rho‖ ≤ (C + C) * ‖D rho‖ := by
    intro N
    filter_upwards [hc₀_bound] with rho hrho
    have happrox :
        ‖cSeq N rho‖ ≤ ‖c₀ rho‖ + ‖c₀ rho‖ := by
      simpa [cSeq] using
        (SimpleFunc.norm_approxOn_zero_le
          (f := c₀) hc₀_meas (s := Set.univ) (Set.mem_univ 0) rho N)
    have hcoeff : ‖cSeq N rho‖ ≤ C + C :=
      happrox.trans (add_le_add hrho hrho)
    calc
      ‖cSeq N rho * D rho‖
          = ‖cSeq N rho‖ * ‖D rho‖ := norm_mul (cSeq N rho) (D rho)
      _ ≤ (C + C) * ‖D rho‖ := by
        exact mul_le_mul hcoeff le_rfl (norm_nonneg (D rho))
          (add_nonneg hC_nonneg hC_nonneg)
  have hleft_lim :
      ∀ᵐ x ∂μ,
        Filter.Tendsto (fun N : ℕ => cSeq N ‖x‖ * f x) Filter.atTop
          (𝓝 (c₀ ‖x‖ * f x)) := by
    filter_upwards [] with x
    exact
      (SimpleFunc.tendsto_approxOn
        (f := c₀) hc₀_meas (s := Set.univ) (Set.mem_univ 0)
        (by simp : c₀ ‖x‖ ∈ closure (Set.univ : Set ℝ))).mul
        tendsto_const_nhds
  have hright_lim :
      ∀ᵐ rho ∂ν,
        Filter.Tendsto (fun N : ℕ => cSeq N rho * D rho) Filter.atTop
          (𝓝 (c₀ rho * D rho)) := by
    filter_upwards [] with rho
    exact
      (SimpleFunc.tendsto_approxOn
        (f := c₀) hc₀_meas (s := Set.univ) (Set.mem_univ 0)
        (by simp : c₀ rho ∈ closure (Set.univ : Set ℝ))).mul
        tendsto_const_nhds
  have hleft_tendsto :
      Filter.Tendsto
        (fun N : ℕ => ∫ x, cSeq N ‖x‖ * f x ∂μ)
        Filter.atTop
        (𝓝 (∫ x, c₀ ‖x‖ * f x ∂μ)) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := μ)
        (F := fun N x => cSeq N ‖x‖ * f x)
        (f := fun x : Domain n => c₀ ‖x‖ * f x)
        (fun x : Domain n => (C + C) * ‖f x‖)
        hleft_meas hleft_bound_int hleft_bound hleft_lim
  have hright_tendsto :
      Filter.Tendsto
        (fun N : ℕ => ∫ rho, cSeq N rho * D rho ∂ν)
        Filter.atTop
        (𝓝 (∫ rho, c₀ rho * D rho ∂ν)) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := ν)
        (F := fun N rho => cSeq N rho * D rho)
        (f := fun rho : ℝ => c₀ rho * D rho)
        (fun rho : ℝ => (C + C) * ‖D rho‖)
        hright_meas hright_bound_int hright_bound hright_lim
  have hsimple : ∀ N : ℕ,
      (∫ x, cSeq N ‖x‖ * f x ∂μ)
        =
      ∫ rho, cSeq N rho * D rho ∂ν := by
    intro N
    simpa [μ, ν, D] using
      radialRNDensity_simpleFunc_integral_eq
        (n := n) (f := f) (R0 := R0) (g := cSeq N) hf
  have hlimit :
      (∫ x, c₀ ‖x‖ * f x ∂μ)
        =
      ∫ rho, c₀ rho * D rho ∂ν := by
    have hleft_as_right :
        Filter.Tendsto
          (fun N : ℕ => ∫ rho, cSeq N rho * D rho ∂ν)
          Filter.atTop
          (𝓝 (∫ x, c₀ ‖x‖ * f x ∂μ)) :=
      hleft_tendsto.congr' (Filter.Eventually.of_forall hsimple)
    exact tendsto_nhds_unique hleft_as_right hright_tendsto
  have hc_pull : (fun x : Domain n => c ‖x‖)
      =ᵐ[μ] (fun x : Domain n => c₀ ‖x‖) := by
    simpa [μ, ν] using
      ae_eq_comp_norm_on_ball_of_ae_eq_radius
        (n := n) (R0 := R0) (c := c) (d := c₀)
        (by simpa [ν] using hc_ae)
  have hleft_congr :
      (fun x : Domain n => c ‖x‖ * f x)
        =ᵐ[μ] (fun x : Domain n => c₀ ‖x‖ * f x) := by
    filter_upwards [hc_pull] with x hx
    rw [hx]
  have hright_congr :
      (fun rho : ℝ => c rho * D rho)
        =ᵐ[ν] (fun rho : ℝ => c₀ rho * D rho) := by
    filter_upwards [hc_ae] with rho hrho
    rw [hrho]
  have hfull :
      (∫ x, c ‖x‖ * f x ∂μ)
        =
      ∫ rho, c rho * D rho ∂ν := by
    calc
      (∫ x, c ‖x‖ * f x ∂μ)
          = ∫ x, c₀ ‖x‖ * f x ∂μ := integral_congr_ae hleft_congr
      _ = ∫ rho, c₀ rho * D rho ∂ν := hlimit
      _ = ∫ rho, c rho * D rho ∂ν := (integral_congr_ae hright_congr).symm
  simpa [μ, ν, D, radiusIntervalMeasure] using hfull

/-- Euclidean radial pushforward/coarea theorem for all radius weights needed
in the weak monotonicity argument. -/
theorem ballIntegralRadiusWeightedRepresentationForWeights_euclidean (n : ℕ) :
    BallIntegralRadiusWeightedRepresentationForWeights n := by
  intro hne f R0 hf
  let : NeZero n := hne
  refine ⟨radialRNDensity (n := n) f R0, ?_, ?_⟩
  · exact radialRNDensity_locallyIntegrableOn (n := n) (f := f) (R0 := R0)
  · intro c hc
    exact radialRNDensity_radiusWeight_integral_eq
      (n := n) (f := f) (R0 := R0) (c := c) hf hc

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
