/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel

/-! # Smooth Representative -/

namespace Homogenization

open scoped Pointwise Convolution

/-!
# Smooth representative, measurability, and L^p bounds for the convex smoothing

Defines the globally smooth representative `convexApproxSmoothRepresentative`
and collects the measurability, `eLpNorm` control, and integrability lemmas
needed downstream: measurable-embedding of `convexApproxSample`, `map` of the
restricted volume measure, `eLpNorm_comp_convexApproxSample_le`,
`eLpNorm_convexApproxSmoothing_le`, `aestronglyMeasurable_/memLpOn_` variants,
the a.e. equality of smoothing vs. its representative, and integrability of
`fun y => u ∘ convexApproxSample y` against a finite measure.
-/

/-- A globally defined smooth representative for the convex-domain smoothing operator. -/
noncomputable def convexApproxSmoothRepresentative {d : ℕ} (U : Set (Vec d))
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        MeasureTheory.volume] Set.indicator U u) ((1 - ε) • x + ε • x0)

theorem contDiff_convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : MeasurableSet U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative U ρ u x0 r ε) := by
  have hεr_pos : 0 < ε * r := by positivity
  have hu_indicator_mem :
      MeasureTheory.MemLp (Set.indicator U u) p MeasureTheory.volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU]
    exact hu
  have hu_indicator_loc :
      MeasureTheory.LocallyIntegrable (Set.indicator U u) MeasureTheory.volume :=
    hu_indicator_mem.locallyIntegrable hp1
  have hconv :
      ContDiff ℝ (⊤ : ℕ∞)
        (scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          MeasureTheory.volume] Set.indicator U u) :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := MeasureTheory.volume)
      (f := scaledConvexApproxKernel ρ (ε * r))
      (g := Set.indicator U u)
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hεr_pos)
      (contDiff_scaledConvexApproxKernel hρ (ε * r))
      hu_indicator_loc
  have haff :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => (1 - ε) • x + ε • x0) := by
    exact
      ((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => x)).const_smul
        (1 - ε)).add contDiff_const
  simpa [convexApproxSmoothRepresentative] using! hconv.comp haff

theorem convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    convexApproxSmoothRepresentative U ρ u x0 r ε x =
      convexApproxSmoothing ρ u x0 r ε x := by
  simpa [convexApproxSmoothRepresentative] using
    (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
      hU hρ hx hball hr hε0 hε1).symm

theorem measurableEmbedding_convexApproxSample
    {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (hε1 : ε < 1) :
    MeasurableEmbedding (convexApproxSample x0 z r ε) := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a ha_ne).trans (Homeomorph.addRight b)
  have heq : (fun x : Vec d => e x) = convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  simpa [heq] using e.toMeasurableEquiv.measurableEmbedding

theorem map_restrict_convexApproxSample
    {d : ℕ} {U : Set (Vec d)} (_hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε1 : ε < 1) :
    MeasureTheory.Measure.map (convexApproxSample x0 z r ε)
        (MeasureTheory.volume.restrict U) =
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
        MeasureTheory.volume.restrict (convexApproxSample x0 z r ε '' U) := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a ha_ne).trans (Homeomorph.addRight b)
  have heq : (fun x : Vec d => e x) = convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  have hrestrict :
      MeasureTheory.Measure.map (convexApproxSample x0 z r ε)
          (MeasureTheory.volume.restrict U) =
        (MeasureTheory.Measure.map (convexApproxSample x0 z r ε) MeasureTheory.volume).restrict
          (convexApproxSample x0 z r ε '' U) := by
    have htmp :
        (MeasureTheory.volume.restrict U).map e =
          (MeasureTheory.volume.map e).restrict (e '' U) := by
      have h :=
        ((e.toMeasurableEquiv.restrict_map (μ := MeasureTheory.volume) (s := e '' U)).symm)
      simpa [Set.preimage_image_eq _ e.injective] using h
    simpa [heq] using htmp
  have hmap_volume :
      MeasureTheory.Measure.map (convexApproxSample x0 z r ε) MeasureTheory.volume =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) • MeasureTheory.volume := by
    have hmap_smul :
        MeasureTheory.Measure.map (fun x : Vec d => a • x) MeasureTheory.volume =
          ENNReal.ofReal ((a ^ d)⁻¹) • MeasureTheory.volume := by
      have hpow_nonneg : 0 ≤ a ^ d := by positivity
      let f : Vec d →ₗ[ℝ] Vec d := a • (1 : Vec d →ₗ[ℝ] Vec d)
      have hf : LinearMap.det f ≠ 0 := by
        simp [f, ha_ne]
      have hdet : LinearMap.det f = a ^ d := by
        simp [f]
      have hmapf :=
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (ι := Fin d) (f := f) hf
      have hpow_inv_nonneg : 0 ≤ (a ^ d)⁻¹ := by positivity
      rw [hdet] at hmapf
      simpa [f, abs_of_nonneg hpow_inv_nonneg] using! hmapf
    calc
      MeasureTheory.Measure.map (convexApproxSample x0 z r ε) MeasureTheory.volume
          = (MeasureTheory.Measure.map (fun x : Vec d => a • x) MeasureTheory.volume).map
              (fun y : Vec d => y + b) := by
              simpa [Function.comp, a, b, convexApproxSample] using!
                (MeasureTheory.Measure.map_map
                  (μ := MeasureTheory.volume)
                  (g := fun y : Vec d => y + b)
                  (f := fun x : Vec d => a • x)
                  (measurable_id.add measurable_const)
                  (measurable_const_smul a)).symm
      _ = MeasureTheory.Measure.map (fun y : Vec d => y + b)
            (ENNReal.ofReal ((a ^ d)⁻¹) • MeasureTheory.volume) := by
            rw [hmap_smul]
      _ = ENNReal.ofReal ((a ^ d)⁻¹) •
            MeasureTheory.Measure.map (fun y : Vec d => y + b) MeasureTheory.volume := by
            exact MeasureTheory.Measure.map_smul _
              (measurable_id.add measurable_const).aemeasurable
      _ = ENNReal.ofReal ((a ^ d)⁻¹) • MeasureTheory.volume := by
            rw [MeasureTheory.map_add_right_eq_self]
      _ = ENNReal.ofReal (((1 - ε) ^ d)⁻¹) • MeasureTheory.volume := by
            simp [a]
  calc
    MeasureTheory.Measure.map (convexApproxSample x0 z r ε)
        (MeasureTheory.volume.restrict U)
      = (MeasureTheory.Measure.map (convexApproxSample x0 z r ε) MeasureTheory.volume).restrict
          (convexApproxSample x0 z r ε '' U) := hrestrict
    _ = (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) • MeasureTheory.volume).restrict
          (convexApproxSample x0 z r ε '' U) := by rw [hmap_volume]
    _ = ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          MeasureTheory.volume.restrict (convexApproxSample x0 z r ε '' U) := by
          rw [MeasureTheory.Measure.restrict_smul]

theorem eLpNorm_comp_convexApproxSample_le
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal}
    (hp : p ≠ ⊤) (hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε1 : ε < 1)
    (hmap : convexApproxSample x0 z r ε '' U ⊆ U) :
    MeasureTheory.eLpNorm (fun x => u (convexApproxSample x0 z r ε x))
        p (MeasureTheory.volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) := by
  calc
    MeasureTheory.eLpNorm (fun x => u (convexApproxSample x0 z r ε x))
        p (MeasureTheory.volume.restrict U)
      = MeasureTheory.eLpNorm u p
          (MeasureTheory.Measure.map (convexApproxSample x0 z r ε)
            (MeasureTheory.volume.restrict U)) := by
            symm
            exact
              (measurableEmbedding_convexApproxSample x0 z r ε hε1).eLpNorm_map_measure
    _ = MeasureTheory.eLpNorm u p
          (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            MeasureTheory.volume.restrict (convexApproxSample x0 z r ε '' U)) := by
            rw [map_restrict_convexApproxSample hU x0 z r ε hε1]
    _ = ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal •
          MeasureTheory.eLpNorm u p
            (MeasureTheory.volume.restrict (convexApproxSample x0 z r ε '' U)) := by
            exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _
    _ ≤ ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal •
          MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) := by
            exact
              smul_le_smul_of_nonneg_left
                (MeasureTheory.eLpNorm_mono_measure u
                  (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hmap))
                (by positivity)
    _ = ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) := by
            rw [smul_eq_mul]

theorem eLpNorm_convexApproxSmoothing_le
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r ε) p
        (MeasureTheory.volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) := by
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume]
      Set.indicator U u
  have hU_meas : MeasurableSet U := hU.isOpen.measurableSet
  have hmap0_mapsTo :
      Set.MapsTo (convexApproxSample x0 0 r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr.le
      (by simp) hε0.le (le_of_lt hε1)
  have hmap0 : convexApproxSample x0 0 r ε '' U ⊆ U := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmap0_mapsTo hx
  have hrepr :
      (fun x => convexApproxSmoothing ρ u x0 r ε x) =ᵐ[MeasureTheory.volume.restrict U]
        fun x => g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU_meas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        hU hρ hx hball hr hε0 hε1)
  have hεr_pos : 0 < ε * r := by positivity
  have hu_indicator_mem :
      MeasureTheory.MemLp (Set.indicator U u) p MeasureTheory.volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU_meas]
    exact hu
  have hconv :
      MeasureTheory.eLpNorm g p MeasureTheory.volume ≤
        MeasureTheory.eLpNorm (Set.indicator U u) p MeasureTheory.volume := by
    dsimp [g]
    exact
      young_convolution_nonneg_integral_one_of_aemeasurable (d := d) hp1 hp
        (scaledConvexApproxKernel_nonneg hρ hεr_pos)
        (integrable_scaledConvexApproxKernel hρ hεr_pos)
        (integral_scaledConvexApproxKernel hρ hεr_pos)
        (measurable_scaledConvexApproxKernel hρ.continuous (ε * r))
        hu_indicator_mem.aestronglyMeasurable.aemeasurable
  calc
    MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r ε) p (MeasureTheory.volume.restrict U)
      = MeasureTheory.eLpNorm (fun x => g (convexApproxSample x0 0 r ε x)) p
          (MeasureTheory.volume.restrict U) := by
            exact MeasureTheory.eLpNorm_congr_ae hrepr
    _ ≤ ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm g p (MeasureTheory.volume.restrict U) := by
            exact eLpNorm_comp_convexApproxSample_le hp hU_meas x0 0 r ε hε1 hmap0
    _ ≤ ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm g p MeasureTheory.volume := by
            exact mul_le_mul' le_rfl
              (MeasureTheory.eLpNorm_mono_measure g MeasureTheory.Measure.restrict_le_self)
    _ ≤ ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm (Set.indicator U u) p MeasureTheory.volume := by
            exact mul_le_mul' le_rfl hconv
    _ = ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) := by
            rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU_meas]

theorem aestronglyMeasurable_convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable (convexApproxSmoothing ρ u x0 r ε)
      (MeasureTheory.volume.restrict U) := by
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume]
      Set.indicator U u
  have hU_meas : MeasurableSet U := hU.isOpen.measurableSet
  have hrepr :
      (fun x => convexApproxSmoothing ρ u x0 r ε x) =ᵐ[MeasureTheory.volume.restrict U]
        fun x => g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU_meas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        hU hρ hx hball hr hε0 hε1)
  have hεr_pos : 0 < ε * r := by positivity
  have hu_indicator_mem :
      MeasureTheory.MemLp (Set.indicator U u) p MeasureTheory.volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU_meas]
    exact hu
  have hg_cont : Continuous g := by
    dsimp [g]
    exact
      HasCompactSupport.continuous_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := MeasureTheory.volume)
        (f := scaledConvexApproxKernel ρ (ε * r))
        (g := Set.indicator U u)
        (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hεr_pos)
        (continuous_scaledConvexApproxKernel hρ.continuous (ε * r))
        (hu_indicator_mem.locallyIntegrable hp1)
  exact
    (aestronglyMeasurable_congr hrepr.symm).1
      ((hg_cont.comp (continuous_convexApproxSample x0 0 r ε)).aestronglyMeasurable)

theorem memLpOn_convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MemLpOn U p (convexApproxSmoothing ρ u x0 r ε) := by
  have hnorm_lt_top :
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict U) < ⊤ := by
    refine ENNReal.mul_lt_top ?_ hu.eLpNorm_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  refine lt_of_le_of_lt ?_ hnorm_lt_top
  · exact eLpNorm_convexApproxSmoothing_le hU hρ hp1 hp hu hball hr hε0 hε1

theorem convexApproxSmoothing_sub_ae_eq
    {d : ℕ} {U : Set (Vec d)} {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (fun x => convexApproxSmoothing ρ (fun y => u y - v y) x0 r ε x)
      =ᵐ[MeasureTheory.volume.restrict U]
        fun x => convexApproxSmoothing ρ u x0 r ε x - convexApproxSmoothing ρ v x0 r ε x := by
  let k : Vec d → ℝ := scaledConvexApproxKernel ρ (ε * r)
  let gu : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] Set.indicator U u
  let gv : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] Set.indicator U v
  let gw : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] Set.indicator U (fun y => u y - v y)
  have hU_meas : MeasurableSet U := hU.isOpen.measurableSet
  have hεr_pos : 0 < ε * r := by positivity
  have hk_cont : Continuous k := by
    dsimp [k]
    exact continuous_scaledConvexApproxKernel hρ.continuous (ε * r)
  have hk_compact : HasCompactSupport k := by
    dsimp [k]
    exact hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hεr_pos
  have hu_indicator_mem :
      MeasureTheory.MemLp (Set.indicator U u) p MeasureTheory.volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU_meas]
    exact hu
  have hv_indicator_mem :
      MeasureTheory.MemLp (Set.indicator U v) p MeasureTheory.volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU_meas]
    exact hv
  have hu_indicator_loc :
      MeasureTheory.LocallyIntegrable (Set.indicator U u) MeasureTheory.volume :=
    hu_indicator_mem.locallyIntegrable hp1
  have hv_indicator_loc :
      MeasureTheory.LocallyIntegrable (Set.indicator U v) MeasureTheory.volume :=
    hv_indicator_mem.locallyIntegrable hp1
  have hnegv_indicator_loc :
      MeasureTheory.LocallyIntegrable ((-1 : ℝ) • Set.indicator U v) MeasureTheory.volume := by
    simpa using hv_indicator_loc.smul (-1 : ℝ)
  have hconv_u :
      MeasureTheory.ConvolutionExists k (Set.indicator U u)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hu_indicator_loc
  have hconv_negv :
      MeasureTheory.ConvolutionExists k ((-1 : ℝ) • Set.indicator U v)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hnegv_indicator_loc
  have hind_sub :
      Set.indicator U (fun y => u y - v y) =
        Set.indicator U u + (-1 : ℝ) • Set.indicator U v := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, sub_eq_add_neg]
    · simp [hx]
  have hconv_sub :
      gw = fun x => gu x - gv x := by
    ext x
    dsimp [gw, gu, gv]
    rw [hind_sub, hconv_u.distrib_add hconv_negv, MeasureTheory.convolution_smul]
    simp [sub_eq_add_neg]
  filter_upwards [MeasureTheory.ae_restrict_mem hU_meas] with x hx
  have hu_repr :
      convexApproxSmoothing ρ u x0 r ε x = gu (convexApproxSample x0 0 r ε x) := by
    simpa [gu, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        hU hρ hx hball hr hε0 hε1)
  have hv_repr :
      convexApproxSmoothing ρ v x0 r ε x = gv (convexApproxSample x0 0 r ε x) := by
    simpa [gv, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        hU hρ hx hball hr hε0 hε1)
  have hw_repr :
      convexApproxSmoothing ρ (fun y => u y - v y) x0 r ε x =
        gw (convexApproxSample x0 0 r ε x) := by
    simpa [gw, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := fun y => u y - v y)
        hU hρ hx hball hr hε0 hε1)
  rw [hu_repr, hv_repr, hw_repr]
  rw [hconv_sub]

theorem eLpNorm_sub_convexApproxSmoothing_le
    {d : ℕ} {U : Set (Vec d)} {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.eLpNorm
        (fun x => convexApproxSmoothing ρ u x0 r ε x - convexApproxSmoothing ρ v x0 r ε x)
        p (MeasureTheory.volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm (fun x => u x - v x) p (MeasureTheory.volume.restrict U) := by
  have huw : MemLpOn U p (fun x => u x - v x) := hu.sub hv
  calc
    MeasureTheory.eLpNorm
        (fun x => convexApproxSmoothing ρ u x0 r ε x - convexApproxSmoothing ρ v x0 r ε x)
        p (MeasureTheory.volume.restrict U)
      = MeasureTheory.eLpNorm
          (convexApproxSmoothing ρ (fun y => u y - v y) x0 r ε) p
          (MeasureTheory.volume.restrict U) := by
            exact MeasureTheory.eLpNorm_congr_ae
              (convexApproxSmoothing_sub_ae_eq hU hρ hp1 hu hv hball hr hε0 hε1).symm
    _ ≤ ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm (fun x => u x - v x) p (MeasureTheory.volume.restrict U) :=
        eLpNorm_convexApproxSmoothing_le hU hρ hp1 hp huw hball hr hε0 hε1

theorem integrableOn_comp_smul_add_of_pos
    {d : ℕ} {s : Set (Vec d)} {u : Vec d → ℝ} {a : ℝ} (ha : 0 < a) (b : Vec d)
    (hs : MeasurableSet s)
    (hu : MeasureTheory.IntegrableOn u (translateSet b (a • s)) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun x => u (a • x + b)) s MeasureTheory.volume := by
  have ha_ne : a ≠ 0 := ha.ne'
  let V : Set (Vec d) := translateSet b (a • s)
  have hV_meas : MeasurableSet V := by
    have hpre : ⇑(Homeomorph.subRight b) ⁻¹' (a • s) = V := by
      ext x
      simp [V, mem_translateSet_iff_sub_mem]
    rw [← hpre]
    exact
      ((Homeomorph.subRight b).toMeasurableEquiv.measurableSet_preimage).2
        (((Homeomorph.smulOfNeZero a ha_ne).toMeasurableEquiv.measurableSet_image).2 hs)
  have h_indicator : MeasureTheory.Integrable (Set.indicator V u) MeasureTheory.volume :=
    hu.integrable_indicator hV_meas
  have h_translated : MeasureTheory.Integrable (fun x => Set.indicator V u (x + b))
      MeasureTheory.volume := by
    exact
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) b).integrable_comp_of_integrable
          h_indicator
  have h_scaled : MeasureTheory.Integrable (fun x => Set.indicator V u (a • x + b))
      MeasureTheory.volume := by
    let g : Vec d → ℝ := fun x => Set.indicator V u (x + b)
    have hg : MeasureTheory.Integrable g MeasureTheory.volume := by
      simpa [g] using h_translated
    simpa [g, Function.comp] using hg.comp_smul ha_ne
  have h_indicator_eq :
      Set.indicator s (fun x => u (a • x + b)) =
        fun x => Set.indicator V u (a • x + b) := by
    funext x
    by_cases hx : x ∈ s
    · have hyV : a • x + b ∈ V := by
        exact ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      simp [Set.indicator_of_mem, hx, hyV]
    · have hyV : a • x + b ∉ V := by
        intro hyV
        rcases hyV with ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with ⟨x', hx', rfl⟩
        have hxx' : x = x' := by
          have := congrArg (fun t : Vec d => a⁻¹ • (t - b)) hyw
          simpa [smul_smul, inv_mul_cancel₀ ha_ne] using this
        exact hx (hxx' ▸ hx')
      simp [Set.indicator_of_notMem, hx, hyV]
  refine (MeasureTheory.integrable_indicator_iff hs).1 ?_
  exact h_indicator_eq ▸ h_scaled

theorem integrableOn_comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U MeasureTheory.volume)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      U MeasureTheory.volume := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • U)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz hε0 (le_of_lt hε1)
  have hV_sub : V ⊆ U :=
    translateSet_smul_subset_of_convexApproxSample_mapsTo (x0 := x0) (z := z) (r := r) (ε := ε)
      hmap
  have huV : MeasureTheory.IntegrableOn u V MeasureTheory.volume :=
    hu.mono_set hV_sub
  simpa [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_of_pos (d := d) (u := u) (a := a) ha_pos b hU.1.measurableSet huV)

theorem integrableOn_comp_convexApproxSample_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hK_sub : K ⊆ U) (hK_compact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      K MeasureTheory.volume := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • K)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz hε0 (le_of_lt hε1)
  have hV_subU : V ⊆ U := by
    intro y hy
    rcases hy with ⟨w, hw, hyw⟩
    rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
    have hxU : x ∈ U := hK_sub hx
    have hyU : convexApproxSample x0 z r ε x ∈ U := hmap hxU
    rw [hyw]
    simpa [convexApproxSample] using hyU
  have hV_compact : IsCompact V := by
    have h_image : (fun x : Vec d => a • x + b) '' K = V := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨a • x, Set.smul_mem_smul_set hx, by simp⟩
      · intro hy
        rcases hy with ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp [hyw]
    rw [← h_image]
    exact hK_compact.image
      (((continuous_const : Continuous fun _ : Vec d => a).smul continuous_id).add
        (continuous_const : Continuous fun _ : Vec d => b))
  have huV : MeasureTheory.IntegrableOn u V MeasureTheory.volume :=
    hu.integrableOn_compact_subset hV_subU hV_compact
  simpa [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_of_pos (d := d) (u := u) (a := a) ha_pos b
      hK_compact.measurableSet huV)

theorem integrableOn_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u ψ : Vec d → ℝ} (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hψ : Continuous ψ) (hK_sub : K ⊆ U) (hK_compact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x)
      K MeasureTheory.volume := by
  have hcomp :
      MeasureTheory.IntegrableOn
        (fun x => u (convexApproxSample x0 z r ε x))
        K MeasureTheory.volume :=
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn hU hu hK_sub hK_compact
      hball hr hz hε0 hε1
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz hε0 (le_of_lt hε1)
  have hmul :
      MeasureTheory.IntegrableOn
        (fun x => u (convexApproxSample x0 z r ε x) * ψ x)
        K MeasureTheory.volume :=
    hcomp.mul_continuousOn hψ.continuousOn hK_compact
  rw [MeasureTheory.IntegrableOn] at hmul ⊢
  refine hmul.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hK_compact.measurableSet] with x hx
  rw [Set.indicator_of_mem (hmap (hK_sub hx))]

theorem integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ} (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hψ : Continuous ψ) (hK_sub : K ⊆ U) (hK_compact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * ψ x)
      K MeasureTheory.volume := by
  rw [MeasureTheory.IntegrableOn]
  simpa [mul_assoc] using
    (integrableOn_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
      hU hu hψ hK_sub hK_compact hball hr hz hε0 hε1).integrable.const_mul (ρ z)

end Homogenization
