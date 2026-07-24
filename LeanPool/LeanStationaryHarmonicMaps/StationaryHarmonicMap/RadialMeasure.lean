/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Basic

/-!
# Radial Measure
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The one-dimensional measure on the radius interval `(0, R0)`. -/
def radiusIntervalMeasure (R0 : ℝ) : Measure ℝ :=
  volume.restrict (Ioo (0 : ℝ) R0)

instance sigmaFinite_radiusIntervalMeasure (R0 : ℝ) :
    SigmaFinite (radiusIntervalMeasure R0) := by
  dsimp [radiusIntervalMeasure]
  infer_instance

/-- The pushforward of Euclidean volume by the radius map is absolutely
continuous with respect to one-dimensional Lebesgue measure.  This is the
measure-theoretic core supplied by `HaarToSphere`, kept separate from the later
Sobolev/radial-density bookkeeping. -/
theorem normPushforwardVolume_absolutelyContinuous (n : ℕ) [NeZero n] :
    Measure.AbsolutelyContinuous
      ((volume : Measure (Domain n)).map (fun x : Domain n => norm x))
      (volume : Measure ℝ) := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [Measure.map_apply continuous_norm.measurable hs]
  let A : Set (Domain n) := {x | s (norm x)}
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    exact hs.preimage continuous_norm.measurable
  have hs_ae : ∀ᵐ y ∂(volume : Measure ℝ), ¬ s y :=
    (measure_eq_zero_iff_ae_notMem).1 hzero
  have hs_ae_restrict :
      ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), ¬ s y :=
    ae_mono Measure.restrict_le_self hs_ae
  have hrad_ae :
      (fun y : ℝ =>
          y ^ (Module.finrank ℝ (Domain n) - 1) •
            s.indicator (fun _ : ℝ => (1 : ℝ)) y)
        =ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hs_ae_restrict] with y hy
    simp [Set.indicator_of_notMem hy]
  have hrad_int :
      IntegrableOn
        (fun y : ℝ =>
          y ^ (Module.finrank ℝ (Domain n) - 1) •
            s.indicator (fun _ : ℝ => (1 : ℝ)) y)
        (Ioi (0 : ℝ)) (volume : Measure ℝ) := by
    rw [IntegrableOn]
    exact
      (integrable_zero ℝ ℝ ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))).congr
        hrad_ae.symm
  have hA_int :
      Integrable
        (fun x : Domain n => s.indicator (fun _ : ℝ => (1 : ℝ)) (norm x))
        volume := by
    rw [MeasureTheory.integrable_fun_norm_addHaar
      (μ := (volume : Measure (Domain n)))]
    simpa using hrad_int
  have hA_int' :
      Integrable (A.indicator (fun _ : Domain n => (1 : ℝ))) volume := by
    refine hA_int.congr ?_
    filter_upwards [] with x
    by_cases hx : norm x ∈ s
    · have hxA : x ∈ A := by
        exact hx
      rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hx]
    · have hxA : x ∉ A := by
        exact hx
      rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hx]
  have hA_intOn : IntegrableOn (fun _ : Domain n => (1 : ℝ)) A volume :=
    (integrable_indicator_iff hA_meas).1 hA_int'
  have hA_finite : IsFiniteMeasure ((volume : Measure (Domain n)).restrict A) := by
    exact
      ((integrable_const_iff_isFiniteMeasure
        (μ := (volume : Measure (Domain n)).restrict A)
        (show (1 : ℝ) ≠ 0 by norm_num)).1 hA_intOn)
  have hA_ne_top : (volume : Measure (Domain n)) A ≠ ∞ := by
    have h := measure_ne_top ((volume : Measure (Domain n)).restrict A) Set.univ
    simpa [Measure.restrict_apply MeasurableSet.univ] using h
  have hrad_int_zero :
      (∫ y in Ioi (0 : ℝ),
        y ^ (Module.finrank ℝ (Domain n) - 1) •
          s.indicator (fun _ : ℝ => (1 : ℝ)) y ∂(volume : Measure ℝ)) = 0 := by
    simpa using integral_congr_ae hrad_ae
  have hpolar := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (Domain n)))
    (f := s.indicator (fun _ : ℝ => (1 : ℝ)))
  rw [hrad_int_zero, smul_zero] at hpolar
  have hleft_zero :
      (∫ x : Domain n, s.indicator (fun _ : ℝ => (1 : ℝ)) (norm x) ∂volume) = 0 := by
    simpa using hpolar
  have hA_real_zero : (volume : Measure (Domain n)).real A = 0 := by
    rw [← integral_indicator_one hA_meas]
    rw [← hleft_zero]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : norm x ∈ s
    · have hxA : x ∈ A := by
        exact hx
      rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hx]
      simp
    · have hxA : x ∉ A := by
        exact hx
      rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hx]
  exact
    (measureReal_eq_zero_iff
      (μ := (volume : Measure (Domain n))) (s := A) hA_ne_top).1 hA_real_zero

/-- Radius pushforward on a fixed ball is absolutely continuous with respect to
the restricted radius-interval measure.  The only point lost when restricting
to `(0, R0)` is the origin, a null set in positive dimension. -/
theorem radiusPushforward_absolutelyContinuous_euclidean {n : ℕ} [NeZero n]
    {R0 : ℝ} :
    Measure.AbsolutelyContinuous
      (((volume : Measure (Domain n)).restrict (Metric.ball (0 : Domain n) R0)).map
        (fun x : Domain n => norm x))
      (radiusIntervalMeasure R0) := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [Measure.map_apply continuous_norm.measurable hs]
  rw [Measure.restrict_apply (hs.preimage continuous_norm.measurable)]
  let t : Set ℝ := s ∩ Ioo (0 : ℝ) R0
  have hzero_t : (volume : Measure ℝ) t = 0 := by
    simpa [t, radiusIntervalMeasure, Measure.restrict_apply hs] using hzero
  have hnorm_t :
      (volume : Measure (Domain n)) {x : Domain n | t (norm x)} = 0 := by
    have hmap_t := normPushforwardVolume_absolutelyContinuous n hzero_t
    have ht_meas : MeasurableSet t := by
      dsimp [t]
      exact hs.inter measurableSet_Ioo
    rw [Measure.map_apply continuous_norm.measurable ht_meas] at hmap_t
    exact hmap_t
  have hsingleton : (volume : Measure (Domain n)) ({0} : Set (Domain n)) = 0 := by
    simp
  have hunion_zero :
      (volume : Measure (Domain n))
        (Set.union {x : Domain n | t (norm x)} ({0} : Set (Domain n))) = 0 :=
    measure_union_null hnorm_t hsingleton
  refine measure_mono_null ?_ hunion_zero
  intro x hx
  rcases hx with ⟨hxnorm, hxball⟩
  have hxlt : norm x < R0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hxball
  by_cases hxpos : 0 < norm x
  · left
    exact ⟨hxnorm, hxpos, hxlt⟩
  · right
    have hxle : norm x ≤ 0 := le_of_not_gt hxpos
    have hxnorm0 : norm x = 0 := le_antisymm hxle (norm_nonneg x)
    exact norm_eq_zero.1 hxnorm0

/-- The radial signed pushforward of an `L¹` scalar density on a ball is
absolutely continuous with respect to the one-dimensional radius interval
measure. -/
theorem radialVectorMeasure_absolutelyContinuous_euclidean {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x)) ≪ᵥ
      (radiusIntervalMeasure R0).toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk ?_
  intro s hs hs0
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hs0
  have hpre_zero :
      (volume.restrict (Metric.ball (0 : Domain n) R0))
        ((fun x : Domain n => norm x) ⁻¹' s) = 0 := by
    have hmap_zero :=
      radiusPushforward_absolutelyContinuous_euclidean (n := n) (R0 := R0) hs0
    rw [Measure.map_apply continuous_norm.measurable hs] at hmap_zero
    exact hmap_zero
  rw [VectorMeasure.map_apply _ continuous_norm.measurable hs]
  rw [withDensityᵥ_apply hf (hs.preimage continuous_norm.measurable)]
  exact setIntegral_measure_zero f hpre_zero

/-- The Radon-Nikodym density of the radial signed pushforward of `f dx` on
`B_R0`, with respect to the radius interval measure. -/
noncomputable def radialRNDensity {n : ℕ} (f : Domain n → ℝ) (R0 : ℝ) : ℝ → ℝ :=
  SignedMeasure.rnDeriv
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
      (fun x : Domain n => norm x))
    (radiusIntervalMeasure R0)

/-- The radial signed pushforward is exactly the vector measure obtained by
integrating its Radon-Nikodym density on the radius interval. -/
theorem radialVectorMeasure_withDensity_rnDeriv_euclidean {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (radiusIntervalMeasure R0).withDensityᵥ (radialRNDensity (n := n) f R0) =
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x)) := by
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
      (fun x : Domain n => norm x))
    (radiusIntervalMeasure R0)
    (radialVectorMeasure_absolutelyContinuous_euclidean (n := n) (f := f) (R0 := R0) hf)

/-- The radial Radon-Nikodym density represents the signed radial pushforward on
every measurable set of radii. -/
theorem radialRNDensity_setIntegral_eq_radialVectorMeasure {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {s : Set ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hs : MeasurableSet s) :
    (∫ rho in s, radialRNDensity (n := n) f R0 rho ∂(radiusIntervalMeasure R0))
      =
    ∫ x in {x : Domain n | norm x ∈ s}, f x
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
  calc
    (∫ rho in s, radialRNDensity (n := n) f R0 rho ∂(radiusIntervalMeasure R0))
        =
      ((radiusIntervalMeasure R0).withDensityᵥ
        (radialRNDensity (n := n) f R0)) s := by
        simpa [radialRNDensity] using
          (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv
          (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
            (fun x : Domain n => norm x))
          (radiusIntervalMeasure R0)) hs).symm
    _ =
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x)) s := by
        rw [radialVectorMeasure_withDensity_rnDeriv_euclidean
          (n := n) (f := f) (R0 := R0) hf]
    _ =
      ∫ x in {x : Domain n | norm x ∈ s}, f x
        ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
        simpa using radialVectorMeasure_apply
          (n := n) (f := f) (R0 := R0) (s := s) hf hs

/-- The radial Radon-Nikodym density represents constant multiples of
measurable radial indicators.  This is the atomic step for passing from the
set-level representation to finite simple radial weights. -/
theorem radialRNDensity_indicatorConst_integral_eq {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 k : ℝ} {s : Set ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hs : MeasurableSet s) :
    (∫ x, s.indicator (fun _ : ℝ => k) (norm x) * f x
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
      =
    ∫ rho, s.indicator (fun _ : ℝ => k) rho *
      radialRNDensity (n := n) f R0 rho ∂(radiusIntervalMeasure R0) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  let ν : Measure ℝ := radiusIntervalMeasure R0
  let t : Set (Domain n) := {x | norm x ∈ s}
  have ht : MeasurableSet t := hs.preimage continuous_norm.measurable
  have hset :
      (∫ rho in s, radialRNDensity (n := n) f R0 rho ∂ν)
        =
      ∫ x in t, f x ∂μ := by
    simpa [ν, μ, t] using
      radialRNDensity_setIntegral_eq_radialVectorMeasure
        (n := n) (f := f) (R0 := R0) (s := s) hf hs
  have hleft :
      (∫ x, s.indicator (fun _ : ℝ => k) (norm x) * f x ∂μ)
        =
      k * ∫ x in t, f x ∂μ := by
    calc
      (∫ x, s.indicator (fun _ : ℝ => k) (norm x) * f x ∂μ)
          =
        ∫ x, t.indicator (fun x : Domain n => k * f x) x ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ t
          · have hxs : norm x ∈ s := by simpa [t] using hx
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxs]
          · have hxs : norm x ∉ s := by simpa [t] using hx
            rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxs]
            simp
      _ = ∫ x in t, k * f x ∂μ := by
        rw [integral_indicator ht]
      _ = k * ∫ x in t, f x ∂μ := by
        rw [integral_const_mul]
  have hright :
      (∫ rho, s.indicator (fun _ : ℝ => k) rho *
        radialRNDensity (n := n) f R0 rho ∂ν)
        =
      k * ∫ rho in s, radialRNDensity (n := n) f R0 rho ∂ν := by
    calc
      (∫ rho, s.indicator (fun _ : ℝ => k) rho *
        radialRNDensity (n := n) f R0 rho ∂ν)
          =
        ∫ rho, s.indicator
          (fun rho : ℝ => k * radialRNDensity (n := n) f R0 rho) rho ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with rho
          by_cases hrho : rho ∈ s
          · rw [Set.indicator_of_mem hrho, Set.indicator_of_mem hrho]
          · rw [Set.indicator_of_notMem hrho, Set.indicator_of_notMem hrho]
            simp
      _ = ∫ rho in s, k * radialRNDensity (n := n) f R0 rho ∂ν := by
        rw [integral_indicator hs]
      _ = k * ∫ rho in s, radialRNDensity (n := n) f R0 rho ∂ν := by
        rw [integral_const_mul]
  calc
    (∫ x, s.indicator (fun _ : ℝ => k) (norm x) * f x
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
        =
      k * ∫ x in t, f x ∂μ := by
        simpa [μ] using hleft
    _ =
      k * ∫ rho in s, radialRNDensity (n := n) f R0 rho ∂ν := by
        rw [hset]
    _ =
      ∫ rho, s.indicator (fun _ : ℝ => k) rho *
        radialRNDensity (n := n) f R0 rho ∂(radiusIntervalMeasure R0) := by
        simpa [ν] using hright.symm

/-- The radial Radon-Nikodym density represents every finite simple radial
weight.  This is the finite-step version of the desired weighted
representation. -/
theorem radialRNDensity_simpleFunc_integral_eq {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} (g : SimpleFunc ℝ ℝ)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (∫ x, g (norm x) * f x
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
      =
    ∫ rho, g rho * radialRNDensity (n := n) f R0 rho
      ∂(radiusIntervalMeasure R0) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  let ν : Measure ℝ := radiusIntervalMeasure R0
  let D : ℝ → ℝ := radialRNDensity (n := n) f R0
  have hfμ : Integrable f μ := hf
  have hDν : Integrable D ν :=
    SignedMeasure.integrable_rnDeriv
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x))
      (radiusIntervalMeasure R0)
  have hleft_int : ∀ g : SimpleFunc ℝ ℝ,
      Integrable (fun x : Domain n => g (norm x) * f x) μ := by
    intro g
    let gr : SimpleFunc (Domain n) ℝ :=
      g.comp (fun x : Domain n => norm x) continuous_norm.measurable
    exact hfμ.simpleFunc_mul gr
  have hright_int : ∀ g : SimpleFunc ℝ ℝ,
      Integrable (fun rho : ℝ => g rho * D rho) ν := by
    intro g
    exact hDν.simpleFunc_mul g
  have hg_sum : ∀ rho : ℝ,
      g rho =
        ∑ y ∈ g.range, (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) rho := by
    intro rho
    classical
    rw [Finset.sum_eq_single (g rho)]
    · simp
    · intro y _hy hy
      have hrho : rho ∉ g ⁻¹' ({y} : Set ℝ) := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy.symm
      simp [Set.indicator_of_notMem hrho]
    · intro hnot
      exact (hnot (g.mem_range_self rho)).elim
  have hleft_term_int : ∀ y ∈ g.range,
      Integrable
        (fun x : Domain n =>
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) (norm x) * f x) μ := by
    intro y _hy
    let gy : SimpleFunc ℝ ℝ :=
      SimpleFunc.piecewise (g ⁻¹' ({y} : Set ℝ)) (g.measurableSet_preimage ({y} : Set ℝ))
        (SimpleFunc.const ℝ y) (SimpleFunc.const ℝ 0)
    exact hleft_int gy
  have hright_term_int : ∀ y ∈ g.range,
      Integrable
        (fun rho : ℝ =>
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) rho * D rho) ν := by
    intro y _hy
    let gy : SimpleFunc ℝ ℝ :=
      SimpleFunc.piecewise (g ⁻¹' ({y} : Set ℝ)) (g.measurableSet_preimage ({y} : Set ℝ))
        (SimpleFunc.const ℝ y) (SimpleFunc.const ℝ 0)
    exact hright_int gy
  calc
    (∫ x, g (norm x) * f x ∂μ)
        =
      ∫ x,
        (∑ y ∈ g.range,
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) (norm x)) * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← hg_sum (norm x)]
    _ =
      ∫ x,
        ∑ y ∈ g.range,
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) (norm x) * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Finset.sum_mul]
    _ =
      ∑ y ∈ g.range,
        ∫ x, (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) (norm x) * f x ∂μ := by
        rw [integral_finsetSum g.range hleft_term_int]
    _ =
      ∑ y ∈ g.range,
        ∫ rho, (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) rho * D rho ∂ν := by
        refine Finset.sum_congr rfl ?_
        intro y _hy
        simpa [D, ν, μ] using
          radialRNDensity_indicatorConst_integral_eq
            (n := n) (f := f) (R0 := R0) (k := y)
            (s := g ⁻¹' ({y} : Set ℝ)) hf (g.measurableSet_preimage ({y} : Set ℝ))
    _ =
      ∫ rho,
        ∑ y ∈ g.range,
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) rho * D rho ∂ν := by
        rw [integral_finsetSum g.range hright_term_int]
    _ =
      ∫ rho,
        (∑ y ∈ g.range,
          (g ⁻¹' ({y} : Set ℝ)).indicator (fun _ : ℝ => y) rho) * D rho ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with rho
        rw [Finset.sum_mul]
    _ =
      ∫ rho, g rho * D rho ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with rho
        rw [← hg_sum rho]

/-- Set-integral version of `radialRNDensity_simpleFunc_integral_eq`, with the
radius interval written explicitly. -/
theorem radialRNDensity_simpleFunc_setIntegral_eq {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} (g : SimpleFunc ℝ ℝ)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (∫ x in Metric.ball (0 : Domain n) R0, g (norm x) * f x)
      =
    ∫ rho in Ioo (0 : ℝ) R0,
      g rho * radialRNDensity (n := n) f R0 rho := by
  simpa [radiusIntervalMeasure] using
    radialRNDensity_simpleFunc_integral_eq
      (n := n) (f := f) (R0 := R0) g hf

/-- The radial Radon-Nikodym density is locally integrable on the open radius
interval. -/
theorem radialRNDensity_locallyIntegrableOn {n : ℕ} {f : Domain n → ℝ} {R0 : ℝ} :
    LocallyIntegrableOn (radialRNDensity (n := n) f R0) (Ioo (0 : ℝ) R0) volume := by
  have hD :
      Integrable (radialRNDensity (n := n) f R0) (radiusIntervalMeasure R0) :=
    SignedMeasure.integrable_rnDeriv
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x))
      (radiusIntervalMeasure R0)
  exact (show
      IntegrableOn (radialRNDensity (n := n) f R0) (Ioo (0 : ℝ) R0) volume from
        hD).locallyIntegrableOn

/-- In positive dimension, the origin is negligible even after restricting
Lebesgue measure to a ball. -/
theorem ae_ne_zero_on_ball {n : ℕ} [NeZero n] {R0 : ℝ} :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0), x ≠ 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure (Domain n)), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  exact ae_mono (Measure.restrict_le_self (s := Metric.ball (0 : Domain n) R0)) hae

/-- In positive dimension and positive radius, points in the ball have radius
in `(0, R0)` almost everywhere. -/
theorem ae_norm_mem_Ioo_zero_radius_on_ball {n : ℕ} [NeZero n] {R0 : ℝ}
    (_hR0_pos : 0 < R0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      ‖x‖ ∈ Ioo (0 : ℝ) R0 := by
  filter_upwards
    [ae_restrict_mem (measurableSet_ball : MeasurableSet (Metric.ball (0 : Domain n) R0)),
      ae_ne_zero_on_ball (n := n) (R0 := R0)] with x hxball hxne
  exact ⟨norm_pos_iff.2 hxne, by
    simpa [Metric.mem_ball, dist_eq_norm] using hxball⟩

/-- Each fixed radius sphere has zero Lebesgue measure in positive dimension. -/
theorem measure_norm_eq_zero {n : ℕ} [NeZero n] {r : ℝ} :
    (volume : Measure (Domain n)) {x : Domain n | ‖x‖ = r} = 0 := by
  have hsphere : {x : Domain n | ‖x‖ = r} = Metric.sphere (0 : Domain n) r := by
    ext x
    simp
  rw [hsphere]
  simpa using (Measure.addHaar_sphere (volume : Measure (Domain n)) (0 : Domain n) r)

/-- The preimage under the radius map of a countable set of radii is null. -/
theorem measure_norm_mem_countable_zero {n : ℕ} [NeZero n] {s : Set ℝ}
    (hs : s.Countable) :
    (volume : Measure (Domain n)) {x : Domain n | ‖x‖ ∈ s} = 0 := by
  change (volume : Measure (Domain n)) ((fun x : Domain n => ‖x‖) ⁻¹' s) = 0
  rw [measure_preimage_eq_zero_iff_of_countable hs]
  intro r _hr
  change (volume : Measure (Domain n)) {x : Domain n | ‖x‖ = r} = 0
  exact measure_norm_eq_zero (n := n) (r := r)

/-- The radius of a ball point avoids any countable set of radii almost everywhere. -/
theorem ae_norm_not_mem_countable_on_ball {n : ℕ} [NeZero n] {R0 : ℝ}
    {s : Set ℝ} (hs : s.Countable) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0), ‖x‖ ∉ s := by
  have hnull : (volume : Measure (Domain n)) {x : Domain n | ‖x‖ ∈ s} = 0 :=
    measure_norm_mem_countable_zero (n := n) hs
  have hae :
      ∀ᵐ x ∂(volume : Measure (Domain n)), ‖x‖ ∉ s := by
    simpa [ae_iff] using hnull
  exact ae_mono (Measure.restrict_le_self (s := Metric.ball (0 : Domain n) R0)) hae

/-- The radius of a ball point avoids any finite set of radii almost everywhere. -/
theorem ae_norm_not_mem_finset_on_ball {n : ℕ} [NeZero n] {R0 : ℝ}
    (s : Finset ℝ) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0), ‖x‖ ∉ (s : Set ℝ) := by
  exact ae_norm_not_mem_countable_on_ball (n := n) (R0 := R0) s.countable_toSet

/-- Pointwise convergence of radius weights on `(0, R0)` pulls back to a.e.
convergence of the corresponding spatial integrands on the ball. -/
theorem tendsto_radiusWeight_mul_pullback_ae_of_tendsto_on_Ioo
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {c : ℝ → ℝ} {cSeq : ℕ → ℝ → ℝ}
    (hR0_pos : 0 < R0)
    (hlim : ∀ rho ∈ Ioo (0 : ℝ) R0,
      Filter.Tendsto (fun N : ℕ => cSeq N rho) Filter.atTop (𝓝 (c rho))) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      Filter.Tendsto (fun N : ℕ => cSeq N ‖x‖ * f x) Filter.atTop
        (𝓝 (c ‖x‖ * f x)) := by
  filter_upwards [ae_norm_mem_Ioo_zero_radius_on_ball (n := n) hR0_pos] with x hx
  exact (hlim ‖x‖ hx).mul_const (f x)

/-- Pointwise convergence of radius weights on `(0, R0)` gives a.e. convergence
after multiplying by any fixed one-dimensional factor on the radius interval. -/
theorem tendsto_radiusWeight_mul_ae_of_tendsto_on_Ioo
    {R0 : ℝ} {c D : ℝ → ℝ} {cSeq : ℕ → ℝ → ℝ}
    (hlim : ∀ rho ∈ Ioo (0 : ℝ) R0,
      Filter.Tendsto (fun N : ℕ => cSeq N rho) Filter.atTop (𝓝 (c rho))) :
    ∀ᵐ rho ∂radiusIntervalMeasure R0,
      Filter.Tendsto (fun N : ℕ => cSeq N rho * D rho) Filter.atTop
        (𝓝 (c rho * D rho)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with rho hrho
  exact (hlim rho hrho).mul_const (D rho)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
