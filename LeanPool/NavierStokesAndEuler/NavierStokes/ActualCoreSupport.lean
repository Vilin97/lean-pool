/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization

@[expose] public section

/-!
# The actual initial support retains its radial and native dyadic cores

The broad source carrier retains the slow spatial mask and the fast source
rectangle.  The actual fields have two further cutoffs: the moving radial
attachment and the original label's dyadic cutoff.  We keep their closed
cores in a fixed carrier and take the ambient closure of its positive-time
part.  No continuity of the totalized similarity coordinate at time zero is
used.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace NavierStokes.ActualCoreSupport

open CorrectionInitialization

abbrev Point := LocalSignedRequest.Point
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

noncomputable def radialRatio (x : Point) : ℝ :=
  x.1 / VariableGaugeMean.qLength (2 * ActualPrimary.h) x.2.1

/-- This is the original label's native similarity scale, not the scale in
the current chart. -/
noncomputable def nativeQ {B N0 : ℕ} (l : Index B N0) (n : ℕ) (x : Point) : ℝ :=
  SimilarityHomogeneity.chartQ ActualPrimary.h
    (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x))

noncomputable def positiveCore {B N0 : ℕ} (l : Index B N0) (n : ℕ) : Set Point :=
  {x | 0 < x.2.1.1 ∧ x ∈ ActualInitialization.labelCarrier l n ∧
    radialRatio x ∈ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
    nativeQ l n x ∈ Icc (1 / 2 : ℝ) 2}

noncomputable def refinedCarrier {B N0 : ℕ} (l : Index B N0) (n : ℕ) : Set Point :=
  closure (positiveCore l n)

theorem refinedCarrier_closed {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    IsClosed (refinedCarrier l n) := isClosed_closure

theorem refinedCarrier_subset_broad {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    refinedCarrier l n ⊆ ActualInitialization.labelCarrier l n :=
  closure_minimal (fun _ hx => hx.2.1) (ActualInitialization.labelCarrier_closed l n)

theorem refinedCarrier_nonnegative_time {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    refinedCarrier l n ⊆ {x : Point | 0 ≤ x.2.1.1} :=
  closure_minimal (fun _ hx => hx.1.le)
    (isClosed_le continuous_const continuous_snd.fst.fst)

theorem radialRatio_continuousAt {x : Point} (hT : 0 < x.2.1.1) :
    ContinuousAt radialRatio x := by
  have hh : 0 < 2 * ActualPrimary.h := by linarith [ActualPrimary.outgoing.data.h_pos]
  have hh1 : 2 * ActualPrimary.h < 1 := by linarith [ActualPrimary.outgoing.data.h_lt_half]
  have hc : ContDiffAt ℝ ∞ (VariableGaugeMean.qLength (2 * ActualPrimary.h)) x.2.1 :=
    (VariableGaugeMean.qLength_contDiffOn hh hh1).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hT)
  have hd : ContinuousAt (fun y : Point =>
      VariableGaugeMean.qLength (2 * ActualPrimary.h) y.2.1) x := by
    have ht : Tendsto (fun y : Point => y.2.1) (𝓝 x) (𝓝 x.2.1) :=
      continuousAt_snd.fst
    exact hc.continuousAt.tendsto.comp ht
  exact (show ContinuousAt (fun y : Point => y.1) x from continuousAt_fst).div hd
    (VariableGaugeMean.qLength_pos hh hh1 hT).ne'

theorem nativeQ_continuousAt {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hT : 0 < x.2.1.1) : ContinuousAt (nativeQ l n) x := by
  have hh : 0 < 2 * ActualPrimary.h := by linarith [ActualPrimary.outgoing.data.h_pos]
  have hh1 : 2 * ActualPrimary.h < 1 := by linarith [ActualPrimary.outgoing.data.h_lt_half]
  have ht : 0 < (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x)).2.2 :=
    div_pos (mul_pos (ChartScales.Q_pos n) hT) (ChartScales.Q_pos _)
  have hs := ((ActualPrimary.nativeSlow_smooth l.1).comp
    (ActualPrimary.toAbsolute_smooth n)).continuous.continuousAt (x := x)
  exact (SimilarityCoordinates.coordinateQ_smooth hh hh1 ht).continuousAt.comp
    (hs.snd.snd.prodMk hs.snd.fst)

/-- Taking ambient closure adds no extra points at positive time. -/
theorem mem_refinedCarrier_iff {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hT : 0 < x.2.1.1) :
    x ∈ refinedCarrier l n ↔ x ∈ ActualInitialization.labelCarrier l n ∧
      radialRatio x ∈ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
      nativeQ l n x ∈ Icc (1 / 2 : ℝ) 2 := by
  constructor
  · intro hx
    refine ⟨refinedCarrier_subset_broad l n hx, ?_, ?_⟩
    · have hc := (radialRatio_continuousAt hT).continuousWithinAt.mem_closure hx
        (show MapsTo radialRatio (positiveCore l n)
          (Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
            (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) from fun _ hp => hp.2.2.1)
      simpa only [isClosed_Icc.closure_eq] using hc
    · have hc := (nativeQ_continuousAt l n hT).continuousWithinAt.mem_closure hx
        (show MapsTo (nativeQ l n) (positiveCore l n) (Icc (1 / 2 : ℝ) 2)
          from fun _ hp => hp.2.2.2)
      simpa only [isClosed_Icc.closure_eq] using hc
  · intro hx
    exact subset_closure ⟨hT, hx⟩

theorem mem_refinedCarrier_of_mem {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hT : 0 < x.2.1.1) (hb : x ∈ ActualInitialization.labelCarrier l n)
    (hr : radialRatio x ∈ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))
    (hq : nativeQ l n x ∈ Icc (1 / 2 : ℝ) 2) : x ∈ refinedCarrier l n :=
  (mem_refinedCarrier_iff l n hT).2 ⟨hb, hr, hq⟩

theorem radialRatio_fast (x : Point) (Y : TorusInverse.Plane) :
    radialRatio (x.1, (x.2.1, Y)) = radialRatio x := rfl

theorem nativeQ_fast {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    (x : Point) (Y : TorusInverse.Plane) :
    nativeQ l n (x.1, (x.2.1, Y)) = nativeQ l n x := rfl

section ActualCutoffs

variable {B N0 : ℕ}

theorem rawVelocity_nativeQ (j : Fin 2) (L : ActualPrimary.Label B N0)
    {x : ActualSignedGeometry.Native} (hx : ActualPrimary.rawVelocity j L x ≠ 0) :
    SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hm : ActualPrimary.spatialMask L x.1 ≠ 0 := by
    intro hz
    exact hx (by simp [ActualPrimary.rawVelocity, PartitionedCovariance.amplitude, hz])
  exact ActualPrimary.spatialMask_q_range L x.1 hm

/-- Both extra constraints come from actual factors of the attached field. -/
theorem attached_velocity_core (j : Fin 2) (L : ActualPrimary.Label B N0)
    {x : ActualSignedGeometry.Native} (hx : ActualPrimary.attachedRawVelocity j L x ≠ 0) :
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
    SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hr : ActualPrimary.rawVelocity j L x ≠ 0 := by
    intro hz
    exact hx (by simp [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, ActualPrimary.outerRawVelocity, hz])
  refine ⟨?_, rawVelocity_nativeQ j L hr⟩
  by_contra hn
  exact hx (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ hn)

theorem attached_pressure_core (j : Fin 2) (L : ActualPrimary.Label B N0)
    {x : ActualSignedGeometry.Native} (hx : ActualPrimary.attachedRawPressure j L x ≠ 0) :
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
    SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hr : ActualPrimary.rawVelocity j L x ≠ 0 := by
    intro hz
    have hp := ActualPrimary.rawPressure_zero_of_velocity_zero j L x hz
    exact hx (by simp [ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, ActualPrimary.outerRawPressure, hp])
  refine ⟨?_, rawVelocity_nativeQ j L hr⟩
  by_contra hn
  exact hx (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ hn)

theorem copy_radial_core (j : Fin 2) (L : ActualPrimary.Label B N0)
    (n : ℕ) (k : TorusInverse.Frequency) {x : ActualPrimary.FullPoint}
    (hT : 0 < x.1.2.1.1)
    (hx : WaveEdgeExtension.nativeRadius ActualPrimary.h
      (ActualPrimaryDynamics.copyPoint j L n k x) ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    radialRatio x.1 ∈ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  have hr : 0 < x.1.1 := by
    by_contra hn
    have hnR : (ActualPrimaryDynamics.copyPoint j L n k x).1.1 ≤ 0 := by
      change Real.sqrt (ChartScales.Q n) * x.1.1 /
        Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_not_gt hn))
        (Real.sqrt_nonneg _)
    have hp := (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans hx.1
    exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hnR (Real.sqrt_nonneg _))) hp
  have he : WaveEdgeExtension.nativeRadius ActualPrimary.h
      (ActualPrimaryDynamics.copyPoint j L n k x) = radialRatio x.1 :=
    ActualPrimaryCoherence.amplitudeRadius_chart L n hT hr
  rwa [he] at hx

theorem cut_amplitude_mem_refined (l : Index B N0) (n : ℕ)
    {x : ActualPrimary.FullPoint} (hT : 0 < x.1.2.1.1)
    (hx : x ∈ support (((ActualInitialization.primaryPiece l).coefficients.withCutoff
      (ActualInitialization.primaryPiece l).cutoff).amplitude n)) :
    x.1 ∈ refinedCarrier l n := by
  have hb := ActualInitialization.cut_amplitude_source_support l n hx
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    have ha := (ActualPrimaryDynamics.amplitude_germ l.2 l.1 n k hk).eq_of_nhds
    have hv : ActualPrimary.attachedRawVelocity l.2 l.1
        (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x •
        (ActualPrimary.chartCoefficients l.2 l.1).amplitude n x = 0
      rw [ha]
      simp only [ActualPrimaryDynamics.copyAmplitude, hz, map_zero, smul_zero]
    obtain ⟨hr, hq⟩ := attached_velocity_core l.2 l.1 hv
    have hrad := copy_radial_core l.2 l.1 n k hT hr
    exact mem_refinedCarrier_of_mem l n hT hb ⟨hrad.1.le, hrad.2.le⟩ ⟨hq.1.le, hq.2.le⟩
  · have hz := (ActualPrimaryDynamics.coefficient_zero_germs l.2 l.1 n (not_exists.mp
    hc)).1.eq_of_nhds
    exact (hx (by
      change ActualPrimary.chartCutoff l.2 l.1 n x •
        (ActualPrimary.chartCoefficients l.2 l.1).amplitude n x = 0
      rw [hz, smul_zero])).elim

theorem cut_pressure_mem_refined (l : Index B N0) (n : ℕ)
    {x : ActualPrimary.FullPoint} (hT : 0 < x.1.2.1.1)
    (hx : x ∈ support ((ActualInitialization.primaryPiece l).exactCoefficients.pressure n)) :
    x.1 ∈ refinedCarrier l n := by
  have hb := ActualInitialization.cut_pressure_source_support l n hx
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    have hp := (ActualPrimaryDynamics.pressure_germ l.2 l.1 n k hk).eq_of_nhds
    have hv : ActualPrimary.attachedRawPressure l.2 l.1
        (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x •
        (ActualPrimary.chartCoefficients l.2 l.1).pressure n x = 0
      rw [hp]
      simp only [ActualPrimaryDynamics.copyPressure, hz, smul_zero]
    obtain ⟨hr, hq⟩ := attached_pressure_core l.2 l.1 hv
    have hrad := copy_radial_core l.2 l.1 n k hT hr
    exact mem_refinedCarrier_of_mem l n hT hb ⟨hrad.1.le, hrad.2.le⟩ ⟨hq.1.le, hq.2.le⟩
  · have hz := (ActualPrimaryDynamics.coefficient_zero_germs l.2 l.1 n (not_exists.mp
    hc)).2.eq_of_nhds
    exact (hx (by
      change ActualPrimary.chartCutoff l.2 l.1 n x •
        (ActualPrimary.chartCoefficients l.2 l.1).pressure n x = 0
      rw [hz, smul_zero])).elim

theorem cut_amplitude_zero_germ (l : Index B N0) (n : ℕ)
    {x : ActualPrimary.FullPoint} (hT : 0 < x.1.2.1.1)
    (hx : x.1 ∉ refinedCarrier l n) :
    ((ActualInitialization.primaryPiece l).coefficients.withCutoff
      (ActualInitialization.primaryPiece l).cutoff).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have ht : ∀ᶠ y : ActualPrimary.FullPoint in 𝓝 x, 0 < y.1.2.1.1 :=
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT
  have hs : ∀ᶠ y : ActualPrimary.FullPoint in 𝓝 x, y.1 ∉ refinedCarrier l n :=
    ((refinedCarrier_closed l n).preimage continuous_fst).isOpen_compl.mem_nhds hx
  filter_upwards [ht, hs] with y hyT hys
  by_contra hn
  exact hys (cut_amplitude_mem_refined l n hyT hn)

theorem primary_velocity_zero (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hx : x ∉ refinedCarrier l n) (θ : ℝ) :
    (ActualInitialization.primaryBlock l).oscillation n (x, θ) = 0 := by
  rw [(ActualInitialization.primaryBlock_represents l).1]
  have ht := (ActualInitialization.primaryPiece l).velocity_tsupport_subset_tangent n
  have ha := cut_amplitude_zero_germ l n (x := (x, θ)) hT hx
  exact (notMem_tsupport_iff_eventuallyEq.mp
    (fun hz => (notMem_tsupport_iff_eventuallyEq.mpr ha) (ht hz))).eq_of_nhds

theorem primary_pressure_zero (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hx : x ∉ refinedCarrier l n) (θ : ℝ) :
    (ActualInitialization.primaryBlock l).oscillatoryPressure n (x, θ) = 0 := by
  rw [(ActualInitialization.primaryBlock_represents l).2]
  have hp : (ActualInitialization.primaryPiece l).exactCoefficients.pressure n (x, θ) = 0 := by
    by_contra hn
    exact hx (cut_pressure_mem_refined l n hT hn)
  simp only [PrimaryPiece.pressure, HarmonicCalculus.mode, hp, zero_mul, Complex.zero_re]

theorem chartGaussian_mem_refined (l : Index B N0) (n : ℕ)
    {x : ActualPrimary.FullPoint} (hT : 0 < x.1.2.1.1)
    (hx : ActualInitialExcluded.chartGaussian (l.2, l.1) n x ≠ 0) :
    x.1 ∈ refinedCarrier l n :=
  cut_amplitude_mem_refined l n hT
    (ActualInitialExcluded.chartGaussian_cut_support (l.2, l.1) n hx)

theorem gaussian_velocity_zero (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hx : x ∉ refinedCarrier l n) (θ : ℝ) :
    (ActualInitialization.gaussianBlock l).oscillation n (x, θ) = 0 := by
  rw [ActualInitialization.gaussianBlock_represents]
  have hg : ActualInitialExcluded.chartGaussian (l.2, l.1) n (x, θ) = 0 := by
    by_contra hn
    exact hx (chartGaussian_mem_refined l n hT hn)
  funext i
  change (ActualInitialExcluded.chartGaussian (l.2, l.1) n (x, θ) i * _).re = _
  simp only [hg, Pi.zero_apply, zero_mul, Complex.zero_re]

/-- This is proved for the literal seed velocity, pressure, Gaussian and
alias coefficients. The stronger support is not an initialization premise. -/
theorem initial_inputSupport (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain (refinedCarrier l)
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0 := by
  apply HarmonicSourceSupport.InputSupportOn.of_fields _ _ _
    (ActualInitialization.angularMode_ne_zero l)
  · intro n x hx hn θ i
    exact congrFun (primary_velocity_zero l n
      (ActualInitialization.geometry.region.time_pos _ hx) hn θ) i
  · intro n x hx hn θ
    exact primary_pressure_zero l n (ActualInitialization.geometry.region.time_pos _ hx) hn θ
  · intro n x hx hn θ i
    exact congrFun (gaussian_velocity_zero l n
      (ActualInitialization.geometry.region.time_pos _ hx) hn θ) i
  · intro n x _ _ θ i
    simp [HarmonicResidual.vectorField, HarmonicResidual.field_zero]

end ActualCutoffs

/-- Reuse the actual initialized state and every established invariant
field. Only its support certificate is strengthened. -/
theorem initial_invariant (B N0 : ℕ) :
    CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry
      (ActualPrimary.commonContext B)
      (ActualInitialization.tangentBlock (B := B) (N0 := N0))
      ActualInitialization.envelope refinedCarrier (1 / 5)
      (ActualInitialization.initialCycleState B N0) := by
  exact { ActualInitialization.initial_invariant B N0 with inputSupport := initial_inputSupport }

end NavierStokes.ActualCoreSupport
