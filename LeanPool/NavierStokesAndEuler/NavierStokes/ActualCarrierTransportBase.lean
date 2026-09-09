/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierGeometry

@[expose] public section

/-!
# The actual broad carrier in the canonical particular coordinates

Only the selected geometry and its closed source support occur here.  No
property of a solved particular or signed field is assumed.
-/

noncomputable section

namespace NavierStokes.ActualCarrierTransportBase

open Set Function Filter
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open CommonCoverSolve
open scoped Topology ContDiff


abbrev Point := LocalSignedRequest.Point
abbrev Parameter := CorrectionStep.CycleSlow
abbrev Plane := TorusInverse.Plane
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

variable {B N0 : ℕ}

noncomputable def domain : Set Point :=
  PhysicalMeanDomain.slowDomain standardRegion.carrier

noncomputable def labelCarrier (l : Index B N0) (n : ℕ) : Set Point :=
  ActualInitialExcluded.labelCarrier (l.2,l.1) n

noncomputable def associatedPoint (p : Parameter) (Y : Plane) : Point :=
  CorrectionStep.cycleAssoc.symm (p, Y)

noncomputable def parameterDomain : Set Parameter :=
  {p | p.2 ∈ standardRegion.carrier}

@[simp] theorem associatedPoint_mem_domain (p : Parameter) (Y : Plane) :
    associatedPoint p Y ∈ domain ↔ p ∈ parameterDomain := Iff.rfl

noncomputable def Ordered (l : Index B N0) (n : ℕ) : Prop :=
  CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.1)

noncomputable def slowMap (l : Index B N0) (n : ℕ) (p : Parameter) : PhaseCalculus.Slow :=
  nativeSlow l.1 (toAbsolute n (associatedPoint p 0))

theorem slowMap_eq (l : Index B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    slowMap l n p = nativeSlow l.1 (toAbsolute n (associatedPoint p Y)) := rfl

theorem slowMap_continuous (l : Index B N0) (n : ℕ) : Continuous (slowMap l n) :=
  (nativeSlow_smooth l.1).continuous.comp ((toAbsolute_smooth n).continuous.comp
    (CorrectionStep.cycleAssoc.symm.continuous.comp (continuous_id.prodMk continuous_const)))

noncomputable def slowCore (l : Index B N0) (n : ℕ) : Set Parameter :=
  slowMap l n ⁻¹' ActualGaussianCoverage.actualSlowCore certificate modulation
    (choice B N0).prepared l.1

theorem slowCore_closed (l : Index B N0) (n : ℕ) : IsClosed (slowCore l n) :=
  (ActualGaussianCoverage.actualSlowCore_closed certificate modulation
    (choice B N0).prepared l.1).preimage (slowMap_continuous l n)

noncomputable def referenceLength (l : Index B N0) : ℝ :=
  (phases B N0 l.2).L l.1

theorem referenceLength_pos (l : Index B N0) : 0 < referenceLength l :=
  (phases B N0 l.2).L_pos l.1

noncomputable def clock (l : Index B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight h (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.1))

theorem clock_pos (l : Index B N0) (n : ℕ) : 0 < clock l n :=
  PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _

noncomputable def spatialLabel (l : Index B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.1) l.2

noncomputable def referenceGeometry (l : Index B N0) : Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

noncomputable def gap (l : Index B N0) (n : ℕ) : ℕ :=
  ChartScales.nativeIndex h (BaseChartJets.cellBand l.1) - CommonWindow.index h n

noncomputable def geometry (l : Index B N0) (n : ℕ) : Geometry :=
  CopySolveCompatibility.transportGeometry (referenceGeometry l) (gap l n) 0
    (clock l n) (clock_pos l n).ne'

theorem reference_refine (l : Index B N0) (n : ℕ) :
    CopySolveCompatibility.refineGeometry (referenceGeometry l) (gap l n) =
      chartGeometry n l.2 l.1 := by
  simp only [CopySolveCompatibility.refineGeometry, referenceGeometry,
    ActualSignedGeometry.slotGeometry, CommonCoverClass.bandGeometry, Nat.zero_add,
    chartGeometry, ActualPrimary.geometry, spatialLabel, gap]
  rfl

noncomputable def sourceRegion (l : Index B N0) (n : ℕ) : Set (Parameter × Plane) :=
  ActualGaussianCoverage.sourceRegion (slowCore l n) (geometry l n)
    slots.radius (referenceLength l) (clock l n)

theorem sourceRegion_closed (l : Index B N0) (n : ℕ) : IsClosed (sourceRegion l n) :=
  ActualGaussianCoverage.sourceRegion_closed (slowCore_closed l n) _ _ _ _

/-- The common-band logarithmic range holds on the full slow domain,
without any restriction on the radial variable. -/
theorem domain_log_band (n : ℕ) {x : Point}
    (hx : x ∈ domain) :
    SquaredPartition.logCoordinate (physicalScale n x) ∈
      Icc ((n : ℝ) - 1) ((n : ℝ) + 1) := by
  have hq : SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Ioo (1/2 : ℝ) 2 := hx.2
  apply PhysicalWaveSum.logCoordinate_in_band
  · change 0 < ChartScales.Q n * _
    exact mul_pos (ChartScales.Q_pos n) (lt_trans (by norm_num) hq.1)
  · change ChartScales.Q n / 2 ≤ ChartScales.Q n * _
    nlinarith [ChartScales.Q_pos n, hq.1]
  · change ChartScales.Q n * _ ≤ 2 * ChartScales.Q n
    nlinarith [ChartScales.Q_pos n, hq.2]

/-- Broad carrier support forces the same finite band distance on the
entire slow domain, including radii outside the analytic strip. -/
theorem carrier_band_distance (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ domain)
    (hc : x ∈ labelCarrier l n) :
    n ≤ BaseChartJets.cellBand l.1 + 2 ∧ BaseChartJets.cellBand l.1 ≤ n + 2 := by
  have hn := domain_log_band n hx
  have hm := ActualCarrierGeometry.labelCarrier_log_band hN (l.2,l.1) n hx.1 hc
  have hnm : n < BaseChartJets.cellBand l.1 + 3 := by
    have he : (n : ℝ) < (BaseChartJets.cellBand l.1 : ℝ) + 3 := by linarith [hn.1, hm.2]
    exact_mod_cast he
  have hmn : BaseChartJets.cellBand l.1 < n + 3 := by
    have he : (BaseChartJets.cellBand l.1 : ℝ) < (n : ℝ) + 3 := by linarith [hm.1, hn.2]
    exact_mod_cast he
  omega

theorem ordered_of_carrier (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ domain)
    (hc : x ∈ labelCarrier l n) : Ordered l n := by
  obtain ⟨hnm, hmn⟩ := carrier_band_distance hN l n hx hc
  have hm4 : 4 ≤ BaseChartJets.cellBand l.1 := ActualPrimaryBounds.label_large (l.2,l.1)
  apply CommonWindow.index_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_Icc.mpr ⟨max_le (by omega) (by omega), hmn⟩

theorem carrier_empty_of_not_ordered
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    (hn : ¬ Ordered l n) :
    Disjoint domain (labelCarrier l n) := by
  rw [Set.disjoint_left]
  intro x hx hc
  exact hn (ordered_of_carrier hN l n hx hc)

/-! The canonical geometry rescales time after the same native refinement. -/

theorem coordinates_clock (l : Index B N0) (n : ℕ) (k : TorusInverse.Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 (clock l n) ((geometry l n).coordinates k Y) =
      (chartGeometry n l.2 l.1).coordinates k Y := by
  change CopySolveCompatibility.nativeTimeMap 0 (clock l n)
      ((CopySolveCompatibility.transportGeometry
        (referenceGeometry l)
        (gap l n) 0 (clock l n) _).coordinates k Y) = _
  rw [ScaledTangentTransport.coordinates_transport,
    ← CopySolveCompatibility.coordinates_refine]
  exact congrArg (fun g : Geometry => g.coordinates k Y)
    (reference_refine l n)

theorem native_coordinates (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (p : Parameter) (Y : Plane) (k : TorusInverse.Frequency) :
    (ActualPrimary.geometry l.2 l.1).coordinates k (toAbsolute n (associatedPoint p Y)).2 =
      CopySolveCompatibility.nativeTimeMap 0 (clock l n) ((geometry l n).coordinates k Y) := by
  rw [coordinates_clock]
  exact chartGeometry_coordinates n l.2 l.1 hn k Y

theorem mem_sourceRegion (l : Index B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    (p,Y) ∈ sourceRegion l n ↔ p ∈ slowCore l n ∧
      ∃ k : TorusInverse.Frequency,
        (geometry l n).coordinates k Y ∈
          ActualGaussianCoverage.sourceCell slots.radius (referenceLength l) (clock l n) := by
  simp only [sourceRegion, ActualGaussianCoverage.sourceRegion, mem_inter_iff, mem_preimage,
    HarmonicSourceSupport.nativeUnion, mem_iUnion, PeriodizedWaveBounds.nativeCell,
      Set.mem_ofPred_eq]

/-- Under the actual index ordering, the broad primary carrier is exactly
the source region of the canonical particular geometry. -/
theorem labelCarrier_iff_sourceRegion (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (p : Parameter) (Y : Plane) :
    associatedPoint p Y ∈ labelCarrier l n ↔
      (p,Y) ∈ sourceRegion l n := by
  rw [mem_sourceRegion]
  change (∃ k : TorusInverse.Frequency,
    (nativeSlow l.1 (toAbsolute n (associatedPoint p Y)),
      (ActualPrimary.geometry l.2 l.1).coordinates k (toAbsolute n (associatedPoint p Y)).2) ∈
        ActualGaussianCoverage.actualSlowCore certificate modulation (choice B N0).prepared l.1 ×ˢ
          ActualGaussianCoverage.sourceCell slots.radius (referenceLength l) 1) ↔ _
  constructor
  · rintro ⟨k, hs, hk⟩
    refine ⟨hs, k, ?_⟩
    apply (ActualGaussianCoverage.mem_sourceCell_clock (clock_pos l n) _).mpr
    rwa [← native_coordinates l n hn p Y k]
  · rintro ⟨hs, k, hk⟩
    refine ⟨k, hs, ?_⟩
    rw [native_coordinates l n hn p Y k]
    exact (ActualGaussianCoverage.mem_sourceCell_clock (clock_pos l n) _).mp hk

/-- The unordered branch is empty. This makes the same source-region
description valid on the full slow domain for every band. -/
noncomputable def activeSlowCore (l : Index B N0) (n : ℕ) : Set Parameter := by
  classical
  exact if Ordered l n then slowCore l n else ∅

theorem activeSlowCore_closed (l : Index B N0) (n : ℕ) : IsClosed (activeSlowCore l n) := by
  classical
  unfold activeSlowCore
  split
  · exact slowCore_closed l n
  · exact isClosed_empty

noncomputable def canonicalSourceRegion (l : Index B N0) (n : ℕ) : Set (Parameter × Plane) :=
  ActualGaussianCoverage.sourceRegion (activeSlowCore l n) (geometry l n)
    slots.radius (referenceLength l) (clock l n)

theorem canonicalSourceRegion_closed (l : Index B N0) (n : ℕ) :
    IsClosed (canonicalSourceRegion l n) :=
  ActualGaussianCoverage.sourceRegion_closed (activeSlowCore_closed l n) _ _ _ _

theorem labelCarrier_iff_canonicalSourceRegion
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {p : Parameter} (hp : p ∈ parameterDomain) (Y : Plane) :
    associatedPoint p Y ∈ labelCarrier l n ↔
      (p,Y) ∈ canonicalSourceRegion l n := by
  classical
  by_cases hn : Ordered l n
  · simpa only [canonicalSourceRegion, activeSlowCore, ite_eq_left hn, sourceRegion] using
      labelCarrier_iff_sourceRegion l n hn p Y
  · have hnot : associatedPoint p Y ∉ labelCarrier l n :=
      fun hc => hn (ordered_of_carrier hN l n hp hc)
    simp only [hnot, canonicalSourceRegion, ActualGaussianCoverage.sourceRegion,
      activeSlowCore, ite_eq_right hn, mem_inter_iff, mem_preimage, mem_empty_iff_false, false_and]

noncomputable def cutoff (l : Index B N0) (n : ℕ) : Plane → ℝ :=
  (fun z => (clockWindow l.1).cutoff z *
    GaussianTailFlat.slotCutoff (referenceLength l) z.2) ∘
      CopySolveCompatibility.nativeTimeMap 0 (clock l n)

theorem cutoff_eq_native (l : Index B N0) (n : ℕ) :
    cutoff l n = ActualGaussianCoverage.nativeCutoff slots.radius (referenceLength l)
      slots.radius_pos (referenceLength_pos l) (clock l n) := by
  funext z
  simp only [cutoff, Function.comp_apply, ActualGaussianCoverage.nativeCutoff,
    CopySolveCompatibility.nativeTimeMap, zero_add]
  rfl

theorem reference_outer_injective (l : Index B N0) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (referenceGeometry l).center +
        (referenceGeometry l).basis z) ''
        (ActualGaussianCoverage.referenceWindow slots.radius (referenceLength l)
          slots.radius_pos (referenceLength_pos l)).outer) := by
  exact ActualGaussianCoverage.actual_outer_injective slots vectors_det outgoing.data.h_pos.le
    (l := spatialLabel l)
    (ActualPrimaryBounds.label_large (l.2,l.1)) 0

theorem geometry_outer_injective (l : Index B N0) (n : ℕ) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (geometry l n).center + (geometry l n).basis z) ''
        ActualGaussianCoverage.outerCell slots.radius (referenceLength l) (clock l n)) :=
  ActualGaussianCoverage.transported_outer_injective
    (referenceGeometry l)
    (gap l n)
    slots.radius_pos (referenceLength_pos l) (clock_pos l n) (reference_outer_injective l)

end NavierStokes.ActualCarrierTransportBase
