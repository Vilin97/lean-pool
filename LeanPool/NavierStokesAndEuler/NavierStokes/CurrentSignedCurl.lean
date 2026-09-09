/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPotentialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalPrefixFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCommonDynamics

/-!
# The curl of the actual current signed potential

The native equation is proved from the actual signed tangency and cutoff
construction.  The weighted amplitude bound supplies its smooth extension
across the radial edges.  All physical statements use the current band.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CurrentSignedCurl

open Set Function Filter ProblemStatement HarmonicCalculus WeightedClasses
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualSignedCoherence ActualSignedPotentialCoherence
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `ActualSignedCoherence.Point`. -/
abbrev Point := ActualSignedCoherence.Point
/-- Full point: an abbreviation for `ActualSignedCoherence.FullPoint`. -/
abbrev FullPoint := ActualSignedCoherence.FullPoint

variable {B N0 : ℕ}

/-- The actual weighted raw-amplitude estimate; no curl equation is included. -/
abbrev AmplitudeBound (l : SignedLabel B N0) (u : CorrectionState.State Point) (α : ℝ) : Prop :=
  MemClass ActualSignedStageControls.fullStrip
    (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
      ActualSignedStageControls.envelope l n x) α (copies l u).common.amplitude

/-- Primitive state regularity and actual mean residual bounds supply the
amplitude hypothesis used below, for the same current request and label. -/
theorem amplitudeBound_of_mean (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge (commonContext
        B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α (u.thetaResidual (commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α (u.axialResidual (commonContext B))) :
    AmplitudeBound l u (α - 1 / 2) :=
  (ActualSignedOutputBounds.actual_common_bounds ActualInitialization.geometry rfl
    (commonContext B) u α H hfixed hθ hz).amplitude.each l

/-- Actual tangency extends to the entire positive native domain: outside the
strict active annulus the common raw amplitude is exactly zero. -/
theorem common_tangent (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) {x : FullPoint} (hx : x ∈ ActualWaveRegularityData.positiveDomain) :
    normalDot ((ActualSignedStageControls.parameters l).base.normal
      ActualSignedStageControls.fullStrip (ActualSignedStageControls.directions B) n x)
      ((copies l u).common.amplitude n x) = 0 := by
  classical
  by_cases hr : ActualWaveRegularityData.radius x ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · have hs : x ∈ ActualSignedStageControls.fullStrip.domain := by
      rw [ActualWaveRegularityData.strip_domain_eq]
      exact ⟨hx.1, hr⟩
    by_cases hk : ∃ k, x ∈ (ActualSignedStageControls.cells l).carrier n k
    · obtain ⟨k, hk⟩ := hk
      rw [((copies l u).common_amplitude_germ (ActualSignedStageControls.cells l)
        (ActualSignedStageControls.cutoff_support l) n hk).self_of_nhds]
      rcases ActualSignedOutputBounds.phaseCell_or_localized_zero (request B u) l n k hs with hc |
          hz
      · change normalDot _ (ActualSignedStageControls.cutoff l k n x •
          ((copies l u).raw k).amplitude n x) = 0
        rw [LocalizedCurlRealization.normalDot_real_smul]
        have ht : normalDot ((ActualSignedStageControls.parameters l).base.normal
            ActualSignedStageControls.fullStrip (ActualSignedStageControls.directions B) n x)
            (((copies l u).raw k).amplitude n x) = 0 :=
          (ActualSignedStageControls.raw_tangent_germ (request B u) hs hc).self_of_nhds
        rw [ht, mul_zero]
      · have ht : ((copies l u).localized k).amplitude n x = 0 := hz.1.self_of_nhds
        rw [ht]
        simp [normalDot]
    · rw [((copies l u).common_zero_germs (ActualSignedStageControls.cells l)
        (ActualSignedStageControls.cutoff_support l) (not_exists.mp hk)).1.self_of_nhds]
      simp [normalDot]
  · have ht : (copies l u).common.amplitude n x = 0 :=
      (ActualWaveRegularityData.signed_common_raw_zero_outside l (request B u) n hx.1 hr).1
    rw [ht]
    simp [normalDot]

/-- Smoothness of the literal current potential on positive native radii. -/
theorem potential_smooth (l : SignedLabel B N0) (u : CorrectionState.State Point)
    {α : ℝ} (ha : AmplitudeBound l u α) (n : ℕ) :
    ContDiffOn ℝ ∞ (potential l u n) ActualWaveRegularityData.positiveDomain := by
  exact CurlClassBounds.vectorPotential_contDiffOn
    (ActualWaveRegularityData.positive_geometry l n)
    ((ActualSignedStageControls.parameters l).base.frequency n)
    (ActualWaveRegularityData.positive_phase l n)
    ((ActualWaveRegularityData.signed_raw_full_regular l (request B u) ha n).1.mono
      inter_subset_left)
    (fun _ hx => ActualPrimaryCoherence.piece_normal_ne standardRegion l.2 l.1 n hx.2)

/-- The real current cylindrical curl is the stored exact signed block. -/
theorem native_curl (l : SignedLabel B N0) (u : CorrectionState.State Point)
    {α : ℝ} (ha : AmplitudeBound l u α) (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularityData.positiveDomain) :
    CurlClassBounds.cylindricalCurl ((ActualSignedStageControls.parameters l).base.radius n)
      ((ActualSignedStageControls.directions B).radialField n)
      (fun _ => (ActualSignedStageControls.directions B).angular)
      ((ActualSignedStageControls.directions B).axialField ActualSignedStageControls.fullStrip n)
      (potential l u n) x =
    vectorMode ((ActualSignedStageControls.parameters l).base.frequency n)
      ((ActualSignedStageControls.parameters l).base.phase n)
      (((copies l u).commonCorrected ActualSignedStageControls.fullStrip
        (ActualSignedStageControls.directions B)).amplitude n) x := by
  exact CurlClassBounds.cylindricalCurl_vectorPotential
    (ActualWaveRegularityData.positive_geometry l n)
    (chartCoefficients_frequency_pos l.2 l.1 n).ne'
    (ActualWaveRegularityData.positive_phase l n)
    ((ActualWaveRegularityData.signed_raw_full_regular l (request B u) ha n).1.mono
      inter_subset_left)
    (fun _ hy => ActualPrimaryCoherence.piece_normal_ne standardRegion l.2 l.1 n hy.2)
    (fun _ hy => common_tangent l u n hy) hx

/-- The actual current potential expressed in the selected Cartesian polar chart. -/
noncomputable def currentPotential (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (a : ℝ) (i : PolarCharts.Index) : VelocityField :=
  PhysicalCurlCovariance.cartesianPotential a i (cylindricalPotential l u n)

theorem nativePoint_mem (n : ℕ) {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.source n) :
    nativePoint n z ∈ ActualWaveRegularityData.positiveDomain :=
  ⟨⟨hz.2.1.1, mem_univ _⟩, hz.2.1.2, standardRegion.time_pos _ hz.2.1.1⟩

theorem cylindricalPotential_smoothAt (l : SignedLabel B N0)
    (u : CorrectionState.State Point) {α : ℝ} (ha : AmplitudeBound l u α)
    (n : ℕ) {z : SpaceTime} (hz : z ∈ ActualPhysicalPrefixFields.source n) :
    ContDiffAt ℝ ∞ (cylindricalPotential l u n) z :=
  (((potential_smooth l u ha n).contDiffAt
    (ActualWaveRegularityData.positiveDomain_open.mem_nhds (nativePoint_mem n hz))).comp z
      (nativePoint_smoothAt n z hz.1)).const_smul (ChartScales.Q n ^ (-h))

theorem currentPotential_smoothAt (l : SignedLabel B N0)
    (u : CorrectionState.State Point) {α : ℝ} (hamp : AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {qbig : ℝ} {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ContDiffAt ℝ ∞ (currentPotential l u n a i) z :=
  PhysicalCurlCovariance.cartesianPotential_smoothAt ha i
    (cylindricalPotential_smoothAt l u hamp n hz.2.2)

/-- Swapping slow coordinates changes the input order, not the vector components. -/
theorem reindexed_curl (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (y : FullPoint) :
    CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius
      (ActualCycleResidualBounds.actualBandGraph n).radial
      PhysicalResidualBridge.ScaledGraph.angular (ActualCycleResidualBounds.actualBandGraph n).axial
      (fun x => potential l u n (PhysicalResidualTZ.swapCylinder x)) y =
    CurlClassBounds.cylindricalCurl ((ActualSignedStageControls.parameters l).base.radius n)
      ((ActualSignedStageControls.directions B).radialField n)
      (fun _ => (ActualSignedStageControls.directions B).angular)
      ((ActualSignedStageControls.directions B).axialField ActualSignedStageControls.fullStrip n)
      (potential l u n) (PhysicalResidualTZ.swapCylinder y) := by
  have he := ActualPrimaryCoherence.cylindricalCurl_equiv
    PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv one_ne_zero
    (fun x : FullPoint => x.1.1) PhysicalResidualBridge.ScaledGraph.radius
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField
      ActualSignedStageControls.fullStrip n)
    (ActualCycleResidualBounds.actualBandGraph n).radial
    PhysicalResidualBridge.ScaledGraph.angular (ActualCycleResidualBounds.actualBandGraph n).axial
    (fun _ => (one_mul _).symm)
    (fun x => by
      simp only [one_smul]
      exact ActualPrimaryCoherence.chart_radial_swap B n x)
    (fun _ => rfl)
    (fun x => by
      simp only [one_smul]
      exact ActualPrimaryCoherence.chart_axial_swap B n standardRegion x)
    1 (fun x => potential l u n (PhysicalResidualTZ.swapCylinder x))
    (PhysicalResidualTZ.swapCylinder y)
  simp only [one_mul, one_smul] at he
  exact he.symm

theorem native_curl_real (l : SignedLabel B N0) (u : CorrectionState.State Point)
    {α : ℝ} (ha : AmplitudeBound l u α) (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularityData.positiveDomain) (j : Fin 3) :
    (CurlClassBounds.cylindricalCurl ((ActualSignedStageControls.parameters l).base.radius n)
      ((ActualSignedStageControls.directions B).radialField n)
      (fun _ => (ActualSignedStageControls.directions B).angular)
      ((ActualSignedStageControls.directions B).axialField ActualSignedStageControls.fullStrip n)
      (potential l u n) x j).re =
    ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
      (request B u)).oscillation n x j := by
  rw [native_curl l u ha n hx]
  have he := congrFun (congrFun (congrFun
    (ActualWaveRegularityData.signedAngles l ActualPrimaryBounds.strip
      ActualInitialization.geometry.patch ActualInitialization.geometry.coord (commonContext B)
          u).block_eq_mode
        n) x) j
  exact he.symm

/-- At a valid current cylindrical chart, the constructed Cartesian potential
has exactly the physical signed velocity as its curl. -/
theorem currentPotential_curl_forward (l : SignedLabel B N0)
    (u : CorrectionState.State Point) {α : ℝ} (hamp : AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hc : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hz : z ∈ ActualPhysicalPrefixFields.source n) :
    SpatialCurl.spatialCurl (currentPotential l u n a i)
        (z.1, CylindricalResidual.chart z.2) =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
            (request B u)).oscillation n)) (z.1, CylindricalResidual.chart z.2) := by
  let G := ActualCycleResidualBounds.actualBandGraph n
  have hx := nativePoint_mem n hz
  have hpot := (potential_smooth l u hamp n).contDiffAt
    (ActualWaveRegularityData.positiveDomain_open.mem_nhds hx)
  have hl : 0 < G.radialScale := Real.rpow_pos_of_pos (ChartScales.Q_pos n) _
  have hB : ∀ j, DifferentiableAt ℝ
      (fun y : FullPoint => potential l u n (PhysicalResidualTZ.swapCylinder y) j) (G.map z) := by
    intro j
    exact (differentiableAt_pi.mp ((hpot.comp (G.map z)
      PhysicalResidualTZ.swapCylinder.contDiff.contDiffAt).differentiableAt (by simp))) j
  have hA : DifferentiableAt ℝ (currentPotential l u n a i)
      (z.1, CylindricalResidual.chart z.2) := by
    apply (PhysicalCurlCovariance.cartesianPotential_smoothAt ha i ?_).differentiableAt (by simp)
    rw [PhysicalCurlCovariance.polarCoordinates_forward ha i hc]
    exact cylindricalPotential_smoothAt l u hamp n hz
  have hrep := PhysicalCurlCovariance.cartesianPotential_forward_germ ha i
    (cylindricalPotential l u n) hc
  have he : CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (currentPotential l u n a i)
        (z.1, CylindricalResidual.chart z.2)) =
      CyclePhysicalPrefixes.velocityMap G
        (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
          (request B u)).oscillation n) z := by
    ext j
    have ht := PhysicalCurlCovariance.ScaledGraph.physical_curl G hl hc.1 hB
      (ChartScales.Q n ^ (-h)) hA (by
        simp only [currentPotential, cylindricalPotential, rescaledPotential, nativePoint,
          PhysicalCurlCovariance.ScaledGraph.realPotential,
          PhysicalCurlCovariance.ScaledGraph.complexPotential, G] at hrep ⊢
        exact hrep) j
    rw [reindexed_curl l u n] at ht
    have hr := native_curl_real l u hamp n hx j
    change (CurlClassBounds.cylindricalCurl _ _ _ _ (potential l u n)
      (PhysicalResidualTZ.swapCylinder (G.map (z.1, z.2))) j).re = _ at hr
    rw [hr] at ht
    rw [show ChartScales.Q n ^ (-h) * G.radialScale = G.velocityScale from
      PhysicalCurlCovariance.commonGraph_curlScale (ChartScales.Q_pos n) h (CommonWindow.index h
          n)] at ht
    simp only [CyclePhysicalPrefixes.velocityMap, LinearMap.coe_mk, AddHom.coe_mk,
      PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply] at ht ⊢
    exact ht
  change _ = CylindricalResidual.frame
    (PhysicalCurlCovariance.polarInput a i (z.1, CylindricalResidual.chart z.2)).2
    (CyclePhysicalPrefixes.velocityMap G
      (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (request B u)).oscillation n)
      (PhysicalCurlCovariance.polarCoordinates a i (z.1, CylindricalResidual.chart z.2)))
  rw [PhysicalCurlCovariance.polarInput_forward ha i hc,
    PhysicalCurlCovariance.polarCoordinates_forward ha i hc]
  simpa only [CylindricalResidual.frame_inverse'] using
    congrArg (CylindricalResidual.frame (z.2 1)) he

/-- The current-band curl identity on the actual Cartesian chart domain. -/
theorem currentPotential_curl (l : SignedLabel B N0)
    (u : CorrectionState.State Point) {α : ℝ} (hamp : AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {qbig : ℝ} {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    SpatialCurl.spatialCurl (currentPotential l u n a i) z =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
            (request B u)).oscillation n)) z := by
  have ht := currentPotential_curl_forward l u hamp n ha i
    (ActualMeanPotentialRealization.polarCoordinates_valid ha i hz.2.1) hz.2.2
  simpa only [ActualMeanPotentialRealization.polarCoordinates_back ha i hz.2.1] using ht

/-- Finite label sums use actual differentiable potentials before taking curl. -/
theorem currentPotential_sum_curl (s : Finset (SignedLabel B N0))
    (u : CorrectionState.State Point) {α : ℝ}
    (hamp : ∀ l ∈ s, AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {qbig : ℝ} {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    SpatialCurl.spatialCurl (fun w => ∑ l ∈ s, currentPotential l u n a i w) z =
      ∑ l ∈ s, CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
            (request B u)).oscillation n)) z := by
  rw [PhysicalParticularWave.spatialCurl_finset_sum s _ (fun l hl =>
    (currentPotential_smoothAt l u (hamp l hl) n ha i hz).differentiableAt (by simp))]
  exact Finset.sum_congr rfl (fun l hl => currentPotential_curl l u (hamp l hl) n ha i hz)

theorem currentPotential_sum_curl_map (s : Finset (SignedLabel B N0))
    (u : CorrectionState.State Point) {α : ℝ}
    (hamp : ∀ l ∈ s, AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {qbig : ℝ} {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    SpatialCurl.spatialCurl (fun w => ∑ l ∈ s, currentPotential l u n a i w) z =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ s, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (request B u)).oscillation n)) z := by
  simpa only [map_sum, Finset.sum_apply] using
    currentPotential_sum_curl s u hamp n ha i hz

/-! ## Integer angular periodicity and independence of the inverse chart -/

theorem potential_periodic (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : Point) :
    Function.Periodic (fun θ => potential l u n (x, θ)) (2 * Real.pi) := by
  let H := ActualWaveRegularityData.signedAngles l ActualPrimaryBounds.strip
    ActualInitialization.geometry.patch ActualInitialization.geometry.coord (commonContext B) u
  have ha := (copies l u).common_amplitude_invariant ((0 : Point), (1 : ℝ))
    (fun n k => H.cutoff k n) H.raw_invariant n
  intro θ
  have he := PhysicalCurlCovariance.vectorPotential_fullTurn
    (Vθ := fun _ => (ActualSignedStageControls.directions B).angular)
    (Vz := (ActualSignedStageControls.directions B).axialField ActualSignedStageControls.fullStrip
        n)
    ((ActualSignedStageControls.parameters l).angularFrequency n)
    (H.radius n) (H.radial n) (by intro x t; rfl)
    (by intro x t; rfl) (H.phase n) ha (H.frequency_slope n) (x, θ)
  simp only [Prod.smul_mk, Prod.mk_add_mk,
    smul_zero, smul_eq_mul, mul_one, add_zero] at he
  exact he

theorem nativePoint_angle (n : ℕ) (t r θ z : ℝ) :
    nativePoint n (t, AxisymmetricResidual.pack r θ z) =
      ((nativePoint n (t, AxisymmetricResidual.pack r 0 z)).1, θ) := by
  simp only [nativePoint, PhysicalResidualBridge.ScaledGraph.map,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
    AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one,
    AxisymmetricResidual.pack_two]

theorem cylindricalPotential_periodic (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (t r z : ℝ) :
    Function.Periodic (fun θ => cylindricalPotential l u n
      (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi) := by
  intro θ
  simp only [cylindricalPotential, rescaledPotential]
  rw [nativePoint_angle n t r (θ + 2 * Real.pi) z, nativePoint_angle n t r θ z]
  exact congrArg (fun v => ChartScales.Q n ^ (-h) • v)
    (potential_periodic l u n _ θ)

/-- A periodic cylindrical field agrees in inverse charts with independently
chosen positive smoothing radii. -/
theorem cartesianPotential_overlap_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i j : PolarCharts.Index) (F : SpaceTime → ComplexVector)
    (hF : ∀ t r z : ℝ, Function.Periodic
      (fun θ => F (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    PhysicalCurlCovariance.cartesianPotential a i F z =
      PhysicalCurlCovariance.cartesianPotential b j F z := by
  let f : PolarCharts.Plane → Space := fun p => CylindricalResidual.frame p.2
    (PhysicalCurlCovariance.realVector (F (z.1, AxisymmetricResidual.pack p.1 p.2 (z.2 2))))
  have hf (r : ℝ) : Function.Periodic (fun θ => f (r, θ)) (2 * Real.pi) := by
    intro θ
    dsimp only [f]
    rw [PhysicalCurlCovariance.frame_periodic θ]
    have he := hF z.1 r (z.2 2) θ
    dsimp only at he
    rw [he]
  change f (PolarCharts.chart a i (PhysicalGraphBounds.radialProjection z)) =
    f (PolarCharts.chart b j (PhysicalGraphBounds.radialProjection z))
  rw [PolarCharts.chart_eq_localChart ha i hi, PolarCharts.chart_eq_localChart hb j hj]
  apply PolarCharts.localChart_periodic_agree f hf i j
  · exact (div_pos ha (by norm_num : (0 : ℝ) < 4)).trans hi
  · exact (div_pos hb (by norm_num : (0 : ℝ) < 4)).trans hj

theorem currentPotential_overlap (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : PolarCharts.Index)
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    currentPotential l u n a i z = currentPotential l u n b j z :=
  cartesianPotential_overlap_radius ha hb i j _ (cylindricalPotential_periodic l u n) hi hj

theorem currentPotential_overlap_germ (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : PolarCharts.Index)
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    currentPotential l u n a i =ᶠ[𝓝 z] currentPotential l u n b j := by
  filter_upwards [(ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hi,
    (ActualMeanPotentialRealization.cartesianDomain_open b j).mem_nhds hj] with y hyi hyj
  exact currentPotential_overlap l u n ha hb i j hyi hyj

/-! ## The actual pressure mode -/

theorem pressureMode_eq_exact (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint) :
    (pressureMode l u n x).re =
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (request B u)).oscillatoryPressure n x := by
  let H := ActualWaveRegularityData.signedAngles l ActualPrimaryBounds.strip
    ActualInitialization.geometry.patch ActualInitialization.geometry.coord (commonContext B) u
  have he := (ActualSignedCommonDynamics.exact_represents (request B u) H.request l).2
  exact (congrFun (congrFun he n) x).symm

/-- Current pressure, defined pointwise by `(cylindricalPressureMode l u n
(PhysicalCurlCovariance.polarCoordinates a i z)).re`. -/
noncomputable def currentPressure (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (a : ℝ) (i : PolarCharts.Index) : PressureField :=
  fun z => (cylindricalPressureMode l u n (PhysicalCurlCovariance.polarCoordinates a i z)).re

theorem currentPressure_eq (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (a : ℝ) (i : PolarCharts.Index) :
    currentPressure l u n a i =
      CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          (((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
            (request B u)).oscillatoryPressure n)) := by
  funext z
  change ((ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h))) •
    pressureMode l u n (nativePoint n (PhysicalCurlCovariance.polarCoordinates a i z))).re =
    (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) ^ 2 * _
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pressureMode_eq_exact]
  congr 1
  rw [← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  congr 1
  ring

theorem realPressureMode_periodic (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : Point) :
    Function.Periodic (fun θ => (pressureMode l u n (x, θ)).re) (2 * Real.pi) := by
  intro θ
  dsimp only
  rw [pressureMode_eq_exact, pressureMode_eq_exact]
  exact congrArg Complex.re (HarmonicFields.field_angular_periodic _ _ _ _ _ θ)

theorem realCylindricalPressure_periodic (l : SignedLabel B N0)
    (u : CorrectionState.State Point) (n : ℕ) (t r z : ℝ) :
    Function.Periodic (fun θ =>
      (cylindricalPressureMode l u n (t, AxisymmetricResidual.pack r θ z)).re)
      (2 * Real.pi) := by
  intro θ
  simp only [cylindricalPressureMode, rescaledPressureMode]
  rw [nativePoint_angle n t r (θ + 2 * Real.pi) z, nativePoint_angle n t r θ z]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact congrArg (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) * ·)
    (realPressureMode_periodic l u n _ θ)

theorem polarScalar_overlap_radius {E : Type*} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i j : PolarCharts.Index) (F : SpaceTime → E)
    (hF : ∀ t r z : ℝ, Function.Periodic
      (fun θ => F (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    F (PhysicalCurlCovariance.polarCoordinates a i z) =
      F (PhysicalCurlCovariance.polarCoordinates b j z) := by
  let f : PolarCharts.Plane → E := fun p => F (z.1, AxisymmetricResidual.pack p.1 p.2 (z.2 2))
  change f (PolarCharts.chart a i (PhysicalGraphBounds.radialProjection z)) =
    f (PolarCharts.chart b j (PhysicalGraphBounds.radialProjection z))
  rw [PolarCharts.chart_eq_localChart ha i hi, PolarCharts.chart_eq_localChart hb j hj]
  exact PolarCharts.localChart_periodic_agree f (fun r => hF z.1 r (z.2 2)) i j
    ((div_pos ha (by norm_num : (0 : ℝ) < 4)).trans hi)
    ((div_pos hb (by norm_num : (0 : ℝ) < 4)).trans hj)

theorem currentPressure_overlap (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : PolarCharts.Index)
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    currentPressure l u n a i z = currentPressure l u n b j z :=
  polarScalar_overlap_radius ha hb i j (fun x => (cylindricalPressureMode l u n x).re)
    (realCylindricalPressure_periodic l u n) hi hj

theorem currentPressure_overlap_germ (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : PolarCharts.Index)
    {z : SpaceTime} (hi : z ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hj : z ∈ ActualMeanPotentialRealization.cartesianDomain b j) :
    currentPressure l u n a i =ᶠ[𝓝 z] currentPressure l u n b j := by
  filter_upwards [(ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hi,
    (ActualMeanPotentialRealization.cartesianDomain_open b j).mem_nhds hj] with y hyi hyj
  exact currentPressure_overlap l u n ha hb i j hyi hyj

end NavierStokes.CurrentSignedCurl
