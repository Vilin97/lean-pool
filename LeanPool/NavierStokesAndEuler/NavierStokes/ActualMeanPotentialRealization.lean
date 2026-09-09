/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CyclePhysicalPrefixes
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization

/-!
# Actual Cartesian curls of the mean stream potentials

The azimuthal potential carries the scale velocity/radialScale. Its genuine
Cartesian curl is the meridional stream pair in the same physical graph.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualMeanPotentialRealization

open Set Filter Function ProblemStatement HarmonicCalculus
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `PhysicalResidualTZ.Lift`. -/
abbrev Point := PhysicalResidualTZ.Lift
/-- Cylinder: an abbreviation for `PhysicalResidualTZ.Cylinder`. -/
abbrev Cylinder := PhysicalResidualTZ.Cylinder
/-- Scaled graph: an abbreviation for `PhysicalResidualBridge.ScaledGraph`. -/
abbrev ScaledGraph := PhysicalResidualBridge.ScaledGraph

/-- Axial, given by `((0, 1), 0)`. -/
noncomputable def axial : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 1), 0)

/-- Chart point, given by `(PhysicalResidualTZ.graphMapTZ G z).1`. -/
noncomputable def chartPoint (G : ScaledGraph) (z : SpaceTime) : Point :=
  (PhysicalResidualTZ.graphMapTZ G z).1

/-- Meridional as an element of `Fin 3 → ℝ`. -/
noncomputable def meridional (G : ScaledGraph) (Ψ : Point → ℝ) (x : Cylinder) : Fin 3 → ℝ :=
  ![PressureStream.streamBeta (G.epsilon • axial) Ψ x.1, 0,
    PressureStream.streamGamma (PressureStream.physicalSpeed G.exponent G.frequency)
      ((0 : ℝ × ℝ), G.radialVector) Ψ x.1]

/-- Component potential, given by `AxisymmetricResidual.pack 0 ((G.velocityScale /
G.radialScale) * Ψ (chartPoint G z)) 0`. -/
noncomputable def componentPotential (G : ScaledGraph) (Ψ : Point → ℝ) (z : SpaceTime) : Space :=
  AxisymmetricResidual.pack 0 ((G.velocityScale / G.radialScale) * Ψ (chartPoint G z)) 0

/-- The same local polar realization used by the physical cycle prefixes. -/
noncomputable def cartesianPotential (a : ℝ) (j : PolarCharts.Index)
    (G : ScaledGraph) (Ψ : Point → ℝ) : VelocityField :=
  CyclePhysicalPrefixes.polarVelocityMap a j (componentPotential G Ψ)

theorem chartPoint_smoothAt (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) : ContDiffAt ℝ ∞ (chartPoint G) z :=
  PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
    (G.map_smoothAt hr).fst

theorem chartPoint_fderiv (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) (w : SpaceTime) :
    fderiv ℝ (chartPoint G) z w = PhysicalResidualTZ.swapSlow ((fderiv ℝ G.map z w).1) := by
  have hd := PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv.hasFDerivAt.comp z
    (((G.map_smoothAt hr).differentiableAt (by simp)).hasFDerivAt.fst)
  change fderiv ℝ (PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv ∘ fun p => (G.map p).1) z w
      = _
  rw [hd.fderiv]
  rfl

theorem chartPoint_radius (G : ScaledGraph) (z : SpaceTime) :
    (chartPoint G z).1 = G.radialScale * z.2 0 := rfl

theorem chartPoint_radial (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) :
    fderiv ℝ (chartPoint G) z (LinearWaveResidual.spaceDirection 0 z) =
      G.radialScale • PressureStream.radialVector
        (PressureStream.physicalSpeed G.exponent G.frequency)
        ((0 : ℝ × ℝ), G.radialVector) (chartPoint G z) := by
  rw [chartPoint_fderiv G hr, G.map_radial hr]
  ext <;> simp [PhysicalResidualBridge.ScaledGraph.radial, PhysicalResidualTZ.swapSlow_apply,
    PressureStream.radialVector, PressureStream.physicalSpeed, RadialPullback.radialJacobian,
    GraphCalculus.radialSpeed, chartPoint_radius, PhysicalResidualBridge.ScaledGraph.map,
    smul_smul, smul_eq_mul] <;> ring_nf <;> simp

theorem chartPoint_axial (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) :
    fderiv ℝ (chartPoint G) z (LinearWaveResidual.spaceDirection 2 z) =
      G.radialScale • ((0 : ℝ), G.epsilon • axial) := by
  rw [chartPoint_fderiv G hr, G.map_axial hr]
  ext <;> simp [PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualTZ.swapSlow_apply,
    axial, smul_eq_mul]

theorem scalar_radial (G : ScaledGraph) (hl : 0 < G.radialScale) {z : SpaceTime}
    (hr : 0 < z.2 0) {Ψ : Point → ℝ} (hΨ : DifferentiableAt ℝ Ψ (chartPoint G z)) :
    along (LinearWaveResidual.spaceDirection 0)
      (fun p => (G.velocityScale / G.radialScale) * Ψ (chartPoint G p)) z =
      G.velocityScale * PressureStream.graphDr
        (PressureStream.physicalSpeed G.exponent G.frequency)
        ((0 : ℝ × ℝ), G.radialVector) Ψ (chartPoint G z) := by
  have he := PhysicalResidualBridge.along_scaled_pull (G.velocityScale / G.radialScale)
      G.radialScale
    ((chartPoint_smoothAt G (mul_pos hl hr).ne').differentiableAt (by simp)) hΨ
    (chartPoint_radial G (mul_pos hl hr).ne')
  simpa only [div_mul_cancel₀ _ hl.ne', along, PressureStream.graphDr] using he

theorem scalar_axial (G : ScaledGraph) (hl : 0 < G.radialScale) {z : SpaceTime}
    (hr : 0 < z.2 0) {Ψ : Point → ℝ} (hΨ : DifferentiableAt ℝ Ψ (chartPoint G z)) :
    along (LinearWaveResidual.spaceDirection 2)
      (fun p => (G.velocityScale / G.radialScale) * Ψ (chartPoint G p)) z =
      G.velocityScale * PressureStream.graphDz (G.epsilon • axial) Ψ (chartPoint G z) := by
  have he := PhysicalResidualBridge.along_scaled_pull
    (V := LinearWaveResidual.spaceDirection 2) (W := fun _ : Point => ((0 : ℝ), G.epsilon • axial))
    (G.velocityScale / G.radialScale) G.radialScale
    ((chartPoint_smoothAt G (mul_pos hl hr).ne').differentiableAt (by simp)) hΨ
    (chartPoint_axial G (mul_pos hl hr).ne')
  simpa only [div_mul_cancel₀ _ hl.ne', along, PressureStream.graphDz] using he

theorem componentPotential_smoothAt (G : ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) {Ψ : Point → ℝ}
    (hΨ : ContDiffAt ℝ ∞ Ψ (chartPoint G z)) :
    ContDiffAt ℝ ∞ (componentPotential G Ψ) z := by
  have h : ContDiffAt ℝ ∞ (fun p => (G.velocityScale / G.radialScale) * Ψ (chartPoint G p)) z :=
    contDiffAt_const.mul (hΨ.comp z (chartPoint_smoothAt G hr))
  convert! h.smul (contDiffAt_const (c := coordinateVector 1)) using 1
  funext p
  simp [componentPotential, AxisymmetricResidual.pack]

/-- The connection term Ψ/R is retained in the actual cylindrical curl. -/
theorem componentPotential_realCurl (G : ScaledGraph) (hl : 0 < G.radialScale) {z : SpaceTime}
    (hr : 0 < z.2 0) {Ψ : Point → ℝ} (hΨ : DifferentiableAt ℝ Ψ (chartPoint G z)) (i : Fin 3) :
    PhysicalCurlCovariance.realCurl LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (fun p i => componentPotential G Ψ p i) z i =
      G.velocityScale * meridional G Ψ (PhysicalResidualTZ.graphMapTZ G z) i := by
  have h0 (k : Fin 3) : along (LinearWaveResidual.spaceDirection k) (fun _ : SpaceTime => (0 : ℝ))
      z = 0 := by
    simp [along]
  have hR := scalar_radial G hl hr hΨ
  have hZ := scalar_axial G hl hr hΨ
  fin_cases i <;> simp only [PhysicalCurlCovariance.realCurl, LinearWaveResidual.coordinateRadius,
      Fin.isValue, componentPotential, AxisymmetricResidual.pack_two, h0, mul_zero,
          AxisymmetricResidual.pack_one, hZ, zero_sub, AxisymmetricResidual.pack_zero, sub_self,
              hR, sub_zero, Fin.zero_eta, Matrix.cons_val_zero, meridional,
                  PressureStream.streamBeta, PressureStream.streamGamma,
                      PressureStream.divideRadius, mul_neg, neg_inj, mul_eq_mul_left_iff,
                          Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val_two,
                              Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
                                  Matrix.head_cons]
  · exact Or.inl rfl
  · rw [show (PhysicalResidualTZ.graphMapTZ G z).1.1 = G.radialScale * z.2 0 from rfl]
    change G.velocityScale * _ + (z.2 0)⁻¹ * ((G.velocityScale / G.radialScale) * Ψ (chartPoint G
        z)) = _
    field_simp [hl.ne', hr.ne']
    unfold chartPoint
    ring

theorem cartesianPotential_smoothAt {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) {Ψ : Point → ℝ} {w : SpaceTime}
    (hr : G.radialScale * (PhysicalCurlCovariance.polarCoordinates a j w).2 0 ≠ 0)
    (hΨ : ContDiffAt ℝ ∞ Ψ (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    ContDiffAt ℝ ∞ (cartesianPotential a j G Ψ) w := by
  exact (CylindricalResidual.contDiff_frame.contDiffAt.comp w
    (PhysicalCurlCovariance.polarInput_smooth ha j).contDiffAt.snd).clm_apply
      ((componentPotential_smoothAt G hr hΨ).comp w
        (PhysicalCurlCovariance.polarCoordinates_smooth ha j).contDiffAt)

theorem polar_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (v : VelocityField)
    {z : SpaceTime} (hz : z ∈ PhysicalCurlCovariance.validCylindrical a j) :
    CyclePhysicalPrefixes.polarVelocityMap a j v (z.1, CylindricalResidual.chart z.2) =
      CylindricalResidual.frame (z.2 1) (v z) := by
  change CylindricalResidual.frame
    (PhysicalCurlCovariance.polarInput a j (z.1, CylindricalResidual.chart z.2)).2
    (v (PhysicalCurlCovariance.polarCoordinates a j (z.1, CylindricalResidual.chart z.2))) = _
  rw [PhysicalCurlCovariance.polarInput_forward ha j hz,
    PhysicalCurlCovariance.polarCoordinates_forward ha j hz]

theorem cartesianPotential_forward_germ {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (Ψ : Point → ℝ) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a j) :
    (fun p : SpaceTime => cartesianPotential a j G Ψ (p.1, CylindricalResidual.chart p.2)) =ᶠ[𝓝 z]
      (fun p => CylindricalResidual.frame (p.2 1) (componentPotential G Ψ p)) :=
  eventually_of_mem ((PhysicalCurlCovariance.validCylindrical_open a j).mem_nhds hz)
    (fun _ hp => polar_forward ha j _ hp)

/-- A value formula for the potential, differentiated by the real Cartesian
curl theorem, yields the actual meridional velocity. -/
theorem cartesianPotential_curl_forward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) {Ψ : Point → ℝ} {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a j)
    (hΨ : ContDiffAt ℝ ∞ Ψ (chartPoint G z)) :
    SpatialCurl.spatialCurl (cartesianPotential a j G Ψ) (z.1, CylindricalResidual.chart z.2) =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G (meridional G
          Ψ))
        (z.1, CylindricalResidual.chart z.2) := by
  have hrad := (mul_pos hl hz.1).ne'
  have hb := componentPotential_smoothAt G hrad hΨ
  have ha' : ContDiffAt ℝ ∞ (cartesianPotential a j G Ψ) (z.1, CylindricalResidual.chart z.2) := by
    apply cartesianPotential_smoothAt ha j G
    · rwa [PhysicalCurlCovariance.polarCoordinates_forward ha j hz]
    · rwa [PhysicalCurlCovariance.polarCoordinates_forward ha j hz]
  have he : CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (cartesianPotential a j G Ψ) (z.1, CylindricalResidual.chart z.2)) =
      CyclePhysicalPrefixes.velocityMap G (meridional G Ψ) z := by
    ext i
    rw [PhysicalCurlCovariance.curl_of_representation (ha'.differentiableAt (by simp))
      (hb.differentiableAt (by simp)) hz.1.ne' (cartesianPotential_forward_germ ha j G Ψ hz) i,
      componentPotential_realCurl G hl hz.1 (hΨ.differentiableAt (by simp))]
    simp [CyclePhysicalPrefixes.velocityMap, PhysicalResidualTZ.velocityTZ,
      PhysicalResidualBridge.ScaledGraph.velocity_apply, PhysicalResidualTZ.graphMapTZ]
  rw [polar_forward ha j _ hz]
  simpa only [CylindricalResidual.frame_inverse'] using
    congrArg (CylindricalResidual.frame (z.2 1)) he

/-! ## Ordinary Cartesian chart domains -/

/-- Cartesian domain, given by `PhysicalGraphBounds.radialProjection ⁻¹' PolarCharts.chartDomain
a j`. -/
noncomputable def cartesianDomain (a : ℝ) (j : PolarCharts.Index) : Set SpaceTime :=
  PhysicalGraphBounds.radialProjection ⁻¹' PolarCharts.chartDomain a j

theorem cartesianDomain_open (a : ℝ) (j : PolarCharts.Index) : IsOpen (cartesianDomain a j) :=
  (PolarCharts.chartDomain_open a j).preimage PhysicalGraphBounds.radialProjection.continuous

theorem polarCoordinates_valid {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j) :
    PhysicalCurlCovariance.polarCoordinates a j w ∈ PhysicalCurlCovariance.validCylindrical a j :=
        by
  have hrot : 0 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection w)).1 :=
    (by positivity : 0 < a / 4).trans hw
  have hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w) := by
    rw [← PolarCharts.radius_rotate j]
    exact PolarCharts.radius_pos_of_fst_pos hrot
  have hp := PolarCharts.polar_chart ha j hw
  have hc : PhysicalCurlCovariance.polarInput a j w =
      (PolarCharts.radius (PhysicalGraphBounds.radialProjection w),
        Real.arctan ((PolarCharts.rotate j (PhysicalGraphBounds.radialProjection w)).2 /
          (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection w)).1) + PolarCharts.offset
              j) := by
    rw [PhysicalCurlCovariance.polarInput, PolarCharts.chart_eq_localChart ha j hw,
      PolarCharts.localChart_apply]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [PhysicalCurlCovariance.polarCoordinates, hc, AxisymmetricResidual.pack_zero] using
      hr
  · simpa only [PhysicalCurlCovariance.polarCoordinates, hc, AxisymmetricResidual.pack_one,
      add_sub_cancel_right, Set.mem_Ioo] using
      And.intro (Real.neg_pi_div_two_lt_arctan _) (Real.arctan_lt_pi_div_two _)
  · simp only [PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_zero,
      AxisymmetricResidual.pack_one, PhysicalCurlCovariance.polarInput, Prod.eta, hp]
    exact hw

theorem polarCoordinates_back {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j) :
    ((PhysicalCurlCovariance.polarCoordinates a j w).1,
      CylindricalResidual.chart (PhysicalCurlCovariance.polarCoordinates a j w).2) = w := by
  have hp := PolarCharts.polar_chart ha j hw
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i
    · simpa [PhysicalCurlCovariance.polarCoordinates, CylindricalResidual.chart,
        AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one,
        PhysicalCurlCovariance.polarInput, PolarCharts.polar,
            PhysicalGraphBounds.radialProjection_apply]
        using congrArg Prod.fst hp
    · simpa [PhysicalCurlCovariance.polarCoordinates, CylindricalResidual.chart,
        AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one,
        PhysicalCurlCovariance.polarInput, PolarCharts.polar,
            PhysicalGraphBounds.radialProjection_apply]
        using congrArg Prod.snd hp
    · simp [PhysicalCurlCovariance.polarCoordinates, CylindricalResidual.chart,
        AxisymmetricResidual.pack_two]

theorem cartesianPotential_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) {Ψ : Point → ℝ} {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j)
    (hΨ : ContDiffAt ℝ ∞ Ψ (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cartesianPotential a j G Ψ) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G (meridional G
          Ψ)) w := by
  have ht := cartesianPotential_curl_forward ha j G hl (polarCoordinates_valid ha j hw) hΨ
  simpa only [polarCoordinates_back ha j hw] using ht

/-! ## The actual variable-gauge temporal and rank fields -/

/-- Only literal chart coefficients are matched here; no derivative or curl
identity is part of this predicate. -/
structure GaugeMatches (g : VariableGaugeMean.GaugeData (ℝ × ℝ))
    (c : CorrectionState.Context Point) (G : ScaledGraph) (n : ℕ) : Prop where
  epsilon : c.operators.epsilon n = G.epsilon
  exponent : g.radial.exponent = G.exponent
  frequency : g.radial.frequency n = G.frequency
  radialVector : g.radial.radialDirection = G.radialVector

theorem similarityGauge_matches (h a b : ℝ) (hab : a < b) (index : ℕ → ℕ)
    (c : CorrectionState.Context Point) (n : ℕ) (hε : c.operators.epsilon n = ChartScales.Q n ^ h) :
    GaugeMatches (VariableGaugeMean.similarityGauge h (ChartScales.radialExponent h) a b 1 hab
        index)
      c (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (index n)) n := by
  refine ⟨hε, rfl, ?_, rfl⟩
  simp [VariableGaugeMean.similarityGauge, MeanChartCompatibility.radialFrequency,
    PhysicalResidualBridge.commonGraph]

theorem meridional_temporal (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (h : ℝ)
    (index : ℕ → ℕ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (G : ScaledGraph) (n : ℕ) (H : GaugeMatches g c G n) :
    meridional G (VariableGaugeMean.temporalPotential g h index c u n) =
      CyclePhysicalPrefixes.meridionalComponents
        (VariableGaugeMean.temporalIncrementState g h index axial c u) n := by
  funext x i
  fin_cases i <;> simp [meridional, CyclePhysicalPrefixes.meridionalComponents,
    VariableGaugeMean.temporalIncrementState, H.epsilon, H.exponent, H.frequency, H.radialVector]

theorem meridional_rank (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : CorrectionState.RankData (ℝ
    × ℝ))
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (G : ScaledGraph) (n : ℕ) (H : GaugeMatches g c G n) :
    meridional G (VariableGaugeMean.rankPotential g r c u n) =
      CyclePhysicalPrefixes.meridionalComponents
        (VariableGaugeMean.rankIncrementState g r axial c u) n := by
  funext x i
  fin_cases i <;> simp [meridional, CyclePhysicalPrefixes.meridionalComponents,
    VariableGaugeMean.rankIncrementState, H.epsilon, H.exponent, H.frequency, H.radialVector]

theorem temporalPotential_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (n : ℕ) (H : GaugeMatches g c G n)
    {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (hΨ : ContDiffAt ℝ ∞ (VariableGaugeMean.temporalPotential g h index c u n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cartesianPotential a j G (VariableGaugeMean.temporalPotential g h
        index c u n)) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents
          (VariableGaugeMean.temporalIncrementState g h index axial c u) n)) w := by
  rw [cartesianPotential_curl ha j G hl hw hΨ, meridional_temporal g h index c u G n H]

theorem rankPotential_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : CorrectionState.RankData (ℝ × ℝ))
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (n : ℕ) (H : GaugeMatches g c G n)
    {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (hΨ : ContDiffAt ℝ ∞ (VariableGaugeMean.rankPotential g r c u n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cartesianPotential a j G (VariableGaugeMean.rankPotential g r c u n))
        w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents (VariableGaugeMean.rankIncrementState g r axial
            c u) n)) w := by
  rw [cartesianPotential_curl ha j G hl hw hΨ, meridional_rank g r c u G n H]

/-! ## Identification with the coherent physical mean potential -/

theorem projection_forward (z : SpaceTime) :
    PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2) =
      PolarCharts.polar (z.2 0, z.2 1) := by
  simp [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart, PolarCharts.polar]

theorem radius_forward {z : SpaceTime} (hr : 0 < z.2 0) :
    PhysicalClassBounds.cartesianRadius
      (PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2)) = z.2 0 := by
  change PolarCharts.radius (PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart
      z.2)) = _
  rw [projection_forward, PolarCharts.radius_polar, abs_of_pos hr]

theorem physicalPoint_forward (h : ℝ) {z : SpaceTime} (hr : 0 < z.2 0) :
    PhysicalMeanJetBounds.physicalPoint h (z.1, CylindricalResidual.chart z.2) =
      PhysicalResidualTZ.absoluteLiftTZ h z := by
  have hp : PhysicalGraphBounds.radialProfile (ChartScales.radialExponent h)
      (PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2)) =
      (z.2 0) ^ ChartScales.radialExponent h • PhysicalGraphBounds.radialDirection := by
    rw [PhysicalGraphBounds.radialProfile, PhysicalGraphBounds.radiusPower_eq]
    change (PhysicalClassBounds.cartesianRadius
      (PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2))) ^ _ • _ = _
    rw [radius_forward hr]
  unfold PhysicalMeanJetBounds.physicalPoint
  rw [radius_forward hr, hp]
  simp only [PhysicalResidualTZ.absoluteLiftTZ, PhysicalResidualBridge.absoluteLift,
    PhysicalResidualTZ.swapSlow_apply, CylindricalResidual.chart, AxisymmetricResidual.pack_two]

theorem physicalToChartTZ_eq (h : ℝ) (n k : ℕ) :
    PhysicalResidualTZ.physicalToChartTZ h n k = VariableGaugeMean.physicalToChartTZ h n k := by
  rfl

theorem chartPoint_eq_graph_forward (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) {z : SpaceTime} (hr : 0 < z.2 0) :
    chartPoint (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
      (ChartScales.nativeIndex h n - d)) z =
      PhysicalMeanJetBounds.graph h n d (z.1, CylindricalResidual.chart z.2) := by
  rw [PhysicalMeanJetBounds.graph_eq_physicalToChartTZ h n d hd, physicalPoint_forward h hr]
  have he := congrArg Prod.fst (PhysicalResidualTZ.commonGraph_eq_physicalToChartTZ h n
    (ChartScales.nativeIndex h n - d) hr)
  simpa only [chartPoint, physicalToChartTZ_eq] using he

theorem chartPoint_eq_graph {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (h : ℝ)
    (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n) {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j) :
    chartPoint (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
      (ChartScales.nativeIndex h n - d)) (PhysicalCurlCovariance.polarCoordinates a j w) =
      PhysicalMeanJetBounds.graph h n d w := by
  have he := chartPoint_eq_graph_forward h n d hd (polarCoordinates_valid ha j hw).1
  simpa only [polarCoordinates_back ha j hw] using he

theorem angularVector_forward {z : SpaceTime} (hr : 0 < z.2 0) :
    PhysicalMeanJetBounds.angularVector
      (PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2)) =
      CylindricalResidual.frame (z.2 1) (coordinateVector 1) := by
  rw [PhysicalMeanJetBounds.angularVector, radius_forward hr]
  ext i
  fin_cases i <;> simp [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart,
    CylindricalResidual.frame_apply, coordinateVector]
  · field_simp [hr.ne']
  · field_simp [hr.ne']

theorem common_potential_units (h : ℝ) (n k : ℕ) :
    ChartScales.Q n ^ (-(CoordinateAlgebra.A h - 1 / 2)) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h k).velocityScale /
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h k).radialScale := by
  rw [PhysicalCurlCovariance.commonGraph_potentialScale (ChartScales.Q_pos n)]
  congr 1
  unfold CoordinateAlgebra.A
  ring

theorem bandAngularField_forward (h : ℝ) (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n)
    (Ψ : Point → ℝ) {z : SpaceTime} (hr : 0 < z.2 0) :
    PhysicalMeanJetBounds.bandAngularField h n d (CoordinateAlgebra.A h - 1 / 2) Ψ
      (z.1, CylindricalResidual.chart z.2) =
      CylindricalResidual.frame (z.2 1) (componentPotential
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d))
            Ψ z) := by
  rw [PhysicalMeanJetBounds.bandAngularField, PhysicalMeanJetBounds.bandField,
    ← chartPoint_eq_graph_forward h n d hd hr, angularVector_forward hr,
    common_potential_units h n (ChartScales.nativeIndex h n - d)]
  simp only [smul_eq_mul, componentPotential, AxisymmetricResidual.pack,
    zero_smul, zero_add, add_zero, map_smul]

theorem bandAngularField_eq_cartesianPotential {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (h : ℝ) (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n) (Ψ : Point → ℝ)
    {w : SpaceTime} (hw : w ∈ cartesianDomain a j) :
    PhysicalMeanJetBounds.bandAngularField h n d (CoordinateAlgebra.A h - 1 / 2) Ψ w =
      cartesianPotential a j
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d))
            Ψ w := by
  have hb := bandAngularField_forward h n d hd Ψ (polarCoordinates_valid ha j hw).1
  have hp := polar_forward ha j (componentPotential
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d)) Ψ)
    (polarCoordinates_valid ha j hw)
  rw [polarCoordinates_back ha j hw] at hb hp
  exact hb.trans hp.symm

theorem coherent_angularField_germ {a h : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {N Δ : ℕ} {U : Set (ℝ × ℝ)}
    (D : PhysicalMeanJetBounds.CoherentFamily h (CoordinateAlgebra.A h - 1 / 2) N Δ U ℝ)
    (hU : IsOpen U) (n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal) (hu : (PhysicalMeanJetBounds.graph h n (D.gap n) w).2.1
        ∈ U)
    (hw : w ∈ cartesianDomain a j) :
    D.angularField =ᶠ[𝓝 w] cartesianPotential a j
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n - D.gap n)) (D.native n) := by
  apply (D.angularField_germ hU n hn ht hu).trans
  filter_upwards [(cartesianDomain_open a j).mem_nhds hw] with z hz
  exact bandAngularField_eq_cartesianPotential ha j h n (D.gap n) (D.gap_native n hn) (D.native n)
      hz

/-- This is a curl identity for the coherent physical field itself, obtained
from its proved value coherence and the actual Cartesian derivative. -/
theorem coherent_angularField_curl {a h : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {N Δ : ℕ} {U : Set (ℝ × ℝ)}
    (D : PhysicalMeanJetBounds.CoherentFamily h (CoordinateAlgebra.A h - 1 / 2) N Δ U ℝ)
    (hU : IsOpen U) (n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal) (hu : (PhysicalMeanJetBounds.graph h n (D.gap n) w).2.1
        ∈ U)
    (hw : w ∈ cartesianDomain a j)
    (hΨ : ContDiffAt ℝ ∞ (D.native n) (PhysicalMeanJetBounds.graph h n (D.gap n) w)) :
    SpatialCurl.spatialCurl D.angularField w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n
          - D.gap n)
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G (meridional G
          (D.native n))) w := by
  rw [PhysicalCurlCovariance.spatialCurl_congr (coherent_angularField_germ ha j D hU n hn ht hu hw)]
  apply cartesianPotential_curl ha j _ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hw
  rwa [chartPoint_eq_graph ha j h n (D.gap n) (D.gap_native n hn) hw]

/-- For the reconstructed mean stream, smoothness of the scalar potential is
proved from the supported axial source. No curl identity or smoothness of the
output is an input. The radial exponent and frequency are the physical ones. -/
theorem reconstructStream_curl {a b h ρ : ℝ} (hρ : 0 < ρ) (j : PolarCharts.Index)
    (U : LocalSignedRequest.SlowRegion (2 * h)) {N Δ : ℕ}
    (D : PhysicalMeanJetBounds.CoherentFamily h (CoordinateAlgebra.A h) N Δ U.carrier ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hf : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U.carrier D.native)
    (n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (D.gap n) w).2.1 ∈ U.carrier)
    (hw : w ∈ cartesianDomain ρ j) :
    let R := D.reconstructStream hh hh1 ha hab (ChartScales.radialExponent_pos h hh.le)
      1 U.isOpen hf hs
    SpatialCurl.spatialCurl R.angularField w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n - D.gap n)
      CyclePhysicalPrefixes.polarVelocityMap ρ j
        (CyclePhysicalPrefixes.velocityMap G (meridional G (R.native n))) w := by
  dsimp only
  apply coherent_angularField_curl hρ j
    (D.reconstructStream hh hh1 ha hab (ChartScales.radialExponent_pos h hh.le) 1 U.isOpen hf hs)
    U.isOpen n hn ht hu hw
  exact (VariableGaugeMean.streamPotential_q_contDiffOn U ha hab
    (ChartScales.radialExponent_pos h hh.le) _ _ (hf n hn) (hs n hn)).contDiffAt
      ((PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hu)

/-! ## Finite sums of the actual potentials -/

theorem cartesianPotential_finset_curl {ι : Type} (S : Finset ι)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (G : ScaledGraph)
    (hl : 0 < G.radialScale) (Ψ : ι → Point → ℝ) {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j)
    (hΨ : ∀ i ∈ S, ContDiffAt ℝ ∞ (Ψ i)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (fun z => ∑ i ∈ S, cartesianPotential a j G (Ψ i) z) w =
      CyclePhysicalPrefixes.polarVelocityMap a j
        (CyclePhysicalPrefixes.velocityMap G (∑ i ∈ S, meridional G (Ψ i))) w := by
  rw [PhysicalParticularWave.spatialCurl_finset_sum S _ (fun i hi =>
    (cartesianPotential_smoothAt ha j G
      (mul_pos hl (polarCoordinates_valid ha j hw).1).ne' (hΨ i hi)).differentiableAt (by simp))]
  simp only [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => cartesianPotential_curl ha j G hl hw (hΨ i hi))

theorem cartesianPotential_add_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (Ψ Φ : Point → ℝ) {w : SpaceTime}
    (hw : w ∈ cartesianDomain a j)
    (hΨ : ContDiffAt ℝ ∞ Ψ (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hΦ : ContDiffAt ℝ ∞ Φ (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cartesianPotential a j G Ψ + cartesianPotential a j G Φ) w =
      CyclePhysicalPrefixes.polarVelocityMap a j
        (CyclePhysicalPrefixes.velocityMap G (meridional G Ψ + meridional G Φ)) w := by
  have he := cartesianPotential_finset_curl (Finset.univ : Finset (Fin 2)) ha j G hl ![Ψ, Φ] hw
    (by
      intro i hi
      fin_cases i
      · exact hΨ
      · exact hΦ)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at he ⊢
  exact he

theorem meridionalComponents_updated (m t : MeanIncrementBounds.Triple Point) (n : ℕ) :
    CyclePhysicalPrefixes.meridionalComponents (MeanIncrementBounds.updated m t) n =
      CyclePhysicalPrefixes.meridionalComponents m n + CyclePhysicalPrefixes.meridionalComponents t
          n := by
  funext x i
  fin_cases i <;> simp [CyclePhysicalPrefixes.meridionalComponents, MeanIncrementBounds.updated]

/-- The temporal and rank inputs may be successive actual states. Their
potentials realize exactly the radial/axial parts of those literal increments. -/
theorem temporal_rank_curl {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : CorrectionState.RankData (ℝ × ℝ))
    (h : ℝ) (index : ℕ → ℕ) (c : CorrectionState.Context Point)
    (ut ur : CorrectionState.State Point) (G : ScaledGraph) (hl : 0 < G.radialScale)
    (n : ℕ) (H : GaugeMatches g c G n) {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (ht : ContDiffAt ℝ ∞ (VariableGaugeMean.temporalPotential g h index c ut n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hr : ContDiffAt ℝ ∞ (VariableGaugeMean.rankPotential g r c ur n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl
      (cartesianPotential a j G (VariableGaugeMean.temporalPotential g h index c ut n) +
        cartesianPotential a j G (VariableGaugeMean.rankPotential g r c ur n)) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents
          (VariableGaugeMean.temporalIncrementState g h index axial c ut) n +
        CyclePhysicalPrefixes.meridionalComponents
          (VariableGaugeMean.rankIncrementState g r axial c ur) n)) w := by
  rw [cartesianPotential_add_curl ha j G hl _ _ hw ht hr,
    meridional_temporal g h index c ut G n H, meridional_rank g r c ur G n H]

open CorrectionState CorrectionStep

/-- The two scalar streams are evaluated at the actual successive states of
the four-stage cycle. -/
noncomputable def cycleMeanPotential {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ) : VelocityField :=
  cartesianPotential a j G
    (VariableGaugeMean.temporalPotential p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c
        u) n) +
  cartesianPotential a j G
    (VariableGaugeMean.rankPotential p.gauge p.rank c (p.afterTemporal v c u) n)

theorem cycleMeanPotential_curl {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (n : ℕ) (H : GaugeMatches p.gauge c G n)
    (hax : p.axial = axial) {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (ht : ContDiffAt ℝ ∞
      (VariableGaugeMean.temporalPotential p.gauge p.timeExponent p.commonIndex c (p.afterSigned v
          c u) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hr : ContDiffAt ℝ ∞ (VariableGaugeMean.rankPotential p.gauge p.rank c (p.afterTemporal v c u)
        n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cycleMeanPotential p v c u a j G n) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents (p.temporalIncrement v c u) n +
          CyclePhysicalPrefixes.meridionalComponents (p.rankIncrement v c u) n)) w := by
  simpa only [cycleMeanPotential, CycleParameters.temporalIncrement, CycleParameters.rankIncrement,
      hax]
    using temporal_rank_curl ha j p.gauge p.rank p.timeExponent p.commonIndex c
      (p.afterSigned v c u) (p.afterTemporal v c u) G hl n H hw ht hr

theorem cycleMeanPotential_smoothAt {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (n : ℕ) {w : SpaceTime} (hw : w ∈ cartesianDomain a
        j)
    (ht : ContDiffAt ℝ ∞
      (VariableGaugeMean.temporalPotential p.gauge p.timeExponent p.commonIndex c (p.afterSigned v
          c u) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hr : ContDiffAt ℝ ∞ (VariableGaugeMean.rankPotential p.gauge p.rank c (p.afterTemporal v c u)
        n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    ContDiffAt ℝ ∞ (cycleMeanPotential p v c u a j G n) w :=
  (cartesianPotential_smoothAt ha j G (mul_pos hl (polarCoordinates_valid ha j hw).1).ne' ht).add
    (cartesianPotential_smoothAt ha j G (mul_pos hl (polarCoordinates_valid ha j hw).1).ne' hr)

/-! ## The actual initialized mean -/

open CorrectionInitialization CorrectionInitialization.GaugeInitialization

/-- Initialized mean potential, constructed using `cartesianPotential`. -/
noncomputable def initializedMeanPotential {ι : Type}
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : RankData (ℝ × ℝ))
    (h : ℝ) (index : ℕ → ℕ) (c : Context Point)
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Point × ℝ))
    (baseError : Oscillation Point) (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ) :
    VelocityField :=
  cartesianPotential a j G (VariableGaugeMean.temporalPotential g h index c
    (primaryBands g c labels pieces baseError) n) +
  cartesianPotential a j G (VariableGaugeMean.rankPotential g r c
    (temporalBands g h index axial c labels pieces baseError) n)

theorem initializedBands_mean {ι : Type}
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : RankData (ℝ × ℝ))
    (h : ℝ) (index : ℕ → ℕ) (c : Context Point)
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Point × ℝ))
    (baseError : Oscillation Point) :
    (initializedBands g r h index axial c labels pieces baseError).mean =
      MeanIncrementBounds.updated
        (VariableGaugeMean.temporalIncrementState g h index axial c (primaryBands g c labels pieces
            baseError))
        (VariableGaugeMean.rankIncrementState g r axial c
          (temporalBands g h index axial c labels pieces baseError)) := by
  change MeanIncrementBounds.updated
    (MeanIncrementBounds.updated ⟨0, 0, 0⟩
      (VariableGaugeMean.temporalIncrementState g h index axial c (primaryBands g c labels pieces
          baseError)))
    (VariableGaugeMean.rankIncrementState g r axial c
      (temporalBands g h index axial c labels pieces baseError)) = _
  simp only [MeanIncrementBounds.updated, zero_add]

/-- The initial mean potential is the sum of the two actual initialized
streams. Its curl equals the initialized mean's meridional components. -/
theorem initializedMeanPotential_curl {ι : Type}
    (g : VariableGaugeMean.GaugeData (ℝ × ℝ)) (r : RankData (ℝ × ℝ))
    (h : ℝ) (index : ℕ → ℕ) (c : Context Point)
    (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (Point × ℝ))
    (baseError : Oscillation Point) {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (hl : 0 < G.radialScale) (n : ℕ) (H : GaugeMatches g c G n)
    {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (ht : ContDiffAt ℝ ∞ (VariableGaugeMean.temporalPotential g h index c
      (primaryBands g c labels pieces baseError) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hr : ContDiffAt ℝ ∞ (VariableGaugeMean.rankPotential g r c
      (temporalBands g h index axial c labels pieces baseError) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (initializedMeanPotential g r h index c labels pieces baseError a j G
        n) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents
          (initializedBands g r h index axial c labels pieces baseError).mean n)) w := by
  rw [initializedBands_mean, meridionalComponents_updated]
  exact temporal_rank_curl ha j g r h index c _ _ G hl n H hw ht hr

/-! ## Finite prefixes of the literal iteration -/

/-- Mean increment components, constructed using `CyclePhysicalPrefixes.meridionalComponents`. -/
noncomputable def meanIncrementComponents {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (n : ℕ) :
    CyclePhysicalPrefixes.Components :=
  CyclePhysicalPrefixes.meridionalComponents (p.temporalIncrement v c u) n +
    CyclePhysicalPrefixes.meridionalComponents (p.rankIncrement v c u) n

theorem meridionalComponents_next {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (n : ℕ) :
    CyclePhysicalPrefixes.meridionalComponents (p.next v c u).mean n =
      CyclePhysicalPrefixes.meridionalComponents u.mean n + meanIncrementComponents p v c u n := by
  rw [p.next_mean, meridionalComponents_updated, meridionalComponents_updated]
  exact add_assoc _ _ _

theorem meridionalComponents_iterate {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (n J : ℕ) :
    CyclePhysicalPrefixes.meridionalComponents (CycleState.iterate p c seed J).state.mean n =
      CyclePhysicalPrefixes.meridionalComponents seed.state.mean n +
        ∑ k ∈ Finset.range J, meanIncrementComponents (p k)
          (CycleState.iterate p c seed k).coefficients c (CycleState.iterate p c seed k).state n :=
              by
  induction J with
  | zero => simp only [CycleState.iterate_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ J ih =>
      change CyclePhysicalPrefixes.meridionalComponents
        ((p J).next (CycleState.iterate p c seed J).coefficients c (CycleState.iterate p c seed
            J).state).mean n = _
      rw [meridionalComponents_next, ih, Finset.sum_range_succ, add_assoc]

/-- The finite sum is evaluated on the actual successive cycle states. -/
noncomputable def cycleMeanPrefix {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι)
    (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n J : ℕ) : VelocityField :=
  fun w => ∑ k ∈ Finset.range J, cycleMeanPotential (p k)
    (CycleState.iterate p c seed k).coefficients c (CycleState.iterate p c seed k).state a j G n w

theorem cycleMeanPrefix_curl {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) (G : ScaledGraph) (hl : 0 < G.radialScale) (n J : ℕ)
    (H : ∀ k < J, GaugeMatches (p k).gauge c G n)
    (hax : ∀ k < J, (p k).axial = axial) {w : SpaceTime} (hw : w ∈ cartesianDomain a j)
    (ht : ∀ k < J, ContDiffAt ℝ ∞
      (VariableGaugeMean.temporalPotential (p k).gauge (p k).timeExponent (p k).commonIndex c
        ((p k).afterSigned (CycleState.iterate p c seed k).coefficients c (CycleState.iterate p c
            seed k).state) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w)))
    (hr : ∀ k < J, ContDiffAt ℝ ∞
      (VariableGaugeMean.rankPotential (p k).gauge (p k).rank c
        ((p k).afterTemporal (CycleState.iterate p c seed k).coefficients c (CycleState.iterate p c
            seed k).state) n)
      (chartPoint G (PhysicalCurlCovariance.polarCoordinates a j w))) :
    SpatialCurl.spatialCurl (cycleMeanPrefix p c seed a j G n J) w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (CyclePhysicalPrefixes.meridionalComponents (CycleState.iterate p c seed J).state.mean n -
          CyclePhysicalPrefixes.meridionalComponents seed.state.mean n)) w := by
  rw [meridionalComponents_iterate, add_sub_cancel_left]
  unfold cycleMeanPrefix
  rw [PhysicalParticularWave.spatialCurl_finset_sum _ _ (fun k hk =>
    (cycleMeanPotential_smoothAt (p k) _ c _ ha j G hl n hw
      (ht k (Finset.mem_range.mp hk)) (hr k (Finset.mem_range.mp hk))).differentiableAt (by simp))]
  simp only [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k hk => cycleMeanPotential_curl (p k) _ c _ ha j G hl n
    (H k (Finset.mem_range.mp hk)) (hax k (Finset.mem_range.mp hk)) hw
    (ht k (Finset.mem_range.mp hk)) (hr k (Finset.mem_range.mp hk)))

end NavierStokes.ActualMeanPotentialRealization
