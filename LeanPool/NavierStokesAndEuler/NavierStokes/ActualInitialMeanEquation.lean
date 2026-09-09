/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity

/-!
# The actual initialized mean equation and incompressibility

This module works with the literal initialized state before the final
initialization consumer. No `MeanHypotheses` or divergence statement is
an input.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualInitialMeanEquation

open Set Function Filter HarmonicCalculus
open CorrectionState CorrectionStep MeanIncrementBounds
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `PressureStream.Lift PressureStream.Plane`. -/
abbrev Point := PressureStream.Lift PressureStream.Plane
/-- Full: an abbreviation for `Point × ℝ`. -/
abbrev Full := Point × ℝ

/-- Strip, given by `BaseContextAssembly.nativeStrip nominal standardRegion`. -/
noncomputable def strip : WeightedClasses.StripData Point :=
  BaseContextAssembly.nativeStrip nominal standardRegion

theorem strip_to_slow {x : Point} (hx : x ∈ strip.domain) :
    x ∈ PhysicalMeanDomain.slowDomain standardRegion.carrier :=
  ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).1

theorem strip_radius {x : Point} (hx : x ∈ strip.domain) : 0 < x.1 :=
  BaseContextAssembly.nativeStrip_radius nominal standardRegion hx

theorem strip_time {x : Point} (hx : x ∈ strip.domain) : 0 < x.2.1.1 :=
  BaseContextAssembly.nativeStrip_time nominal standardRegion hx

/-! ## A reusable local mean-equation interface -/

/-- Angular regularity of the actual fields. The mean coefficients and
their pressure are supplied separately by the primitive invariant. -/
structure AngularData (V : Set Point) (u : State Point) : Prop where
  velocity_smooth : ∀ n i, ContDiffOn ℝ ∞ (fun p => u.oscillation n p i)
    (LiftedMeanResidual.cylinder V)
  pressure_smooth : ∀ n, ContDiffOn ℝ ∞ (u.oscillatoryPressure n)
    (LiftedMeanResidual.cylinder V)
  velocity_periodic : ∀ n i, LiftedMeanResidual.PeriodicOn V (fun p => u.oscillation n p i)
  pressure_periodic : ∀ n, LiftedMeanResidual.PeriodicOn V (u.oscillatoryPressure n)
  velocity_mean_zero : ∀ n x, x ∈ V → ∀ i,
    angularAverage (fun k p => u.oscillation k p i) n x = 0
  pressure_mean_zero : ∀ n x, x ∈ V → angularAverage u.oscillatoryPressure n x = 0
  base_error_continuous : ∀ n x, x ∈ V → ∀ i,
    Continuous (fun θ : ℝ => u.errors.base n (x, θ) i)
  excluded_continuous : ∀ n x, x ∈ V → ∀ i,
    Continuous (fun θ : ℝ => u.errors.total n (x, θ) i)

theorem totalVelocity_smooth_of_primitive {coord a b : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} {c : Context Point} {u : State Point}
    (HP : MeanStateRegularity.PrimitiveData U a b c u)
    {V : Set Point} (hsub : V ⊆ LocalRankDefect.positiveDomain U.carrier)
    (hw : ∀ n i, ContDiffOn ℝ ∞ (fun p => u.oscillation n p i)
      (LiftedMeanResidual.cylinder V)) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => u.totalVelocity c n p i) (LiftedMeanResidual.cylinder V) := by
  have hs : V ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun _ hx => (hsub hx).2
  have hb := LiftedMeanResidual.liftScalar_smooth (LiftedMeanResidual.tripleVector_smooth
    (GaugeDebtIncrement.smoothTriple_mono HP.base.smooth hsub) n i)
  have hm := LiftedMeanResidual.liftScalar_smooth (LiftedMeanResidual.tripleVector_smooth
    (GaugeDebtIncrement.smoothTriple_mono HP.mean.regular.smooth hs) n i)
  rw [LiftedMeanResidual.totalVelocity_eq]
  exact hb.add (hm.add (hw n i))

theorem meanHypotheses_of_primitive {coord : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {g : VariableGaugeMean.GaugeData PressureStream.Plane} {c : Context Point} {u : State Point}
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    {V : Set Point} (hV : IsOpen V) (hsub : V ⊆ LocalRankDefect.positiveDomain U.carrier)
    (HA : AngularData V u)
    (hbase : ∀ n p, p ∈ LiftedMeanResidual.cylinder V →
      LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
        (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
        (LiftedMeanResidual.axialDirection c n) (LiftedMeanResidual.baseLift c n) p = 0)
    (hdiv : ∀ n p, p ∈ LiftedMeanResidual.cylinder V → fullDivergence c u n p = 0) :
    LiftedMeanResidual.MeanHypotheses V c u := by
  have hs : V ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun _ hx => (hsub hx).2
  refine ⟨hV, ?_, ?_, HP.operators.regular.radialProfile.mono hsub,
    GaugeDebtIncrement.smoothTriple_mono HP.base.smooth hsub,
    GaugeDebtIncrement.smoothTriple_mono HP.mean.regular.smooth hs,
    fun n => ((HP.pressure ha hd hell hfixed).smooth n).mono hs,
    HA.velocity_smooth, HA.pressure_smooth, HA.velocity_periodic, HA.pressure_periodic,
    HA.velocity_mean_zero, HA.pressure_mean_zero, hbase, hdiv,
    HA.base_error_continuous, HA.excluded_continuous⟩
  · rw [HP.operators.regular.radius_eq]
    exact contDiffOn_fst
  · intro x hx
    rw [HP.operators.regular.radius_eq]
    exact (hsub hx).1.ne'

section LocalMeanStages

variable {coord : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {g : VariableGaugeMean.GaugeData PressureStream.Plane} {c : Context Point} {u : State Point}

theorem temporalIncrement_meanDivergence_zero_local
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (htime : ℝ) (index : ℕ → ℕ) (axial slowTime : PressureStream.Plane × PressureStream.Plane)
    (temporal : PressureStream.Plane)
    (hcompat : c.operators = graphOperators g.radial c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hr : x.1 ≠ 0) :
    meanDivergence c (VariableGaugeMean.temporalIncrementState g htime index axial c u) n x = 0 :=
        by
  rw [meanDivergence_eq_graph g.radial c.operators.epsilon c.operators.fastCoefficient
    axial slowTime temporal c hcompat]
  have hz := HP.axial_reconstructed ha hd hell hfixed
  exact VariableGaugeMean.temporalIncrementState_divergence_zero U g ha hd hell c u
    htime index axial n (hz.smooth n) (hz.periodic n) (hz.supported n) hx hr

theorem rankIncrement_meanDivergence_zero_local {r : RankData PressureStream.Plane}
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (axial slowTime : PressureStream.Plane × PressureStream.Plane) (temporal : PressureStream.Plane)
    (hcompat : c.operators = graphOperators g.radial c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hr : x.1 ≠ 0) :
    meanDivergence c (VariableGaugeMean.rankIncrementState g r axial c u) n x = 0 := by
  rw [meanDivergence_eq_graph g.radial c.operators.epsilon c.operators.fastCoefficient
    axial slowTime temporal c hcompat]
  have hf := MeanStageRegularity.rankDesired_moving hg hell
  simpa only [VariableGaugeMean.rankIncrementState, VariableGaugeMean.rankPotential, hell] using
    VariableGaugeMean.stream_divergence_zero U hg.primitive_inner_pos g.radial.inner_lt_outer
      hg.exponent_pos (g.radial.frequency n) g.radial.radialDirection (c.operators.epsilon n •
          axial)
      (hf.smooth n) (hf.supported n) hx hr

theorem temporalStage_fullDivergence_local
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (htime : ℝ) (index : ℕ → ℕ) (axial slowTime : PressureStream.Plane × PressureStream.Plane)
    (temporal : PressureStream.Plane)
    (hcompat : c.operators = graphOperators g.radial c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hr : x.1 ≠ 0) (θ : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) (x, θ)) :
    fullDivergence c (VariableGaugeMean.temporalStageState g htime index axial c u) n (x, θ) =
      fullDivergence c u n (x, θ) := by
  change fullDivergence c (u.addIncrement
    (VariableGaugeMean.temporalIncrementState g htime index axial c u) 0 0 0
      ⟨0, 0, VariableGaugeMean.temporalAliasState g htime index c u⟩) n (x, θ) = _
  rw [meanAddition_fullDivergence (PhysicalMeanDomain.slowDomain_open U.isOpen) c u _ _ _ _
    (MeanStageRegularity.temporalIncrement_moving HP ha hd hell hfixed htime index
        axial).regular.smooth
    n hx θ hu, temporalIncrement_meanDivergence_zero_local HP ha hd hell hfixed
      htime index axial slowTime temporal hcompat n hx hr, add_zero]

theorem rankStage_fullDivergence_local {r : RankData PressureStream.Plane}
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (axial slowTime : PressureStream.Plane × PressureStream.Plane) (temporal : PressureStream.Plane)
    (hcompat : c.operators = graphOperators g.radial c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hr : x.1 ≠ 0) (θ : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) (x, θ)) :
    fullDivergence c (VariableGaugeMean.rankStageState g r axial c u) n (x, θ) =
      fullDivergence c u n (x, θ) := by
  change fullDivergence c (u.addIncrement
    (VariableGaugeMean.rankIncrementState g r axial c u) 0 0 0 ExcludedErrors.zero) n (x, θ) = _
  rw [meanAddition_fullDivergence (PhysicalMeanDomain.slowDomain_open U.isOpen) c u _ _ _ _
    (MeanStageRegularity.rankIncrement_moving hg hell axial).regular.smooth n hx θ hu,
    rankIncrement_meanDivergence_zero_local hg hell axial slowTime temporal hcompat n hx hr,
        add_zero]

end LocalMeanStages

/-! ## First derivatives of the actual physical base -/

/-- Component divergence, given by `along Vr (fun y => a y 0) x + a x 0 / R x + along Vθ (fun y
=> a y 1) x / R x + along Vz (fun y => a y 2) x`. -/
noncomputable def componentDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E → ℝ) (Vr Vθ Vz : E → E) (a : E → Fin 3 → ℝ) (x : E) : ℝ :=
  along Vr (fun y => a y 0) x + a x 0 / R x +
    along Vθ (fun y => a y 1) x / R x + along Vz (fun y => a y 2) x

theorem componentDivergence_of_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E → ℝ) (Vr Vθ Vz : E → E) {a : E → Fin 3 → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hz : cylindricalDivergence R Vr Vθ Vz (fun y i => (a y i : ℂ)) x = 0) :
    componentDivergence R Vr Vθ Vz a x = 0 := by
  have he := congrArg Complex.re hz
  simpa only [cylindricalDivergence, along_ofReal _ (ha _), map_add, Complex.add_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.zero_re, componentDivergence, div_eq_mul_inv, mul_comm] using he

theorem componentDivergence_sum {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset ι) (R : E → ℝ) (Vr Vθ Vz : E → E) {a : ι → E → Fin 3 → ℝ} {x : E}
    (ha : ∀ j ∈ J, ∀ i, DifferentiableAt ℝ (fun y => a j y i) x) :
    componentDivergence R Vr Vθ Vz (fun y i => ∑ j ∈ J, a j y i) x =
      ∑ j ∈ J, componentDivergence R Vr Vθ Vz (a j) x := by
  simp only [componentDivergence,
    ParticularWaveAssembly.along_finset_sum J Vr (fun j y => a j y 0) (fun j hj => ha j hj 0),
    ParticularWaveAssembly.along_finset_sum J Vθ (fun j y => a j y 1) (fun j hj => ha j hj 1),
    ParticularWaveAssembly.along_finset_sum J Vz (fun j y => a j y 2) (fun j hj => ha j hj 2),
    Finset.sum_div, Finset.sum_add_distrib]

theorem componentDivergence_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (R : E → ℝ) (Vr Vθ Vz : E → E)
    {a b : E → Fin 3 → ℝ} (he : EqOn a b U) {x : E} (hx : x ∈ U) :
    componentDivergence R Vr Vθ Vz a x = componentDivergence R Vr Vθ Vz b x := by
  have hd (V : E → E) (i : Fin 3) :=
    along_congr (V := V) hU (fun y hy => congrFun (he hy) i) hx
  simp only [componentDivergence, hd, he hx]

theorem componentDivergence_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} {U : Set F} {Γ : E → F} {l v : ℝ}
    {R : F → ℝ} {Vr Vθ Vz Vt : F → F} {Sr Sθ Sz St : E → E} {r : E → ℝ}
    (G : PhysicalResidualBridge.PullbackData Ω U Γ l v R Vr Vθ Vz Vt Sr Sθ Sz St r)
    (hl : l ≠ 0) {a : F → Fin 3 → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U) {x : E} (hx : x ∈ Ω) (hr : r x ≠ 0) :
    componentDivergence r Sr Sθ Sz (fun y i => v * a (Γ y) i) x =
      v * l * componentDivergence R Vr Vθ Vz a (Γ x) := by
  have hΓ := (G.smooth.contDiffAt (G.source_open.mem_nhds hx)).differentiableAt (by simp)
  have hd i := ((ha i).contDiffAt (G.target_open.mem_nhds (G.mapsTo hx))).differentiableAt (by simp)
  have ht : fderiv ℝ Γ x (Sθ x) = (1 : ℝ) • Vθ (Γ x) := by
    simpa only [one_smul] using G.angular x hx
  simp only [componentDivergence,
    PhysicalResidualBridge.along_scaled_pull v l hΓ (hd 0) (G.radial x hx),
    PhysicalResidualBridge.along_scaled_pull v 1 hΓ (hd 1) ht,
    PhysicalResidualBridge.along_scaled_pull v l hΓ (hd 2) (G.axial x hx), G.radius x hx]
  field_simp [hl, hr]

theorem coordinate_divergence_eq {a : ProblemStatement.SpaceTime → ProblemStatement.Space}
    {t : ℝ} {q : ProblemStatement.Space} (ha : DifferentiableAt ℝ a (t, q)) :
    componentDivergence LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (fun z i => a z i) (t,q) =
      CylindricalResidual.vectorDivergence (fun y => a (t,y)) q := by
  have hs := ha.comp q (differentiableAt_const t |>.prodMk differentiableAt_id)
  have hd (i j : Fin 3) :
      along (LinearWaveResidual.spaceDirection i) (fun z => a z j) (t,q) =
        CylindricalResidual.dCoord i (fun y => a (t,y)) q j := by
    have hc : DifferentiableAt ℝ (fun z => a z j) (t,q) := by
      simpa only [Function.comp_def, AxisymmetricFields.projection_apply] using
        ((AxisymmetricFields.projection j).differentiableAt.comp (t,q) ha)
    rw [LinearWaveResidual.along_space_slice hc]
    exact CylindricalResidual.dCoord_map (AxisymmetricFields.projection j) hs i
  simp only [componentDivergence, hd, LinearWaveResidual.coordinateRadius,
    CylindricalResidual.vectorDivergence]

theorem radialDirection_match {c : Context Point} {G : PhysicalResidualBridge.ScaledGraph} {n : ℕ}
    (H : PhysicalResidualTZ.MatchesAtTZ c.operators G n) :
    LiftedMeanResidual.radialDirection c n = PhysicalResidualTZ.graphRadialTZ G := by
  funext x
  simp [LiftedMeanResidual.radialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.radialVector, H.eR, H.frequency, H.profile, H.vR,
    PhysicalResidualTZ.graphRadialTZ_eq, PhysicalResidualBridge.ScaledGraph.radial]
  rfl

theorem axialDirection_match {c : Context Point} {G : PhysicalResidualBridge.ScaledGraph} {n : ℕ}
    (H : PhysicalResidualTZ.MatchesAtTZ c.operators G n) :
    LiftedMeanResidual.axialDirection c n = PhysicalResidualTZ.graphAxialTZ G := by
  funext x
  simp [LiftedMeanResidual.axialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.axialVector, H.epsilon, H.eZ, PhysicalResidualTZ.graphAxialTZ_apply]

theorem scaled_base_divergence (B n : ℕ) {x : Full} (hx : x ∈ ActualBaseResidual.domain) :
    componentDivergence PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualTZ.graphRadialTZ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (CorrectionInitialization.CommonWindow.index h n))) PhysicalResidualTZ.graphAngularTZ
      (PhysicalResidualTZ.graphAxialTZ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (CorrectionInitialization.CommonWindow.index h n)))
      (ActualBaseResidual.velocityAtScale certificate modulation upper B (ChartScales.Q n)) x = 0
          := by
  let a : ProblemStatement.SpaceTime → ProblemStatement.Space :=
    CylindricalResidual.velocityComponents (FinalSlowBase.velocity certificate modulation upper B)
  have ha : ContDiffOn ℝ ∞ a BaseResidual.past :=
    ActualBaseResidual.velocityComponents_smooth (FinalSlowBase.velocity_smooth certificate
        modulation upper B)
  have hac (i : Fin 3) : ContDiffOn ℝ ∞ (fun z => a z i) BaseResidual.past := by
    simpa only [Function.comp_def, AxisymmetricFields.projection_apply] using
      (AxisymmetricFields.projection i).contDiff.comp_contDiffOn ha
  have hs := componentDivergence_pullback
    (ActualBaseResidual.cylinderPullback (ChartScales.Q_pos n) h
      (CorrectionInitialization.CommonWindow.index h n)) (Real.sqrt_pos.2 (ChartScales.Q_pos n)).ne'
    hac hx hx.1.ne'
  have ht : (ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).1 < 1 :=
    ActualBaseResidual.physicalPoint_time (h := h) (ChartScales.Q_pos n) hx.2
  have hq : 0 < (ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).2 0 := by
    simpa only [ActualBaseResidual.cylinderPoint, AxisymmetricResidual.pack_zero] using
      mul_pos (Real.sqrt_pos.2 (ChartScales.Q_pos n)) hx.1
  have hda := (ha.contDiffAt (BaseResidual.past_isOpen.mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt
      (by
      simp)
  have hmem :
      ((ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).1,
        CylindricalResidual.chart (ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).2) ∈
        BaseResidual.past := ⟨ht, mem_univ _⟩
  have hu : DifferentiableAt ℝ (FinalSlowBase.velocity certificate modulation upper B)
      ((ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).1,
        CylindricalResidual.chart (ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x).2) :=
    ((FinalSlowBase.velocity_smooth certificate modulation upper B).contDiffAt
    (BaseResidual.past_isOpen.mem_nhds hmem)).differentiableAt (by simp)
  have hv : componentDivergence LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (fun z i => a z i)
      (ActualBaseResidual.cylinderPoint h (ChartScales.Q n) x) = 0 := by
    exact (coordinate_divergence_eq hda).trans ((CylindricalResidual.divergence_cylindrical
      (hu.comp _ (differentiableAt_const _ |>.prodMk differentiableAt_id)) hq).symm.trans
      (FinalSlowBase.divergence_zero certificate modulation upper B ht _))
  rw [hv, mul_zero] at hs
  simp only [a,
    CylindricalResidual.velocityComponents, CylindricalResidual.components,
    ActualBaseResidual.cylinderPoint, AxisymmetricResidual.pack_one] at hs ⊢
  exact hs

theorem base_divergence (B n : ℕ) {x : Full} (hx : x ∈ LiftedMeanResidual.cylinder strip.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar (commonContext
        B).operators.radius)
      (LiftedMeanResidual.radialDirection (commonContext B) n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection (commonContext B) n)
      (LiftedMeanResidual.baseLift (commonContext B) n) x = 0 := by
  have hx' : x ∈ ActualBaseResidual.domain := ⟨strip_radius hx.1, strip_time hx.1⟩
  have he := componentDivergence_congr ActualBaseResidual.domain_open
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualTZ.graphRadialTZ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
      (CorrectionInitialization.CommonWindow.index h n))) PhysicalResidualTZ.graphAngularTZ
    (PhysicalResidualTZ.graphAxialTZ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
      (CorrectionInitialization.CommonWindow.index h n)))
    (fun y hy => ActualBaseResidual.velocityAtScale_eq_baseComponents certificate modulation upper B
      (CorrectionInitialization.CommonWindow.index h) n hy) hx'
  have hz := scaled_base_divergence B n hx'
  rw [he] at hz
  have HM : PhysicalResidualTZ.MatchesAtTZ (commonContext B).operators
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (CorrectionInitialization.CommonWindow.index h n)) n :=
    CommonBaseContext.operators_match_physical h (CorrectionInitialization.CommonWindow.index h)
      (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
      (PrimaryTargetBounds.radii_ordered nominal) n
  rw [radialDirection_match HM, axialDirection_match HM]
  exact hz

/-! ## The actual primary sum is divergence free -/

theorem strip_to_positive {x : Point} (hx : x ∈ strip.domain) :
    x ∈ LocalRankDefect.positiveDomain standardRegion.carrier :=
  ⟨strip_radius hx, strip_to_slow hx⟩

theorem piece_divergence {B N0 : ℕ} (l : Label B N0 × Fin 2) (n : ℕ) {x : Full}
    (hx : x ∈ ActualPrimaryCoherence.positiveRadialChart) :
    componentDivergence (fun y : Full => y.1.1)
      (LiftedMeanResidual.radialDirection (commonContext B) n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection (commonContext B) n)
      ((ActualInitialCoherence.pieces B N0 l).velocity n) x = 0 := by
  have hv (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (ActualInitialCoherence.pieces B N0 l).velocity n y i) x :=
    ((contDiffOn_pi.mp (ActualPrimaryCoherence.piece_velocity_smooth standardRegion l.2 l.1 n)
        i).contDiffAt
      (ActualPrimaryCoherence.positiveChart_open.mem_nhds hx.2)).differentiableAt (by simp)
  have hz := ActualPrimaryCoherence.piece_full_divergence standardRegion l.2 l.1 n hx
  have hr : (PrimaryResidualClass.directions (commonContext B)).radialField n =
      LiftedMeanResidual.radialDirection (commonContext B) n := by
    funext y
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.radialField,
      LiftedMeanResidual.radialDirection, LiftedMeanResidual.radialVector,
      LiftedMeanResidual.liftDirection, smul_smul]
  have hzz : (PrimaryResidualClass.directions (commonContext B)).axialField
      (piece standardRegion l.2 l.1).strip n =
        LiftedMeanResidual.axialDirection (commonContext B) n := by
    funext y
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.axialField,
      LiftedMeanResidual.axialDirection, LiftedMeanResidual.axialVector,
      LiftedMeanResidual.liftDirection]
    rfl
  rw [hr, hzz] at hz
  exact componentDivergence_of_complex _ _ _ _ hv hz

theorem seed_oscillation_divergence (B N0 n : ℕ) {x : Full}
    (hx : x ∈ LiftedMeanResidual.cylinder strip.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar (commonContext
        B).operators.radius)
      (LiftedMeanResidual.radialDirection (commonContext B) n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection (commonContext B) n)
      ((ActualInitialCoherence.seed B N0).oscillation n) x = 0 := by
  change componentDivergence (fun y : Full => y.1.1) _ _ _
    (fun y i => ∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).velocity n y i) x = 0
  rw [componentDivergence_sum _ _ _ _ _ (fun l _ i =>
    ((contDiffOn_pi.mp (ActualPrimaryCoherence.piece_velocity_smooth standardRegion l.2 l.1 n)
        i).contDiffAt
      (ActualPrimaryCoherence.positiveChart_open.mem_nhds (strip_time hx.1))).differentiableAt (by
          simp))]
  exact Finset.sum_eq_zero (fun l _ => piece_divergence l n ⟨strip_radius hx.1, strip_time hx.1⟩)

theorem primary_oscillation (B N0 : ℕ) :
    (ActualInitialCoherence.primary B N0).oscillation =
      (ActualInitialCoherence.seed B N0).oscillation := rfl

theorem temporal_oscillation (B N0 : ℕ) :
    (ActualInitialCoherence.temporal B N0).oscillation =
      (ActualInitialCoherence.seed B N0).oscillation := by
  change (ActualInitialCoherence.seed B N0).oscillation + 0 = _
  exact add_zero _

theorem initialized_oscillation (B N0 : ℕ) :
    (ActualInitialCoherence.initialized B N0).oscillation =
      (ActualInitialCoherence.seed B N0).oscillation :=
  CorrectionInitialization.GaugeInitialization.initializedBands_oscillation _ _ _ _ _ _ _ _ _

theorem primary_fullDivergence (B N0 n : ℕ) {x : Full}
    (hx : x ∈ LiftedMeanResidual.cylinder strip.domain) :
    fullDivergence (commonContext B) (ActualInitialCoherence.primary B N0) n x = 0 := by
  have he : (ActualInitialCoherence.primary B N0).totalVelocity (commonContext B) n =
      fun y => LiftedMeanResidual.baseLift (commonContext B) n y +
        (ActualInitialCoherence.seed B N0).oscillation n y := by
    funext y i
    fin_cases i <;> simp [State.totalVelocity, ActualInitialCoherence.primary,
      CorrectionInitialization.GaugeInitialization.primaryBands, VariableGaugeMean.reconstructState,
      ActualInitialCoherence.seed, CorrectionInitialization.bandSeed, LiftedMeanResidual.baseLift,
      LiftedMeanResidual.tripleVector, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hb (i : Fin 3) := (LiftedMeanResidual.liftScalar_smooth
    (LiftedMeanResidual.tripleVector_smooth (GaugeDebtIncrement.smoothTriple_mono
      (ActualInitialCoherence.common_base_data B).smooth (fun _ hx => strip_to_positive hx)) n i))
  have hw (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (ActualInitialCoherence.seed B N0).oscillation n y i)
        (LiftedMeanResidual.cylinder strip.domain) :=
    (ActualInitialCoherence.seed_smooth B N0 n i).mono
      (fun _ hy => ⟨strip_to_slow hy.1, hy.2⟩)
  unfold fullDivergence
  rw [he, LiftedMeanResidual.realDivergence_add _ _ _ _
    (a := LiftedMeanResidual.baseLift (commonContext B) n)
    (b := (ActualInitialCoherence.seed B N0).oscillation n)
    (fun i => ((hb i).contDiffAt ((LiftedMeanResidual.cylinder_open strip.isOpen_domain).mem_nhds
        hx)).differentiableAt (by
        simp))
    (fun i => ((hw i).contDiffAt ((LiftedMeanResidual.cylinder_open strip.isOpen_domain).mem_nhds
        hx)).differentiableAt (by
        simp))]
  exact (congrArg₂ (fun a b : ℝ => a + b) (base_divergence B n hx)
    (seed_oscillation_divergence B N0 n hx)).trans (zero_add 0)

theorem common_graphOperators (B : ℕ) :
    (commonContext B).operators = graphOperators commonGauge.radial
      (commonContext B).operators.epsilon (commonContext B).operators.fastCoefficient
      ((0,1),0) ((1,0),0) (TorusInverse.vector .temporal) := rfl

theorem initialized_fullDivergence (B N0 n : ℕ) {x : Full}
    (hx : x ∈ LiftedMeanResidual.cylinder strip.domain) :
    fullDivergence (commonContext B) (ActualInitialCoherence.initialized B N0) n x = 0 := by
  have hw : ∀ n i, ContDiffOn ℝ ∞
      (fun p => (ActualInitialCoherence.seed B N0).oscillation n p i)
        (LiftedMeanResidual.cylinder strip.domain) :=
    fun n i => (ActualInitialCoherence.seed_smooth B N0 n i).mono
      (fun _ hy => ⟨strip_to_slow hy.1, hy.2⟩)
  have hp := totalVelocity_smooth_of_primitive (ActualInitialCoherence.primary_primitive B N0)
    (fun _ hy => strip_to_positive hy) hw
  have ht := totalVelocity_smooth_of_primitive (ActualInitialCoherence.temporal_primitive B N0)
    (fun _ hy => strip_to_positive hy) (by simpa only [temporal_oscillation] using hw)
  have hm := temporalStage_fullDivergence_local (ActualInitialCoherence.primary_primitive B N0)
    (PrimaryTargetBounds.leftRadius_pos nominal) (ChartScales.radialExponent_pos h
        outgoing.data.h_pos.le)
    commonGauge_length rfl h (CorrectionInitialization.CommonWindow.index h) ((0,1),0) ((1,0),0)
    (TorusInverse.vector .temporal) (common_graphOperators B) n (strip_to_slow hx.1)
    (strip_radius hx.1).ne' x.2
    (fun i => ((hp n i).contDiffAt ((LiftedMeanResidual.cylinder_open strip.isOpen_domain).mem_nhds
        hx)).differentiableAt (by
        simp))
  have hr := rankStage_fullDivergence_local (ActualInitialCoherence.rank_geometry_of_primitive B _
    (ActualInitialCoherence.temporal_primitive B N0)) commonGauge_length ((0,1),0) ((1,0),0)
    (TorusInverse.vector .temporal) (common_graphOperators B) n (strip_to_slow hx.1)
    (strip_radius hx.1).ne' x.2
    (fun i => ((ht n i).contDiffAt ((LiftedMeanResidual.cylinder_open strip.isOpen_domain).mem_nhds
        hx)).differentiableAt (by
        simp))
  exact hr.trans (hm.trans (primary_fullDivergence B N0 n hx))

/-! ## Literal angular harmonics and the retained errors -/

section Angular

variable {B N0 : ℕ}

theorem piece_velocity_angularContinuous (l : Label B N0 × Fin 2) (n : ℕ)
    (x : Point) (i : Fin 3) :
    Continuous (fun θ : ℝ => (ActualInitialCoherence.pieces B N0 l).velocity n (x, θ) i) := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).1]
  exact Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)

theorem piece_pressure_angularContinuous (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) :
    Continuous (fun θ : ℝ => (ActualInitialCoherence.pieces B N0 l).pressure n (x, θ)) := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).2]
  exact Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)

theorem piece_excluded_angularContinuous (l : Label B N0 × Fin 2) (n : ℕ)
    (x : Point) (i : Fin 3) :
    Continuous (fun θ : ℝ => (ActualInitialCoherence.pieces B N0 l).excluded n (x, θ) i) := by
  rw [← ActualInitialCoherence.gaussianBlock_represents l]
  exact Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)

theorem piece_velocity_angularPeriodic (l : Label B N0 × Fin 2) (n : ℕ)
    (x : Point) (i : Fin 3) :
    Function.Periodic (fun θ : ℝ => (ActualInitialCoherence.pieces B N0 l).velocity n (x, θ) i)
      (2 * Real.pi) := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).1]
  intro θ
  exact congrArg Complex.re (HarmonicFields.field_angular_periodic _ _ _ _ _ θ)

theorem piece_pressure_angularPeriodic (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) :
    Function.Periodic (fun θ : ℝ => (ActualInitialCoherence.pieces B N0 l).pressure n (x, θ))
      (2 * Real.pi) := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).2]
  intro θ
  exact congrArg Complex.re (HarmonicFields.field_angular_periodic _ _ _ _ _ θ)

private theorem conjugatePair_zero (a : Point → ℂ) (x : Point) :
    ErrorHarmonics.conjugatePair 1 a 0 x = 0 := by
  classical
  change Finsupp.single (1 : ℤ) (fun y => a y / 2) 0 x +
    (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => a y / 2) 0 x) = 0
  simp

theorem piece_velocity_mean_zero (l : Label B N0 × Fin 2) (n : ℕ)
    (x : Point) (i : Fin 3) :
    angularAverage (fun k p => (ActualInitialCoherence.pieces B N0 l).velocity k p i) n x = 0 := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).1]
  change HarmonicResidual.realAngularMean (fun θ =>
    (HarmonicFields.field ((ActualInitialCoherence.primaryBlock l).velocity n i)
      ((ActualInitialCoherence.primaryBlock l).frequency n)
      ((ActualInitialCoherence.primaryBlock l).phase n)
      ((ActualInitialCoherence.primaryBlock l).angularFrequency n) (x, θ)).re) = 0
  trans (((ActualInitialCoherence.primaryBlock l).velocity n i) 0 x).re
  · exact HarmonicResidual.realAngularMean_field _ _ _ (ActualInitialCoherence.angularMode_ne l n) x
  · simp [ActualInitialCoherence.primaryBlock, CorrectionInitialization.PrimaryPiece.harmonicBlock,
      CorrectionInitialization.PrimaryHarmonics.block, conjugatePair_zero]

theorem piece_pressure_mean_zero (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) :
    angularAverage (ActualInitialCoherence.pieces B N0 l).pressure n x = 0 := by
  rw [← (ActualInitialCoherence.primaryBlock_represents l).2]
  change HarmonicResidual.realAngularMean (fun θ =>
    (HarmonicFields.field ((ActualInitialCoherence.primaryBlock l).pressure n)
      ((ActualInitialCoherence.primaryBlock l).frequency n)
      ((ActualInitialCoherence.primaryBlock l).phase n)
      ((ActualInitialCoherence.primaryBlock l).angularFrequency n) (x, θ)).re) = 0
  trans (((ActualInitialCoherence.primaryBlock l).pressure n) 0 x).re
  · exact HarmonicResidual.realAngularMean_field _ _ _ (ActualInitialCoherence.angularMode_ne l n) x
  · simp [ActualInitialCoherence.primaryBlock, CorrectionInitialization.PrimaryPiece.harmonicBlock,
      CorrectionInitialization.PrimaryHarmonics.block, conjugatePair_zero]

end Angular

theorem seed_velocity_mean_zero (B N0 n : ℕ) (x : Point) (i : Fin 3) :
    angularAverage (fun k p => (ActualInitialCoherence.seed B N0).oscillation k p i) n x = 0 := by
  change HarmonicResidual.realAngularMean (fun θ =>
    ∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).velocity n (x, θ) i) = 0
  rw [HarmonicResidual.realAngularMean_sum _ _
    (fun l _ => piece_velocity_angularContinuous l n x i)]
  exact Finset.sum_eq_zero (fun l _ => piece_velocity_mean_zero l n x i)

theorem seed_pressure_mean_zero (B N0 n : ℕ) (x : Point) :
    angularAverage (ActualInitialCoherence.seed B N0).oscillatoryPressure n x = 0 := by
  change HarmonicResidual.realAngularMean (fun θ =>
    ∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).pressure n (x, θ)) = 0
  rw [HarmonicResidual.realAngularMean_sum _ _
    (fun l _ => piece_pressure_angularContinuous l n x)]
  exact Finset.sum_eq_zero (fun l _ => piece_pressure_mean_zero l n x)

theorem initialized_oscillatoryPressure (B N0 : ℕ) :
    (ActualInitialCoherence.initialized B N0).oscillatoryPressure =
      (ActualInitialCoherence.seed B N0).oscillatoryPressure := by
  change ((ActualInitialCoherence.seed B N0).oscillatoryPressure + 0) + 0 = _
  simp only [add_zero]

theorem initialized_errors_angularContinuous (B N0 n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (i : Fin 3) :
    Continuous (fun θ : ℝ => (ActualInitialCoherence.initialized B N0).errors.base n (x, θ) i) ∧
      Continuous (fun θ : ℝ => (ActualInitialCoherence.initialized B N0).errors.total n (x, θ) i)
          := by
  obtain ⟨hb, hg, ha⟩ :=
      CorrectionInitialization.GaugeInitialization.initializedBands_error_components
    commonGauge rankData h (CorrectionInitialization.CommonWindow.index h) ((0,1),0) (commonContext
        B)
    (activeLabels standardRegion B N0) (ActualInitialCoherence.pieces B N0)
        (ActualInitialCoherence.baseError B)
  change (ActualInitialCoherence.initialized B N0).errors.base = _ at hb
  change (ActualInitialCoherence.initialized B N0).errors.gaussian = _ at hg
  change (ActualInitialCoherence.initialized B N0).errors.aliasError = _ at ha
  have hbc : Continuous (fun θ : ℝ => (ActualInitialCoherence.initialized B N0).errors.base n (x,
      θ) i) := by
    rw [hb]
    exact ActualBaseResidual.baseError_angular_continuous certificate modulation upper B n hT i
  have hgc : Continuous (fun θ : ℝ => (ActualInitialCoherence.initialized B N0).errors.gaussian n
      (x, θ) i) := by
    rw [hg]
    exact continuous_finsetSum _ (fun l _ => piece_excluded_angularContinuous l n x i)
  have hac : Continuous (fun θ : ℝ => (ActualInitialCoherence.initialized B N0).errors.aliasError n
      (x, θ) i) := by
    rw [ha]
    change Continuous (fun _ : ℝ =>
      VariableGaugeMean.temporalAliasState commonGauge h
          (CorrectionInitialization.CommonWindow.index h)
        (commonContext B) (ActualInitialCoherence.primary B N0) n (x, 0) i +
      VariableGaugeMean.pressureAliasState commonGauge (commonContext B)
        (ActualInitialCoherence.ranked B N0) n (x, 0) i)
    exact continuous_const
  exact ⟨hbc, (hbc.add hgc).add hac⟩

theorem initialized_angularData (B N0 : ℕ) :
    AngularData strip.domain (ActualInitialCoherence.initialized B N0) where
  velocity_smooth n i := by
    rw [initialized_oscillation]
    exact (ActualInitialCoherence.seed_smooth B N0 n i).mono
      (fun _ hx => ⟨strip_to_slow hx.1, hx.2⟩)
  pressure_smooth n := by
    rw [initialized_oscillatoryPressure]
    change ContDiffOn ℝ ∞ (fun p => ∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).pressure n p) (LiftedMeanResidual.cylinder
          strip.domain)
    apply ContDiffOn.sum
    intro l _
    exact (ActualPrimaryCoherence.piece_pressure_smooth standardRegion l.2 l.1 n).mono
      (fun _ hx => strip_time hx.1)
  velocity_periodic n i := by
    rw [initialized_oscillation]
    intro x _ θ
    change (∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).velocity n (x, θ + 2 * Real.pi) i) =
        ∑ l ∈ activeLabels standardRegion B N0 n,
          (ActualInitialCoherence.pieces B N0 l).velocity n (x, θ) i
    exact Finset.sum_congr rfl (fun l _ => piece_velocity_angularPeriodic l n x i θ)
  pressure_periodic n := by
    rw [initialized_oscillatoryPressure]
    intro x _ θ
    change (∑ l ∈ activeLabels standardRegion B N0 n,
      (ActualInitialCoherence.pieces B N0 l).pressure n (x, θ + 2 * Real.pi)) =
        ∑ l ∈ activeLabels standardRegion B N0 n,
          (ActualInitialCoherence.pieces B N0 l).pressure n (x, θ)
    exact Finset.sum_congr rfl (fun l _ => piece_pressure_angularPeriodic l n x θ)
  velocity_mean_zero n x _ i := by
    rw [initialized_oscillation]
    exact seed_velocity_mean_zero B N0 n x i
  pressure_mean_zero n x _ := by
    rw [initialized_oscillatoryPressure]
    exact seed_pressure_mean_zero B N0 n x
  base_error_continuous n x hx i := (initialized_errors_angularContinuous B N0 n (strip_time hx)
      i).1
  excluded_continuous n x hx i := (initialized_errors_angularContinuous B N0 n (strip_time hx) i).2

/-- The literal initializer satisfies the local hypotheses of the
nonlinear angular-mean identity. No PDE or divergence premise is supplied. -/
theorem initialized_meanHypotheses (B N0 : ℕ) :
    LiftedMeanResidual.MeanHypotheses strip.domain (commonContext B)
      (ActualInitialCoherence.initialized B N0) :=
  meanHypotheses_of_primitive (g := commonGauge) (ActualInitialCoherence.initialized_primitive B N0)
    (PrimaryTargetBounds.leftRadius_pos nominal) (ChartScales.radialExponent_pos h
        outgoing.data.h_pos.le)
    commonGauge_length rfl strip.isOpen_domain (fun _ hx => strip_to_positive hx)
    (initialized_angularData B N0) (fun n _ hx => base_divergence B n hx)
    (fun n _ hx => initialized_fullDivergence B N0 n hx)

/-- Exact mean equation, with the same Gaussian and alias errors retained
by `initializedBands`. -/
theorem initialized_angularMean_fullGoodResidual (B N0 n : ℕ) {x : Point}
    (hx : x ∈ strip.domain) (i : Fin 3) :
    angularMeanVector (fullGoodResidual (commonContext B) (ActualInitialCoherence.initialized B
        N0)) n x i =
      (ActualInitialCoherence.initialized B N0).meanGoodResidual (commonContext B) n x i :=
  LiftedMeanResidual.angularMean_fullGoodResidual (initialized_meanHypotheses B N0) n hx i

end NavierStokes.ActualInitialMeanEquation
