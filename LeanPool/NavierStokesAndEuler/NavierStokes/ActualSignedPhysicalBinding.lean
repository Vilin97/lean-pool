/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualReferenceRebase
public import LeanPool.NavierStokesAndEuler.NavierStokes.TorusMeanRequestRebase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters

@[expose] public section

/-!
# The actual signed family at its native reference bands

Each primary label retains its own prepared slow domain.  The otherwise
irrelevant band index in a physical reference is frozen at that label's
reference band.  In particular, no global ordering of a fixed native cover
above all common covers is asserted.

The request uses the actual common-reference state and its torus average.
Only the wave geometry is put in native coordinates: inverse-cover pullback
of the entire state would in general have only subcover periodicity.
-/

noncomputable section

namespace NavierStokes.ActualSignedPhysicalBinding

open Set Function Filter WeightedClasses CorrectionState TorusMeanRequestRebase
open scoped ContDiff Topology BigOperators


abbrev Point := LocalSignedRequest.Point
abbrev Cylinder := PhysicalSignedWave.Cylinder
abbrev Slow := PhaseCalculus.Slow
abbrev Plane := TorusInverse.Plane
abbrev Space := ProblemStatement.Space
abbrev Label (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

noncomputable def reference (l : Label B N0) : ℕ := BaseChartJets.cellBand l.1

noncomputable def domain (l : Label B N0) : PhaseJetBounds.Domain ℕ Slow :=
  ActualParticularStageControls.reindexDomain
    (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N) (fun _ => l.1)

noncomputable def pulse (l : Label B N0) (j : Fin 2) :
    PrimaryPulseBounds.PhaseConstruction (domain l) :=
  ActualParticularStageControls.reindexConstruction (phases B N0 j) (fun _ => l.1)

@[simp] theorem pulse_frame (l : Label B N0) (j : Fin 2) (n : ℕ) :
    (pulse l j).frame n = (phases B N0 j).frame l.1 := rfl

noncomputable def spatialLabel (l : Label B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.1) l.2

noncomputable def geometry (l : Label B N0) : CommonCoverSolve.Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

noncomputable def nativeClock (l : Label B N0) (Y : Plane) : ℝ :=
  PeriodicPhaseAssembly.periodicClock (geometry l) (clockWindow l.1).cutoff Y

/-- Native free coordinates mapped to the actual common reference lift. -/
noncomputable def toCommon (l : Label B N0) : Point ≃L[ℝ] Point :=
  (CorrectionStep.cycleAssoc.toContinuousLinearEquiv.trans
    (ActualReferenceRebase.inverseCover
      (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l)))).trans
        CorrectionStep.cycleAssoc.symm.toContinuousLinearEquiv

noncomputable def toCommonCylinder (l : Label B N0) : Cylinder ≃L[ℝ] Cylinder :=
  PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv.trans
    ((toCommon l).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp] theorem toCommon_apply (l : Label B N0) (x : Point) :
    toCommon l x = (x.1, (x.2.1,
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l))).symm x.2.2)) := rfl

@[simp] theorem toCommonCylinder_apply (l : Label B N0) (x : Cylinder) :
    toCommonCylinder l x = ((x.1.1, ((x.1.2.1.2, x.1.2.1.1),
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l))).symm x.1.2.2)), x.2) := rfl

@[simp] theorem toCommonCylinder_symm_apply (l : Label B N0) (x : Cylinder) :
    (toCommonCylinder l).symm x = ((x.1.1, ((x.1.2.1.2, x.1.2.1.1),
      CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l)) x.1.2.2)), x.2) := by
  apply (toCommonCylinder l).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, toCommonCylinder_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

noncomputable def strip (l : Label B N0) : StripData Cylinder :=
  freezeStrip (ParticularWaveBounds.reindexStrip PhysicalResidualTZ.swapCylinder
    (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal standardRegion)))
      (reference l)

noncomputable def base (l : Label B N0) : LinearWaveBounds.WaveCoefficients Cylinder :=
  freezeWave (ActualReferenceRebase.pullWave (toCommonCylinder l)
    (chartCoefficients l.2 l.1)) (reference l)

noncomputable def directions (l : Label B N0) : LinearWaveBounds.GraphDirections Cylinder :=
  freezeDirections (ActualReferenceRebase.pullDirections (toCommonCylinder l)
    (PrimaryResidualClass.directions (commonContext B))) (reference l)

/-- Actual selected primary data. Only the dummy index is repeated. -/
noncomputable def primary (l : Label B N0) : PhysicalSignedWave.PrimaryData (domain l) where
  strip := strip l
  base := base l
  directions := directions l
  pulse := pulse l
  prefactor j _ := prefactor j l.1
  coordinate _ x := ((x.1.1, x.1.2.1), nativeClock l x.1.2.2 / (phases B N0 0).L l.1)
  target _ x := fun q => PrimaryTargetBounds.actualTarget modulation (x.1.1, x.1.2.1) q
  mask _ x := spatialMask l.1 (x.1.1, x.1.2.1)
  normalMotion _ x := (phases B N0 l.2).phase.velocity l.1
    ((x.1.1, x.1.2.1), nativeClock l x.1.2.2)
  action _ x := PrimaryCopyBridge.baseOperator
    ((phases B N0 l.2).phase.F l.1 (x.1.1, x.1.2.1))
    ((phases B N0 l.2).phase.shear l.1 ((x.1.1, x.1.2.1), nativeClock l x.1.2.2))

/-- All dummy bands describe this one native physical reference. -/
noncomputable def nativeViews (l : Label B N0) : (primary l).Views (reference l) :=
  identityViews (primary l) (reference l) h (ChartScales.Q (reference l))
    (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
      (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'

@[simp] theorem nativeViews_map (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (nativeViews l).map n x = x := by
  simp [PhysicalSignedWave.PrimaryData.Views.map, nativeViews, identityViews,
    PhysicalParticularWave.cylinderChange, ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos
      _),
    CommonCoverSolve.coverPower]

@[simp] theorem nativeViews_velocity (l : Label B N0) (n : ℕ) :
    (nativeViews l).velocity n = 1 := by
  exact ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _

@[simp] theorem primary_frequency (l : Label B N0) (n : ℕ) :
    (primary l).base.frequency n = (ChartScales.carrier h (reference l) : ℝ) := rfl

@[simp] theorem primary_epsilon (l : Label B N0) (n : ℕ) :
    (primary l).strip.epsilon n = ChartScales.epsilon h (reference l) := rfl

theorem primary_matrix (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).matrix n x = covariance B N0 l.1 (x.1.1, x.1.2.1) := by
  rw [covariance_eq_integral]
  rfl

theorem native_change_cancel (l : Label B N0) (x : Cylinder) :
    PhysicalParticularWave.cylinderChange h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l))
      (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l))
      (PhysicalResidualTZ.swapCylinder (toCommonCylinder l x)) = x := by
  simp [PhysicalParticularWave.cylinderChange_apply, PhysicalParticularWave.chartChange_apply,
    toCommonCylinder, toCommon, PhysicalResidualTZ.swapCylinder_apply,
    PhysicalResidualTZ.swapSlow_apply, ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _),
    CorrectionStep.cycleAssoc, ActualReferenceRebase.inverseCover, ParticularWaveBounds.liftAssoc]

theorem primary_phase (l : Label B N0) (n : ℕ) :
    (primary l).base.phase n =
      ActualSignedGeometry.periodicPhase slots (spatialLabel l) 0
        (ChartScales.epsilon h (reference l)) ((pulse l l.2).phase.p (reference l))
        ((pulse l l.2).phase.pz (reference l)) ((pulse l l.2).phase.x0 (reference l))
        ((pulse l l.2).phase.F (reference l)) ((pulse l l.2).phase.G (reference l)) := by
  funext x
  change (chartCoefficients l.2 l.1).phase (reference l) (toCommonCylinder l x) = _
  rw [chartCoefficients_phase_view l.2 l.1 (reference l) (CommonWindow.index_le_native h _)]
  unfold ActualSignedGeometry.preparedViewPhase
  change ((ChartScales.carrier h (reference l) : ℝ) / ChartScales.carrier h (reference l)) *
    ActualSignedGeometry.preparedPhase certificate modulation slots (choice B N0).prepared l.2 l.1
      (PhysicalParticularWave.cylinderChange h (ChartScales.Q (reference l)) (ChartScales.Q
        (reference l))
        (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l))
        (PhysicalResidualTZ.swapCylinder (toCommonCylinder l x))) = _
  rw [native_change_cancel l x]
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  rw [div_self hK, one_mul]
  rfl

/-- The native record retains the exact annular domain; it is not an empty
or shrinking domain chosen to make the reference data vacuous. -/
theorem primary_domain (l : Label B N0) (x : Cylinder) :
    x ∈ (primary l).strip.domain ↔
      PhysicalResidualTZ.swapSlow x.1 ∈
        (BaseContextAssembly.nativeStrip nominal standardRegion).domain := Iff.rfl

theorem primary_time_pos (l : Label B N0) {x : Cylinder}
    (hx : x ∈ (primary l).strip.domain) : 0 < x.1.2.1.2 :=
  BaseContextAssembly.nativeStrip_time nominal standardRegion hx

theorem primary_slow_mem (l : Label B N0) {x : Cylinder}
    (hx : x ∈ (primary l).strip.domain) : (x.1.2.1.2, x.1.2.1.1) ∈ standardRegion.carrier :=
  ((BaseContextAssembly.nativeStrip_mem nominal standardRegion
    (PhysicalResidualTZ.swapSlow x.1)).mp hx).1

theorem primary_radial (l : Label B N0) (n : ℕ) :
    (primary l).directions.radialField n =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q (reference l)) h
        (ChartScales.nativeIndex h (reference l))).radial := by
  funext x
  simp only [primary, directions, freezeDirections,
    LinearWaveBounds.GraphDirections.radialField, ActualReferenceRebase.pullDirections,
    ← map_smul, ← map_add]
  change (toCommonCylinder l).symm
    ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l)
      (toCommonCylinder l x)) = _
  have hr := ActualPrimaryCoherence.chart_radial_swap B (reference l) (toCommonCylinder l x)
  apply (toCommonCylinder l).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply PhysicalResidualTZ.swapCylinder.injective
  rw [hr]
  simp [toCommonCylinder, toCommon, PhysicalResidualTZ.swapCylinder_apply,
    PhysicalResidualTZ.swapSlow_apply, CorrectionStep.cycleAssoc, ParticularWaveBounds.liftAssoc,
    ActualReferenceRebase.inverseCover, PhysicalResidualBridge.ScaledGraph.radial,
    PhysicalResidualBridge.commonGraph]
  apply (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
    CommonWindow.index h (reference l))).injective
  simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rw [show CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
      CommonWindow.index h (reference l)) PhysicalGraphBounds.radialDirection =
      ChartScales.Lambda ^ (ChartScales.nativeIndex h (reference l) - CommonWindow.index h
        (reference l)) •
        PhysicalGraphBounds.radialDirection from CommonBaseContext.coverPower_radial _,
    smul_smul]
  congr 1
  have hi := Nat.add_sub_of_le (CommonWindow.index_le_native h (reference l))
  conv_rhs => rw [← hi, pow_add]
  ring

theorem primary_angular (l : Label B N0) :
    (primary l).directions.angular = ((0, 1) : Cylinder) := by
  change (toCommonCylinder l).symm (0, 1) = _
  simp only [toCommonCylinder_symm_apply, Prod.fst_zero, Prod.snd_zero, map_zero]
  rfl

theorem primary_axial (l : Label B N0) (n : ℕ) :
    (primary l).directions.axialField (primary l).strip n =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q (reference l)) h
        (ChartScales.nativeIndex h (reference l))).axial := by
  funext x
  change (primary l).strip.epsilon n •
    (toCommonCylinder l).symm (((0, ((0, 1), 0)), 0) : Cylinder) = _
  rw [primary_epsilon, toCommonCylinder_symm_apply]
  simp [PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualBridge.commonGraph,
    ChartScales.epsilon]

theorem primary_chart (l : Label B N0) (n : ℕ) :
    PhysicalSignedWave.ChartGeometry (primary l).base (primary l).strip (primary l).directions n
      h (ChartScales.Q (reference l)) (ChartScales.nativeIndex h (reference l)) := by
  refine ⟨rfl, primary_radial l n, ?_, primary_axial l n⟩
  funext x
  exact primary_angular l

/-- The actual current common state supplies the torus-mean request. The
primitive hypotheses concern only the real local incoming fields. -/
noncomputable def nativeStateData (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (nativeViews l).StateData :=
  TorusMeanRequestRebase.stateData (primary l) (reference l) h (ChartScales.Q (reference l))
    (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
    outgoing.data.h_pos outgoing.data.h_lt_half standardRegion P (commonContext B) u H hp
    (fun _ hx => primary_slow_mem l hx)

theorem nativeStateData_referenceRequest (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) (x : Cylinder) :
    (nativeStateData l P u H hp).referenceRequest (reference l) x =
      LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
        P (2 * h) (commonContext B) u (reference l) (toCommonCylinder l x) :=
  TorusMeanRequestRebase.stateData_referenceRequest_fast (primary l) (reference l) h
    (ChartScales.Q (reference l)) (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
    outgoing.data.h_pos outgoing.data.h_lt_half standardRegion P (commonContext B) u H hp
    (fun _ hx => primary_slow_mem l hx)
    (BaseContextAssembly.nativeStrip nominal standardRegion) rfl
    (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
      CommonWindow.index h (reference l))).symm x

theorem primary_phase_affine (l : Label B N0) (n : ℕ) :
    CopyAngularInvariance.AffinePhase (0, 1)
      ((PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1 :
        ℤ) /
        (primary l).base.frequency n) ((primary l).base.phase n) := by
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  have he := PrimaryGeometryAssembly.carrier_mul_phase_p certificate modulation
    (choice B N0).prepared slots.radius_pos l.2 l.1
  have hp : (pulse l l.2).phase.p (reference l) =
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1 :
        ℝ) /
        (ChartScales.carrier h (reference l) : ℝ) := by
    apply (eq_div_iff hK).mpr
    simp only [mul_comm]
    exact he
  rw [primary_phase, primary_frequency]
  intro x t
  simp only [ActualSignedGeometry.periodicPhase, PhaseCalculus.phase,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, add_zero, smul_eq_mul, mul_one]
  rw [hp]
  ring

noncomputable def primaryAngular (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (primary l).Angular (nativeStateData l P u H hp).referenceRequest (reference l) where
  mode := PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1
  phase := primary_phase_affine l (reference l)
  coordinate := by intro x t; simp [primary]
  target := by intro x t; simp [primary]
  request := PhysicalSignedWave.stateRequest_invariant _ _ _ _ _ _
  mask := by intro x t; simp [primary]
  normalMotion := by intro x t; simp [primary]
  action := by intro x t; simp [primary]

/-! The same individual native copy as the frozen signed stage. -/

theorem label_large (l : Label B N0) : 4 ≤ (spatialLabel l).1 :=
  ActualPrimaryBounds.label_large (l.2, l.1)

noncomputable def layout (l : Label B N0) : ActualPeriodizedSignedRealization.Layout :=
  ActualSignedPhysicalData.layout slots outgoing.data.h_pos.le (spatialLabel l) (label_large l) 0

@[simp] theorem layout_geometry (l : Label B N0) (n : ℕ) :
    (layout l).geometry n = geometry l := rfl

@[simp] theorem layout_window (l : Label B N0) (n : ℕ) :
    (layout l).window n = clockWindow l.1 := rfl

@[simp] theorem pulse_length (l : Label B N0) (j : Fin 2) (n : ℕ) :
    (pulse l j).L n = ChartScales.slotLength slots.radius h (reference l) := rfl

noncomputable def nativeCopyPoint (l : Label B N0) (k : TorusInverse.Frequency)
    (x : Cylinder) : ActualSignedGeometry.Native :=
  ((x.1.1, x.1.2.1), (geometry l).coordinates k x.1.2.2)

theorem nativePoint_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.nativePoint l (reference l) k (toCommonCylinder l x) =
      nativeCopyPoint l k x := by
  apply Prod.ext
  · exact nativeSlow_toAbsolute l.1 ((toCommonCylinder l x).1)
  · change (ActualPrimary.geometry l.2 l.1).coordinates k
      ((CommonCoverSolve.coverPower (CommonWindow.index h (reference l))).symm
        ((CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
          CommonWindow.index h (reference l))).symm x.1.2.2)) = _
    rw [chartGeometry_coordinates (reference l) l.2 l.1 (CommonWindow.index_le_native h _)]
    rw [← ActualCarrierTransportBase.reference_refine l (reference l)]
    rw [CopySolveCompatibility.coordinates_refine]
    dsimp only [ActualCarrierTransportBase.gap, reference]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl

@[simp] theorem signed_coefficientScale_reference (l : Label B N0) :
    ActualSignedStageControls.coefficientScale l (reference l) = 1 := by
  unfold ActualSignedStageControls.coefficientScale
  change PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
    (ChartScales.epsilon h (reference l))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l))) = 1
  rw [show PhysicalParticularWave.velocityWeight h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l)) = 1 from
        ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _]
  simp [PhysicalSignedWave.coefficientScale, (Real.sqrt_pos.mpr (ChartScales.epsilon_pos h _)).ne']

@[simp] theorem signed_clockScale_reference (l : Label B N0) :
    ActualSignedStageControls.clockScale l (reference l) = 1 :=
  ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _

@[simp] theorem signed_normalScale_reference (l : Label B N0) :
    ActualSignedStageControls.normalScale l (reference l) = 1 := by
  unfold ActualSignedStageControls.normalScale PhysicalParticularWave.normalWeight
  change ((ChartScales.carrier h (reference l) : ℝ) / ChartScales.carrier h (reference l)) *
    PhysicalParticularWave.ratioPower (ChartScales.Q (reference l))
      (ChartScales.Q (reference l)) (1 / 2) = 1
  rw [ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _]
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  simp [hK]

theorem signed_matrix_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.matrix l k (reference l) (toCommonCylinder l x) =
      (primary l).matrix (reference l) x := by
  rw [ActualSignedStageControls.matrix, nativePoint_reference, primary_matrix]
  rfl

theorem signed_target_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.target l k (reference l) (toCommonCylinder l x) =
      (primary l).target (reference l) x := by
  rw [ActualSignedStageControls.target, signed_coefficientScale_reference, nativePoint_reference]
  simp only [one_pow, one_smul]
  rfl

theorem signed_mask_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.mask l k (reference l) (toCommonCylinder l x) =
      (primary l).mask (reference l) x := by
  rw [ActualSignedStageControls.mask, nativePoint_reference]
  rfl

theorem signed_unit_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.fundamental l k (reference l) (toCommonCylinder l x) =
      ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l)
        l.2 k (reference l) x := by
  rw [ActualSignedStageControls.fundamental, nativePoint_reference]
  simp only [ActualPeriodizedSignedRealization.nativeUnit, nativeViews_map]
  rfl

theorem signed_cutoff_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.cutoff l k (reference l) (toCommonCylinder l x) =
      PartitionedCovariance.cutoff slots.radius ((geometry l).coordinates k x.1.2.2).1 *
        (layout l).nativeGaussian (reference l) k x.1.2.2 := by
  rw [ActualSignedStageControls.cutoff, nativePoint_reference]
  rfl

theorem nativeClock_on_core (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    nativeClock l x.1.2.2 = ((geometry l).coordinates k x.1.2.2).2 := by
  exact (PeriodicPhaseAssembly.periodicClock_germ (P := Slow) (geometry l) (clockWindow l.1)
    (ActualSignedGeometry.clockWindow_injective slots vectors_det outgoing.data.h_pos.le
      (label_large l) 0) k (z := ((x.1.1, x.1.2.1), x.1.2.2)) hx).self_of_nhds

theorem signed_normalMotion_reference (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    ActualSignedStageControls.normalMotion l k (reference l) (toCommonCylinder l x) =
      (primary l).normalMotion (reference l) x := by
  rw [ActualSignedStageControls.normalMotion, signed_normalScale_reference,
    signed_clockScale_reference, nativePoint_reference]
  simp only [one_mul, one_smul]
  change _ = (phases B N0 l.2).phase.velocity l.1
    ((x.1.1, x.1.2.1), nativeClock l x.1.2.2)
  rw [nativeClock_on_core l k hx]
  rfl

theorem signed_action_reference (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    ActualSignedStageControls.action l k (reference l) (toCommonCylinder l x) =
      (primary l).action (reference l) x := by
  rw [ActualSignedStageControls.action, signed_clockScale_reference, nativePoint_reference]
  simp only [one_smul]
  change _ = PrimaryCopyBridge.baseOperator _
    ((phases B N0 l.2).phase.shear l.1 ((x.1.1, x.1.2.1), nativeClock l x.1.2.2))
  rw [nativeClock_on_core l k hx]
  rfl

/-- The lower endpoint is the integration anchor; the physical carrier
retains the individual copy midpoint. -/
theorem carrier_midpoint (l : Label B N0) (k : TorusInverse.Frequency) :
    ActualSignedPhysicalData.center (h := h) (spatialLabel l) k =
      (geometry l).center + TorusAverages.latticePoint k + slots.radius •
        ActualSignedGeometry.temporalVector :=
  ActualSignedPhysicalData.center_eq_anchor slots (spatialLabel l) 0 k

theorem primary_radial_pull (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).directions.radialField n x =
      (toCommonCylinder l).symm ((PrimaryResidualClass.directions (commonContext B)).radialField
        (reference l) (toCommonCylinder l x)) := by
  simp only [primary, directions, freezeDirections, ActualReferenceRebase.pullDirections,
    LinearWaveBounds.GraphDirections.radialField, map_add, map_smul]

theorem primary_axial_pull (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).directions.axialField (primary l).strip n x =
      (toCommonCylinder l).symm ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
          standardRegion))
          (reference l) (toCommonCylinder l x)) := by
  simp only [primary, directions, freezeDirections, ActualReferenceRebase.pullDirections,
    LinearWaveBounds.GraphDirections.axialField, map_smul]
  rfl

/-- Actual Fréchet derivatives transform with the native frame; no smoothness
of the raw phase outside its active domain is postulated. -/
theorem primary_normal_reference (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).base.normal (primary l).strip (primary l).directions n x =
      (chartCoefficients l.2 l.1).normal
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
          standardRegion))
        (PrimaryResidualClass.directions (commonContext B)) (reference l) (toCommonCylinder l x) :=
          by
  unfold LinearWaveBounds.WaveCoefficients.normal
  have he := ActualPrimaryCoherence.phaseNormal_equiv (toCommonCylinder l) one_ne_zero
    ((primary l).base.radius n) ((chartCoefficients l.2 l.1).radius (reference l))
    ((primary l).directions.radialField n) (fun _ => (primary l).directions.angular)
    ((primary l).directions.axialField (primary l).strip n)
    ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l))
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
        standardRegion))
        (reference l))
    (fun _ => by simp only [one_mul]; rfl)
    (fun y => by rw [primary_radial_pull, ContinuousLinearEquiv.apply_symm_apply, one_smul])
    (fun y => by
      change (toCommonCylinder l) ((toCommonCylinder l).symm _) = _
      exact (toCommonCylinder l).apply_symm_apply _)
    (fun y => by rw [primary_axial_pull, ContinuousLinearEquiv.apply_symm_apply, one_smul])
    1 ((chartCoefficients l.2 l.1).phase (reference l)) x
  simp only [one_mul, one_smul] at he
  exact he

theorem nativeView_base (l : Label B N0) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (primary l) (layout l)).viewBase
      (nativeViews l).background (nativeViews l).frequency
      (fun n => (nativeViews l).map n) (reference l) = (primary l).base := by
  have hK : (primary l).base.frequency (reference l) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  have hphase : (fun n x => ((primary l).base.frequency (reference l) /
      (nativeViews l).frequency n) * (primary l).base.phase (reference l) ((nativeViews l).map n
        x)) =
      (primary l).base.phase := by
    funext n x
    rw [nativeViews_map]
    change ((primary l).base.frequency (reference l) / (primary l).base.frequency (reference l)) *
      _ = _
    rw [div_self hK, one_mul]
    rfl
  change { (primary l).base with
      frequency := (nativeViews l).frequency
      phase := fun n x => ((primary l).base.frequency (reference l) / (nativeViews l).frequency n) *
        (primary l).base.phase (reference l) ((nativeViews l).map n x) } = _
  rw [hphase]
  rfl

theorem nativeViews_clock (l : Label B N0) (n : ℕ) : (nativeViews l).clock n = 1 :=
  ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _

theorem nativeViews_normal (l : Label B N0) (n : ℕ) : (nativeViews l).normal n = 1 := by
  change ActualSignedStageControls.normalScale l (reference l) = 1
  exact signed_normalScale_reference l

theorem nativeView_target (l : Label B N0) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (primary l) (layout l)).viewTarget
      (nativeViews l).strip (nativeViews l).velocity (fun n => (nativeViews l).map n) (reference l)
        =
      (primary l).target := by
  funext n x
  simp only [PhysicalSignedWave.PrimaryData.viewTarget, nativeViews_velocity, nativeViews_map]
  change PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
    (ChartScales.epsilon h (reference l)) 1 ^ 2 • (primary l).target (reference l) x = _
  have he : PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
      (ChartScales.epsilon h (reference l)) 1 = 1 := by
    unfold PhysicalSignedWave.coefficientScale
    simp [(Real.sqrt_pos.mpr (ChartScales.epsilon_pos h (reference l))).ne']
  rw [he]
  simp only [one_pow, one_smul]
  rfl

noncomputable def nativeCoefficients (l : Label B N0)
    (R : ℕ → Cylinder → SignedWaveUpdate.Vec2) (k : TorusInverse.Frequency) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients (primary l).base (primary l).strip (primary l).directions
    (primary l).matrix (primary l).target R (primary l).mask
    (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k)
    (primary l).normalMotion (primary l).action l.2

/-- The scalar and the reference copy family are definable before proving
their regularity. No proof or independently chosen request is stored. -/
noncomputable def nativeRequest (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point) : ℕ → Cylinder → SignedWaveUpdate.Vec2 :=
  PhysicalSignedWave.stateRequest (primary l).strip P h
    (freezeContext (commonContext B) (reference l)) (freezeState u (reference l))

noncomputable def nativeCopies (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point) : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  ActualSignedPhysicalData.dynamicCopyData slots outgoing.data.h_pos.le (spatialLabel l)
    (label_large l) 0 (primary l) (nativeViews l) (nativeRequest l P u) l.2

theorem nativeStateData_request_eq (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (nativeStateData l P u H hp).referenceRequest = nativeRequest l P u := rfl

theorem dynamicCoefficients_eq (l : Label B N0)
    (R : ℕ → Cylinder → SignedWaveUpdate.Vec2) (k : TorusInverse.Frequency) :
    ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l) R l.2 k =
      nativeCoefficients l R k := by
  change ActualPeriodizedSignedRealization.coefficientsWith (primary l) (layout l) (nativeViews l)
    R l.2 (ActualPeriodizedSignedRealization.sharedMask (primary l) (nativeViews l))
    (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k) = _
  unfold ActualPeriodizedSignedRealization.coefficientsWith nativeCoefficients
  rw [nativeView_base, nativeView_target]
  congr 1
  · funext n x
    simp only [nativeViews_map]
    rfl
  · funext n x
    simp only [ActualPeriodizedSignedRealization.sharedMask, nativeViews_map]
    rfl
  · funext n x
    simp only [nativeViews_normal, nativeViews_clock, nativeViews_map, one_mul, one_smul]
    rfl
  · funext n x
    simp only [nativeViews_clock, nativeViews_map, one_smul]
    rfl

section LocalizedComparison

variable (l : Label B N0) (P : SignedStressPrimitive.Patch) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

noncomputable def referenceCopies : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  ActualSignedPhysicalData.dynamicCopyData slots outgoing.data.h_pos.le (spatialLabel l)
    (label_large l) 0 (primary l) (nativeViews l) (nativeStateData l P u H hp).referenceRequest l.2

noncomputable def commonCopies : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  (ActualSignedStageControls.parameters l).copyData
    (BaseContextAssembly.nativeStrip nominal standardRegion)
    (LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
      P (2 * h) (commonContext B) u)

theorem signedVector_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    SignedWaveUpdate.signedVector
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
        standardRegion))
      (ActualSignedStageControls.matrix l k) (ActualSignedStageControls.target l k)
      (LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
        P (2 * h) (commonContext B) u)
      (ActualSignedStageControls.mask l k) (ActualSignedStageControls.fundamental l k)
      l.2 (reference l) (toCommonCylinder l x) =
    SignedWaveUpdate.signedVector (primary l).strip (primary l).matrix (primary l).target
      (nativeStateData l P u H hp).referenceRequest (primary l).mask
      (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k)
      l.2 (reference l) x := by
  unfold SignedWaveUpdate.signedVector SignedWaveUpdate.signedScalar
  rw [signed_matrix_reference, signed_target_reference, signed_mask_reference,
    signed_unit_reference, nativeStateData_referenceRequest]
  rfl

theorem raw_amplitude_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    (commonCopies l P u).amplitude (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).amplitude (reference l) k x := by
  change CurlClassBounds.complexify _ =
    (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
      (nativeStateData l P u H hp).referenceRequest l.2 k).amplitude (reference l) x
  rw [dynamicCoefficients_eq]
  exact congrArg CurlClassBounds.complexify (signedVector_reference l P u H hp k x)

theorem raw_pressure_reference (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    (commonCopies l P u).pressure (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).pressure (reference l) k x := by
  change _ = (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2 k).pressure (reference l) x
  rw [dynamicCoefficients_eq]
  dsimp only [commonCopies, CorrectionStep.PeriodizedSignedParameters.copyData,
    CorrectionStep.PeriodizedSignedParameters.native, CorrectionStep.SignedParameters.coefficients,
    ActualSignedStageControls.parameters, nativeCoefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, ParticularWaveBounds.projectedPressure,
    ActualSignedStageControls.directions]
  rw [signedVector_reference l P u H hp k x, signed_normalMotion_reference l k hx,
    signed_action_reference l k hx, ← primary_normal_reference l (reference l) x]
  rfl

theorem cutoff_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    (commonCopies l P u).cutoff (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).cutoff (reference l) k x := by
  change ActualSignedStageControls.cutoff l k (reference l) (toCommonCylinder l x) = _
  rw [signed_cutoff_reference]
  simp only [referenceCopies, ActualSignedPhysicalData.dynamicCopyData, nativeViews_map]
  rfl

theorem reference_cutoff_core (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (referenceCopies l P u H hp).cutoff (reference l) k x ≠ 0) :
    (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core := by
  have he := PrimaryCopyBounds.profile_mul_outerCutoff
    (((geometry l).coordinates k x.1.2.2).2 / ChartScales.slotLength slots.radius h (reference l))
  have hm : ActualSignedPhysicalData.nativeMask slots (spatialLabel l)
      ((geometry l).coordinates k x.1.2.2) ≠ 0 := by
    intro hm
    apply hx
    change PartitionedCovariance.cutoff slots.radius
      ((geometry l).coordinates k ((nativeViews l).map (reference l) x).1.2.2).1 *
        (layout l).nativeGaussian (reference l) k ((nativeViews l).map (reference l) x).1.2.2 = 0
    rw [nativeViews_map]
    change PartitionedCovariance.cutoff slots.radius ((geometry l).coordinates k x.1.2.2).1 *
      GaussianTailFlat.profile (((geometry l).coordinates k x.1.2.2).2 /
        ChartScales.slotLength slots.radius h (reference l)) = 0
    rw [← he, mul_comm (GaussianTailFlat.profile _), ← mul_assoc]
    change ActualSignedPhysicalData.nativeMask slots (spatialLabel l)
      ((geometry l).coordinates k x.1.2.2) * GaussianTailFlat.profile _ = 0
    rw [hm, zero_mul]
  exact ActualSignedPhysicalData.nativeMask_support slots (spatialLabel l) hm

theorem localized_amplitude_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    ((commonCopies l P u).localized k).amplitude (reference l) (toCommonCylinder l x) =
      ((referenceCopies l P u H hp).localized k).amplitude (reference l) x := by
  change (commonCopies l P u).cutoff _ _ _ • (commonCopies l P u).amplitude _ _ _ =
    (referenceCopies l P u H hp).cutoff _ _ _ • (referenceCopies l P u H hp).amplitude _ _ _
  rw [cutoff_reference, raw_amplitude_reference]

theorem localized_pressure_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    ((commonCopies l P u).localized k).pressure (reference l) (toCommonCylinder l x) =
      ((referenceCopies l P u H hp).localized k).pressure (reference l) x := by
  change ((commonCopies l P u).cutoff _ _ _ : ℂ) * (commonCopies l P u).pressure _ _ _ =
    ((referenceCopies l P u H hp).cutoff _ _ _ : ℂ) * (referenceCopies l P u H hp).pressure _ _ _
  rw [cutoff_reference]
  by_cases hc : (referenceCopies l P u H hp).cutoff (reference l) k x = 0
  · simp only [hc, Complex.ofReal_zero, zero_mul]
  · rw [raw_pressure_reference l P u H hp k (reference_cutoff_core l P u H hp k hc)]

theorem referenceCopies_eq_nativeCopies :
    referenceCopies l P u H hp = nativeCopies l P u := rfl

/-- Exact cutoff repartition into the existing compact periodized family. -/
theorem referenceCopies_localized (k : TorusInverse.Frequency) :
    (referenceCopies l P u H hp).localized k =
      (ActualPeriodizedSignedRealization.copyData (primary l) (layout l) (nativeViews l)
        (nativeStateData l P u H hp).referenceRequest l.2).localized k :=
  ActualSignedPhysicalData.dynamic_localized_eq slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2 k

theorem common_amplitude_reference (x : Cylinder) :
    (commonCopies l P u).common.amplitude (reference l) (toCommonCylinder l x) =
      (referenceCopies l P u H hp).common.amplitude (reference l) x := by
  change (∑' k, ((commonCopies l P u).localized k).amplitude (reference l) (toCommonCylinder l x)) =
    ∑' k, ((referenceCopies l P u H hp).localized k).amplitude (reference l) x
  exact tsum_congr (fun k => localized_amplitude_reference l P u H hp k x)

theorem common_pressure_reference (x : Cylinder) :
    (commonCopies l P u).common.pressure (reference l) (toCommonCylinder l x) =
      (referenceCopies l P u H hp).common.pressure (reference l) x := by
  change (∑' k, ((commonCopies l P u).localized k).pressure (reference l) (toCommonCylinder l x)) =
    ∑' k, ((referenceCopies l P u H hp).localized k).pressure (reference l) x
  exact tsum_congr (fun k => localized_pressure_reference l P u H hp k x)

theorem reference_background : (referenceCopies l P u H hp).background = (primary l).base :=
  nativeView_base l

theorem reference_common_normal :
    (referenceCopies l P u H hp).common.normal (primary l).strip (primary l).directions (reference
      l) =
      (primary l).base.normal (primary l).strip (primary l).directions (reference l) := by
  simp only [LinearWaveBounds.WaveCoefficients.normal, PeriodizedWaveBounds.CopyData.common,
    reference_background]

theorem curlCoefficient_reference (x : Cylinder) :
    CurlClassBounds.inverseCarrier ((referenceCopies l P u H hp).common.frequency (reference l)) •
      CurlClassBounds.coefficient ((referenceCopies l P u H hp).common.radius (reference l))
        ((primary l).directions.radialField (reference l)) (fun _ => (primary l).directions.angular)
        ((primary l).directions.axialField (primary l).strip (reference l))
        ((referenceCopies l P u H hp).common.phase (reference l))
        ((referenceCopies l P u H hp).common.amplitude (reference l)) x =
    CurlClassBounds.inverseCarrier ((commonCopies l P u).common.frequency (reference l)) •
      CurlClassBounds.coefficient ((commonCopies l P u).common.radius (reference l))
        ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l))
        (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
        ((PrimaryResidualClass.directions (commonContext B)).axialField
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion))
            (reference l)) ((commonCopies l P u).common.phase (reference l))
        ((commonCopies l P u).common.amplitude (reference l)) (toCommonCylinder l x) := by
  unfold CurlClassBounds.coefficient
  change CurlClassBounds.inverseCarrier _ • CurlClassBounds.normalCoefficient
    ((referenceCopies l P u H hp).common.normal (primary l).strip (primary l).directions
      (reference l) x) ((referenceCopies l P u H hp).common.amplitude (reference l) x) = _
  rw [reference_common_normal, primary_normal_reference, ← common_amplitude_reference]
  rfl

theorem reference_phase (x : Cylinder) :
    (referenceCopies l P u H hp).common.phase (reference l) x =
      (commonCopies l P u).common.phase (reference l) (toCommonCylinder l x) := by
  change (referenceCopies l P u H hp).background.phase (reference l) x = _
  rw [reference_background]
  rfl

/-- The complete oscillatory curl potential, including its carrier, is the
same native reference. -/
theorem curlPotential_reference (x : Cylinder) :
    (referenceCopies l P u H hp).common.curlPotential (primary l).strip (primary l).directions
      (reference l) x =
    (commonCopies l P u).common.curlPotential
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
        standardRegion))
      (PrimaryResidualClass.directions (commonContext B)) (reference l) (toCommonCylinder l x) := by
  funext i
  simp only [LinearWaveBounds.WaveCoefficients.curlPotential, CurlClassBounds.vectorPotential,
    HarmonicCalculus.vectorMode, HarmonicCalculus.mode]
  rw [curlCoefficient_reference]
  unfold HarmonicCalculus.carrier
  rw [reference_phase]
  rfl

theorem reference_exactCoefficients :
    (referenceCopies l P u H hp).commonCorrected (primary l).strip (primary l).directions =
      (ActualPeriodizedSignedRealization.views (primary l) (layout l) (nativeViews
        l)).exactCoefficients
        (nativeStateData l P u H hp).referenceRequest l.2 :=
  ActualSignedPhysicalData.dynamic_commonCorrected_eq slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2

end LocalizedComparison

/-! Bind to the literal request after the actual particular update. -/

noncomputable def afterParticular (x : CorrectionStep.CycleState (Label B N0)) : State Point :=
  (ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients (commonContext B)
    x.state

noncomputable def cycleStateData (l : Label B N0) (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x))
    (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure) : (nativeViews l).StateData :=
  nativeStateData l ActualInitialization.patch (afterParticular x) H hp

theorem afterParticular_pressure (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x)) :
    GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure :=
  H.pressure (g := ActualInitialization.geometry.gauge) ActualInitialization.geometry.inner_pos
    ActualInitialization.geometry.exponent_pos ActualInitialization.geometry.length_eq rfl

noncomputable def cycleStateDataOfPrimitive (l : Label B N0) (x : CorrectionStep.CycleState (Label
  B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x)) : (nativeViews
        l).StateData :=
  cycleStateData l x H (afterParticular_pressure x H)

theorem cycleStateData_request (l : Label B N0) (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x))
    (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure) (z : Cylinder) :
    (cycleStateData l x H hp).referenceRequest (reference l) z =
      (ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients
        (commonContext B) x.state (reference l) (toCommonCylinder l z) :=
  nativeStateData_referenceRequest l ActualInitialization.patch (afterParticular x) H hp z

end NavierStokes.ActualSignedPhysicalBinding
