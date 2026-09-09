/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualReferenceRebase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianErrorNaturality
public import LeanPool.NavierStokesAndEuler.NavierStokes.CycleStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.IntervalCopyTransport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCopySliceRegularity

@[expose] public section

/-!
# Coherence of the actual particular increment

The source is the residual of the current state.  Its reference value is
rebased to the native cover before solving.  The identities below retain the
full auxiliary fibers and the differentiated copy cutoffs.
-/

noncomputable section

namespace NavierStokes.ActualParticularCoherence

open Set Function Filter WeightedClasses CorrectionState HarmonicCalculus
open CommonCoverSolve TorusInverse PhysicalParticularWave
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology BigOperators


variable {B N0 : ℕ}

abbrev Label := ActualParticularStageControls.Label

/-- The unchanged current-state copy construction. -/
noncomputable def copyData (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) : PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (ActualParticularStageControls.parameters x l).copyData
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j

noncomputable def corrected (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) : LinearWaveBounds.WaveCoefficients WaveSpace :=
  ActualParticularRealization.corrected (ActualParticularStageControls.assembly x l)
    ActualParticularStageControls.associatedStrip h (ActualParticularStageControls.gap l) j

noncomputable def cylinderParameter (z : Cylinder) : Parameter := (waveEquiv z).1.1

noncomputable def cylinderDomain (V : Set Plane) : Set Cylinder :=
  {z | (cylinderParameter z).2 ∈ V}

theorem cylinderDomain_open {V : Set Plane} (hV : IsOpen V) : IsOpen (cylinderDomain V) :=
  hV.preimage waveEquiv.continuous.fst.fst.snd

/-- The target operator is the literal common-cover graph at the target
band.  This identification is independent of the current source. -/
theorem targetChart (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    ActualParticularRealization.TargetChart (ActualParticularStageControls.assembly x l)
      ActualParticularStageControls.associatedStrip h n (CommonWindow.index h n) := by
  constructor
  · rfl
  · funext z
    apply waveEquiv.injective
    change (ActualParticularStageControls.directions (B := B)).radialField n (waveEquiv z) = _
    rw [ActualReferenceRebase.associatedDirections_radial,
      ActualReferenceRebase.associatedContext_frame]
    rfl
  · rfl
  · funext z
    apply waveEquiv.injective
    change (ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
        ActualParticularStageControls.associatedStrip)
        n (waveEquiv z) = _
    rw [ActualReferenceRebase.associatedDirections_axial,
      ActualReferenceRebase.associatedContext_frame]
    rfl

theorem corrected_amplitude_chart (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    (fun z => (corrected x l j).amplitude n (waveEquiv z)) =
      CurlClassBounds.realizedCoefficient ((j : ℝ) * (x.coefficients.blocks l).frequency n)
        PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (fun z => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv z))
        (fun z => (ActualReferenceRebase.actualCoefficients x l j).amplitude n (waveEquiv z)) := by
  have hp := ActualParticularRealization.realizedCoefficient_pull waveEquiv
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    ((ActualParticularStageControls.assembly x l).background.radius n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
    ((ActualParticularStageControls.assembly x l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.assembly x l).directions.angular)
    ((ActualParticularStageControls.assembly x l).directions.axialField
      (CorrectionStep.ParticularParameters.nativeStrip
        ActualParticularStageControls.associatedStrip) n)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude n)
  rw [(targetChart x l n).radius, (targetChart x l n).radial,
    (targetChart x l n).angular, (targetChart x l n).axial] at hp
  exact hp.symm

/-- Local agreement of the two primitive inputs propagates through the
entire curl correction, including all cutoff derivatives. -/
theorem corrected_eq_band_of_germs (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) (z : Cylinder)
    (ha : (fun y => (ActualReferenceRebase.actualCoefficients x l j).amplitude n (waveEquiv y))
      =ᶠ[𝓝 z] bandRaw (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j)
    (hphi : (fun y => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv y))
      =ᶠ[𝓝 z] bandPhase (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j) :
    vectorMode ((corrected x l j).frequency n) ((corrected x l j).phase n)
      ((corrected x l j).amplitude n) (waveEquiv z) =
      bandVelocity (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (CommonWindow.index h n)
        (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j z := by
  have hg := ParticularWaveAssembly.realizedCoefficient_germ ha
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (fun y => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv y))
  have hq := ActualParticularRealization.realizedCoefficient_phase_germ hphi
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (bandRaw (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
      (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) j)
  have hv := congrFun (corrected_amplitude_chart x l j n) z
  rw [(hg.trans hq).eq_of_nhds] at hv
  funext i
  change (corrected x l j).amplitude n (waveEquiv z) i *
    carrier ((j : ℝ) * (x.coefficients.blocks l).frequency n)
      ((ActualReferenceRebase.actualCoefficients x l j).phase n) (waveEquiv z) = _
  rw [hv]
  exact congrArg₂ (· * ·) rfl (PhysicalCurlCovariance.carrier_eq_of_products
    (congrArg (((j : ℝ) * (x.coefficients.blocks l).frequency n) * ·) hphi.eq_of_nhds))

/-- Forward cover order: the germ inputs are consequences of the current
state and coefficient identities, not assumptions about the solved wave. -/
theorem corrected_forward (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n (BaseChartJets.cellBand l.2) k)
    (HB : ActualReferenceRebase.BlockComparison x l V n (BaseChartJets.cellBand l.2) k)
    (j : ℤ) (hj : j ≠ 0)
    (hn : (x.coefficients.blocks l).frequency n ≠ 0)
    (hm : (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) ≠ 0)
    (z : Cylinder) (hz : z ∈ cylinderDomain V) :
    vectorMode ((corrected x l j).frequency n) ((corrected x l j).phase n)
      ((corrected x l j).amplitude n) (waveEquiv z) =
      bandVelocity (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (CommonWindow.index h n)
        (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j z := by
  apply corrected_eq_band_of_germs
  · filter_upwards [(cylinderDomain_open hV).mem_nhds hz] with y hy
    exact ActualReferenceRebase.actualAmplitude_forward x l hV htime n k hi HS HB j
      (cylinderParameter y) hy (waveEquiv y).1.2 (waveEquiv y).2
  · filter_upwards [(cylinderDomain_open hV).mem_nhds hz] with y hy
    exact (ActualReferenceRebase.actualPhase_forward x l V n k hi HB j hj hn hm
      (cylinderParameter y) hy (waveEquiv y).1.2 (waveEquiv y).2).symm

/-! ## Composition of the actual primitive copy data

These identities allow two current bands to be compared directly.  In
particular, they do not require extending a current reference-band state
outside the slow overlap on which state coherence was proved.
-/

theorem ratioPower_comp {Q Qm Qr : ℝ} (hQm : 0 < Qm) (a : ℝ) :
    ratioPower Q Qm a * ratioPower Qm Qr a = ratioPower Q Qr a := by
  unfold ratioPower
  exact div_mul_div_cancel₀ (Real.rpow_pos_of_pos hQm a).ne'

theorem parameterChange_comp (h Q Qm Qr : ℝ) (hQm : 0 < Qm) (p : Parameter) :
    parameterChange h Qm Qr (parameterChange h Q Qm p) = parameterChange h Q Qr p := by
  ext <;> simp only [parameterChange, ← mul_assoc]
  all_goals rw [mul_comm (ratioPower Qm Qr _), ratioPower_comp hQm]

theorem normalWeight_comp {Q Qm Qr K Km Kr : ℝ} (hQm : 0 < Qm) (hKm : Km ≠ 0) :
    normalWeight Q Qm K Km * normalWeight Qm Qr Km Kr = normalWeight Q Qr K Kr := by
  by_cases hK : K = 0
  · simp [normalWeight, hK]
  unfold normalWeight
  calc
    _ = ((Km / K) * (Kr / Km)) *
        (ratioPower Q Qm (1/2) * ratioPower Qm Qr (1/2)) := by ring
    _ = _ := by rw [ratioPower_comp hQm]; field_simp [hKm, hK]

theorem nativeTimeMap_comp (r s : ℝ) (z : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 r (CopySolveCompatibility.nativeTimeMap 0 s z) =
      CopySolveCompatibility.nativeTimeMap 0 (r*s) z := by
  ext <;> simp [CopySolveCompatibility.nativeTimeMap, mul_assoc]

theorem scaledBasis_comp (e : Plane ≃L[ℝ] Plane) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    CommonCoverClass.scaledBasis (CommonCoverClass.scaledBasis e r hr) s hs =
      CommonCoverClass.scaledBasis e (r*s) (mul_ne_zero hr hs) := by
  apply ContinuousLinearEquiv.ext
  funext z
  simp only [CommonCoverClass.scaledBasis_apply, mul_assoc]

theorem transportGeometry_comp (g : Geometry) (k d : ℕ) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    CopySolveCompatibility.transportGeometry
      (CopySolveCompatibility.transportGeometry g k 0 r hr) d 0 s hs =
      CopySolveCompatibility.transportGeometry g (k+d) 0 (r*s) (mul_ne_zero hr hs) := by
  simp only [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.refineGeometry,
    CopySolveCompatibility.timeGeometry, scaledBasis_comp, Nat.add_assoc]
  simp

theorem transportTangent_comp (t : TangentData Parameter ProblemStatement.Space)
    (f g : Parameter → Parameter) (k d : ℕ) (r s a b v w : ℝ) :
    ScaledTangentTransport.transportTangent
      (ScaledTangentTransport.transportTangent t f k 0 r a v) g d 0 s b w =
      ScaledTangentTransport.transportTangent t (fun p => f (g p)) (k+d) 0
        (r*s) (a*b) (v*w) := by
  unfold ScaledTangentTransport.transportTangent
  congr 1 <;> funext z <;>
    simp [nativeTimeMap_comp, CopySolveCompatibility.coverPower_add,
      smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem gap_comp (l : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) :
    ActualParticularStageControls.gap l m + k = ActualParticularStageControls.gap l n := by
  unfold ActualParticularStageControls.gap
  omega

theorem parameters_geometry (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) :
    CopySolveCompatibility.transportGeometry ((ActualParticularStageControls.parameters x
      l).geometry m)
      k 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
        (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne' =
      (ActualParticularStageControls.parameters x l).geometry n := by
  change CopySolveCompatibility.transportGeometry
    (CopySolveCompatibility.transportGeometry (ActualParticularStageControls.reference l).geometry
      (ActualParticularStageControls.gap l m) 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))) _)
    k 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) _ = _
  erw [transportGeometry_comp, gap_comp l n m k hi hm]
  have hr : clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]
    exact ratioPower_comp (ChartScales.Q_pos m) _
  simp only [hr]
  rfl

theorem parameters_length (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m : ℕ) :
    (ActualParticularStageControls.parameters x l).length m /
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      (ActualParticularStageControls.parameters x l).length n := by
  change (_ / clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))) /
    clockWeight h (ChartScales.Q n) (ChartScales.Q m) = _
  rw [div_div, mul_comm]
  change _ / (ratioPower _ _ _ * ratioPower _ _ _) = _
  rw [ratioPower_comp (ChartScales.Q_pos m)]
  rfl

theorem parameters_cutoff (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m : ℕ) :
    (ActualParticularStageControls.parameters x l).cutoff m ∘
      CopySolveCompatibility.nativeTimeMap 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) =
      (ActualParticularStageControls.parameters x l).cutoff n := by
  funext z
  change (ActualParticularStageControls.reference l).cutoff
    (CopySolveCompatibility.nativeTimeMap 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (CopySolveCompatibility.nativeTimeMap 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
        z)) = _
  rw [nativeTimeMap_comp, mul_comm]
  change (ActualParticularStageControls.reference l).cutoff
    (CopySolveCompatibility.nativeTimeMap 0 (ratioPower _ _ _ * ratioPower _ _ _) z) = _
  rw [ratioPower_comp (ChartScales.Q_pos m)]
  rfl

theorem parameters_tangent (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0) :
    ScaledTangentTransport.transportTangent ((ActualParticularStageControls.parameters x l).tangent
      j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k 0
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q m))
      (normalWeight (ChartScales.Q n) (ChartScales.Q m)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency m)) =
      (ActualParticularStageControls.parameters x l).tangent j n := by
  change ScaledTangentTransport.transportTangent
    (ScaledTangentTransport.transportTangent (ActualParticularStageControls.reference l |>.tangent
      j)
      (parameterChange h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (ActualParticularStageControls.gap l m) 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (velocityWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (normalWeight (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))
        ((j : ℝ) * (x.coefficients.blocks l).frequency m)
        ((j : ℝ) * (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2)))) _ _ _ _ _ _
          = _
  rw [transportTangent_comp, gap_comp l n m k hi hm]
  have hp := funext (parameterChange_comp h (ChartScales.Q n) (ChartScales.Q m)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) (ChartScales.Q_pos m))
  rw [hp]
  have hr : clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]; exact ratioPower_comp (ChartScales.Q_pos m) _
  have ha : velocityWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]; exact ratioPower_comp (ChartScales.Q_pos m) _
  rw [hr, ha, mul_comm (normalWeight _ _ _ _), normalWeight_comp (ChartScales.Q_pos m) hKm]
  rfl

/-- Actual source transport on the two-band overlap.  All fast variables
remain free, and all excluded residual terms are retained. -/
theorem source_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (p : Parameter) (hp : p.2 ∈ V) (Y : Plane) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
        l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
      (ActualParticularStageControls.assembly x l).aliasInput j n (p,Y) =
    ScaledTangentTransport.transportSource
      (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
        (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly
          x l).carrierBlock
        (ActualParticularStageControls.assembly x l).gaussianInput
        (ActualParticularStageControls.assembly x l).aliasInput j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q m)) (p,Y) := by
  have he := HS.source (ActualInitialCoherence.context_band B htime n m k hi)
    (PhysicalMeanDomain.slowDomain_open hV) (GaugeStateCoherence.bandScale_pos n m).ne'
      HB j (x := CorrectionStep.cycleAssoc.symm (p,Y)) hp
  rw [ActualReferenceRebase.state_sourceWeight] at he
  rw [ActualReferenceRebase.assembly_source]
  change _ = (clockWeight _ _ _ * velocityWeight _ _ _) • _
  rw [clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos m),
    ActualReferenceRebase.assembly_source]
  simpa only [← ActualReferenceRebase.associatedChart_stateChart,
    PhysicalResidualNaturality.associatedChart_apply] using he

/-! ## The global linear map and its actual spatial directions -/

noncomputable def absoluteMap (n : ℕ) : WaveSpace ≃L[ℝ] ActualPrimaryCoherence.Absolute :=
  ActualParticularStageControls.nativeToFull.toContinuousLinearEquiv.trans
    (ActualPrimaryCoherence.absoluteChart n)

noncomputable def bandMap (n m : ℕ) : WaveSpace ≃L[ℝ] WaveSpace :=
  (absoluteMap n).trans (absoluteMap m).symm

theorem absoluteMap_band (n m : ℕ) (z : WaveSpace) :
    absoluteMap m (bandMap n m z) = absoluteMap n z :=
  (absoluteMap m).apply_symm_apply _

theorem bandMap_apply (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (z : WaveSpace) :
    bandMap n m z = ((parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,z.1.2),
      coverPower k z.2) := by
  apply (absoluteMap m).injective
  rw [absoluteMap_band]
  change (ActualPrimaryCoherence.absoluteChart n) (ActualParticularStageControls.nativeToFull z) =
    (ActualPrimaryCoherence.absoluteChart m) _
  rw [ActualPrimaryCoherence.absoluteChart_apply, ActualPrimaryCoherence.absoluteChart_apply]
  apply Prod.ext
  · symm
    change toAbsolute m (CorrectionStep.cycleAssoc.symm
      (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m)
        k (z.1.1,z.2))) = _
    rw [ActualReferenceRebase.associatedChart_stateChart]
    exact ActualPrimaryCoherence.toAbsolute_bandChart n m k hi _
  · rfl

theorem absoluteMap_radius (n : ℕ) (z : WaveSpace) :
    ActualPrimaryCoherence.absoluteRadius (absoluteMap n z) =
      Real.sqrt (ChartScales.Q n) * z.1.1.1 :=
  ActualPrimaryCoherence.absoluteChart_radius n (ActualParticularStageControls.nativeToFull z)

theorem absoluteMap_radial (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).radialField n z) =
      Real.sqrt (ChartScales.Q n) • ActualPrimaryCoherence.absoluteRadial (absoluteMap n z) := by
  simp only [absoluteMap, ActualParticularStageControls.directions,
    ParticularWaveBounds.reindex_radialField, ParticularWaveBounds.reindexVector,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_radial B n _

theorem absoluteMap_fast (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).fastField n z) =
      ChartScales.Q n ^ (1+h) • ActualPrimaryCoherence.absoluteFast (absoluteMap n z) := by
  simp only [absoluteMap, ActualParticularStageControls.directions,
    ParticularWaveBounds.reindex_fastField, ParticularWaveBounds.reindexVector,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_fast B n _

theorem between_direction {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e f : E ≃L[ℝ] F) (a b : ℝ) (hb : b ≠ 0) (U V : E → E) (W : F → F)
    (he : ∀ z, e (U z) = a • W (e z)) (hf : ∀ z, f (V z) = b • W (f z)) (z : E) :
    (e.trans f.symm) (U z) = (a/b) • V ((e.trans f.symm) z) := by
  apply f.injective
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    map_smul, hf, he, smul_smul, div_mul_cancel₀ _ hb]

theorem bandMap_fast (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).fastField n z) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualParticularStageControls.directions (B := B)).fastField m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.rpow_pos_of_pos (ChartScales.Q_pos m) (1+h)).ne' _ _ _
    (absoluteMap_fast B n) (absoluteMap_fast B m) z
  change _ = (ChartScales.Q n ^ (1+h) / ChartScales.Q m ^ (1+h)) • _ at he
  simp only [clockWeight, ratioPower, CoordinateAlgebra.A,
    show (1/2 : ℝ) + h + 1/2 = 1+h by ring] at he ⊢
  exact he

theorem absoluteMap_axial (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
        ActualParticularStageControls.associatedStrip) n z) =
      Real.sqrt (ChartScales.Q n) • ActualPrimaryCoherence.absoluteAxial (absoluteMap n z) := by
  change (ActualPrimaryCoherence.absoluteChart n)
    (ActualParticularStageControls.nativeToFull
      (ActualParticularStageControls.nativeToFull.symm
        ((PrimaryResidualClass.directions (commonContext B)).axialField
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion)) n
          (ActualParticularStageControls.nativeToFull z)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_axial B n standardRegion _

theorem absoluteMap_angular (B n : ℕ) (z : WaveSpace) :
    absoluteMap n (ActualParticularStageControls.directions (B := B)).angular =
      ActualPrimaryCoherence.absoluteAngular (absoluteMap n z) := by
  change (ActualPrimaryCoherence.absoluteChart n)
    (ActualParticularStageControls.nativeToFull
      (ActualParticularStageControls.nativeToFull.symm
        (PrimaryResidualClass.directions (commonContext B)).angular)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_angular B n _

theorem bandMap_radial (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).radialField n z) =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) •
        (ActualParticularStageControls.directions (B := B)).radialField m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne' _ _ _
    (absoluteMap_radial B n) (absoluteMap_radial B m) z
  simp only [Real.sqrt_eq_rpow, ratioPower] at he ⊢
  exact he

theorem bandMap_axial (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
        ActualParticularStageControls.associatedStrip) n z) =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) •
        (ActualParticularStageControls.directions (B := B)).axialField
          (CorrectionStep.ParticularParameters.nativeStrip
            ActualParticularStageControls.associatedStrip)
            m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne' _ _ _
    (absoluteMap_axial B n) (absoluteMap_axial B m) z
  simp only [Real.sqrt_eq_rpow, ratioPower] at he ⊢
  exact he

theorem bandMap_angular (B n m : ℕ) (z : WaveSpace) :
    bandMap n m (ActualParticularStageControls.directions (B := B)).angular =
      (ActualParticularStageControls.directions (B := B)).angular := by
  have he := between_direction (absoluteMap n) (absoluteMap m) 1 1 one_ne_zero
    (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
    (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
    ActualPrimaryCoherence.absoluteAngular
    (by simpa only [one_smul] using absoluteMap_angular B n)
    (by simpa only [one_smul] using absoluteMap_angular B m) z
  simp only [div_self one_ne_zero, one_smul] at he
  exact he

theorem bandMap_radius (n m : ℕ) (z : WaveSpace) :
    (bandMap n m z).1.1.1 =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) * z.1.1.1 := by
  have he := absoluteMap_radius m (bandMap n m z)
  rw [absoluteMap_band, absoluteMap_radius] at he
  have hm := (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne'
  calc
    _ = (Real.sqrt (ChartScales.Q n) * z.1.1.1) / Real.sqrt (ChartScales.Q m) :=
      (eq_div_iff hm).2 (by simpa only [mul_comm] using he.symm)
    _ = _ := by
      unfold ratioPower
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      ring

theorem reference_cutoff_smooth (l : Label B N0) :
    ContDiff ℝ ∞ (ActualParticularStageControls.reference l).cutoff := by
  change ContDiff ℝ ∞ (fun z : Plane =>
    (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff _ z.2)
  exact (clockWindow l.2).cutoff_contDiff.mul
    ((GaussianTailFlat.slotCutoff_contDiff _).comp contDiff_snd)

theorem reference_cutoff_support (l : Label B N0) :
    support (ActualParticularStageControls.reference l).cutoff ⊆
      univ ×ˢ Icc 0 (ActualParticularStageControls.reference l).length := by
  classical
  intro z hz
  refine ⟨mem_univ _, ?_⟩
  have hL := (ActualParticularStageControls.reference l).length_pos
  have hs : GaussianTailFlat.slotCutoff (ActualParticularStageControls.reference l).length z.2 ≠ 0
    := by
    intro he
    apply hz
    change (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff _ z.2 = 0
    exact (congrArg ((clockWindow l.2).cutoff z * ·) he).trans (mul_zero _)
  constructor
  · by_contra hlt
    apply hs
    apply GaussianTailFlat.slotCutoff_zero hL
    rw [abs_of_neg (by linarith : z.2 - (ActualParticularStageControls.reference l).length/2 < 0)]
    linarith
  · by_contra hgt
    apply hs
    apply GaussianTailFlat.slotCutoff_zero hL
    rw [abs_of_pos (by linarith : 0 < z.2 - (ActualParticularStageControls.reference l).length/2)]
    linarith

theorem parameter_cutoff_smooth (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    ContDiff ℝ ∞ ((ActualParticularStageControls.parameters x l).cutoff n) := by
  apply (reference_cutoff_smooth l).comp
  exact contDiff_fst.prodMk (contDiff_const.add (contDiff_const.mul contDiff_snd))

theorem parameter_cutoff_support (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    support ((ActualParticularStageControls.parameters x l).cutoff n) ⊆
      univ ×ˢ Icc 0 ((ActualParticularStageControls.parameters x l).length n) := by
  intro z hz
  have hb := (reference_cutoff_support l hz).2
  have hr : 0 < clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) :=
    ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) _
  change 0 ≤ 0 + clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) * z.2
    ∧
    0 + clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) * z.2 ≤ _ at hb
  refine ⟨mem_univ _, ?_, ?_⟩
  · exact nonneg_of_mul_nonneg_right (by simpa using hb.1) hr
  · apply (le_div_iff₀ hr).2
    have hh := hb.2
    simp only [zero_add, mul_comm] at hh ⊢
    exact hh

noncomputable def source (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) : Parameter × Plane → ComplexVector :=
  ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
      l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j n

/-- Only finite path continuity of the actual input equation is required.
There is no continuation in the clock variable in this record. -/
structure PathRegular (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (Y : Plane) (copy : Frequency) : Prop where
  coefficient : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
    =>
    ((ActualParticularStageControls.parameters x l).tangent j n).linearData.coefficientAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))
  realForcing : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
    =>
    (ParticularWaveBounds.realData ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n)).linearData.forcingAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))
  imagForcing : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
    =>
    (ParticularWaveBounds.imagData ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n)).linearData.forcingAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))

section CopyComparison

variable (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
  {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
  (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
  (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
  (HS : ActualReferenceRebase.StateComparison x V n m k)
  (HB : ActualReferenceRebase.BlockComparison x l V n m k)
  (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
  (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
  (p : Parameter) (hp : p.2 ∈ V) (Y : Plane)

include hV htime hi hm HS HB hKn hKm hp in
theorem copy_amplitude_band (copy : Frequency)
    (H : PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy)
    (hslot : (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length n)) :
    ParticularWaveBounds.complexCopyVelocity ((ActualParticularStageControls.parameters x
      l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le copy (p,Y) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.complexCopyVelocity ((ActualParticularStageControls.parameters x
          l).tangent j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le copy
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
      l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have hz : ((CopySolveCompatibility.transportGeometry
      ((ActualParticularStageControls.parameters x l).geometry m) k 0 r hr.ne').coordinates copy
        Y).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length m / r) := by
    simpa only [r, parameters_geometry x l n m k hi hm, parameters_length x l n m] using hslot
  have he := IntervalCopyTransport.complexCopyVelocity_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn p copy Y
    H.coefficient H.realForcing H.imagForcing hz
  have hs := ActualReferenceRebase.copyVelocity_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le p
    (source_band x l hV htime n m k hi HS HB j p hp) copy Y
  apply hs.trans
  dsimp only [r, c, s] at he
  simp only [parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm] at he
  refine Eq.trans ?_ he
  exact GaussianErrorNaturality.interval_congr
    (fun a b hab => ParticularWaveBounds.complexCopyVelocity _ _ _ hab copy (p,Y))
    _ _ rfl (parameters_length x l n m).symm

include hV htime hi hm HS HB hKn hKm hp in
theorem common_amplitude_band
    (H : ∀ copy, PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy) :
    ParticularWaveBounds.commonVelocity ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le
      ((ActualParticularStageControls.parameters x l).cutoff n) (p,Y) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.commonVelocity ((ActualParticularStageControls.parameters x l).tangent
          j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le
          ((ActualParticularStageControls.parameters x l).cutoff m)
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
      l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have he := IntervalCopyTransport.commonVelocity_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn
    ((ActualParticularStageControls.parameters x l).cutoff m) (parameter_cutoff_support x l m) p Y
    (fun copy _ => (H copy).coefficient) (fun copy _ => (H copy).realForcing)
    (fun copy _ => (H copy).imagForcing)
  have hs := ActualReferenceRebase.commonVelocity_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le
    ((ActualParticularStageControls.parameters x l).cutoff n) p
    (source_band x l hV htime n m k hi HS HB j p hp) Y
  apply hs.trans
  dsimp only [r, c, s] at he
  simp only [parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm, parameters_cutoff x l n m] at he
  refine Eq.trans ?_ he
  exact GaussianErrorNaturality.interval_congr
    (fun a b hab => ParticularWaveBounds.commonVelocity _ _ _ hab _ (p,Y))
    _ _ rfl (parameters_length x l n m).symm

include hV htime hi hm HS HB hKn hKm hp in
theorem common_pressure_band
    (H : ∀ copy, PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy) :
    ParticularWaveBounds.commonPressure ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le
      ((ActualParticularStageControls.parameters x l).cutoff n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) (p,Y) =
      pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.commonPressure ((ActualParticularStageControls.parameters x l).tangent
          j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le
          ((ActualParticularStageControls.parameters x l).cutoff m)
          ((j : ℝ) * (x.coefficients.blocks l).frequency m)
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
      l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have he := IntervalCopyTransport.commonPressure_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((j : ℝ) * (x.coefficients.blocks l).frequency m) ((j : ℝ) * (x.coefficients.blocks
      l).frequency n)
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn hKm hKn
    ((ActualParticularStageControls.parameters x l).cutoff m) (parameter_cutoff_support x l m) p Y
    (fun copy _ => (H copy).coefficient) (fun copy _ => (H copy).realForcing)
    (fun copy _ => (H copy).imagForcing)
  dsimp only [r, c, s] at he
  rw [pressure_scaling (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm] at he
  have hs := ActualReferenceRebase.commonPressure_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le
    ((ActualParticularStageControls.parameters x l).cutoff n)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) p
    (source_band x l hV htime n m k hi HS HB j p hp) Y
  exact hs.trans (by simpa only [r, c, parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm, parameters_length x l n m, parameters_cutoff x l n m]
      using he)

end CopyComparison

theorem copy_cutoff_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (copy : Frequency) :
    (copyData x l j).cutoff n copy = fun z => (copyData x l j).cutoff m copy (bandMap n m z) := by
  funext z
  rw [bandMap_apply n m k hi]
  change (ActualParticularStageControls.parameters x l).cutoff n
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy z.2) =
    (ActualParticularStageControls.parameters x l).cutoff m
      (((ActualParticularStageControls.parameters x l).geometry m).coordinates copy (coverPower k
        z.2))
  rw [← parameters_geometry x l n m k hi hm, ← parameters_cutoff x l n m]
  exact congrArg ((ActualParticularStageControls.parameters x l).cutoff m)
    (ScaledTangentTransport.coordinates_transport _ k 0 _ _ copy z.2)

theorem copy_cutoff_smooth (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (copy : Frequency) :
    ContDiff ℝ ∞ ((copyData x l j).cutoff n copy) :=
  ((parameter_cutoff_smooth x l n).comp
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates_contDiff copy)).comp
      contDiff_snd

theorem copy_derivative_slot (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (copy : Frequency) {z : WaveSpace}
    (hz : (ActualParticularStageControls.directions (B := B)).Dfast
      (fun n => (copyData x l j).cutoff n copy) n z ≠ 0) :
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy z.2).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length n) := by
  apply GaussianErrorNaturality.along_ne_zero_mem_closed
    (isClosed_Icc.preimage
      ((((ActualParticularStageControls.parameters x l).geometry n).coordinates_contDiff
        copy).continuous.comp
        continuous_snd).snd) _
    ((ActualParticularStageControls.directions (B := B)).fastField n) hz
  intro y hy
  exact (parameter_cutoff_support x l n hy).2

theorem gaussian_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) n z =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B))
          m (bandMap n m z) := by
  rw [← clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  apply GaussianErrorNaturality.globalGaussian_transport (bandMap n m).toContinuousLinearMap
    (ActualParticularStageControls.directions (B := B)) (ActualParticularStageControls.directions
      (B := B))
    (copyData x l j) (copyData x l j) n m
  · exact copy_cutoff_band x l j n m k hi hm
  · exact bandMap_fast B n m z
  · intro copy
    exact (copy_cutoff_smooth x l j m copy).contDiffAt.differentiableAt (by simp)
  · intro copy hne
    have hd := GaussianErrorNaturality.fast_cutoff_transport (bandMap n m).toContinuousLinearMap
      (ActualParticularStageControls.directions (B := B)) (ActualParticularStageControls.directions
        (B := B))
      (copyData x l j) (copyData x l j) n m
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) copy z
      (copy_cutoff_band x l j n m k hi hm copy) (bandMap_fast B n m z)
      ((copy_cutoff_smooth x l j m copy).contDiffAt.differentiableAt (by simp))
    have hdn : (ActualParticularStageControls.directions (B := B)).Dfast
        (fun n => (copyData x l j).cutoff n copy) n z ≠ 0 := by
      rw [hd]
      exact mul_ne_zero (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne' hne
    have hs := copy_derivative_slot x l j n copy hdn
    change (copyData x l j).amplitude n copy z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (copyData x l j).amplitude m copy (bandMap n m z)
    rw [bandMap_apply n m k hi]
    simp only [copyData, GaussianErrorNaturality.copyData_amplitude]
    exact copy_amplitude_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 copy (H copy) hs
  · change (copyData x l j).source n z =
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m) *
        velocityWeight h (ChartScales.Q n) (ChartScales.Q m)) •
        (copyData x l j).source m (bandMap n m z)
    rw [bandMap_apply n m k hi]
    exact source_band x l hV htime n m k hi HS HB j z.1.1 hz z.2

/-! ## Actual finite-path inputs and zero source fibers -/

structure SourceInputs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0) : Prop where
  continuous : ∀ j n p, p.2 ∈ standardRegion.carrier →
    Continuous (fun Y : Plane => source x l j n (p,Y))
  supported : ∀ j n p, p.2 ∈ standardRegion.carrier → ∀ Y,
    source x l j n (p,Y) ≠ 0 →
      (p.1,(p.2,Y)) ∈ ActualCoreSupport.refinedCarrier (l.2,l.1) n
  ordered : ∀ j n p, p.2 ∈ standardRegion.carrier → ∀ Y,
    source x l j n (p,Y) ≠ 0 →
      CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)

theorem SourceInputs.pathRegular {x : CorrectionStep.CycleState (Label B N0)} {l : Label B N0}
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter) (hp : p.2 ∈ standardRegion.carrier)
    (hne : ∃ Y, source x l j n (p,Y) ≠ 0) (Y : Plane) (copy : Frequency) :
    PathRegular x l j n p Y copy := by
  have hs : ∃ Z : Plane, (p.1,(p.2,Z)) ∈ ActualCoreSupport.refinedCarrier (l.2,l.1) n := by
    obtain ⟨Z,hZ⟩ := hne
    exact ⟨Z,I.supported j n p hp Z hZ⟩
  have ha := ActualCopySliceRegularity.actual_copy_slices_of_refinedFiber x l hfrequency j hj n p
    (standardRegion.time_pos p.2 hp) hs Y copy
  let G : Geometry := (ActualParticularStageControls.parameters x l).geometry n
  let L : ℝ := (ActualParticularStageControls.parameters x l).length n
  have ht : Continuous (fun s : Icc (0 : ℝ) L => (Y,(s : ℝ))) :=
    continuous_const.prodMk continuous_subtype_val
  have hpath := (G.path_contDiff copy).continuous.comp ht
  have hf := (I.continuous j n p hp).comp hpath
  dsimp only [Function.comp_def] at hf
  exact ⟨ha.1, IntervalCopyTransport.real_forcingAlong_continuous _ _ _ _ _ _ ha.2 hf,
    IntervalCopyTransport.imag_forcingAlong_continuous _ _ _ _ _ _ ha.2 hf⟩

theorem copy_amplitude_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p,Y) = 0)
    (theta : ℝ) (Y : Plane) (copy : Frequency) :
    (copyData x l j).amplitude n copy ((p,theta),Y) = 0 := by
  rw [copyData, GaussianErrorNaturality.copyData_amplitude]
  exact ParticularWaveBounds.complexCopyVelocity_zero_of_path _ _ _ _ copy p Y (fun _ _ => hz _)

theorem raw_amplitude_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p,Y) = 0)
    (theta : ℝ) (Y : Plane) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n ((p,theta),Y) = 0 := by
  change (∑' copy, (copyData x l j).cutoff n copy ((p,theta),Y) •
    (copyData x l j).amplitude n copy ((p,theta),Y)) = 0
  simp only [copy_amplitude_zero x l j n p hz, smul_zero, tsum_zero]

theorem raw_pressure_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (p : Parameter) (hz : ∀ Y, source x l j n (p,Y) = 0) (theta : ℝ) (Y : Plane) :
    (ActualReferenceRebase.actualCoefficients x l j).pressure n ((p,theta),Y) = 0 := by
  rw [ActualReferenceRebase.actualCoefficients, CorrectionStep.ParticularParameters.common_pressure
    _ _ _ _ _ _ _ _ hKn]
  change (∑' copy, ((ActualParticularStageControls.parameters x l).cutoff n
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y) : ℂ) *
      ParticularWaveBounds.complexCopyPressure _ _ _ _ copy _ (p,Y)) = 0
  trans ∑' _ : Frequency, (0 : ℂ)
  · apply tsum_congr
    intro copy
    by_cases hc : (ActualParticularStageControls.parameters x l).cutoff n
        (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y) = 0
    · simp only [hc, Complex.ofReal_zero, zero_mul]
    · change (_ : ℂ) * ParticularWaveBounds.complexCopyPressure
        ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
        ((ActualParticularStageControls.parameters x l).geometry n)
        ((ActualParticularStageControls.parameters x l).length_pos n).le copy
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) (p,Y) = 0
      rw [ParticularWaveBounds.complexCopyPressure_zero_of_path _ _ _ _ copy _ p Y
        (fun _ _ => hz _) (parameter_cutoff_support x l n hc).2, mul_zero]
  · exact tsum_zero

theorem gaussian_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p,Y) = 0)
    (theta : ℝ) (Y : Plane) :
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B))
      n ((p,theta),Y) = 0 := by
  have hs : (copyData x l j).source n ((p,theta),Y) = 0 := hz Y
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, PeriodizedWaveBounds.CopyData.globalTail,
    PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail, copy_amplitude_zero x l
      j n p hz,
    smul_zero, tsum_zero, hs, add_zero]

theorem raw_amplitude_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m z) := by
  rw [bandMap_apply n m k hi, ActualReferenceRebase.actualCoefficients,
    CorrectionStep.ParticularParameters.common_amplitude,
    CorrectionStep.ParticularParameters.common_amplitude]
  exact common_amplitude_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 H

theorem raw_pressure_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (ActualReferenceRebase.actualCoefficients x l j).pressure n z =
      pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).pressure m (bandMap n m z) := by
  rw [bandMap_apply n m k hi, ActualReferenceRebase.actualCoefficients,
    CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hKn,
    CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hKm]
  exact common_pressure_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 H

/-- All three raw output identities are derived from the current source.
A zero source fiber needs no ODE regularity or ordering premise. -/
theorem raw_outputs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (hmap : (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1).2 ∈
      standardRegion.carrier) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n z =
        velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m z) ∧
    (ActualReferenceRebase.actualCoefficients x l j).pressure n z =
        pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (ActualReferenceRebase.actualCoefficients x l j).pressure m (bandMap n m z) ∧
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) n z =
        sourceWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) m
            (bandMap n m z) := by
  classical
  have hk (a : ℕ) : (j : ℝ) * (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact mul_ne_zero (by exact_mod_cast hj) (Scaling.carrier_frequency_pos
      (ChartScales.epsilon_pos h a)).ne'
  by_cases hne : ∃ Y, source x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,Y) ≠ 0
  · have hm := let ⟨Y,hY⟩ := hne; I.ordered j m _ hmap Y hY
    have H := I.pathRegular hfrequency j hj m _ hmap hne
    exact ⟨raw_amplitude_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _),
      raw_pressure_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _),
      gaussian_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _)⟩
  · have hm : ∀ Y, source x l j m
        (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,Y) = 0 := by
      simpa only [not_exists, not_not] using hne
    have hn : ∀ Y, source x l j n (z.1.1,Y) = 0 := by
      intro Y
      rw [show source x l j n (z.1.1,Y) = _ from source_band x l hV htime n m k hi HS HB j _ hz Y]
      change (_ : ℝ) • source x l j m (_,_) = 0
      rw [hm, smul_zero]
    rw [bandMap_apply n m k hi]
    simp only [raw_amplitude_zero x l j n z.1.1 hn, raw_amplitude_zero x l j m _ hm,
      raw_pressure_zero x l j n (hk n) z.1.1 hn, raw_pressure_zero x l j m (hk m) _ hm,
      gaussian_zero x l j n z.1.1 hn, gaussian_zero x l j m _ hm, smul_zero, and_self]

noncomputable def waveDomain (V : Set Plane) : Set WaveSpace := {z | z.1.1.2 ∈ V}

theorem waveDomain_open {V : Set Plane} (hV : IsOpen V) : IsOpen (waveDomain V) :=
  hV.preimage continuous_fst.fst.snd

theorem parameterChange_slow (n m : ℕ) (p : Parameter) :
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p).2 =
      GaugeStateCoherence.bandSlowEquiv h n m p.2 :=
  congrArg (fun z : CorrectionStep.CyclePoint => z.2.1)
    (ActualReferenceRebase.associatedChart_stateChart n m 0 (p,0))

theorem phase_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k) (j : ℤ) (hj : j ≠ 0)
    (hn : (x.coefficients.blocks l).frequency n ≠ 0) (hm : (x.coefficients.blocks l).frequency m ≠
      0)
    (z : WaveSpace) (hz : z ∈ waveDomain V) :
    (ActualReferenceRebase.actualCoefficients x l j).phase n z =
      (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m (bandMap n m z) := by
  have hp := HB.phase (x := CorrectionStep.cycleAssoc.symm (z.1.1,z.2)) hz
  dsimp only at hp
  rw [← ActualReferenceRebase.associatedChart_stateChart,
    PhysicalResidualNaturality.associatedChart_apply] at hp
  rw [bandMap_apply n m k hi]
  change (x.coefficients.blocks l).phase n (CorrectionStep.cycleAssoc.symm (z.1.1,z.2)) +
      ((x.coefficients.blocks l).angularFrequency n : ℝ) /
        (x.coefficients.blocks l).frequency n * z.1.2 = _
  rw [HB.angular]
  exact (ActualReferenceRebase.carrier_phase_rebase hn hm (by exact_mod_cast hj) hp).symm

theorem corrected_amplitude_of_germs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n m : ℕ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0) (z : WaveSpace)
    (ha : (ActualReferenceRebase.actualCoefficients x l j).amplitude n =ᶠ[𝓝 z]
      fun y => velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m y))
    (hp : (ActualReferenceRebase.actualCoefficients x l j).phase n =ᶠ[𝓝 z]
      fun y => (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m (bandMap n m y)) :
    (corrected x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (corrected x l j).amplitude m (bandMap n m z) := by
  let d := ActualParticularStageControls.directions (B := B)
  let s := CorrectionStep.ParticularParameters.nativeStrip
    ActualParticularStageControls.associatedStrip
  have h1 := ParticularWaveAssembly.realizedCoefficient_germ ha
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
  have h2 := ActualParticularRealization.realizedCoefficient_phase_germ hp
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (fun y => velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
      (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m y))
  change CurlClassBounds.realizedCoefficient ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    (fun y : WaveSpace => y.1.1.1) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude n) z = _
  rw [(h1.trans h2).eq_of_nhds]
  exact ActualPrimaryCoherence.realizedCoefficient_equiv (bandMap n m)
    (L := (j : ℝ) * (x.coefficients.blocks l).frequency m)
    (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne'
    (div_ne_zero hKm hKn) hKn (by field_simp [hKn, (mul_ne_zero_iff.mp hKn).2])
    (fun y => y.1.1.1) (fun y => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.radialField m) (fun _ => d.angular) (d.axialField s m)
    (bandMap_radius n m) (bandMap_radial B n m) (bandMap_angular B n m) (bandMap_axial B n m)
    (velocityWeight h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualReferenceRebase.actualCoefficients x l j).phase m)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude m) z

theorem corrected_amplitude_on (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ waveDomain V) :
    (corrected x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (corrected x l j).amplitude m (bandMap n m z) := by
  have hf (a : ℕ) : (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h a)).ne'
  apply corrected_amplitude_of_germs x l j n m
    (mul_ne_zero (by exact_mod_cast hj) (hf n)) (mul_ne_zero (by exact_mod_cast hj) (hf m)) z
  · filter_upwards [(waveDomain_open hV).mem_nhds hz] with y hy
    exact (raw_outputs x l I hfrequency hV htime n m k hi HS HB j hj y hy
      (by rw [parameterChange_slow]; exact hmap hy)).1
  · filter_upwards [(waveDomain_open hV).mem_nhds hz] with y hy
    exact phase_band x l n m k hi HB j hj (hf n) (hf m) y hy

end NavierStokes.ActualParticularCoherence
