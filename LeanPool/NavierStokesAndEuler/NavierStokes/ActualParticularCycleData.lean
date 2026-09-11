/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierTransport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularMeanGain
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePeriodicity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCoreSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanBoundsReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ClosedNativeWaveIdentities
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedDynamics
import LeanPool.NavierStokesAndEuler.NavierStokes.NativePrincipalEquations
public import LeanPool.NavierStokesAndEuler.NavierStokes.StateReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction

/-!
# Particular-wave data for the actual correction cycle

The record below names the particular half of the cycle's analytic data.
Its producer uses the literal fixed-parameter solve and incoming invariant.
-/

section

/-!
# Exact dynamics of the actual particular correction

The current harmonic residual is solved on the common cover.  Geometry and
carrier identities are proved for the actual selected primary labels;
quantitative controls are supplied by `ActualParticularStageControls`.
-/

section

/-!
# Actual harmonic divergence under a change of product association

The same complex single-mode field is pulled back along the cylinder
isometry. Its genuine cylindrical divergence is preserved, including the
transported radial and axial directions. No new divergence premise is
needed for the associated particular-solver coordinates.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ModeSolenoidalReindex

open HarmonicCalculus WeightedClasses

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem amplitude_pull (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) :
    HarmonicWaveInteraction.amplitude (StateReindex.block e b) j n =
      fun x => HarmonicWaveInteraction.amplitude b j n (e x) := by
  funext x i
  simp only [HarmonicWaveInteraction.amplitude, HarmonicMeanInteraction.blockAmplitude,
    StateReindex.block, StateReindex.realCoefficients_pull, StateReindex.coefficients_apply]

theorem singleMode_pull (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) :
    HarmonicWaveInteraction.singleMode (StateReindex.block e b) j n =
      fun x => HarmonicWaveInteraction.singleMode b j n (StateReindex.cylinder e x) := by
  funext x i
  simp only [HarmonicWaveInteraction.singleMode, HarmonicResidual.vectorField,
    HarmonicFields.field, HarmonicFields.evaluate_single,
    HarmonicWaveInteraction.amplitude, HarmonicMeanInteraction.blockAmplitude,
    StateReindex.block, StateReindex.realCoefficients_pull,
    StateReindex.coefficients_apply, StateReindex.cylinder_apply]

theorem liftDirection_pull (e : D ≃ₗᵢ[ℝ] E) (V : E → E) :
    HarmonicResidual.liftDirection (StateReindex.vector e V) =
      StateReindex.vector (StateReindex.cylinder e) (HarmonicResidual.liftDirection V) := by
  funext x
  simp only [HarmonicResidual.liftDirection, StateReindex.vector,
    ParticularWaveBounds.reindexVector, StateReindex.cylinder_apply,
    StateReindex.cylinder_symm_apply]

theorem angularDirection_pull (e : D ≃ₗᵢ[ℝ] E) :
    StateReindex.vector (StateReindex.cylinder e)
      (HarmonicResidual.angularDirection (D := E)) = HarmonicResidual.angularDirection := by
  funext x
  change (e.symm 0, (1 : ℝ)) = (0, 1)
  rw [map_zero]

theorem cylindricalDivergence_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (a : E → ComplexVector) (x : D) :
    cylindricalDivergence (fun y => R (e y)) (StateReindex.vector e Vr)
      (StateReindex.vector e Vθ) (StateReindex.vector e Vz) (fun y => a (e y)) x =
      cylindricalDivergence R Vr Vθ Vz a (e x) := by
  simp only [cylindricalDivergence, StateReindex.along_pull_component]

theorem singleMode_divergence_pull (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) (p : D × ℝ) :
    cylindricalDivergence (fun q => (StateReindex.context e c).operators.radius q.1)
      (HarmonicResidual.liftDirection
        (HarmonicResidual.contextFrame (StateReindex.context e c) n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection
        (HarmonicResidual.contextFrame (StateReindex.context e c) n).axial)
      (HarmonicWaveInteraction.singleMode (StateReindex.block e b) j n) p =
    cylindricalDivergence (fun q => c.operators.radius q.1)
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
      (HarmonicWaveInteraction.singleMode b j n) (StateReindex.cylinder e p) := by
  rw [StateReindex.contextFrame_pull, singleMode_pull]
  change cylindricalDivergence (fun q => c.operators.radius (e q.1))
    (HarmonicResidual.liftDirection (StateReindex.vector e (HarmonicResidual.contextFrame c
        n).radial))
    HarmonicResidual.angularDirection
    (HarmonicResidual.liftDirection (StateReindex.vector e (HarmonicResidual.contextFrame c
        n).axial))
    (fun q => HarmonicWaveInteraction.singleMode b j n (StateReindex.cylinder e q)) p = _
  rw [liftDirection_pull, liftDirection_pull, ← angularDirection_pull e]
  exact cylindricalDivergence_pull (StateReindex.cylinder e)
    (fun q : E × ℝ => c.operators.radius q.1)
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
    HarmonicResidual.angularDirection
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
    (HarmonicWaveInteraction.singleMode b j n) p

theorem modeSolenoidal_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} {b : CorrectionState.HarmonicBlock E}
    (hb : HarmonicWaveInteraction.ModeSolenoidal s c b) :
    HarmonicWaveInteraction.ModeSolenoidal (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c) (StateReindex.block e b) := by
  intro j hj n p hp
  rw [singleMode_divergence_pull]
  exact hb j hj n (StateReindex.cylinder e p) hp

end NavierStokes.ModeSolenoidalReindex

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularDynamics

open Set Function Filter HarmonicCalculus
open CorrectionInitialization CorrectionState CorrectionStep
open ActualParticularStageControls CommonCoverSolve TorusInverse ParticularWaveBounds
    ParticularWaveAssembly
open scoped ContDiff Topology InnerProductSpace BigOperators

variable {B N0 : ℕ}

/-- Primary carrier as an element of `HarmonicBlock CyclePoint`. -/
noncomputable def primaryCarrier (l : Label B N0) : HarmonicBlock CyclePoint :=
  (ActualPrimary.piece ActualPrimary.standardRegion l.1 l.2).tangentBlock
    (fun n x => (ActualPrimary.chartCoefficients l.1 l.2).phase n (x,0))
    (fun _ => PrimaryGeometryAssembly.angularMode ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared l.1 l.2)

/-- Preserves carriers: an abbreviation for `∀ l, SameCarrier (x.coefficients.blocks l)
(primaryCarrier l)`. -/
abbrev PreservesCarriers (x : CycleState (Label B N0)) : Prop :=
  ∀ l, SameCarrier (x.coefficients.blocks l) (primaryCarrier l)

theorem carrier_frequency {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) :
    (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n :=
  (congrFun (H l).frequency n).symm

@[simp] theorem nativeToFull_apply (z : Native) :
    nativeToFull z = ((z.1.1.1,(z.1.1.2,z.2)),z.1.2) := rfl

/-- Reference point as an element of `ActualSignedGeometry.Native`. -/
noncomputable def referencePoint (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : Native) : ActualSignedGeometry.Native :=
  (ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) z.1.1),
    (reference l).geometry.coordinates k (coverPower (gap l n) z.2))

theorem referencePoint_eq_copy (l : Label B N0) (n : ℕ) (k : Frequency)
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2)) (z : Native) :
    referencePoint l n k z =
      ActualPrimaryDynamics.copyPoint l.1 l.2 n k (nativeToFull z) := by
  apply Prod.ext
  · ext <;>
      simp [referencePoint, PhysicalParticularWave.parameterChange,
        PhysicalParticularWave.ratioPower, ActualSignedGeometry.swapParameter,
        ActualPrimaryDynamics.copyPoint, ActualPrimary.nativeSlow,
        ActualPrimary.toAbsolute, Real.sqrt_eq_rpow, nativeToFull_apply] <;> ring
  · change (referenceGeometry l).coordinates k (coverPower (gap l n) z.2) = _
    have he : CopySolveCompatibility.refineGeometry (referenceGeometry l) (gap l n) =
        ActualPrimary.chartGeometry n l.1 l.2 := by
      simp only [CopySolveCompatibility.refineGeometry, referenceGeometry,
        ActualSignedGeometry.slotGeometry, CommonCoverClass.bandGeometry,
        Nat.zero_add, ActualPrimary.chartGeometry, ActualPrimary.geometry, spatialLabel, gap]
      rfl
    rw [← CopySolveCompatibility.coordinates_refine, he]
    exact (ActualPrimary.chartGeometry_coordinates n l.1 l.2 hi k z.2).symm

theorem normalWeight_eq (l : Label B N0) (n : ℕ) (j : ℤ) (hj : j ≠ 0) :
    PhysicalParticularWave.normalWeight (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
      ((j:ℝ)*ChartScales.carrier ActualPrimary.h n)
      ((j:ℝ)*ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand l.2)) =
        ActualPrimaryDynamics.normalScale l.2 n := by
  rw [ScaledActualParticularControl.normalWeight_harmonic _ _ _ _ j hj]
  simp only [PhysicalParticularWave.normalWeight, ActualPrimaryDynamics.normalScale,
    ActualPrimaryDynamics.radialScale_eq]

/-- Data used in actual particular dynamics. -/
noncomputable def data (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :=
  (parameters x l).copyData (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

theorem data_phase {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) :
    (data x l j).background.phase = (background l).phase := by
  funext n z
  change (x.coefficients.blocks l).phase n (cycleAssoc.symm (z.1.1,z.2)) +
      ((x.coefficients.blocks l).angularFrequency n : ℝ) /
        (x.coefficients.blocks l).frequency n * z.1.2 = _
  rw [← (H l).phase, ← (H l).angular, ← (H l).frequency]
  change (ActualPrimary.chartCoefficients l.1 l.2).phase n
      ((z.1.1.1,(z.1.1.2,z.2)),0) +
      (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate
        ActualPrimary.modulation (ActualPrimary.choice B N0).prepared l.1 l.2 : ℝ) /
        (ChartScales.carrier ActualPrimary.h n : ℝ) * z.1.2 =
      (ActualPrimary.chartCoefficients l.1 l.2).phase n (nativeToFull z)
  simp only [ActualPrimary.chartCoefficients, ActualPrimary.absolutePhase,
    nativeToFull_apply, mul_zero, zero_add]
  ring

theorem data_frequency {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    (data x l j).background.frequency n = (j:ℝ)*ChartScales.carrier ActualPrimary.h n := by
  change (j:ℝ)*(x.coefficients.blocks l).frequency n = _
  rw [carrier_frequency H]

theorem native_strip_eq :
    ParticularParameters.nativeStrip (associatedStrip) =
      ParticularWaveBounds.reindexStrip nativeToFull
        (HarmonicWaveInteraction.productStrip
          (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)) :=
              rfl

theorem background_normal (l : Label B N0) (n : ℕ) {z : Native}
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1) :
    (background l).normal (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
        n z =
      (ActualPrimary.chartCoefficients l.1 l.2).normal
        (HarmonicWaveInteraction.productStrip
          (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion))
        (PrimaryResidualClass.directions (ActualPrimary.commonContext B)) n (nativeToFull z) := by
  have hΦ := ((ActualPrimaryCoherence.chart_phase_smooth l.1 l.2 n).contDiffAt
    (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds
      (show nativeToFull z ∈ ActualPrimaryCoherence.positiveRadialChart from
          ⟨hR,hT⟩))).differentiableAt (by
          simp)
  rw [native_strip_eq]
  have he := ParticularWaveBounds.phaseNormal_reindex nativeToFull
    ((ActualPrimary.chartCoefficients l.1 l.2).radius n)
    ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (ActualPrimary.commonContext B)).angular)
    ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip
        (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)) n) hΦ
  simp only [background, directions, LinearWaveBounds.WaveCoefficients.normal,
    ParticularWaveBounds.reindexCoefficients, ParticularWaveBounds.reindex_radialField,
    ParticularWaveBounds.reindex_axialField] at he ⊢
  exact he

theorem data_normal {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (z : Native) :
    (data x l j).background.normal (ParticularParameters.nativeStrip associatedStrip) (directions
        (B := B)) n z =
      (background l).normal (ParticularParameters.nativeStrip associatedStrip) (directions (B :=
          B)) n z := by
  unfold LinearWaveBounds.WaveCoefficients.normal
  rw [data_phase H]
  rfl

theorem tangent_normal {x : CycleState (Label B N0)}
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier
        ActualPrimary.h n)
    (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) (k : Frequency) (z : Native) :
    ((parameters x l).nativeTangent j n).normal
      (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) =
      ActualPrimaryDynamics.normalScale l.2 n •
        ((ActualPrimary.phases B N0 l.1).frame l.2).normal
          ((referencePoint l n k z).1, (referencePoint l n k z).2.2) := by
  change PhysicalParticularWave.normalWeight (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
      ((j:ℝ)*(x.coefficients.blocks l).frequency n)
      ((j:ℝ)*(x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2)) •
    ((ActualPrimary.phases B N0 l.1).frame l.2).normal
      ((referencePoint l n k z).1,
        (CopySolveCompatibility.nativeTimeMap 0
          (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
            (ChartScales.Q (BaseChartJets.cellBand l.2)))
          (((parameters x l).geometry n).coordinates k z.2)).2) = _
  rw [hfrequency, hfrequency, normalWeight_eq l n j hj]
  apply congrArg (fun v => ActualPrimaryDynamics.normalScale l.2 n •
    ((ActualPrimary.phases B N0 l.1).frame l.2).normal ((referencePoint l n k z).1, v))
  exact congrArg Prod.snd (ScaledTangentTransport.coordinates_transport
    (reference l).geometry (gap l n) 0 _ _ k z.2)

theorem native_normal_match {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (ht : (referencePoint l n k z).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 l.1).L l.2))
    (hc : (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core) :
    (data x l j).background.normal (ParticularParameters.nativeStrip associatedStrip) (directions
        (B := B)) n z =
      ((parameters x l).nativeTangent j n).normal
        (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) := by
  rw [data_normal H, background_normal l n hR hT,
    tangent_normal (carrier_frequency H) l j hj]
  have he := referencePoint_eq_copy l n k hi z
  rw [he] at hp ht hc ⊢
  rw [ActualPrimaryDynamics.normal_eq_copy l.1 l.2 n ActualPrimary.standardRegion k hR hT hc]
  congr 1
  exact (ActualPrimaryDynamics.frame_normal (ActualPrimary.phases B N0 l.1) l.2
    ⟨hp,(ActualPrimary.phases B N0 l.1).interval l.2 ht⟩).symm

theorem transported_coordinates (x : CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native) :
    CopySolveCompatibility.nativeTimeMap 0
      (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (((parameters x l).geometry n).coordinates k z.2) = (referencePoint l n k z).2 :=
  ScaledTangentTransport.coordinates_transport (reference l).geometry (gap l n) 0 _ _ k z.2

theorem tangent_action (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) (z : Native) :
    ((parameters x l).nativeTangent j n).action
      (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) =
      ActualPrimaryDynamics.clockScale l.2 n • PrimaryCopyBridge.baseOperator
        ((ActualPrimary.phases B N0 l.1).phase.F l.2 (referencePoint l n k z).1)
        ((ActualPrimary.phases B N0 l.1).phase.shear l.2
          ((referencePoint l n k z).1,(referencePoint l n k z).2.2)) := by
  change PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) •
    PrimaryCopyBridge.baseOperator
      ((ActualPrimary.phases B N0 l.1).phase.F l.2 (referencePoint l n k z).1)
      ((ActualPrimary.phases B N0 l.1).phase.shear l.2
        ((referencePoint l n k z).1,
          (CopySolveCompatibility.nativeTimeMap 0
            (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
              (ChartScales.Q (BaseChartJets.cellBand l.2)))
            (((parameters x l).geometry n).coordinates k z.2)).2)) = _
  rw [transported_coordinates, ← ActualPrimaryDynamics.clockScale_eq]

theorem tangent_damping (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) (z : Native) :
    ((parameters x l).nativeTangent j n).damping
      (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) =
      ActualPrimaryDynamics.clockScale l.2 n * ((j:ℝ)^2 *
        (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2) *
          (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand l.2) : ℝ)^2 *
          ‖(ActualPrimary.phases B N0 l.1).phase.normal l.2
            ((referencePoint l n k z).1,(referencePoint l n k z).2.2)‖^2)) := by
  change PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) * ((j:ℝ)^2 *
    ((ActualPrimary.phases B N0 l.1).frame l.2).viscosity
      ((referencePoint l n k z).1,
        (CopySolveCompatibility.nativeTimeMap 0
            (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
              (ChartScales.Q (BaseChartJets.cellBand l.2)))
          (((parameters x l).geometry n).coordinates k z.2)).2)) = _
  rw [transported_coordinates, ← ActualPrimaryDynamics.clockScale_eq]
  rfl

theorem native_damping_match {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hc : (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core) :
    ((parameters x l).nativeTangent j n).damping
      (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) =
      (ParticularParameters.nativeStrip associatedStrip).epsilon n *
        (data x l j).background.frequency n ^ 2 *
        ‖(data x l j).background.normal (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) n z‖ ^ 2 := by
  rw [tangent_damping, data_normal H, background_normal l n hR hT, data_frequency H]
  rw [referencePoint_eq_copy l n k hi z] at hc ⊢
  rw [ActualPrimaryDynamics.normal_eq_copy l.1 l.2 n ActualPrimary.standardRegion k hR hT hc]
  change _ = ChartScales.epsilon ActualPrimary.h n * _ ^ 2 * _
  rw [mul_pow]
  calc
    _ = (j:ℝ)^2 * (ActualPrimaryDynamics.clockScale l.2 n *
        (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2) *
          (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand l.2) : ℝ)^2 *
          ‖(ActualPrimary.phases B N0 l.1).phase.normal l.2
            (ActualPrimary.phasePoint l.2
              (ActualPrimaryDynamics.copyPoint l.1 l.2 n k (nativeToFull z)))‖^2)) := by
                  simp only [ActualPrimary.phasePoint]; ring
    _ = _ := by rw [← ActualPrimaryDynamics.damping_scale]; ring

theorem reference_slotDirection (l : Label B N0) :
    ParticularWaveBounds.slotDirection (reference l).geometry =
      ChartScales.timeCoefficient ActualPrimary.h (BaseChartJets.cellBand l.2) •
        ActualPrimary.temporalVector := by
  change (ActualSignedGeometry.slotGeometry ActualPrimary.slots ActualPrimary.vectors_det
    (spatialLabel l) 0).basis (0,1) = _
  have he := ActualSignedGeometry.slotGeometry_basis ActualPrimary.slots ActualPrimary.vectors_det
    (spatialLabel l) 0 (0,1)
  simp only [zero_smul, zero_add, mul_one] at he
  exact he

theorem native_fast (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2)) :
    (directions (B := B)).fastScale n • (directions (B := B)).fast =
      ((0 : Parameter × ℝ), ParticularWaveBounds.slotDirection ((parameters x l).geometry n)) := by
  have hs : ParticularWaveBounds.slotDirection ((parameters x l).geometry n) =
      CommonBaseContext.fastCoefficient ActualPrimary.h (CommonWindow.index ActualPrimary.h) n •
        ActualPrimary.temporalVector := by
    apply (coverPower (gap l n)).injective
    change coverPower (gap l n)
      (ParticularWaveBounds.slotDirection
        (CopySolveCompatibility.transportGeometry (reference l).geometry (gap l n) 0 _ _)) = _
    conv_lhs => erw [ScaledTangentTransport.slotDirection_transport]
    rw [reference_slotDirection, map_smul,
      show coverPower (gap l n) ActualPrimary.temporalVector =
        ChartScales.Tg ^ gap l n • ActualPrimary.temporalVector from
          CommonBaseContext.coverPower_temporal _, smul_smul, smul_smul]
    change (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) *
        ChartScales.timeCoefficient ActualPrimary.h (BaseChartJets.cellBand l.2)) •
        ActualPrimary.temporalVector = _
    congr 1
    rw [← ActualPrimaryDynamics.clockScale_eq]
    unfold CommonBaseContext.fastCoefficient ChartScales.timeCoefficient
        ActualPrimaryDynamics.clockScale
    have he : CommonWindow.index ActualPrimary.h n + gap l n =
        ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2) := Nat.add_sub_of_le hi
    rw [← he, pow_add]
    field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand l.2))
      (1+ActualPrimary.h)).ne']
  rw [hs]
  change CommonBaseContext.fastCoefficient ActualPrimary.h (CommonWindow.index ActualPrimary.h) n •
      ((0 : Parameter × ℝ), ActualPrimary.temporalVector) = _
  simp only [Prod.smul_mk, smul_zero]

theorem native_action_match (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1) (v : ProblemStatement.Space) :
    CurlClassBounds.complexify (((parameters x l).nativeTangent j n).action
      (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k z) v) =
      LinearWaveResidual.shear ((data x l j).background.radius n)
        ((data x l j).background.frequencyBase n) ((data x l j).background.axialBase n)
        ((directions (B := B)).radialField n) (fun _ => CurlClassBounds.complexify v) z := by
  let q := nativeToFull z
  let a := ActualPrimary.chartCoefficients l.1 l.2
  let d := PrimaryResidualClass.directions (ActualPrimary.commonContext B)
  have hfg := ActualPrimaryDynamics.frequency_germ l.1 l.2 n k (x := q) hR hT
  have hgg := ActualPrimaryDynamics.axial_germ l.1 l.2 n k (x := q) hT
  obtain ⟨hFr,hGr⟩ := ActualPrimaryDynamics.native_base_differentiable l.1 l.2 n k (x := q) hR hT
  have hF : DifferentiableAt ℝ (a.frequencyBase n) q :=
    ((hFr.comp q (ActualPrimaryDynamics.copyPoint_hasFDerivAt l.1 l.2 n k
        q).fst.differentiableAt).const_mul
      (ActualPrimaryDynamics.clockScale l.2 n)).congr_of_eventuallyEq hfg
  have hG : DifferentiableAt ℝ (a.axialBase n) q :=
    ((hGr.comp q (ActualPrimaryDynamics.copyPoint_hasFDerivAt l.1 l.2 n k
        q).fst.differentiableAt).const_mul
      (ActualPrimaryDynamics.velocityScale l.2 n)).congr_of_eventuallyEq hgg
  have hr : LinearWaveResidual.shear ((data x l j).background.radius n)
      ((data x l j).background.frequencyBase n) ((data x l j).background.axialBase n)
      ((directions (B := B)).radialField n) (fun _ => CurlClassBounds.complexify v) z =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n)
        (d.radialField n) (fun _ => CurlClassBounds.complexify v) q := by
    change LinearWaveResidual.shear (fun y => a.radius n (nativeToFull y))
      (fun y => a.frequencyBase n (nativeToFull y)) (fun y => a.axialBase n (nativeToFull y))
      ((ParticularWaveBounds.reindexDirections nativeToFull d).radialField n)
      (fun _ => CurlClassBounds.complexify v) z = _
    rw [ParticularWaveBounds.reindex_radialField]
    simp only [LinearWaveResidual.shear, ParticularWaveBounds.along_reindex nativeToFull _ hF,
      ParticularWaveBounds.along_reindex nativeToFull _ hG, q]
  rw [hr, tangent_action, referencePoint_eq_copy l n k hi z]
  have hs := ActualPrimaryDynamics.copy_shear_function l.1 l.2 n k (fun _ => v) (x := q) hR hT
  rw [SignedWaveUpdate.shear_smul] at hs
  apply smul_right_injective _ (ActualPrimaryDynamics.velocityScale_pos l.2 n).ne'
  simpa only [_root_.smul_apply, map_smul, smul_smul, mul_comm,
    ActualPrimary.phasePoint, q, a, d] using hs.symm

theorem referencePoint_contDiff (l : Label B N0) (n : ℕ) (k : Frequency)
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2)) :
    ContDiff ℝ ∞ (referencePoint l n k) := by
  have he : referencePoint l n k =
      fun z => ActualPrimaryDynamics.copyPoint l.1 l.2 n k (nativeToFull z) :=
    funext (referencePoint_eq_copy l n k hi)
  rw [he]
  exact (ActualPrimaryDynamics.copyPoint_smooth l.1 l.2 n k).comp nativeToFull.contDiff

/-- The copied normal equality is a true germ, including on the closed
transverse core boundary.  Only slot time and the slow carrier are open. -/
theorem native_normal_germ {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (ht : (referencePoint l n k z).2.2 ∈ Ioo 0 ((ActualPrimary.phases B N0 l.1).L l.2))
    (hc : (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core) :
    (data x l j).background.normal (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n =ᶠ[𝓝 z]
      fun y => ((parameters x l).nativeTangent j n).normal
        (ParticularWaveBounds.nativePoint ((parameters x l).geometry n) k y) := by
  have hc' := hc
  rw [referencePoint_eq_copy l n k hi z] at hc'
  have hn := nativeToFull.continuous.continuousAt.eventually
    (ActualSignedDynamics.normal_eq_copy_germ l.1 l.2 n ActualPrimary.standardRegion k hR hT hc')
  have hp' := (referencePoint_contDiff l n k hi).continuous.fst.continuousAt.eventually
    ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).isOpen l.2
      |>.mem_nhds hp)
  have ht' := (referencePoint_contDiff l n k hi).continuous.snd.snd.continuousAt.eventually
    (isOpen_Ioo.mem_nhds ht)
  filter_upwards [hn, hp', ht',
    (isOpen_lt continuous_const continuous_fst.fst.fst).mem_nhds hR,
    (isOpen_lt continuous_const continuous_fst.fst.snd.fst).mem_nhds hT] with y hny hpy hty hRy hTy
  rw [data_normal H, background_normal l n hRy hTy, hny,
    tangent_normal (carrier_frequency H) l j hj,
    ← referencePoint_eq_copy l n k hi y]
  congr 1
  have hf := ActualPrimaryDynamics.frame_normal (ActualPrimary.phases B N0 l.1) l.2
    (z := ((referencePoint l n k y).1,(referencePoint l n k y).2.2))
    ⟨hpy,(ActualPrimary.phases B N0 l.1).interval l.2 ⟨hty.1.le,hty.2.le⟩⟩
  simpa only [ActualPrimary.phasePoint] using hf.symm

section ModalTangency

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {s : WeightedClasses.StripData (P × TorusInverse.Plane)} {α : ℝ}
  {ds : LinearWaveBounds.GraphDirections (P × TorusInverse.Plane)}
  {frame : ℕ → PrimaryODE.FrameData (P × ℝ)}
  {t : ℕ → TangentData P ProblemStatement.Space}
  {source : ℕ → P × TorusInverse.Plane → ComplexVector} {j : ℤ}
  {g : ℕ → Geometry} {len : ℕ → ℝ} {envelope : ℕ → ℝ → ℝ}
  {C : ℕ → Frequency → Set (P × TorusInverse.Plane)}

/-- The actual modal reconstruction is tangent throughout a neighborhood
of a closed-cell point.  The normal match is a primitive geometric germ;
the tangency of both solved components follows from the modal bridges. -/
theorem complexCopy_tangent_germ
    (a : LinearWaveBounds.WaveCoefficients (P × TorusInverse.Plane)) (hL : ∀ n, 0 < len n)
    (hr : ParticularCopyBounds.ModalControl s α frame
      (fun n => ParticularWaveBounds.realData (t n) (source n)) j g len envelope C)
    (hi : ParticularCopyBounds.ModalControl s α frame
      (fun n => ParticularWaveBounds.imagData (t n) (source n)) j g len envelope C)
    (n : ℕ) (k : Frequency) {z : P × TorusInverse.Plane} (hz : z ∈ s.domain) (hC : z ∈ C n k)
    (hN : a.normal s ds n =ᶠ[𝓝 z]
      fun y => (t n).normal (ParticularWaveBounds.nativePoint (g n) k y)) :
    (fun y => normalDot (a.normal s ds n y)
      ((ParticularWaveBounds.complexCopyCoefficients a t source g (fun _ => k) len hL).amplitude n
          y))
      =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [hN,
    (hr.open_neighborhood n k).mem_nhds (hr.contains n k z hz hC),
    (hi.open_neighborhood n k).mem_nhds (hi.contains n k z hz hC)] with y hy hyr hyi
  have htR := ParticularWaveBounds.copyVelocity_tangent_of_modal (frame n)
    (ParticularWaveBounds.realData (t n) (source n)) j (g n) k (hL n).le (hr.bridge n k) hyr
    ⟨(hr.current_slot n k y hyr).1.le,(hr.current_slot n k y hyr).2.le⟩
  have htI := ParticularWaveBounds.copyVelocity_tangent_of_modal (frame n)
    (ParticularWaveBounds.imagData (t n) (source n)) j (g n) k (hL n).le (hi.bridge n k) hyi
    ⟨(hi.current_slot n k y hyi).1.le,(hi.current_slot n k y hyi).2.le⟩
  rw [hy]
  change normalDot ((t n).normal (ParticularWaveBounds.nativePoint (g n) k y))
    (ParticularWaveBounds.copyVelocity (ParticularWaveBounds.realData (t n) (source n)) (g n) (hL
        n).le k y +
      Complex.I • ParticularWaveBounds.copyVelocity
        (ParticularWaveBounds.imagData (t n) (source n)) (g n) (hL n).le k y) = 0
  have hadd (N : ProblemStatement.Space) (u v : ComplexVector) :
      normalDot N (u + Complex.I • v) = normalDot N u + Complex.I * normalDot N v := by
    simp only [normalDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change normalDot ((t n).normal (ParticularWaveBounds.nativePoint (g n) k y))
    (ParticularWaveBounds.copyVelocity (ParticularWaveBounds.realData (t n) (source n)) (g n) (hL
        n).le k y) = 0 at htR
  change normalDot ((t n).normal (ParticularWaveBounds.nativePoint (g n) k y))
    (ParticularWaveBounds.copyVelocity (ParticularWaveBounds.imagData (t n) (source n)) (g n) (hL
        n).le k y) = 0 at htI
  rw [hadd,htR,htI,mul_zero,add_zero]

end ModalTangency

section ReindexGeometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem reindex_vector_derivative (e : E ≃ₗᵢ[ℝ] F) {V : F → F} {z : E}
    (hV : DifferentiableAt ℝ V (e z)) (w : F) :
    fderiv ℝ (ParticularWaveBounds.reindexVector e V) z (e.symm w) =
      e.symm (fderiv ℝ V (e z) w) := by
  have hd := e.symm.toContinuousLinearEquiv.hasFDerivAt.comp z
    (hV.hasFDerivAt.comp z e.toContinuousLinearEquiv.hasFDerivAt)
  change fderiv ℝ (e.symm.toContinuousLinearEquiv ∘ V ∘ e) z (e.symm w) = _
  rw [hd.fderiv]
  simp

theorem geometryAt_reindex (e : E ≃ₗᵢ[ℝ] F) {R : F → ℝ} {Vr Vθ Vz : F → F} {z : E}
    (G : ClosedNativeWaveIdentities.GeometryAt R Vr Vθ Vz (e z)) :
    ClosedNativeWaveIdentities.GeometryAt (fun y => R (e y))
      (ParticularWaveBounds.reindexVector e Vr) (ParticularWaveBounds.reindexVector e Vθ)
      (ParticularWaveBounds.reindexVector e Vz) z := by
  have smooth (V : F → F) (hV : ContDiffAt ℝ ∞ V (e z)) :
      ContDiffAt ℝ ∞ (ParticularWaveBounds.reindexVector e V) z :=
    e.symm.contDiff.contDiffAt.comp z (hV.comp z e.contDiff.contDiffAt)
  refine ⟨G.radius_smooth.comp z e.contDiff.contDiffAt, G.radius_ne,
    smooth Vr G.radial_smooth, smooth Vθ G.angular_smooth, smooth Vz G.axial_smooth, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
  · rw [ParticularWaveBounds.along_reindex e _ (G.radius_smooth.differentiableAt (by simp))]
    exact G.radial_radius
  · rw [ParticularWaveBounds.along_reindex e _ (G.radius_smooth.differentiableAt (by simp))]
    exact G.angular_radius
  · rw [ParticularWaveBounds.along_reindex e _ (G.radius_smooth.differentiableAt (by simp))]
    exact G.axial_radius
  · simp only [ParticularWaveBounds.reindexVector,
      reindex_vector_derivative e (G.radial_smooth.differentiableAt (by simp)),
      reindex_vector_derivative e (G.angular_smooth.differentiableAt (by simp)), G.radial_angular]
  · simp only [ParticularWaveBounds.reindexVector,
      reindex_vector_derivative e (G.radial_smooth.differentiableAt (by simp)),
      reindex_vector_derivative e (G.axial_smooth.differentiableAt (by simp)), G.radial_axial]
  · simp only [ParticularWaveBounds.reindexVector,
      reindex_vector_derivative e (G.angular_smooth.differentiableAt (by simp)),
      reindex_vector_derivative e (G.axial_smooth.differentiableAt (by simp)), G.angular_axial]

theorem geometryAt_of_cylindrical {Ω : Set F} {R : F → ℝ} {Vr Vθ Vz : F → F} {z : F}
    (G : CurlClassBounds.CylindricalGeometry Ω R Vr Vθ Vz) (hz : z ∈ Ω) :
    ClosedNativeWaveIdentities.GeometryAt R Vr Vθ Vz z :=
  ⟨G.radius_smooth.contDiffAt (G.isOpen.mem_nhds hz), G.radius_ne z hz,
    G.radial_smooth.contDiffAt (G.isOpen.mem_nhds hz),
    G.angular_smooth.contDiffAt (G.isOpen.mem_nhds hz),
    G.axial_smooth.contDiffAt (G.isOpen.mem_nhds hz),
    G.radial_radius z hz, G.angular_radius z hz, G.axial_radius z hz,
    G.radial_angular z hz, G.radial_axial z hz, G.angular_axial z hz⟩

end ReindexGeometry

theorem native_geometry (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) {z : Native} (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1) :
    ClosedNativeWaveIdentities.GeometryAt ((data x l j).background.radius n)
      ((directions (B := B)).radialField n) (fun _ => (directions (B := B)).angular)
      ((directions (B := B)).axialField (ParticularParameters.nativeStrip associatedStrip) n) z :=
          by
  have G := geometryAt_of_cylindrical
    (ActualPrimaryCoherence.piece_geometry ActualPrimary.standardRegion B n)
    (show nativeToFull z ∈ ActualPrimaryCoherence.positiveRadialChart from ⟨hR,hT⟩)
  have he := geometryAt_reindex nativeToFull G
  rw [native_strip_eq]
  simp only [directions, ParticularWaveBounds.reindex_radialField,
    ParticularWaveBounds.reindex_axialField] at he ⊢
  exact he

theorem invariant_native {E : Type} {f : ActualPrimary.FullPoint → E}
    (hf : CopyAngularInvariance.Invariant ((0 : CyclePoint), 1) f) :
    CopyAngularInvariance.Invariant (directions (B := B)).angular (fun z => f (nativeToFull z)) :=
        by
  intro z t
  have he : nativeToFull (z+t • (directions (B := B)).angular) =
      nativeToFull z + t • ((0 : CyclePoint),1) := by
    rw [map_add,map_smul]
    rfl
  change f (nativeToFull (z+t • (directions (B := B)).angular)) = f (nativeToFull z)
  rw [he]
  exact hf _ _

theorem native_angular (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) (k : Frequency) :
    ClosedNativeWaveIdentities.AngularData ((data x l j).raw k)
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
      (fun m => (data x l j).cutoff m k) n := by
  have hA := ActualPrimary.chartCoefficients_angular l.1 l.2
  refine ⟨invariant_native (B := B) (hA.radius n),
    invariant_native (B := B) (hA.radialBase n),
    invariant_native (B := B) (hA.frequencyBase n),
    invariant_native (B := B) (hA.axialBase n), ?_, ?_, ?_, ?_, ?_⟩
  · have hi := (invariant_native (B := B)
      (PrimaryResidualClass.directions_radial_invariant (ActualPrimary.commonContext B) n)).map
        nativeToFull.symm
    simp only [directions, ParticularWaveBounds.reindex_radialField] at hi ⊢
    exact hi
  · exact ⟨_, ParticularWaveAssembly.actualCarrier_affine (parameters x l).background
      (assembly x l).carrierBlock j n⟩
  · exact ParticularWaveAssembly.complexCopyVelocity_invariant
      (ParticularWaveAssembly.angleTangent_invariant _) (ParticularWaveAssembly.angleLift_invariant
          _)
      ((parameters x l).geometry n) ((parameters x l).length_pos n).le k
  · exact ParticularWaveAssembly.complexCopyPressure_invariant
      (ParticularWaveAssembly.angleTangent_invariant _) (ParticularWaveAssembly.angleLift_invariant
          _)
      ((parameters x l).geometry n) ((parameters x l).length_pos n).le k _
  · exact CopyAngularInvariance.nativeCutoff_invariant ((0 : Parameter), (1 : ℝ))
      ((parameters x l).geometry n) ((parameters x l).cutoff n) k

theorem associated_frame_match (l : Label B N0) :
    WaveFrameMatch (associatedContext (B := B)) (HarmonicWaveInteraction.productStrip
        associatedStrip)
      (ParticularWaveBounds.reindexDirections ParticularWaveAssembly.angleShuffle (directions (B :=
          B)))
      (ParticularWaveBounds.reindexCoefficients ParticularWaveAssembly.angleShuffle (background l))
          := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, rfl, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro n
    exact PrimaryResidualClass.directions_radial (associatedContext (B := B)) n
  · intro n
    exact PrimaryResidualClass.directions_axial associatedStrip (associatedContext (B := B)) rfl n
  · intro n
    exact PrimaryResidualClass.directions_time associatedStrip (associatedContext (B := B)) rfl n

theorem native_radialProfile_smoothAt {z : Native} (hR : 0 < z.1.1.1) :
    ContDiffAt ℝ ∞ (directions (B := B)).radialProfile z := by
  change ContDiffAt ℝ ∞ (fun y : Native =>
    ChartScales.radialExponent ActualPrimary.h * y.1.1.1 ^ (ChartScales.radialExponent
        ActualPrimary.h - 1)) z
  exact contDiffAt_const.mul (contDiffAt_fst.fst.fst.rpow_const_of_ne hR.ne')

theorem native_base_smoothAt (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) {z : Native} (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1) :
    ContDiffAt ℝ ∞ ((data x l j).background.radialBase n) z ∧
    ContDiffAt ℝ ∞ ((data x l j).background.frequencyBase n) z ∧
    ContDiffAt ℝ ∞ ((data x l j).background.axialBase n) z := by
  let χ : Native → PhaseCalculus.Slow := fun y => (y.1.1.1,(y.1.1.2.2,y.1.1.2.1))
  have hχ : ContDiff ℝ ∞ χ := contDiff_fst.fst.fst.prodMk
    (contDiff_fst.fst.snd.snd.prodMk contDiff_fst.fst.snd.fst)
  refine ⟨?_,?_,?_⟩
  · exact (BaseContextAssembly.radialSlow_smoothAt ActualPrimary.certificate
      ActualPrimary.modulation
      ActualPrimary.upper B n (p := χ z) hT).comp z hχ.contDiffAt
  · exact (ActualPrimaryCoherence.frequencySlow_smoothAt B n (p := χ z) hR hT).comp z hχ.contDiffAt
  · exact (ActualPrimaryCoherence.axialSlow_smoothAt B n (p := χ z) hT).comp z hχ.contDiffAt

theorem data_phase_smoothAt {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : Native}
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1) :
    ContDiffAt ℝ ∞ ((data x l j).background.phase n) z := by
  rw [data_phase H]
  exact ((ActualPrimaryCoherence.chart_phase_smooth l.1 l.2 n).contDiffAt
    (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds
      (show nativeToFull z ∈ ActualPrimaryCoherence.positiveRadialChart from ⟨hR,hT⟩))).comp z
        nativeToFull.contDiff.contDiffAt

theorem native_cutoff_smooth (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ ((data x l j).cutoff n k) := by
  let χ : Native → TorusInverse.Plane := fun z => CopySolveCompatibility.nativeTimeMap 0
    (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (((parameters x l).geometry n).coordinates k z.2)
  have hχ : ContDiff ℝ ∞ χ := by
    change ContDiff ℝ ∞ (fun z : Native =>
      ((((parameters x l).geometry n).coordinates k z.2).1,
        0 + PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
          (ChartScales.Q (BaseChartJets.cellBand l.2)) *
            (((parameters x l).geometry n).coordinates k z.2).2))
    have hcoord : ContDiff ℝ ∞ (fun z : Native =>
        ((parameters x l).geometry n).coordinates k z.2) :=
      (((parameters x l).geometry n).coordinates_contDiff k).comp contDiff_snd
    exact hcoord.fst.prodMk (contDiff_const.add (contDiff_const.mul hcoord.snd))
  dsimp only [data, ParticularParameters.copyData, parameters, ParticularParameters.fromReference]
  exact ((ActualPrimary.clockWindow l.2).cutoff_contDiff.comp hχ).mul
    ((GaussianTailFlat.slotCutoff_contDiff ((ActualPrimary.phases B N0 l.1).L l.2)).comp hχ.snd)

theorem native_normal_ne {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (ht : (referencePoint l n k z).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 l.1).L l.2))
    (hc : (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core) :
    (data x l j).background.normal (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n z ≠ 0 := by
  rw [data_normal H, background_normal l n hR hT]
  rw [referencePoint_eq_copy l n k hi z] at hp ht hc
  rw [ActualPrimaryDynamics.normal_eq_copy l.1 l.2 n ActualPrimary.standardRegion k hR hT hc]
  apply smul_ne_zero (ActualPrimaryDynamics.normalScale_pos l.2 n).ne'
  intro hzero
  have hn := ActualPrimaryDynamics.frame_tail_ne (ActualPrimary.phases B N0 l.1) l.2
    (z := ActualPrimary.phasePoint l.2 (ActualPrimaryDynamics.copyPoint l.1 l.2 n k (nativeToFull
        z)))
    ⟨hp,(ActualPrimary.phases B N0 l.1).interval l.2 ht⟩
  exact hn (by rw [hzero]; ext i; fin_cases i <;> rfl)

theorem rawJets_at {x : CycleState (Label B N0)} (H : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2))
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (ht : (referencePoint l n k z).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 l.1).L l.2))
    (hc : (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core)
    (ha : ContDiffAt ℝ ∞ ((data x l j).amplitude n k) z)
    (hpres : ContDiffAt ℝ ∞ ((data x l j).pressure n k) z) :
    ClosedNativeWaveIdentities.RawJetsAt ((data x l j).raw k)
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
      (fun m => (data x l j).cutoff m k) n z := by
  obtain ⟨hb,hF,hG⟩ := native_base_smoothAt x l j n hR hT
  exact ⟨native_radialProfile_smoothAt hR, data_phase_smoothAt H l j n hR hT,
    contDiffAt_fst.fst.fst, hb.differentiableAt (by simp), hF.differentiableAt (by simp),
    hG.differentiableAt (by simp), ha, hpres.differentiableAt (by simp),
    (native_cutoff_smooth x l j n k).contDiffAt, hR.ne', native_normal_ne H l j n k hi hR hT hp ht
        hc⟩

section ZeroCutoff

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedSpace ℝ D] in
theorem localized_zero_of_cutoff_germ (a : PeriodizedWaveBounds.CopyData D I)
    {n : ℕ} {i : I} {z : D} (h : a.cutoff n i =ᶠ[𝓝 z] fun _ => 0) :
    ((a.localized i).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
      ((a.localized i).pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  constructor
  · filter_upwards [h] with y hy
    change a.cutoff n i y • a.amplitude n i y = 0
    rw [hy, zero_smul]
  · filter_upwards [h] with y hy
    change (a.cutoff n i y : ℂ) * a.pressure n i y = 0
    rw [hy, Complex.ofReal_zero, zero_mul]

theorem gaussian_eq_source_of_cutoff_germ (a : PeriodizedWaveBounds.CopyData D I)
    (d : LinearWaveBounds.GraphDirections D) {n : ℕ} {i : I} {z : D}
    (h : a.cutoff n i =ᶠ[𝓝 z] fun _ => 0) :
    a.localGaussian d n i =ᶠ[𝓝 z] a.source n := by
  have hd := ParticularWaveAssembly.along_germ h (d.fastField n)
  filter_upwards [h, hd] with y hy hdy
  change along (d.fastField n) (a.cutoff n i) y • a.amplitude n i y +
    (1-a.cutoff n i y) • a.source n y = a.source n y
  rw [hdy,hy]
  simp [along]

theorem cancellation_of_cutoff_germ (a : PeriodizedWaveBounds.CopyData D I)
    (s : WeightedClasses.StripData D) (d : LinearWaveBounds.GraphDirections D)
    {n : ℕ} {i : I} {z : D} (h : a.cutoff n i =ᶠ[𝓝 z] fun _ => 0) :
    (a.corrected s d i).harmonicResidual s d n z +
        (fun q => a.source n z q * carrier (a.background.frequency n) (a.background.phase n) z) =
      (fun q => (a.localGood s d n i z q + a.localGaussian d n i z q) *
        carrier (a.background.frequency n) (a.background.phase n) z) := by
  obtain ⟨ha,hp⟩ := localized_zero_of_cutoff_germ a h
  have hout := (LocalizedWaveBounds.nativeFamily a).outputs_zero_germs s d ha hp
  have hr := CorrectionStep.harmonicResidual_zero_germ (a.corrected s d i) s d hout.2.1 hp
  have hg : a.localGood s d n i =ᶠ[𝓝 z] fun _ => 0 := hout.2.2
  rw [hr.eq_of_nhds,hg.eq_of_nhds,(gaussian_eq_source_of_cutoff_germ a d h).eq_of_nhds]
  ext q
  simp

end ZeroCutoff

/-- Selected directions as an element of `LinearWaveBounds.GraphDirections Native`. -/
noncomputable def selectedDirections (e : ℕ → ActivePair B N0) :
    LinearWaveBounds.GraphDirections Native :=
  { directions (B := B) with
    radialScale := fun q => (directions (B := B)).radialScale (selectedBand e q)
    fastScale := fun q => (directions (B := B)).fastScale (selectedBand e q) }

/-- Modal strip, constructed using `UniformPrimaryWeights.reindexedStrip`. -/
noncomputable def modalStrip (e : ℕ → ActivePair B N0) :=
  UniformPrimaryWeights.reindexedStrip
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
    (fun q => (q, ()))

theorem selected_principal {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (e : ℕ → ActivePair B N0) (q : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (modalStrip e).domain) (hcell : z ∈ selectedPatch e () q k)
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint (selectedLabel e q) (selectedBand e q) k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier
        (selectedLabel e q).2)
    (ht : (referencePoint (selectedLabel e q) (selectedBand e q) k z).2.2 ∈
      Icc 0 ((ActualPrimary.phases B N0 (selectedLabel e q).1).L (selectedLabel e q).2))
    (hc : (referencePoint (selectedLabel e q) (selectedBand e q) k z).2 ∈
      (ActualPrimary.clockWindow (selectedLabel e q).2).core) :
    ((data x (selectedLabel e q) j).raw k).principal
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) (selectedBand e q) z
          =
        -(data x (selectedLabel e q) j).source (selectedBand e q) z := by
  let hr := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.realPart).pull (fun q => (q, ()))
  let hi := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.imagPart).pull (fun q => (q, ()))
  have hindex := CommonWindow.index_le (h := ActualPrimary.h) (e q).property.2
  have hfreq : (selectedBackground e x j ()).frequency q ≠ 0 := by
    change (data x (selectedLabel e q) j).background.frequency (selectedBand e q) ≠ 0
    rw [data_frequency Hc]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hj)
      (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos ActualPrimary.h (selectedBand e
          q))).ne'
  have hnormal :
      (selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z =
        (data x (selectedLabel e q) j).background.normal
          (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
          (selectedBand e q) z := rfl
  have hN : (selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z =
      (selectedTangent e x j () q).normal
        (ParticularWaveBounds.nativePoint (selectedGeometry e () q) k z) := by
    rw [hnormal]
    exact native_normal_match Hc (selectedLabel e q) j hj (selectedBand e q) k
      hindex hR hT hp ht hc
  have hδ : (selectedTangent e x j () q).damping
      (ParticularWaveBounds.nativePoint (selectedGeometry e () q) k z) =
      (modalStrip e).epsilon q * (selectedBackground e x j ()).frequency q ^ 2 *
        ‖(selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z‖ ^ 2 := by
    rw [hnormal]
    exact native_damping_match Hc (selectedLabel e q) j (selectedBand e q) k hindex hR hT hc
  have hfast : (selectedDirections e).fastScale q • (selectedDirections e).fast =
      ((0 : Parameter × ℝ), slotDirection (selectedGeometry e () q)) :=
    native_fast x (selectedLabel e q) (selectedBand e q) hindex
  have hA := native_action_match x (selectedLabel e q) j (selectedBand e q) k hindex hR hT
  have result := NativePrincipalEquations.complexCopyCoefficients_principal_at
    (s := modalStrip e) (dirs := selectedDirections e)
    (frame := fun r => selectedFrame e r) (t := selectedTangent e x j ())
    (source := selectedSource e x j ()) (harmonic := j)
    (g := selectedGeometry e ()) (L := selectedLength e ())
    (envelope := selectedPulseEnvelope e ()) (K := fun r => selectedPatch e () r)
    (selectedBackground e x j ())
    (fun r => ScaledActualParticularControl.length_pos (selectedConstruction e) (selectedClock e)
        () r)
    hr hi q k hz hcell hfreq hN hδ hfast hA
  exact result

theorem controlPatch_geometry (x : CycleState (Label B N0)) (l : Label B N0)
    (n : ℕ) (k : Frequency) {z : Native} (hz : z ∈ controlPatch l n k) :
    0 < z.1.1.1 ∧ 0 < z.1.1.2.1 ∧
    (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2 ∧
    (referencePoint l n k z).2.2 ∈ Ioo 0 ((ActualPrimary.phases B N0 l.1).L l.2) ∧
    (referencePoint l n k z).2 ∈ (ActualPrimary.clockWindow l.2).core := by
  have hp := ActualPrimaryCoherence.piece_domain_positive ActualPrimary.standardRegion
    (show nativeToFull z ∈ (HarmonicWaveInteraction.productStrip
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)).domain
          from hz.2.1.1)
  have hslow : (referencePoint l n k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2 :=
    hz.2.1.2.1
  have hclock : 0 < PhysicalParticularWave.clockWeight ActualPrimary.h
      (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) :=
    PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _
  have hc : (referencePoint l n k z).2 =
      CopySolveCompatibility.nativeTimeMap 0
        (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
          (ChartScales.Q (BaseChartJets.cellBand l.2)))
        (((canonicalParameters l).geometry n).coordinates k z.2) :=
    (transported_coordinates x l n k z).symm
  have ht : (referencePoint l n k z).2.2 ∈ Ioo 0 ((ActualPrimary.phases B N0 l.1).L l.2) := by
    rw [hc]
    simp only [CopySolveCompatibility.nativeTimeMap, zero_add, mem_Ioo]
    refine ⟨mul_pos hclock hz.2.1.2.2.1, ?_⟩
    have hh := (lt_div_iff₀ hclock).mp hz.2.1.2.2.2
    simp only [mul_comm] at hh ⊢
    exact hh
  refine ⟨hp.1,hp.2,hslow,ht,?_⟩
  change (referencePoint l n k z).2.1 ∈ Icc (-ActualPrimary.slots.radius)
      ActualPrimary.slots.radius ∧
    (referencePoint l n k z).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 0).L l.2)
  constructor
  · rw [hc]
    exact hz.2.2
  · exact ⟨ht.1.le,ht.2.le⟩

theorem native_principal {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    ((data x l j).raw k).principal (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n z = -(data x l j).source n z := by
  let e : ℕ → ActivePair B N0 := fun _ => ⟨(l,n),hz.1⟩
  obtain ⟨hR,hT,hp,ht,hcore⟩ := controlPatch_geometry x l n k hz
  have hcell : z ∈ selectedPatch e () 0 k := by
    rw [← selected_controlPatch e () 0 k]
    exact hz
  exact selected_principal Hc j hj Hs e 0 k hz.2.1.1 hcell hR hT hp
    ⟨ht.1.le,ht.2.le⟩ hcore

theorem native_tangency_germ {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    (fun y => normalDot ((data x l j).background.normal
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) n y)
      ((data x l j).amplitude n k y)) =ᶠ[𝓝 z] fun _ => 0 := by
  let e : ℕ → ActivePair B N0 := fun _ => ⟨(l,n),hz.1⟩
  let hr := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.realPart).pull (fun q => (q, ()))
  let hi := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.imagPart).pull (fun q => (q, ()))
  obtain ⟨hR,hT,hp,ht,hcore⟩ := controlPatch_geometry x l n k hz
  have hindex := CommonWindow.index_le (h := ActualPrimary.h) hz.1.2
  have hcell : z ∈ selectedPatch e () 0 k := by
    rw [← selected_controlPatch e () 0 k]
    exact hz
  have hN : (selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) 0 =ᶠ[𝓝 z]
      fun y => (selectedTangent e x j () 0).normal
        (ParticularWaveBounds.nativePoint (selectedGeometry e () 0) k y) :=
    native_normal_germ Hc l j hj n k hindex hR hT hp ht hcore
  have result := complexCopy_tangent_germ
    (s := modalStrip e) (ds := selectedDirections e)
    (frame := fun r => selectedFrame e r) (t := selectedTangent e x j ())
    (source := selectedSource e x j ()) (j := j)
    (g := selectedGeometry e ()) (len := selectedLength e ())
    (envelope := selectedPulseEnvelope e ()) (C := fun r => selectedPatch e () r)
    (selectedBackground e x j ())
    (fun r => ScaledActualParticularControl.length_pos (selectedConstruction e) (selectedClock e)
        () r)
    hr hi 0 k hz.2.1.1 hcell hN
  exact result

theorem native_rawJets {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    ClosedNativeWaveIdentities.RawJetsAt ((data x l j).raw k)
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
      (fun m => (data x l j).cutoff m k) n z := by
  obtain ⟨hR,hT,hp,ht,hcore⟩ := controlPatch_geometry x l n k hz
  have hindex := CommonWindow.index_le (h := ActualPrimary.h) hz.1.2
  have hraw := ActualParticularStageControls.raw_jets x (carrier_frequency Hc) j hj Hs
  exact rawJets_at Hc l j n k hindex hR hT hp ⟨ht.1.le,ht.2.le⟩ hcore
    (hraw.1.smooth l n k z hz.2.1.1 hz) (hraw.2.smooth l n k z hz.2.1.1 hz)

theorem frequency_ne {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    (data x l j).background.frequency n ≠ 0 := by
  rw [data_frequency Hc]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hj)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos ActualPrimary.h n)).ne'

/-- The literal common-cover inverse solves the current source at every
closed transverse cell point. No open-cell or final equation hypothesis is used. -/
theorem native_cancellation {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    ((data x l j).corrected (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) k).harmonicResidual (ParticularParameters.nativeStrip associatedStrip)
        (directions (B := B)) n z +
        (fun i => (data x l j).source n z i *
          carrier ((data x l j).background.frequency n) ((data x l j).background.phase n) z) =
      (fun i => ((data x l j).localGood (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) n k z i + (data x l j).localGaussian (directions (B := B)) n k z i)
              *
        carrier ((data x l j).background.frequency n) ((data x l j).background.phase n) z) := by
  obtain ⟨hR,hT,_⟩ := controlPatch_geometry x l n k hz
  exact (native_rawJets Hc j hj Hs l n k hz).cancellation (native_angular x l j n k)
    (native_geometry x l j n hR hT).radial_radius (data x l j).source
    (native_principal Hc j hj Hs l n k hz)

theorem native_realizes_curl {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    CurlClassBounds.cylindricalCurl ((data x l j).background.radius n)
      ((directions (B := B)).radialField n) (fun _ => (directions (B := B)).angular)
      ((directions (B := B)).axialField (ParticularParameters.nativeStrip associatedStrip) n)
      (((data x l j).localized k).curlPotential (ParticularParameters.nativeStrip associatedStrip)
        (directions (B := B)) n) z =
      vectorMode ((data x l j).background.frequency n) ((data x l j).background.phase n)
        (((data x l j).corrected (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) k).amplitude n) z :=
  ClosedNativeWaveIdentities.native_realizes_curl_at (a := data x l j)
    (s := ParticularParameters.nativeStrip associatedStrip) (d := directions (B := B)) n k z
    (native_rawJets Hc j hj Hs l n k hz) (frequency_ne Hc l j hj n)
    (native_tangency_germ Hc j hj Hs l n k hz).eq_of_nhds

theorem native_divergence_zero {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    cylindricalDivergence ((data x l j).background.radius n)
      ((directions (B := B)).radialField n) (fun _ => (directions (B := B)).angular)
      ((directions (B := B)).axialField (ParticularParameters.nativeStrip associatedStrip) n)
      (vectorMode ((data x l j).background.frequency n) ((data x l j).background.phase n)
        (((data x l j).corrected (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) k).amplitude n)) z = 0 := by
  obtain ⟨hR,hT,_⟩ := controlPatch_geometry x l n k hz
  exact ClosedNativeWaveIdentities.native_divergence_zero_at (a := data x l j)
    (s := ParticularParameters.nativeStrip associatedStrip) (d := directions (B := B)) n k z
    (native_rawJets Hc j hj Hs l n k hz) (native_geometry x l j n hR hT)
    (frequency_ne Hc l j hj n) (native_tangency_germ Hc j hj Hs l n k hz)

/-- The support information supplied by the actual incoming source and
the common-cover cutoff. The last alternative is proved by zero source
on the whole native solve path. It contains no differential equation. -/
structure SupportData (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) where
  /-- Cells of `SupportData`, of type `PeriodizedWaveBounds.Cells Native Frequency`. -/
  cells : PeriodizedWaveBounds.Cells Native Frequency
  cutoff_support : ∀ n k, support ((data x l j).cutoff n k) ⊆ cells.carrier n k
  cover : ∀ n k z, z ∈ (ParticularParameters.nativeStrip associatedStrip).domain →
    z ∈ cells.carrier n k → z ∈ controlPatch l n k ∨
      ((data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∨
      (((data x l j).amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
        ((data x l j).pressure n k =ᶠ[𝓝 z] fun _ => 0) ∧
        ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0))

theorem localized_zero_of_fields {D I : Type} [NormedAddCommGroup D]
    (a : PeriodizedWaveBounds.CopyData D I) {n : ℕ} {k : I} {z : D}
    (ha : a.amplitude n k =ᶠ[𝓝 z] fun _ => 0)
    (hp : a.pressure n k =ᶠ[𝓝 z] fun _ => 0) :
    ((a.localized k).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    ((a.localized k).pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  constructor
  · filter_upwards [ha] with y hy
    change a.cutoff n k y • a.amplitude n k y = 0
    rw [hy,smul_zero]
  · filter_upwards [hp] with y hy
    change (a.cutoff n k y : ℂ) * a.pressure n k y = 0
    rw [hy,mul_zero]

theorem SupportData.localized_alternative {x : CycleState (Label B N0)}
    {l : Label B N0} {j : ℤ} (S : SupportData x l j)
    {n : ℕ} {k : Frequency} {z : Native}
    (hz : z ∈ (ParticularParameters.nativeStrip associatedStrip).domain)
    (hk : z ∈ S.cells.carrier n k) : z ∈ controlPatch l n k ∨
      (((data x l j).localized k).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
      (((data x l j).localized k).pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  rcases S.cover n k z hz hk with hc | hcut | ⟨ha,hp,_⟩
  · exact Or.inl hc
  · exact Or.inr (localized_zero_of_cutoff_germ _ hcut)
  · exact Or.inr (localized_zero_of_fields _ ha hp)

/-- Actual wave used in actual particular dynamics. -/
noncomputable def actualWave (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :=
  (parameters x l).wave associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

theorem common_cancellation {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) {z : Native}
    (hz : z ∈ (ParticularParameters.nativeStrip associatedStrip).domain) :
    (actualWave x l j).harmonicResidual (ParticularParameters.nativeStrip associatedStrip)
        (directions (B := B)) n z +
      (fun i => (data x l j).source n z i *
        carrier ((data x l j).background.frequency n) ((data x l j).background.phase n) z) =
      (fun i => ((data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) n z i + (data x l j).globalGaussian (directions (B := B)) n z i) *
        carrier ((data x l j).background.frequency n) ((data x l j).background.phase n) z) := by
  apply (data x l j).common_cancellation S.cells S.cutoff_support
    (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) ?_ n hz
  intro m k y hy hk
  rcases S.cover m k y hy hk with hc | hcut | ⟨ha,hp,hf⟩
  · exact native_cancellation Hc j hj Hs l m k hc
  · exact cancellation_of_cutoff_germ _ _ _ hcut
  · obtain ⟨ha',hp'⟩ := localized_zero_of_fields _ ha hp
    exact CorrectionStep.local_cancellation_of_zero_germs _ _ _ ha' hp'
      ((data x l j).localGaussian_zero_of_fields _ ha hf) hf

theorem common_realizes_curl {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) {z : Native}
    (hz : z ∈ (ParticularParameters.nativeStrip associatedStrip).domain) :
    CurlClassBounds.cylindricalCurl ((data x l j).background.radius n)
      ((directions (B := B)).radialField n) (fun _ => (directions (B := B)).angular)
      ((directions (B := B)).axialField (ParticularParameters.nativeStrip associatedStrip) n)
      ((data x l j).common.curlPotential (ParticularParameters.nativeStrip associatedStrip)
        (directions (B := B)) n) z =
      vectorMode ((actualWave x l j).frequency n) ((actualWave x l j).phase n)
        ((actualWave x l j).amplitude n) z := by
  apply (data x l j).common_realizes_curl S.cells S.cutoff_support
    (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) ?_ n hz
  intro m k y hy hk
  rcases S.localized_alternative hy hk with hc | ⟨ha,_⟩
  · exact native_realizes_curl Hc j hj Hs l m k hc
  · exact (LocalizedCurlRealization.native_identities_of_zero_germ _ _ _ ha).1

theorem common_divergence_zero {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) {z : Native}
    (hz : z ∈ (ParticularParameters.nativeStrip associatedStrip).domain) :
    cylindricalDivergence ((data x l j).background.radius n)
      ((directions (B := B)).radialField n) (fun _ => (directions (B := B)).angular)
      ((directions (B := B)).axialField (ParticularParameters.nativeStrip associatedStrip) n)
      (vectorMode ((actualWave x l j).frequency n) ((actualWave x l j).phase n)
        ((actualWave x l j).amplitude n)) z = 0 := by
  apply (data x l j).common_divergence_zero S.cells S.cutoff_support
    (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) ?_ n hz
  intro m k y hy hk
  rcases S.localized_alternative hy hk with hc | ⟨ha,_⟩
  · exact native_divergence_zero Hc j hj Hs l m k hc
  · exact (LocalizedCurlRealization.native_identities_of_zero_germ _ _ _ ha).2

theorem common_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) :
    ContDiffOn ℝ ∞ ((actualWave x l j).amplitude n)
      (ParticularParameters.nativeStrip associatedStrip).domain ∧
    ContDiffOn ℝ ∞ ((actualWave x l j).pressure n)
      (ParticularParameters.nativeStrip associatedStrip).domain := by
  have hs := (ParticularParameters.nativeStrip associatedStrip).isOpen_domain
  constructor <;> apply hs.contDiffOn_iff.mpr <;> intro z hz
  · by_cases he : ∃ k, z ∈ S.cells.carrier n k
    · obtain ⟨k,hk⟩ := he
      have hn : ContDiffAt ℝ ∞
          (((data x l j).corrected (ParticularParameters.nativeStrip associatedStrip)
            (directions (B := B)) k).amplitude n) z := by
        rcases S.localized_alternative hz hk with hc | ⟨ha,_⟩
        · exact (native_rawJets Hc j hj Hs l n k hc).corrected_amplitude
        · exact contDiffAt_const.congr_of_eventuallyEq
            (LocalizedCurlRealization.native_zero_germs _ _ _ ha).2.1
      exact hn.congr_of_eventuallyEq ((data x l j).commonCorrected_amplitude_germ
        S.cells S.cutoff_support (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) n hk)
    · exact contDiffAt_const.congr_of_eventuallyEq ((data x l j).commonCorrected_zero_germ
        S.cells S.cutoff_support (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) (not_exists.mp he))
  · by_cases he : ∃ k, z ∈ S.cells.carrier n k
    · obtain ⟨k,hk⟩ := he
      have hn : ContDiffAt ℝ ∞ (((data x l j).localized k).pressure n) z := by
        rcases S.localized_alternative hz hk with hc | ⟨_,hp⟩
        · have hr := (ActualParticularStageControls.raw_jets x (carrier_frequency Hc) j hj Hs).2
          exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z
            (native_cutoff_smooth x l j n k).contDiffAt).mul (hr.smooth l n k z hz hc)
        · exact contDiffAt_const.congr_of_eventuallyEq hp
      exact hn.congr_of_eventuallyEq ((data x l j).common_pressure_germ S.cells S.cutoff_support n
          hk)
    · exact contDiffAt_const.congr_of_eventuallyEq
        ((data x l j).common_zero_germs S.cells S.cutoff_support (not_exists.mp he)).2

theorem common_amplitude_invariant (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) :
    CopyAngularInvariance.Invariant (directions (B := B)).angular ((actualWave x l j).amplitude n)
        := by
  exact (data x l j).commonCorrected_invariant (ParticularParameters.nativeStrip associatedStrip)
    (directions (B := B)) (directions (B := B)).angular
    (fun m k => (native_angular x l j m k).cutoff)
    (fun m k => (native_angular x l j m k).amplitude)
    (fun m => (native_angular x l j m 0).radius)
    (fun m => (native_angular x l j m 0).radial_field)
    (fun _ => CopyAngularInvariance.Invariant.const _)
    (fun m => (native_angular x l j m 0).phase) n

theorem common_pressure_invariant (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) :
    CopyAngularInvariance.Invariant (directions (B := B)).angular ((actualWave x l j).pressure n) :=
  (data x l j).common_pressure_invariant (directions (B := B)).angular
    (fun m k => (native_angular x l j m k).cutoff)
    (fun m k => (native_angular x l j m k).pressure) n

theorem common_good_invariant (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) :
    CopyAngularInvariance.Invariant (directions (B := B)).angular
      ((data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip) (directions (B :=
          B)) n) :=
  (data x l j).globalGood_invariant (ParticularParameters.nativeStrip associatedStrip) (directions
      (B := B))
    (fun m k => (native_angular x l j m k).cutoff)
    (fun m k => (native_angular x l j m k).amplitude)
    (fun m k => (native_angular x l j m k).pressure)
    (fun m => (native_angular x l j m 0).radius)
    (fun m => (native_angular x l j m 0).radial_base)
    (fun m => (native_angular x l j m 0).frequency_base)
    (fun m => (native_angular x l j m 0).axial_base)
    (fun m => (native_angular x l j m 0).radial_field)
    (fun _ => CopyAngularInvariance.Invariant.const _)
    (fun m => (native_angular x l j m 0).phase) n

theorem common_gaussian_invariant (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) :
    CopyAngularInvariance.Invariant (directions (B := B)).angular
      ((data x l j).globalGaussian (directions (B := B)) n) :=
  (data x l j).globalGaussian_invariant (directions (B := B)) (directions (B := B)).angular
    (fun m k => (native_angular x l j m k).cutoff)
    (fun m k => (native_angular x l j m k).amplitude)
    (by
      intro m
      change CopyAngularInvariance.Invariant (((0 : Parameter),1),(0 : TorusInverse.Plane))
        (angleLift (residualSource (assembly x l).context (assembly x l).state
          (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j m))
      exact angleLift_invariant _) n

theorem source_frequency_ne {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) : (assembly x l).carrierBlock.frequency n ≠ 0 := by
  change (x.coefficients.blocks l).frequency n ≠ 0
  rw [carrier_frequency Hc]
  exact (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos ActualPrimary.h n)).ne'

/-- Actual update used in actual particular dynamics. -/
noncomputable def actualUpdate (x : CycleState (Label B N0)) (l : Label B N0) (N : ℕ) :=
  (parameters x l).updateBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

/-- Actual good used in actual particular dynamics. -/
noncomputable def actualGood (x : CycleState (Label B N0)) (l : Label B N0) (N : ℕ) :=
  (parameters x l).goodBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

/-- Actual gaussian used in actual particular dynamics. -/
noncomputable def actualGaussian (x : CycleState (Label B N0)) (l : Label B N0) (N : ℕ) :=
  (parameters x l).gaussianBlock (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

theorem update_represents {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (N : ℕ) :
    (actualUpdate x l N).oscillation =
      (fun n z i => ∑ j ∈ modes N, (vectorMode ((actualWave x l j).frequency n)
        ((actualWave x l j).phase n) ((actualWave x l j).amplitude n) (angleShuffle z) i).re) ∧
    (actualUpdate x l N).oscillatoryPressure =
      (fun n z => ∑ j ∈ modes N, (mode ((actualWave x l j).frequency n)
        ((actualWave x l j).phase n) ((actualWave x l j).pressure n) (angleShuffle z)).re) := by
  have hθ : (directions (B := B)).angular = (((0 : Parameter),1),(0 : TorusInverse.Plane)) := rfl
  constructor
  · funext n z i
    rw [actualUpdate, ParticularParameters.updateBlock, assembledBlock_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := common_amplitude_invariant x l j n
    rw [hθ] at hinv
    have hi := invariant_angleShuffle hinv z.1 z.2
    change Complex.re (_ * _) = ((actualWave x l j).amplitude n (angleShuffle z) i *
      carrier ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).frequency
          n)
        ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).phase n)
        (angleShuffle z)).re
    rw [actualCarrier_character (parameters x l).background (assembly x l).carrierBlock j
      (source_frequency_ne Hc l) n z, hi]
    rfl
  · funext n z
    rw [actualUpdate, ParticularParameters.updateBlock, assembledBlock_pressure_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := common_pressure_invariant x l j n
    rw [hθ] at hinv
    have hi := invariant_angleShuffle hinv z.1 z.2
    change Complex.re (_ * _) = ((actualWave x l j).pressure n (angleShuffle z) *
      carrier ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).frequency
          n)
        ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).phase n)
        (angleShuffle z)).re
    rw [actualCarrier_character (parameters x l).background (assembly x l).carrierBlock j
      (source_frequency_ne Hc l) n z, hi]
    rfl

theorem native_phase_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((data x l j).background.phase n)
      (ParticularParameters.nativeStrip associatedStrip).domain := by
  apply (ParticularParameters.nativeStrip associatedStrip).isOpen_domain.contDiffOn_iff.mpr
  intro z hz
  have hp := ActualPrimaryCoherence.piece_domain_positive ActualPrimary.standardRegion
    (show nativeToFull z ∈ (HarmonicWaveInteraction.productStrip
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)).domain
          from hz)
  exact data_phase_smoothAt Hc l j n hp.1 hp.2

theorem wave_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z => vectorMode ((actualWave x l j).frequency n)
      ((actualWave x l j).phase n) ((actualWave x l j).amplitude n) (angleShuffle z) i)
      (HarmonicResidual.liftDomain associatedStrip.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((actualWave x l j).frequency n)
    (native_phase_smooth Hc l j n) (contDiffOn_pi.mp (common_smooth Hc j hj Hs l S n).1 i)
  exact hf.comp (angleShuffle (P := Parameter)).contDiff.contDiffOn (fun _ hz => hz.1)

theorem pressure_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z => mode ((actualWave x l j).frequency n)
      ((actualWave x l j).phase n) ((actualWave x l j).pressure n) (angleShuffle z))
      (HarmonicResidual.liftDomain associatedStrip.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((actualWave x l j).frequency n)
    (native_phase_smooth Hc l j n) (common_smooth Hc j hj Hs l S n).2
  exact hf.comp (angleShuffle (P := Parameter)).contDiff.contDiffOn (fun _ hz => hz.1)

/-- Support data, bundling `cells`, `cutoff_support`, `cover`. -/
noncomputable def supportData (x : CycleState (Label B N0))
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Label B N0) (j : ℤ) :
    SupportData x l j where
  cells := ActualParticularStageControls.carrierCells l
  cutoff_support := ActualParticularStageControls.data_cutoff_support x l j
  cover n k _ hz hk := ActualParticularStageControls.data_control_alternative x hs hN l j n k hz hk

theorem source_phase_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((assembly x l).carrierBlock.phase n) associatedStrip.domain := by
  have hsection : ContDiff ℝ ∞ (fun z : Parameter × TorusInverse.Plane => angleShuffle (z,0)) :=
    (angleShuffle (P := Parameter)).contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hmap : MapsTo (fun z : Parameter × TorusInverse.Plane => angleShuffle (z,0))
      associatedStrip.domain (ParticularParameters.nativeStrip associatedStrip).domain := fun _ hz
          => hz
  have hh := (native_phase_smooth Hc l 1 n).comp hsection.contDiffOn hmap
  have he : (fun z => (data x l 1).background.phase n (angleShuffle (z,0))) =
      (assembly x l).carrierBlock.phase n := by
    funext z
    change (assembly x l).carrierBlock.phase n z +
      ((assembly x l).carrierBlock.angularFrequency n : ℝ) /
        (assembly x l).carrierBlock.frequency n * 0 = _
    simp
  change ContDiffOn ℝ ∞ (fun z => (data x l 1).background.phase n (angleShuffle (z,0)))
    associatedStrip.domain at hh
  rw [he] at hh
  exact hh

theorem source_angular_ne {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) : (assembly x l).carrierBlock.angularFrequency n ≠ 0 := by
  change (x.coefficients.blocks l).angularFrequency n ≠ 0
  rw [← (Hc l).angular]
  exact PrimaryGeometryAssembly.angularMode_ne_zero ActualPrimary.certificate
      ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.1 l.2

theorem associated_base_smooth :
    MeanIncrementBounds.SmoothTriple associatedStrip.domain (associatedContext (B := B)).base := by
  have hh := (CommonBaseContext.context_base_bounds ActualPrimary.certificate
      ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion (CommonWindow.index ActualPrimary.h)).smooth
  exact ⟨fun n => (hh.radial n).comp cycleAssoc.symm.contDiff.contDiffOn (fun _ hz => hz),
    fun n => (hh.angular n).comp cycleAssoc.symm.contDiff.contDiffOn (fun _ hz => hz),
    fun n => (hh.axial n).comp cycleAssoc.symm.contDiff.contDiffOn (fun _ hz => hz)⟩

theorem associated_radial_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame (associatedContext (B := B)) n).radial
      associatedStrip.domain := by
  apply associatedStrip.isOpen_domain.contDiffOn_iff.mpr
  intro z hz
  have hR : 0 < z.1.1 := BaseContextAssembly.nativeStrip_radius
    ActualPrimary.nominal ActualPrimary.standardRegion hz
  have hp : ContDiffAt ℝ ∞ (associatedContext (B := B)).operators.radialProfile z := by
    change ContDiffAt ℝ ∞ (fun y : Parameter × TorusInverse.Plane =>
      ChartScales.radialExponent ActualPrimary.h * y.1.1 ^ (ChartScales.radialExponent
          ActualPrimary.h - 1)) z
    exact contDiffAt_const.mul (contDiffAt_fst.fst.rpow_const_of_ne hR.ne')
  exact contDiffAt_const.add ((contDiffAt_const.mul hp).smul contDiffAt_const)

theorem pair_smooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} {f : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (ErrorHarmonics.conjugatePair j f) := by
  have hh := HarmonicWaveInteraction.smoothCoefficients_single (hf.div_const 2) j
  exact hh.add hh.conjugateReverse

theorem update_smooth {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ)
    (Hs : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j) (n : ℕ) :
    (∀ i, HarmonicResidual.SmoothCoefficients associatedStrip.domain ((actualUpdate x l N).velocity
        n i)) ∧
      HarmonicResidual.SmoothCoefficients associatedStrip.domain ((actualUpdate x l N).pressure n)
          := by
  have hj (j : ℤ) (h : j ∈ modes N) : j ≠ 0 := (mem_modes N j).mp h |>.1
  have hsection : ContDiff ℝ ∞ (fun z : Parameter × TorusInverse.Plane => angleShuffle (z,0)) :=
    (angleShuffle (P := Parameter)).contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hmap : MapsTo (fun z : Parameter × TorusInverse.Plane => angleShuffle (z,0))
      associatedStrip.domain (ParticularParameters.nativeStrip associatedStrip).domain := fun _ hz
          => hz
  constructor
  · intro i m
    change ContDiffOn ℝ ∞ ((∑ j ∈ modes N,
      ErrorHarmonics.conjugatePair j (fun z => (actualWave x l j).amplitude n (angleShuffle (z,0))
          i)) m) _
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    convert! ContDiffOn.sum (fun j h => pair_smooth
      ((contDiffOn_pi.mp (common_smooth Hc j (hj j h) (Hs j h) l (S j h) n).1 i).comp
        hsection.contDiffOn hmap) j m) using 1
    ext y
    simp only [Finset.sum_apply, Function.comp_def]
  · intro m
    change ContDiffOn ℝ ∞ ((∑ j ∈ modes N,
      ErrorHarmonics.conjugatePair j (fun z => (actualWave x l j).pressure n (angleShuffle (z,0))))
          m) _
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    convert! ContDiffOn.sum (fun j h => pair_smooth
      ((common_smooth Hc j (hj j h) (Hs j h) l (S j h) n).2.comp
        hsection.contDiffOn hmap) j m) using 1
    ext y
    simp only [Finset.sum_apply, Function.comp_def]

/-- Source classes type used in actual particular dynamics. -/
abbrev SourceClasses (x : CycleState (Label B N0)) (N : ℕ) (α : ℝ) : Prop :=
  ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
    nativeEnvelope α (currentSource x j)

theorem section_equation {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (l : Label B N0) (S : SupportData x l j) (n : ℕ)
    (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) (i : Fin 3) :
    (actualWave x l j).harmonicResidual (ParticularParameters.nativeStrip associatedStrip)
        (directions (B := B)) n (angleShuffle z) i +
      residualSource (assembly x l).context (assembly x l).state (assembly x l).carrierBlock
        (assembly x l).gaussianInput (assembly x l).aliasInput j n z.1 i *
          HarmonicFields.character j ((assembly x l).carrierBlock.frequency n *
            (assembly x l).carrierBlock.phase n z.1 +
              ((assembly x l).carrierBlock.angularFrequency n : ℝ) * z.2) =
      ((data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip)
          (directions (B := B)) n (angleShuffle (z.1,0)) i +
        (data x l j).globalGaussian (directions (B := B)) n (angleShuffle (z.1,0)) i) *
          HarmonicFields.character j ((assembly x l).carrierBlock.frequency n *
            (assembly x l).carrierBlock.phase n z.1 +
              ((assembly x l).carrierBlock.angularFrequency n : ℝ) * z.2) := by
  have hg := common_good_invariant x l j n
  have he := common_gaussian_invariant x l j n
  have hθ : (directions (B := B)).angular = (((0 : Parameter),1),(0 : TorusInverse.Plane)) := rfl
  rw [hθ] at hg he
  have hgs := invariant_angleShuffle hg z.1 z.2
  have hes := invariant_angleShuffle he z.1 z.2
  have hh := congrFun (common_cancellation Hc j hj Hs l S n (z := angleShuffle z) hz) i
  change (actualWave x l j).harmonicResidual (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n (angleShuffle z) i +
    residualSource (assembly x l).context (assembly x l).state (assembly x l).carrierBlock
      (assembly x l).gaussianInput (assembly x l).aliasInput j n z.1 i *
      carrier ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).frequency
          n)
        ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).phase n)
        (angleShuffle z) =
    ((data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n (angleShuffle z) i +
      (data x l j).globalGaussian (directions (B := B)) n (angleShuffle z) i) *
      carrier ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).frequency
          n)
        ((actualCarrier (parameters x l).background (assembly x l).carrierBlock j).phase n)
        (angleShuffle z) at hh
  rw [actualCarrier_character (parameters x l).background (assembly x l).carrierBlock j
    (source_frequency_ne Hc l) n z, hgs, hes] at hh
  exact hh

theorem cancellation_sum {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j)
    (hBand : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).BandLimited N)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    (fun i => ∑ j ∈ modes N, ((actualWave x l j).harmonicResidual
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) n (angleShuffle z)
          i).re) +
      (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
            l).aliasInput).oscillation n z =
      (actualGood x l N).oscillation n z + (actualGaussian x l N).oscillation n z := by
  apply finite_cancellation (assembly x l).context (assembly x l).state (assembly x l).carrierBlock
    (assembly x l).gaussianInput (assembly x l).aliasInput N hBand
    (fun j n z => (actualWave x l j).harmonicResidual (ParticularParameters.nativeStrip
        associatedStrip)
      (directions (B := B)) n (angleShuffle z))
    (fun j n z => (data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n (angleShuffle (z,0)))
    (fun j n z => (data x l j).globalGaussian (directions (B := B)) n (angleShuffle (z,0))) n z
  intro j hj i
  exact section_equation Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n z hz i

theorem context_linear_sum {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    linearBlockField (assembly x l).context (assembly x l).carrierBlock (actualUpdate x l N) n z =
      fun i => ∑ j ∈ modes N, ((actualWave x l j).harmonicResidual
        (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) n (angleShuffle z)
            i).re := by
  have hu := update_represents Hc l N
  have hv (j : ℤ) (hj : j ∈ modes N) (i : Fin 3) :=
    wave_smooth Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n i
  have hp (j : ℤ) (hj : j ∈ modes N) :=
    pressure_smooth Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n
  have hvs (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (actualUpdate x l N).oscillation n y i) (HarmonicResidual.liftDomain
          associatedStrip.domain) := by
    rw [hu.1]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hv j hj i))
  have hps : ContDiffOn ℝ ∞ ((actualUpdate x l N).oscillatoryPressure n)
      (HarmonicResidual.liftDomain associatedStrip.domain) := by
    rw [hu.2]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hp j hj))
  have hcarrier : SameCarrier (assembly x l).carrierBlock (actualUpdate x l N) := ⟨rfl,rfl,rfl⟩
  have hr : ContDiffOn ℝ ∞ (radialDirection (assembly x l).context n)
      (HarmonicResidual.liftDomain associatedStrip.domain) :=
    HarmonicResidual.liftDirection_smooth (associated_radial_smooth n)
  have hB := associated_base_smooth (B := B)
  rw [linearBlockField_eq_real associatedStrip.isOpen_domain (assembly x l).context
    (assembly x l).carrierBlock (actualUpdate x l N) n hr contDiffOn_const hB
    (by simpa only [withCarrier_of_same hcarrier] using hvs)
    (by simpa only [withCarrier_of_same hcarrier] using hps) ⟨hz,trivial⟩,
    withCarrier_of_same hcarrier, hu.1, hu.2]
  have he := real_linearResidual_sum (Vθ := angularDirection) (modes N)
    (HarmonicResidual.liftDomain_open associatedStrip.isOpen_domain)
    ((assembly x l).context.operators.epsilon n)
    (fun y : (Parameter × TorusInverse.Plane) × ℝ => (assembly x l).context.operators.radius y.1)
    (timeDirection (assembly x l).context n) hr contDiffOn_const
    (show ContDiffOn ℝ ∞ (axialDirection (assembly x l).context n)
      (HarmonicResidual.liftDomain associatedStrip.domain) from contDiffOn_const)
    (contextRealBase (assembly x l).context n)
    (fun j y => vectorMode ((actualWave x l j).frequency n) ((actualWave x l j).phase n)
      ((actualWave x l j).amplitude n) (angleShuffle y))
    (fun j y => mode ((actualWave x l j).frequency n) ((actualWave x l j).phase n)
      ((actualWave x l j).pressure n) (angleShuffle y)) hv hp
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt
      ((HarmonicResidual.liftDomain_open associatedStrip.isOpen_domain).mem_nhds
          ⟨hz,trivial⟩)).differentiableAt (by
          simp))
    ⟨hz,trivial⟩
  rw [← complexBase_eq_realLift] at he
  rw [he]
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun f => (f i).re) ((parameters x l).native_context_residual associatedStrip
      (assembly x l).context
    (assembly x l).state (assembly x l).carrierBlock (assembly x l).gaussianInput
    (assembly x l).aliasInput j (associated_frame_match l) n z).symm

theorem context_linear_cancellation_of_support {x : CycleState (Label B N0)} (Hc :
    PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j)
    (hBand : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).BandLimited N)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    linearBlockField (assembly x l).context (assembly x l).carrierBlock (actualUpdate x l N) n z +
      (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
            l).aliasInput).oscillation n z =
      (actualGood x l N).oscillation n z + (actualGaussian x l N).oscillation n z := by
  rw [context_linear_sum Hc N Hs l S n z hz]
  exact cancellation_sum Hc N Hs l S hBand n z hz

theorem full_divergence_zero {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    cylindricalDivergence (fun y => (assembly x l).context.operators.radius y.1)
      (radialDirection (assembly x l).context n) angularDirection
      (axialDirection (assembly x l).context n)
      (fun y i => ((actualUpdate x l N).oscillation n y i : ℂ)) z = 0 := by
  rw [(update_represents Hc l N).1]
  apply real_divergence_sum_zero (modes N)
  · intro j hj i
    exact ((wave_smooth Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n i).contDiffAt
      ((HarmonicResidual.liftDomain_open associatedStrip.isOpen_domain).mem_nhds
          ⟨hz,trivial⟩)).differentiableAt (by
          simp)
  · intro j hj
    rw [(parameters x l).native_context_divergence associatedStrip (assembly x l).context
        (associated_frame_match l)]
    exact common_divergence_zero Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n hz

theorem modeSolenoidal_of_support {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j) :
    HarmonicWaveInteraction.ModeSolenoidal associatedStrip (assembly x l).context (actualUpdate x l
        N) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full (assembly x l).context (actualUpdate x l N)
  · exact source_phase_smooth Hc l
  · exact source_angular_ne Hc l
  · intro n
    exact (update_smooth Hc N Hs l S n).1
  · exact full_divergence_zero Hc N Hs l S

/-- Actual incoming support and source classes imply solenoidality of
the finite particular correction. -/
theorem modeSolenoidal {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α) (l : Label B N0) :
    HarmonicWaveInteraction.ModeSolenoidal associatedStrip (assembly x l).context (actualUpdate x l
        N) :=
  modeSolenoidal_of_support Hc N Hs l (fun j _ => supportData x hs hN l j)

/-- The actual current residual is cancelled by the finite common-cover
solve, with the computed retained and Gaussian terms on the right. -/
theorem context_linear_cancellation {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α) (l : Label B N0)
    (hBand : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).BandLimited N)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    linearBlockField (assembly x l).context (assembly x l).carrierBlock (actualUpdate x l N) n z +
      (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
            l).aliasInput).oscillation n z =
      (actualGood x l N).oscillation n z + (actualGaussian x l N).oscillation n z :=
  context_linear_cancellation_of_support Hc N Hs l (fun j _ => supportData x hs hN l j) hBand n z hz

/-- Cycle update, given by `StateReindex.block cycleAssoc (actualUpdate x l N)`. -/
noncomputable def cycleUpdate (x : CycleState (Label B N0)) (l : Label B N0) (N : ℕ) :=
  StateReindex.block cycleAssoc (actualUpdate x l N)

theorem cycle_modeSolenoidal {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α) (l : Label B N0) :
    HarmonicWaveInteraction.ModeSolenoidal
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)
      (ActualPrimary.commonContext B) (cycleUpdate x l N) := by
  have hh := ModeSolenoidalReindex.modeSolenoidal_pull cycleAssoc (modeSolenoidal Hc hs hN N Hs l)
  simp only [assembly, associatedStrip, associatedContext, MeanBoundsReindex.strip_roundtrip,
    StateReindex.context_roundtrip] at hh ⊢
  exact hh

theorem actualUpdate_eq_canonical {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (l : Label B N0) (N : ℕ) : actualUpdate x l N =
      (canonicalParameters l).updateBlock associatedStrip (assembly x l).context (assembly x
          l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N := by
  unfold actualUpdate
  rw [parameters_eq_canonical x l (carrier_frequency Hc l)]

theorem linearBlockField_pull {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : D ≃ₗᵢ[ℝ] E)
    (c : Context E) (a b : HarmonicBlock E) (n : ℕ) (z : D × ℝ) :
    linearBlockField (StateReindex.context e c) (StateReindex.block e a) (StateReindex.block e b) n
        z =
      linearBlockField c a b n (StateReindex.cylinder e z) := by
  have hcar : HarmonicWaveInteraction.withCarrier (StateReindex.block e a) (StateReindex.block e b)
      =
      StateReindex.block e (HarmonicWaveInteraction.withCarrier a b) := rfl
  have he := StateReindex.linearResidual_field_pull (StateReindex.cylinder e) (c.operators.epsilon
      n)
    (fun y : E × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
    (axialDirection c n) (timeDirection c n) (complexBase c n)
    (LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n))
    (fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ)) z
  have hθ : StateReindex.vector (StateReindex.cylinder e) (angularDirection (D := E)) =
      angularDirection (D := D) := by
    funext y
    change (e.symm 0, (1 : ℝ)) = (0,1)
    rw [map_zero]
  have hr : radialDirection (StateReindex.context e c) n =
      StateReindex.vector (StateReindex.cylinder e) (radialDirection c n) :=
    StateReindex.radialDirection_pull e c n
  have hz : axialDirection (StateReindex.context e c) n =
      StateReindex.vector (StateReindex.cylinder e) (axialDirection c n) :=
    StateReindex.axialDirection_pull e c n
  have ht : timeDirection (StateReindex.context e c) n =
      StateReindex.vector (StateReindex.cylinder e) (timeDirection c n) :=
    StateReindex.timeDirection_pull e c n
  have hb : complexBase (StateReindex.context e c) n =
      fun y => complexBase c n (StateReindex.cylinder e y) := rfl
  rw [hθ] at he
  unfold linearBlockField
  rw [hcar, StateReindex.block_oscillation, StateReindex.block_pressure,
    hr, hz, ht, hb]
  exact congrArg (fun f => fun i => (f i).re) he

theorem cycle_context_linear_cancellation {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α) (l : Label B N0)
    (hBand : (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
          l)).BandLimited N)
    (n : ℕ) (z : CyclePoint × ℝ)
    (hz : z.1 ∈ (BaseContextAssembly.nativeStrip ActualPrimary.nominal
        ActualPrimary.standardRegion).domain) :
    linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l) (cycleUpdate x l N)
        n z +
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
            l)).oscillation n z =
      (StateReindex.block cycleAssoc (actualGood x l N)).oscillation n z +
        (StateReindex.block cycleAssoc (actualGaussian x l N)).oscillation n z := by
  have hBand' : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).BandLimited N := by
    change (HarmonicResidual.residualBlock (StateReindex.context cycleAssoc.symm
        (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state) (StateReindex.block cycleAssoc.symm
          (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients
          l))).BandLimited N
    rw [StateReindex.residualBlock_pull]
    exact StateReindex.block_bandLimited cycleAssoc.symm hBand
  have hz' : (StateReindex.cylinder cycleAssoc z).1 ∈ associatedStrip.domain := by
    change cycleAssoc.symm (cycleAssoc z.1) ∈
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion).domain
    simpa only [cycleAssoc.symm_apply_apply] using hz
  have hh := context_linear_cancellation Hc hs hN N Hs l hBand' n (StateReindex.cylinder cycleAssoc
      z) hz'
  have hlin := linearBlockField_pull cycleAssoc (assembly x l).context (assembly x l).carrierBlock
    (actualUpdate x l N) n z
  have hlin' : linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l)
      (cycleUpdate x l N) n z =
      linearBlockField (assembly x l).context (assembly x l).carrierBlock (actualUpdate x l N) n
        (StateReindex.cylinder cycleAssoc z) := by
    simp only [assembly, associatedContext, StateReindex.context_roundtrip,
      StateReindex.block_roundtrip] at hlin ⊢
    exact hlin
  have hres : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).oscillation n
        (StateReindex.cylinder cycleAssoc z) =
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
            l)).oscillation n z := by
    change (HarmonicResidual.residualBlock (StateReindex.context cycleAssoc.symm
        (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state) (StateReindex.block cycleAssoc.symm
          (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients
          l))).oscillation n _ = _
    rw [StateReindex.residualBlock_pull, StateReindex.block_oscillation]
    simp only [StateReindex.oscillation, StateReindex.cylinder_apply,
      cycleAssoc.symm_apply_apply, Prod.eta]
  rw [hres] at hh
  rw [hlin', StateReindex.block_oscillation, StateReindex.block_oscillation]
  exact hh

end NavierStokes.ActualParticularDynamics

end
end

end

section

/-!
# The weighted Gaussian error of the actual particular update

The native estimates are those of the selected actual Volterra solves, already
transferred back to the original label and band in `raw_jets`.  Gaussian decay
is applied at that original band.  The square-root moving-edge weight is kept
through the entire estimate, including the uncovered source term.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularGaussian

open Set Function Filter WeightedClasses
open CorrectionState CorrectionStep CommonCoverSolve TorusInverse
open ActualParticularStageControls CorrectionInitialization
open scoped ContDiff Topology

variable {B N0 : ℕ}

/-- Native strip, given by `CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
slowStrip)`. -/
noncomputable def nativeStrip : StripData Native :=
  CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)

/-- Band scales, bundling `power`, `epsilon_eq`, `boundConstant`, `constant_one_le` and the
required compatibility proofs. -/
noncomputable def bandScales : GaussianTailFlat.BandScaleControl nativeStrip where
  power := ActualPrimary.h
  epsilon_eq := fun _ => rfl
  boundConstant := 1
  constant_one_le := le_rfl
  degree := 1
  slow_le := fun n => by
    change max 1 (ChartScales.S n) ≤ 1 * (1 + ChartScales.S n) ^ 1
    simp only [pow_one, one_mul]
    have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
    exact max_le (by linarith) (by linarith)

theorem fast_bound : BandBound nativeStrip 0 (directions (B := B)).fastScale :=
  (CommonBaseContext.context_operator_bounds ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion
    (CommonWindow.index_le_native ActualPrimary.h)).fastCoefficient

/-! The clock bounds are imposed only on active pairs. -/

/-- Clock upper, given by `ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h
+ 1 / 2)`. -/
noncomputable def clockUpper : ℝ :=
  ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h + 1 / 2)

theorem clockUpper_pos : 0 < clockUpper :=
  zero_lt_one.trans_le (ActualSignedGeometry.powerBound_one _)

theorem clock_bounds {l : Label B N0} {n : ℕ} (ha : Active l n) :
    1 / clockUpper ≤ ActualCarrierTransportBase.clock (supportLabel l) n ∧
      ActualCarrierTransportBase.clock (supportLabel l) n ≤ clockUpper := by
  have hd := CommonWindow.distance ha.2
  exact ⟨ActualSignedGeometry.dyadic_ratioPower_lower hd.1 hd.2 _,
    ActualSignedGeometry.dyadic_ratioPower_le hd.1 hd.2 _⟩

/-- Transported length, given by `ActualCarrierTransportBase.referenceLength (supportLabel l) /
ActualCarrierTransportBase.clock (supportLabel l) n`. -/
noncomputable def transportedLength (l : Label B N0) (n : ℕ) : ℝ :=
  ActualCarrierTransportBase.referenceLength (supportLabel l) /
    ActualCarrierTransportBase.clock (supportLabel l) n

theorem transportedLength_pos (l : Label B N0) (n : ℕ) : 0 < transportedLength l n :=
  div_pos (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n)

/-- Length lower, given by `ActualInitialExcluded.gaussianLengthLower / clockUpper`. -/
noncomputable def lengthLower : ℝ := ActualInitialExcluded.gaussianLengthLower / clockUpper

theorem lengthLower_pos : 0 < lengthLower :=
  div_pos ActualInitialExcluded.gaussianLengthLower_pos clockUpper_pos

theorem transportedLength_lower {l : Label B N0} {n : ℕ} (ha : Active l n) :
    lengthLower * ChartScales.S n ≤ transportedLength l n := by
  have href : ActualInitialExcluded.gaussianLengthLower * ChartScales.S n ≤
      ActualCarrierTransportBase.referenceLength (supportLabel l) := by
    simpa only [ActualCarrierTransportBase.referenceLength, supportLabel,
      ActualPrimary.length_sign] using ActualInitialExcluded.gaussianLength_near l n ha
  calc
    _ = (ActualInitialExcluded.gaussianLengthLower * ChartScales.S n) / clockUpper := by
      unfold lengthLower; ring
    _ ≤ ActualCarrierTransportBase.referenceLength (supportLabel l) / clockUpper :=
      div_le_div_of_nonneg_right href clockUpper_pos.le
    _ ≤ transportedLength l n :=
      div_le_div_of_nonneg_left
        (ActualCarrierTransportBase.referenceLength_pos (supportLabel l)).le
        (ActualCarrierTransportBase.clock_pos (supportLabel l) n) (clock_bounds ha).2

/-- The auxiliary length agrees with the actual transported slot wherever
the analytic patch is used.  It only totalizes the Gaussian bookkeeping on
inactive label-band pairs. -/
noncomputable def gaussianLength (l : Label B N0) (n : ℕ) : ℝ :=
  max (transportedLength l n) (lengthLower * ChartScales.S n)

theorem gaussianLength_pos (l : Label B N0) (n : ℕ) : 0 < gaussianLength l n :=
  (transportedLength_pos l n).trans_le (le_max_left _ _)

theorem gaussianLength_lower (l : Label B N0) (n : ℕ) :
    lengthLower * ChartScales.S n ≤ gaussianLength l n := le_max_right _ _

theorem gaussianLength_eq {l : Label B N0} {n : ℕ} (ha : Active l n) :
    gaussianLength l n = transportedLength l n := max_eq_left (transportedLength_lower ha)

/-- Theta, given by `((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k
z.2).2 / transportedLength l n`. -/
noncomputable def theta (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native) : ℝ :=
  ((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2).2 /
    transportedLength l n

/-- Gaussian rate, given by `ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B
N0).prepared.M⁻¹ (ActualPrimary.choice B N0).prepared.u / clockUpper`. -/
noncomputable def gaussianRate (B N0 : ℕ) : ℝ :=
  ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
    (ActualPrimary.choice B N0).prepared.u / clockUpper

theorem gaussianRate_pos (B N0 : ℕ) : 0 < gaussianRate B N0 :=
  div_pos (ActualGaussianCoverage.prepared_gaussian_rate_pos ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared) clockUpper_pos

/-! Exact envelope and cutoff readouts on the actual analytic patch. -/

theorem envelope_gaussian (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    nativeEnvelope l n z ≤ Real.exp (-gaussianRate B N0 * (theta l n k z - 1 / 2) ^ 2 *
      gaussianLength l n) := by
  let e : ℕ → ActivePair B N0 := fun _ => ⟨(l,n),hz.1⟩
  have hp : z ∈ selectedPatch e () 0 k := by
    rw [← selected_controlPatch e () 0 k]
    exact hz
  have hw : nativeEnvelope l n z = selectedPulseEnvelope e () 0
      ((selectedGeometry e () 0).coordinates k z.2).2 :=
    (selected_envelope_eq e 0 (z.1.1,z.2)).symm.trans (selectedWeight_eq e () 0 k hp)
  rw [hw, gaussianLength_eq hz.1]
  have hl : ∀ u q, (ActualPrimary.choice B N0).prepared.M⁻¹ ≤
      (selectedConstruction e).lam (u,q) := by
    intro u q
    exact ActualGaussianCoverage.prepared_lambda_lower ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
      ActualPrimary.slots.radius_pos l.1 l.2
  have hb := ActualGaussianCoverage.envelope_uniform_bound
    (selectedConstruction e) (selectedClock e)
    (inv_pos.mpr (zero_lt_one.trans_le (ActualPrimary.choice B N0).prepared.one_le_M))
    (ActualPrimary.choice B N0).prepared.u_pos hl (selected_u e) () 0
    (show ((selectedGeometry e () 0).coordinates k z.2).2 ∈
      Icc 0 (ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e) () 0)
      from ⟨hz.2.1.2.2.1.le, hz.2.1.2.2.2.le⟩)
  have hr : ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
      (ActualPrimary.choice B N0).prepared.u * (selectedClock e).lower = gaussianRate B N0 := by
    change _ * (1 / clockUpper) = _ / clockUpper
    ring
  have ht : ActualGaussianCoverage.theta (selectedConstruction e) (selectedClock e) () 0
      ((selectedGeometry e () 0).coordinates k z.2).2 = theta l n k z := by
    rw [ActualGaussianCoverage.theta_eq]
    rfl
  have hlen : ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e) () 0 =
      transportedLength l n := rfl
  simp only [hr, ht, hlen] at hb
  exact hb

theorem cutoff_central (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) (k : Frequency) {z : Native} (hz : z ∈ controlPatch l n k)
    (hm : |theta l n k z - 1 / 2| < 1 / 5) :
    (data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 1 := by
  rw [data_scalar_eq x l j]
  have hrect : (ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2 ∈
      WaveEnvelopeTransport.rectangle ActualPrimary.slots.radius (transportedLength l n) :=
    ⟨hz.2.2,hz.2.1.2.2.1.le,hz.2.1.2.2.2.le⟩
  exact (ActualGaussianCoverage.nativeCutoff_central_germ ActualPrimary.slots.radius_pos
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hrect hm).comp_tendsto
      (((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates_contDiff
          k).continuous.comp
        continuous_snd).continuousAt

/-! The uncovered source is zero; it is not estimated without its edge weight. -/

theorem outside_alternative (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ nativeStrip.domain) (hk : z ∈ (carrierCells l).carrier n k)
    (hn : z ∉ controlPatch l n k) :
    (((data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0)) ∨
    (((data x l j).amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0)) := by
  have hnot : (z.1.1,z.2) ∉ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n :=
    fun hreg => hn (sourceRegion_mem_controlPatch hN l n k hz hk hreg)
  have hf := currentSource_zero_germ x hs hN l j n (native_parameter_domain hz) hnot
  rcases data_control_alternative x hs hN l j n k hz hk with hc | hcut | ⟨ha,_,hf'⟩
  · exact (hn hc).elim
  · exact Or.inl ⟨hcut,hf⟩
  · exact Or.inr ⟨ha,hf'⟩

theorem source_complement (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (β : ℝ) :
    LocalizedGaussianBounds.UniformComplementJets nativeStrip
      (fun _ _ z => Real.sqrt (nativeStrip.zeta z)) β
      (fun l => (carrierCells l).carrier) (fun l => (data x l j).source) := by
  apply LocalizedGaussianBounds.UniformComplementJets.of_zero_germs
  intro l n z hz hn
  apply currentSource_zero_germ x hs hN l j n (native_parameter_domain hz)
  intro hreg
  obtain ⟨k,hk⟩ := mem_iUnion.mp hreg.2
  exact hn k (ActualGaussianCoverage.sourceCell_subset_outer ActualPrimary.slots.radius_pos
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hk)

/-- Every power gain for the literal particular Gaussian error, with
constants chosen before the original spatial label and band.  The hypotheses
concern the incoming source and its actual support, never the solved error. -/
theorem globalGaussian_all_gains (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier
        ActualPrimary.h n)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope α (currentSource x j))
    (β : ℝ) :
    LabelSumBounds.UniformClass nativeStrip (fun _ _ z => Real.sqrt (nativeStrip.zeta z)) β
      (fun l => (data x l j).globalGaussian (directions (B := B))) := by
  apply ActualGaussianCoverage.uniform_globalGaussian_weighted_from_supported_native
    (fun l => data x l j) carrierCells (data_cutoff_support x · j)
    (directions (B := B)) controlPatch
    (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (cutoff_jets x j) fast_bound (raw_jets x hfrequency j hj H).1
    (uniform_to_local H controlPatch) bandScales theta gaussianLength gaussianLength_pos
    lengthLower lengthLower_pos gaussianLength_lower (gaussianRate_pos B N0)
    (fun l n k z _ hz => envelope_gaussian l n k hz)
    (fun l n k z _ hz hm => Or.inl (cutoff_central x l j n k hz hm))
    (fun l n k z hz hk hn => outside_alternative x hs hN l j n k hz hk hn)
    β (source_complement x hs hN j β)

/-- The literal finite harmonic Gaussian block inherits the same weighted
all-power estimate.  Its finite modal sum changes the constant, not its
uniformity in the original spatial label and band. -/
theorem gaussianBlock_all_gains (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier
        ActualPrimary.h n)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ)
    (H : ∀ j ∈ ParticularWaveAssembly.modes N,
      LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope α (currentSource x j))
    (β : ℝ) (i : Fin 3) (m : ℤ) :
    LabelSumBounds.UniformClass associatedStrip (fun _ _ z => Real.sqrt (associatedStrip.zeta z)) β
      (fun l n z => ((parameters x l).gaussianBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput
            N).velocity
        n i m z) := by
  have hh := UniformBlockBounds.native_assembledBlock_original_uniform
    (s := associatedStrip)
    (w := fun (_ : Label B N0) (_ : ℕ) z => Real.sqrt (nativeStrip.zeta z))
    (α := β) (γ := β) N
    (fun l => (assembly x l).carrierBlock.frequency)
    (fun l => (assembly x l).carrierBlock.phase)
    (fun l => (assembly x l).carrierBlock.angularFrequency)
    (v := fun l j => (data x l j).globalGaussian (directions (B := B)))
    (p := fun _ _ _ _ => (0 : ℂ))
    (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun j hj => globalGaussian_all_gains x hfrequency hs hN j
      ((ParticularWaveAssembly.mem_modes N j).mp hj).1 (H j hj) β)
    (fun _ _ => LabelSumBounds.UniformClass.zero (fun _ _ _ _ => Real.sqrt_nonneg _))
  exact hh.1 i m

end NavierStokes.ActualParticularGaussian

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularCycleData

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

/-- Parameters: an abbreviation for `ActualCycleParameters.fixedParameters B N0`. -/
noncomputable abbrev parameters (B N0 : ℕ) := ActualCycleParameters.fixedParameters B N0

/-- Block: an abbreviation for `(parameters B N0).particularBlock x.coefficients
(ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev block {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (parameters B N0).particularBlock x.coefficients (ActualPrimary.commonContext B) x.state

/-- Gaussian block: an abbreviation for `(parameters B N0).particularGaussianBlock
x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev gaussianBlock {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (parameters B N0).particularGaussianBlock x.coefficients (ActualPrimary.commonContext B) x.state

/-- Invariant type used in actual particular cycle data. -/
abbrev Invariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop :=
  CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope
    ActualCoreSupport.refinedCarrier σ x

/-- The literal particular increment's analytic outputs. No signed-wave
estimate is required to prepare its mean and the subsequent signed request. -/
structure Data {B N0 : ℕ} (x : CycleState (Index B N0)) (σ : ℝ) : Prop where
  amplitude : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1/2+σ) (fun l n z => (block x l).velocity n i j z)
  pressure : ∀ j, LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1+σ) (fun l n z => (block x l).pressure n j z)
  coefficients : ∀ l n i, HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain
    ((block x l).velocity n i)
  pressureCoefficients : ∀ l n, HarmonicResidual.SmoothCoefficients
      ActualInitialization.geometry.domain
    ((block x l).pressure n)
  gaussianCoefficients : ∀ l n i, HarmonicResidual.SmoothCoefficients
      ActualInitialization.geometry.domain
    ((gaussianBlock x l).velocity n i)
  solenoidal : ∀ l, HarmonicWaveInteraction.ModeSolenoidal ActualInitialization.strip
    (ActualPrimary.commonContext B) (block x l)
  gaussian : ∀ β i j, LabelSumBounds.UniformClass ActualInitialization.strip
    (fun _ _ z => Real.sqrt (ActualInitialization.strip.zeta z)) β
    (fun l n z => (gaussianBlock x l).velocity n i j z)
  field : WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  pressureField : ∀ n, ContDiffOn ℝ ∞
    ((parameters B N0).particularPressure x.coefficients (ActualPrimary.commonContext B) x.state n)
    (ActualInitialization.geometry.domain ×ˢ (univ : Set ℝ))
  periodic : OscillationPeriodic ActualPrimary.standardRegion.carrier
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  support : WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  linear : ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1+σ-3*ChartScales.kappa)
    (fun l n z =>
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).velocity n i j z +
      (HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B)
        (x.coefficients.blocks l) (block x l) (gaussianBlock x l).velocity).velocity n i j z)

namespace Data

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

/-- The actual geometric support supplies the remaining first-wave mean
inputs; this does not use any signed increment. -/
theorem inputs (d : Data x σ) (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualParticularMeanGain.Inputs x σ where
  amplitude := d.amplitude
  smooth := d.field
  periodic := d.periodic
  supported := d.support
  old_support := ActualCycleAssembly.old_supported x H hN
    ActualCoreSupport.refinedCarrier_subset_broad
  particular_support := ActualCycleAssembly.particular_supported_of_inputSupport x hN
    (ActualCycleAssembly.cycle_particular_inputSupport hN x (ActualPrimary.commonContext B)
      (fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport l)
        (ActualCoreSupport.refinedCarrier_subset_broad l)))

end Data

section NativeData

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

/-- Native data used in actual particular cycle data. -/
noncomputable def nativeData (x : CycleState (Index B N0)) (l : Index B N0) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j

theorem preservesCarriers (H : Invariant σ x) :
    ActualParticularDynamics.PreservesCarriers (ActualCycleParameters.particularState x) :=
  fun l => H.carrier (l.2,l.1)

theorem native_inputSupport (H : Invariant σ x) :
    ActualParticularStageControls.InputSupport (ActualCycleParameters.particularState x) :=
  fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport (l.2,l.1))
    (ActualCoreSupport.refinedCarrier_subset_broad (l.2,l.1))

theorem nativeData_eq_data (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    nativeData x l j = ActualParticularStageControls.data
      (ActualCycleParameters.particularState x) (l.2,l.1) j := by
  unfold ActualParticularStageControls.data
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem native_phase (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    (nativeData x l j).background.phase =
      (ActualParticularStageControls.background (l.2,l.1)).phase := by
  rw [nativeData_eq_data H]
  exact ActualParticularDynamics.data_phase (preservesCarriers H) (l.2,l.1) j

theorem native_source_pull (l : Index B N0) (j : ℤ) (n : ℕ) :
    (nativeData x l j).source n = fun z =>
      ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
        j n (ActualCarrierTransport.associatedPoint z.1.1 z.2) :=
  ActualParticularStageControls.currentSource_pull (ActualCycleParameters.particularState x)
      (l.2,l.1) j n

theorem native_source_smooth (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).source n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
  rw [native_source_pull]
  apply (ActualCycleCoherence.source_smooth H ActualCoreSupport.refinedCarrier_closed
    (fun l n _ hz hc => ActualCycleCoherence.core_radius_pos l n hz hc) l j n).comp
  · exact (show ContDiff ℝ ∞ (fun z : ActualParticularStageControls.Native =>
      ActualCarrierTransport.associatedPoint z.1.1 z.2) by
        exact cycleAssoc.symm.contDiff.comp
          (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn
  · intro z hz
    exact hz.1

theorem native_source_exterior (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).source n z = 0 := by
  rw [native_source_pull]
  apply (HarmonicSourceSupport.residualSource_zero_germ_on (ActualPrimary.commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    ActualInitialization.geometry.domain_open (ActualCoreSupport.refinedCarrier_closed l)
    (H.inputSupport l) j n hz.1 ?_).self_of_nhds
  intro hc
  exact hr ((ActualCoreSupport.mem_refinedCarrier_iff l n hz.1.1).mp hc).2.1

theorem native_inactive (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :
    (nativeData x l j).common.amplitude n =ᶠ[𝓝 z] fun _ => 0 := by
  exact (ActualCycleAssembly.refined_particular_zero_germs hN l (ActualPrimary.commonContext B)
    x.state (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
        l)
    (H.inputSupport l) j ActualWaveRegularityData.particularFullStrip n hz.1
      (fun hc => hn (ActualCycleCoherence.core_ordered l n hz.1 hc))).1

theorem native_source_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).source n z = 0 :=
  ActualWaveRegularityData.particular_zero_on_radial_faces
    (native_source_smooth H l j n).continuousOn
    (fun _ hz hr => native_source_exterior H l j n hz hr) hz hr

theorem native_raw_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    (k : TorusInverse.Frequency) {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).amplitude n k z = 0 := by
  change ParticularWaveBounds.complexCopyVelocity
    (ParticularWaveAssembly.angleTangent ((ActualParticularStageControls.canonicalParameters
        (l.2,l.1)).tangent j n))
    ((nativeData x l j).source n) ((ActualParticularStageControls.canonicalParameters
        (l.2,l.1)).geometry n)
    ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).length_pos n).le k z = 0
  apply ParticularWaveBounds.complexCopyVelocity_zero_of_path
  intro v _hv
  exact native_source_boundary H l j n hz hr

theorem native_pressure_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    (k : TorusInverse.Frequency) {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).pressure n k z = 0 := by
  let t := ParticularWaveAssembly.angleTangent
    ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).tangent j n)
  let g := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).geometry n
  let L := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).length n
  have hL : 0 ≤ L := ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).length_pos n).le
  let f := (nativeData x l j).source n
  have hpath (v : ℝ) (_hv : v ∈ Icc 0 L) : f (z.1, g.path k z.2 v) = 0 :=
    native_source_boundary H l j n hz hr
  have hcurrent : f z = 0 := native_source_boundary H l j n hz hr
  change ParticularWaveBounds.complexCopyPressure t f g hL k
    ((nativeData x l j).background.frequency n) z = 0
  unfold ParticularWaveBounds.complexCopyPressure
  have hr0 := ParticularWaveBounds.copyPressure_zero_of_path (ParticularWaveBounds.realData t f)
    g hL k ((nativeData x l j).background.frequency n) z.1 z.2
    (fun v hv => by
      change ParticularWaveBounds.realPart (f (z.1,g.path k z.2 v)) = 0
      rw [hpath v hv, map_zero])
    (by change ParticularWaveBounds.realPart (f z) = 0; rw [hcurrent, map_zero])
  have hi0 := ParticularWaveBounds.copyPressure_zero_of_path (ParticularWaveBounds.imagData t f)
    g hL k ((nativeData x l j).background.frequency n) z.1 z.2
    (fun v hv => by
      change ParticularWaveBounds.imagPart (f (z.1,g.path k z.2 v)) = 0
      rw [hpath v hv, map_zero])
    (by change ParticularWaveBounds.imagPart (f z) = 0; rw [hcurrent, map_zero])
  rw [hr0, hi0, mul_zero, add_zero]

theorem native_common_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).common.amplitude n z = 0 ∧ (nativeData x l j).common.pressure n z = 0 := by
  constructor
  · change (∑' k, (nativeData x l j).cutoff n k z • (nativeData x l j).amplitude n k z) = 0
    simp only [native_raw_boundary H l j n _ hz hr, smul_zero, tsum_zero]
  · change (∑' k, ((nativeData x l j).cutoff n k z : ℂ) * (nativeData x l j).pressure n k z) = 0
    simp only [native_pressure_boundary H l j n _ hz hr, mul_zero, tsum_zero]

theorem native_gaussian_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).globalGaussian (ActualParticularStageControls.canonicalParameters
        (l.2,l.1)).directions n z = 0 := by
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, PeriodizedWaveBounds.CopyData.globalTail,
    PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail,
    native_raw_boundary H l j n _ hz hr, native_source_boundary H l j n hz hr,
    smul_zero, tsum_zero, add_zero]

theorem native_residual (H : Invariant σ x) :
    UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)
      ActualParticularStageControls.meanEnvelope (1/2+σ)
      (fun l => HarmonicResidual.residualBlock (ActualPrimary.commonContext B)
        (ActualCycleParameters.particularState x).state
        ((ActualCycleParameters.particularState x).coefficients.blocks l)
        ((ActualCycleParameters.particularState x).coefficients.gaussian l)
        ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l)) := by
  intro i j hj
  have hh := (H.residual i j hj).reindex
    (fun l : ActualParticularStageControls.Label B N0 => (l.2,l.1))
  refine ⟨?_, hh.smooth, ?_⟩
  · intro l n z hz
    simp only [ActualParticularStageControls.meanEnvelope_eq_primary]
    exact hh.weight_nonneg l n z hz
  · intro m
    obtain ⟨C,hC,p,hb⟩ := hh.bounds m
    refine ⟨C,hC,p,?_⟩
    intro l n z hz q hq
    have he := hb l n z hz q hq
    simp only [majorant, ActualParticularStageControls.meanEnvelope_eq_primary] at he ⊢
    exact he

theorem native_source_class (H : Invariant σ x) (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
          ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope (1/2+σ)
      (ActualParticularStageControls.currentSource (ActualCycleParameters.particularState x) j) :=
  ActualParticularStageControls.current_source_class _ (native_residual H) j hj

theorem native_envelope_le_one (l : Index B N0) (n : ℕ) (z : ActualParticularStageControls.Native) :
    ActualParticularStageControls.nativeEnvelope (l.2,l.1) n z ≤ 1 :=
  ActualPrimaryBounds.envelope_le_one (l.2,l.1) n (0,z.2)

theorem native_raw_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z))
      (1/2+σ) (nativeData x l j).common.amplitude := by
  have ha := (ActualParticularStageControls.common_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN j hj (native_source_class H j hj)).1.each (l.2,l.1)
  rw [← nativeData_eq_data H l j] at ha
  exact ha.mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    (fun n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (native_envelope_le_one l n z))

theorem native_pressure_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
    N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z))
      ((1/2+σ)+1/2) (nativeData x l j).common.pressure := by
  have hp := (ActualParticularStageControls.common_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN j hj (native_source_class H j hj)).2.2.1.each (l.2,l.1)
  rw [← nativeData_eq_data H l j] at hp
  exact hp.mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    (fun n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (native_envelope_le_one l n z))

theorem native_gaussian_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
    N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (β : ℝ) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) β
      ((nativeData x l j).globalGaussian (ActualParticularStageControls.canonicalParameters
          (l.2,l.1)).directions) := by
  have hg := (ActualParticularGaussian.globalGaussian_all_gains _
    (fun l => ActualCycleParameters.current_frequency x (l.2,l.1) (H.carrier (l.2,l.1)))
    (native_inputSupport H) hN j hj (native_source_class H j hj) β).each (l.2,l.1)
  rwa [← nativeData_eq_data H l j] at hg

theorem native_raw_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).common.amplitude n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1) n).1

theorem native_pressure_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
    N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).common.pressure n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_pressure_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).2) n).1

theorem native_gaussian_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
    N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).globalGaussian
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_gaussian_class H hN l j hj 0)
    (fun n _ hz hr => native_gaussian_boundary H l j n hz hr) n).1

theorem native_corrected_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold
    ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (((nativeData x l j).commonCorrected ActualWaveRegularityData.particularFullStrip
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions).amplitude n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) :=
  ActualWaveRegularityData.particular_corrected_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1) n

theorem source_inactive (H : Invariant σ x) (l : Index B N0) (n : ℕ)
    (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain) :
    ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j
          n z = 0 :=
  (HarmonicSourceSupport.residualSource_zero_germ_on (ActualPrimary.commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    ActualInitialization.geometry.domain_open (ActualCoreSupport.refinedCarrier_closed l)
    (H.inputSupport l) j n hz (fun hc => hn (ActualCycleCoherence.core_ordered l n hz
        hc))).self_of_nhds

theorem native_source_periodic (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (l : Index B N0) (j : ℤ) (n : ℕ) (z : ActualParticularStageControls.Native)
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :
    CommonCoverSolve.PeriodicAt ((nativeData x l j).source n) z.1 :=
  ActualCyclePeriodicity.copies_source_periodic H T
    (fun l n hn j _ hz => source_inactive H l n hn j hz) l j n z hz

/-- Native mode, constructed using `ActualWaveRegularity.modeOscillation`. -/
noncomputable def nativeMode (x : CycleState (Index B N0)) (l : Index B N0) (j : ℤ) :=
  ActualWaveRegularity.modeOscillation (nativeData x l j)
      ActualWaveRegularityData.particularFullStrip
    (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions
    ActualWaveRegularity.particularChart

theorem native_mode_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1)

theorem native_mode_support (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_support (l.2,l.1) _ _ _ _ _ j
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1)

theorem native_mode_periodic (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (j : ℤ) :
    OscillationPeriodic ActualPrimary.standardRegion.carrier (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_periodic (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_source_periodic H T l j)
    (fun n hn _ hz => native_inactive H hN l n hn j hz)

theorem block_eq_modes (H : Invariant σ x) (l : Index B N0) :
    (block x l).oscillation = LabelSumBounds.fieldSum
      (fun _ => ParticularWaveAssembly.modes x.coefficients.residualBand) (nativeMode x l) :=
  ActualWaveRegularity.particularBlock_eq_modes (parameters B N0) x.coefficients
    (ActualPrimary.commonContext B) x.state l
    (fun n => (ActualParticularDynamics.native_angular (ActualCycleParameters.particularState x)
      (l.2,l.1) 1 n 0).radius)
    (fun n => (ActualParticularDynamics.native_angular (ActualCycleParameters.particularState x)
      (l.2,l.1) 1 n 0).radial_field)
    (H.frequency l)

theorem block_regular (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain (block x l).oscillation ∧
    OscillationPeriodic ActualPrimary.standardRegion.carrier (block x l).oscillation ∧
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (block x l).oscillation := by
  rw [block_eq_modes H l]
  exact ActualWaveRegularity.finset_regular _ _ (fun j hj =>
    ⟨native_mode_smooth H hN l j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1,
      native_mode_periodic H T hN l j, native_mode_support H l j⟩)

theorem field_regular (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
          ∧
    OscillationPeriodic ActualPrimary.standardRegion.carrier
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
          ∧
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
          :=
  ⟨ActualWaveRegularity.finite_smooth _ _ (fun l => (block_regular H T hN l).1),
    ActualWaveRegularity.finite_periodic _ _ (fun l => (block_regular H T hN l).2.1),
    ActualWaveRegularity.finite_support _ _ (fun l => (block_regular H T hN l).2.2)⟩

end NativeData

section FiniteCoefficients

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem pair_smooth {U : Set D} {f : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (ErrorHarmonics.conjugatePair j f) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x => ErrorHarmonics.conjugatePair j f m x) U
  simp only [ParticularWaveAssembly.pair_apply]
  have hleft : ContDiffOn ℝ ∞ (fun x => if m = j then f x / 2 else 0) U := by
    split_ifs
    · exact hf.div_const _
    · exact contDiffOn_const
  have hright : ContDiffOn ℝ ∞ (fun x => if -m = j then f x / 2 else 0) U := by
    split_ifs
    · exact hf.div_const _
    · exact contDiffOn_const
  exact hleft.add (Complex.conjCLE.contDiff.comp_contDiffOn hright)

theorem assembled_velocity_smooth {U : Set D} (N : ℕ) (k : ℕ → ℝ)
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℤ → ℕ → D → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n, ContDiffOn ℝ ∞ (v j n) U)
    (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients U
      ((ParticularWaveAssembly.assembledBlock N k Φ kp v p).velocity n i) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x =>
    (∑ j ∈ ParticularWaveAssembly.modes N, ErrorHarmonics.conjugatePair j (fun y => v j n y i)) m
        x) U
  have he : (fun x => (∑ j ∈ ParticularWaveAssembly.modes N,
      ErrorHarmonics.conjugatePair j (fun y => v j n y i)) m x) =
      (fun x => ∑ j ∈ ParticularWaveAssembly.modes N,
        ErrorHarmonics.conjugatePair j (fun y => v j n y i) m x) := by
    funext x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  rw [he]
  apply ContDiffOn.sum
  intro j hj
  exact pair_smooth (contDiffOn_pi.mp (hv j hj n) i) j m

theorem assembled_pressure_smooth {U : Set D} (N : ℕ) (k : ℕ → ℝ)
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℤ → ℕ → D → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n, ContDiffOn ℝ ∞ (p j n) U)
    (n : ℕ) :
    HarmonicResidual.SmoothCoefficients U
      ((ParticularWaveAssembly.assembledBlock N k Φ kp v p).pressure n) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x =>
    (∑ j ∈ ParticularWaveAssembly.modes N, ErrorHarmonics.conjugatePair j (p j n)) m x) U
  have he : (fun x => (∑ j ∈ ParticularWaveAssembly.modes N,
      ErrorHarmonics.conjugatePair j (p j n)) m x) =
      (fun x => ∑ j ∈ ParticularWaveAssembly.modes N,
        ErrorHarmonics.conjugatePair j (p j n) m x) := by
    funext x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  rw [he]
  apply ContDiffOn.sum
  intro j hj
  exact pair_smooth (hp j hj n) j m

end FiniteCoefficients

section Outputs

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

/-- Associated domain, given by `ActualCarrierTransport.parameterDomain ×ˢ Set.univ`. -/
noncomputable def associatedDomain : Set (CycleSlow × TorusInverse.Plane) :=
  ActualCarrierTransport.parameterDomain ×ˢ Set.univ

theorem native_slice_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ActualParticularStageControls.Native → E}
    (hf : ContDiffOn ℝ ∞ f (ActualWaveRegularity.nativeDomain
      ActualWaveRegularity.particularChart ActualPrimary.standardRegion)) :
    ContDiffOn ℝ ∞ (fun z => f (ParticularWaveAssembly.angleShuffle (z,0))) associatedDomain := by
  apply hf.comp
    (ParticularWaveAssembly.angleShuffle.contDiff.comp (contDiff_id.prodMk
        contDiff_const)).contDiffOn
  intro z hz
  exact ⟨hz.1, mem_univ _⟩

theorem coefficients_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain ((block x l).velocity
        n i) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
      (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.updateBlock ActualParticularStageControls.associatedStrip a.context a.state a.carrierBlock
        a.gaussianInput a.aliasInput x.coefficients.residualBand).velocity n i) := by
    apply assembled_velocity_smooth
    intro j hj m
    exact native_slice_smooth (native_corrected_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem pressure_coefficients_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain ((block x l).pressure
        n) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
      (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.updateBlock ActualParticularStageControls.associatedStrip a.context a.state a.carrierBlock
        a.gaussianInput a.aliasInput x.coefficients.residualBand).pressure n) := by
    apply assembled_pressure_smooth
    intro j hj m
    exact native_slice_smooth (native_pressure_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem gaussian_coefficients_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain
      ((gaussianBlock x l).velocity n i) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
      (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.gaussianBlock a.context a.state a.carrierBlock a.gaussianInput a.aliasInput
        x.coefficients.residualBand).velocity n i) := by
    apply assembled_velocity_smooth
    intro j hj m
    exact native_slice_smooth (native_gaussian_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem block_eq_output (H : Invariant σ x) (l : Index B N0) :
    block x l = ActualParticularStageControls.outputBlock (ActualCycleParameters.particularState x)
      x.coefficients.residualBand (l.2,l.1) := by
  unfold ActualParticularStageControls.outputBlock ActualParticularStageControls.associatedUpdate
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

/-- Good block, given by `ActualParticularStageControls.outputGood
(ActualCycleParameters.particularState x) x.coefficients.residualBand (l.2,l.1)`. -/
noncomputable def goodBlock (x : CycleState (Index B N0)) (l : Index B N0) :=
  ActualParticularStageControls.outputGood (ActualCycleParameters.particularState x)
    x.coefficients.residualBand (l.2,l.1)

theorem amplitude_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1/2+σ) (fun l n z => (block x l).velocity n i j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).1 i j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have ht : LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1/2+σ) (fun l n z => (ActualParticularStageControls.outputBlock
        (ActualCycleParameters.particularState x) x.coefficients.residualBand (l.2,l.1)).velocity n
            i j z) := by
    simp only [LabelSumBounds.UniformWaveClass,
        ActualParticularStageControls.meanEnvelope_eq_primary] at hh ⊢
    exact hh
  apply ht.congr
  intro l n z _
  exact congrArg (fun b : HarmonicBlock Point => b.velocity n i j z) (block_eq_output H l).symm

theorem pressure_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ) (fun l n z => (block x l).pressure n j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).2.1 j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have he : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  have ht : LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ) (fun l n z => (ActualParticularStageControls.outputBlock
        (ActualCycleParameters.particularState x) x.coefficients.residualBand (l.2,l.1)).pressure n
            j z) := by
    simp only [LabelSumBounds.UniformWaveClass,
        ActualParticularStageControls.meanEnvelope_eq_primary, he] at hh ⊢
    exact hh
  apply ht.congr
  intro l n z _
  exact congrArg (fun b : HarmonicBlock Point => b.pressure n j z) (block_eq_output H l).symm

theorem good_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ-3*ChartScales.kappa) (fun l n z => (goodBlock x l).velocity n i j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).2.2 i j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have he : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  simp only [LabelSumBounds.UniformWaveClass,
      ActualParticularStageControls.meanEnvelope_eq_primary, he] at hh ⊢
  exact hh

theorem gaussian_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (β : ℝ) (i : Fin 3) (m : ℤ) :
    LabelSumBounds.UniformClass ActualInitialization.strip
      (fun _ _ z => Real.sqrt (ActualInitialization.strip.zeta z)) β
      (fun l n z => (gaussianBlock x l).velocity n i m z) := by
  have hg := ActualParticularGaussian.gaussianBlock_all_gains _
    (fun l => ActualCycleParameters.current_frequency x (l.2,l.1) (H.carrier (l.2,l.1)))
    (native_inputSupport H) hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1) β i m
  have hh := (MeanBoundsReindex.uniformClass_return (s := ActualInitialization.strip)
    (w := fun (_ : ActualParticularStageControls.Label B N0) _ z =>
      Real.sqrt (ActualInitialization.strip.zeta z)) cycleAssoc hg).reindex
    (fun l : Index B N0 => (l.2,l.1))
  apply hh.congr
  intro l n z _
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem solenoidal (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) : HarmonicWaveInteraction.ModeSolenoidal ActualInitialization.strip
      (ActualPrimary.commonContext B) (block x l) := by
  rw [block_eq_output H l]
  exact ActualParticularDynamics.cycle_modeSolenoidal (preservesCarriers H) (native_inputSupport H)
    hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1) (l.2,l.1)

theorem good_carrier (x : CycleState (Index B N0)) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l) (goodBlock x l) := ⟨rfl,rfl,rfl⟩

theorem good_real (x : CycleState (Index B N0)) (l : Index B N0) :
    ErrorHarmonics.RealBlock (goodBlock x l) := by
  constructor
  · intro n i j z
    exact (ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i j (cycleAssoc z)
  · intro n j z
    exact (ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2 n j (cycleAssoc z)

theorem gaussian_eq_cycle (H : Invariant σ x) (l : Index B N0) :
    gaussianBlock x l = StateReindex.block cycleAssoc
      (ActualParticularDynamics.actualGaussian (ActualCycleParameters.particularState x) (l.2,l.1)
        x.coefficients.residualBand) := by
  unfold ActualParticularDynamics.actualGaussian
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem field_cancellation (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0)
    (n : ℕ) (z : Point × ℝ) (hz : z.1 ∈ ActualInitialization.strip.domain) :
    linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l) (block x l) n z +
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).oscillation n z =
      (goodBlock x l).oscillation n z + (gaussianBlock x l).oscillation n z := by
  have hh := ActualParticularDynamics.cycle_context_linear_cancellation
    (preservesCarriers H) (native_inputSupport H) hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1)
    (l.2,l.1) (H.sourceBand l) n z hz
  change linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l)
      (ActualParticularStageControls.outputBlock (ActualCycleParameters.particularState x)
        x.coefficients.residualBand (l.2,l.1)) n z +
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).oscillation n z =
      (goodBlock x l).oscillation n z + (StateReindex.block cycleAssoc
        (ActualParticularDynamics.actualGaussian (ActualCycleParameters.particularState x) (l.2,l.1)
          x.coefficients.residualBand)).oscillation n z at hh
  rwa [← block_eq_output H l, ← gaussian_eq_cycle H l] at hh

theorem linear_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass ActualInitialization.strip
      ActualInitialization.envelope (1+σ-3*ChartScales.kappa)
      (fun l n z =>
        (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
          (x.coefficients.blocks l) (x.coefficients.gaussian l)
          (x.coefficients.aliasCoefficients l)).velocity n i j z +
        (HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B)
          (x.coefficients.blocks l) (block x l) (gaussianBlock x l).velocity).velocity n i j z) :=
              by
  apply linearGoodBlock_cancel_uniform (ActualPrimary.commonContext B) x.coefficients.blocks (block
      x)
    (fun l => HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (goodBlock x) (fun l => (gaussianBlock x l).velocity)
  · intro n
    exact contDiffOn_const.add ((contDiffOn_const.mul
      ((ActualInitialization.operators B).radialProfile.smooth 0)).smul contDiffOn_const)
  · intro n
    exact contDiffOn_const
  · exact (ActualInitialization.base_bounds B).smooth
  · intro l n i j
    exact (coefficients_smooth H hN l n i j).mono ActualInitialization.geometry.strip_subset
  · intro l n j
    exact (pressure_coefficients_smooth H hN l n j).mono ActualInitialization.geometry.strip_subset
  · exact H.phase
  · exact H.angular
  · intro l n i
    exact HarmonicResidual.residualBlock_conjugate _ _ _ _ _ n i
  · intro l n i
    exact (good_real x l).1 n i
  · intro i j _
    exact good_bounds H hN i j
  · intro l n z hz θ i
    have hs : SameCarrier (x.coefficients.blocks l)
        (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
          (x.coefficients.blocks l) (x.coefficients.gaussian l)
          (x.coefficients.aliasCoefficients l)) := ⟨rfl,rfl,rfl⟩
    rw [withCarrier_of_same hs, withCarrier_of_same (good_carrier x l)]
    change _ + _ = _ + (gaussianBlock x l).oscillation n (z,θ) i
    exact congrArg (fun f : Fin 3 → ℝ => f i) (field_cancellation H hN l n (z,θ) hz)

section PressureAssembly

open HarmonicCalculus LinearWaveBounds PeriodizedWaveBounds ParticularWaveAssembly
open ParticularWaveBounds CopyAngularInvariance ActualWaveRegularity

/-- Pressure is assembled from the same actual modes as velocity. -/
theorem particularBlock_pressure_eq_modes {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι)
    (hf : ∀ n, (v.blocks l).frequency n ≠ 0) :
    (p.particularBlock v c u l).oscillatoryPressure = fun n z =>
      ∑ j ∈ modes v.residualBand,
        (mode ((particularCopyData p v c u l j).background.frequency n)
          ((particularCopyData p v c u l j).background.phase n)
          ((particularCopyData p v c u l j).common.pressure n) (particularChart z)).re := by
  have ha (j : ℤ) (n : ℕ) :
      CopyAngularInvariance.Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
        ((particularCopyData p v c u l j).common.pressure n) := by
    apply CopyData.common_pressure_invariant
    · intro m k
      exact nativeCutoff_invariant ((0 : CycleSlow), (1 : ℝ)) _ _ k
    · intro m k
      exact complexCopyPressure_invariant (angleTangent_invariant _) (angleLift_invariant _)
        _ ((p.particular l).length_pos m).le k _
  funext n z
  unfold CycleParameters.particularBlock
  rw [StateReindex.block_pressure]
  change ((p.particular l).updateBlock _ _ _ _ _ _ _).oscillatoryPressure n
    (cycleAssoc z.1, z.2) = _
  rw [ParticularParameters.updateBlock, assembledBlock_pressure_value]
  apply Finset.sum_congr rfl
  intro j _hj
  have hi := invariant_angleShuffle (ha j n) (cycleAssoc z.1) z.2
  have hc := actualCarrier_character (p.particular l).background
    (StateReindex.block cycleAssoc.symm (v.blocks l)) j hf n (cycleAssoc z.1, z.2)
  change Complex.re (_ * _) = Complex.re
    (((particularCopyData p v c u l j).common.pressure n
      (angleShuffle (cycleAssoc z.1, z.2))) *
      carrier ((actualCarrier (p.particular l).background
        (StateReindex.block cycleAssoc.symm (v.blocks l)) j).frequency n)
        ((actualCarrier (p.particular l).background
          (StateReindex.block cycleAssoc.symm (v.blocks l)) j).phase n)
        (angleShuffle (cycleAssoc z.1, z.2)))
  rw [hc, hi]
  rfl

theorem pressure_field_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((parameters B N0).particularPressure x.coefficients
      (ActualPrimary.commonContext B) x.state n)
      (ActualInitialization.geometry.domain ×ˢ (univ : Set ℝ)) := by
  change ContDiffOn ℝ ∞ (fun z => ∑ l ∈ x.coefficients.labels n,
    (block x l).oscillatoryPressure n z) _
  apply ContDiffOn.sum
  intro l _hl
  change ContDiffOn ℝ ∞ (((parameters B N0).particularBlock x.coefficients
    (ActualPrimary.commonContext B) x.state l).oscillatoryPressure n) _
  rw [particularBlock_pressure_eq_modes _ _ _ _ _ (H.frequency l)]
  apply ContDiffOn.sum
  intro j hj
  exact ActualWaveRegularityData.particular_mode_pressure_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j)
    (native_pressure_class H hN l j ((mem_modes _ _).mp hj).1)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).2) n

end PressureAssembly

/-- Every field is derived for the literal particular construction from
the incoming analytic invariant and its separately tracked periods. -/
theorem actual_data (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (_hσ : 1 / 5 ≤ σ) : Data x σ where
  amplitude := amplitude_bounds H hN
  pressure := pressure_bounds H hN
  coefficients := coefficients_smooth H hN
  pressureCoefficients := pressure_coefficients_smooth H hN
  gaussianCoefficients := gaussian_coefficients_smooth H hN
  solenoidal := solenoidal H hN
  gaussian := gaussian_bounds H hN
  field := (field_regular H T hN).1
  pressureField := pressure_field_smooth H hN
  periodic := (field_regular H T hN).2.1
  support := (field_regular H T hN).2.2
  linear := linear_bounds H hN

theorem actual_inputs (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ) :
    ActualParticularMeanGain.Inputs x σ :=
  (actual_data H T hN hσ).inputs H hN

end Outputs

end NavierStokes.ActualParticularCycleData
