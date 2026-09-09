/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedDynamics
import LeanPool.NavierStokesAndEuler.NavierStokes.NativePrincipalEquations

/-!
# Native controls for the actual signed correction

The fixed physical primary labels and their selected frames are reused.
The raw signed mask contains only the slow spatial factor.  Both compact
native factors belong to the cutoff, so no time cutoff is declared frozen
along the fast field.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedStageControls

open Set Function Filter
open scoped ContDiff Topology BigOperators
open WeightedClasses

open CorrectionInitialization

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Full point: an abbreviation for `Point × ℝ`. -/
abbrev FullPoint := Point × ℝ
/-- Native: an abbreviation for `ActualSignedGeometry.Native`. -/
abbrev Native := ActualSignedGeometry.Native
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Signed label: an abbreviation for `ActualPrimary.Label B N0 × Fin 2`. -/
abbrev SignedLabel (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

variable {B N0 : ℕ}

/-- Directions, given by `PrimaryResidualClass.directions (ActualPrimary.commonContext B)`. -/
noncomputable def directions (B : ℕ) := PrimaryResidualClass.directions
    (ActualPrimary.commonContext B)

/-- Native point as an element of `Native`. -/
noncomputable def nativePoint (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    (x : FullPoint) : Native :=
  (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1),
    (ActualPrimary.geometry l.2 l.1).coordinates k (ActualPrimary.toAbsolute n x.1).2)

/-- Coefficient scale, constructed using `PhysicalSignedWave.coefficientScale`. -/
noncomputable def coefficientScale (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  PhysicalSignedWave.coefficientScale (ChartScales.epsilon ActualPrimary.h n)
    (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.1))
    (PhysicalParticularWave.velocityWeight ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.1)))

/-- Normal scale, constructed using `PhysicalParticularWave.normalWeight`. -/
noncomputable def normalScale (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.normalWeight (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.1)) (ChartScales.carrier ActualPrimary.h n)
    (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand l.1))

/-- Clock scale, given by `PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
(ChartScales.Q (BaseChartJets.cellBand l.1))`. -/
noncomputable def clockScale (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.1))

/-- Matrix, given by `ActualPrimary.covariance B N0 l.1 (nativePoint l n k x).1`. -/
noncomputable def matrix (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : SignedWaveUpdate.Mat2 :=
  ActualPrimary.covariance B N0 l.1 (nativePoint l n k x).1

/-- Target, given by `coefficientScale l n ^ 2 • (fun q => PrimaryTargetBounds.actualTarget
ActualPrimary.modulation (nativePoint l n k x).1 q)`. -/
noncomputable def target (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : SignedWaveUpdate.Vec2 :=
  coefficientScale l n ^ 2 •
    (fun q => PrimaryTargetBounds.actualTarget ActualPrimary.modulation (nativePoint l n k x).1 q)

/-- Mask, given by `ActualPrimary.spatialMask l.1 (nativePoint l n k x).1`. -/
noncomputable def mask (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : ℝ := ActualPrimary.spatialMask l.1 (nativePoint l n k x).1

/-- Fundamental, constructed using `PrimaryPulseBounds.normalizedPulse`. -/
noncomputable def fundamental (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : Space :=
  PrimaryPulseBounds.normalizedPulse ((ActualPrimary.phases B N0 l.2).frame l.1)
    ((ActualPrimary.phases B N0 l.2).lam l.1) ((ActualPrimary.phases B N0 l.2).u l.1)
    ((ActualPrimary.phases B N0 l.2).L l.1) (ActualPrimary.pulseCoordinates l.1 (nativePoint l n k
        x))

/-- Normal motion as an element of `Space`. -/
noncomputable def normalMotion (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : Space :=
  (normalScale l n * clockScale l n) • (ActualPrimary.phases B N0 l.2).phase.velocity l.1
    (ActualPrimary.phasePoint l.1 (nativePoint l n k x))

/-- Action, constructed using `clockScale`. -/
noncomputable def action (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : Space →L[ℝ] Space :=
  clockScale l n • PrimaryCopyBridge.baseOperator
    ((ActualPrimary.phases B N0 l.2).phase.F l.1 (nativePoint l n k x).1)
    ((ActualPrimary.phases B N0 l.2).phase.shear l.1 (ActualPrimary.phasePoint l.1 (nativePoint l n
        k x)))

/-- Cutoff, constructed using `PartitionedCovariance.cutoff`. -/
noncomputable def cutoff (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : ℝ :=
  PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1 *
    ActualPrimary.gaussian l.1 (nativePoint l n k x)

/-- The literal raw data accepted by the correction stage.  The same
selected primary frame is used for the matrix, unit pulse, and pressure. -/
noncomputable def parameters (l : SignedLabel B N0) : CorrectionStep.PeriodizedSignedParameters
    Point Frequency where
  base := ActualPrimary.chartCoefficients l.2 l.1
  directions := directions B
  matrix := matrix l
  target := target l
  mask := mask l
  fundamental := fundamental l
  normalMotion := normalMotion l
  action := action l
  cutoff := cutoff l
  angularFrequency _ := PrimaryGeometryAssembly.angularMode ActualPrimary.certificate
      ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1
  column := l.2

theorem parameters_raw (l : SignedLabel B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (k : Frequency) :
    ((parameters l).copyData s request).raw k = SignedWaveUpdate.coefficients
      (ActualPrimary.chartCoefficients l.2 l.1) (HarmonicWaveInteraction.productStrip s)
          (directions B)
      (matrix l k) (target l k) request (mask l k) (fundamental l k)
      (normalMotion l k) (action l k) l.2 := rfl

theorem coefficientScale_pos (l : SignedLabel B N0) (n : ℕ) :
    0 < coefficientScale l n :=
  PhysicalSignedWave.coefficientScale_pos (ChartScales.epsilon_pos ActualPrimary.h n)
    (ChartScales.epsilon_pos ActualPrimary.h (BaseChartJets.cellBand l.1))
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _)

theorem nativePoint_slow_auxiliary (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    (x : FullPoint) (v : Plane) (t : ℝ) :
    (nativePoint l n k (x + t • ((0, (0, v)), 0))).1 = (nativePoint l n k x).1 := by
  simp [nativePoint, ActualPrimary.nativeSlow, ActualPrimary.toAbsolute]

theorem nativePoint_angle (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    (x : FullPoint) (t : ℝ) :
    nativePoint l n k (x + t • ((0 : Point), (1 : ℝ))) = nativePoint l n k x := by
  simp only [nativePoint, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]

theorem directions_fast (B : ℕ) : (directions B).fast = ((0, (0, ActualPrimary.temporalVector)), 0)
    := rfl

theorem matrix_frozen (l : SignedLabel B N0) (k : Frequency) :
    SignedWaveUpdate.FrozenAlong (directions B).fast (matrix l k) := by
  intro n x t
  rw [directions_fast]
  simp only [matrix, nativePoint_slow_auxiliary]

theorem target_frozen (l : SignedLabel B N0) (k : Frequency) :
    SignedWaveUpdate.FrozenAlong (directions B).fast (target l k) := by
  intro n x t
  rw [directions_fast]
  simp only [target, nativePoint_slow_auxiliary]

theorem mask_frozen (l : SignedLabel B N0) (k : Frequency) :
    SignedWaveUpdate.FrozenAlong (directions B).fast (mask l k) := by
  intro n x t
  rw [directions_fast]
  simp only [mask, nativePoint_slow_auxiliary]

theorem request_frozen (s : StripData Point) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    SignedWaveUpdate.FrozenAlong (directions B).fast (LocalSignedRequest.fullRequest s P coord c u)
        := by
  rw [directions_fast]
  exact LocalSignedRequest.fullRequest_torus_frozen s P coord c u ActualPrimary.temporalVector

/-! ## The request is estimated from actual current residuals -/

theorem fullRequest_jets_from_residuals (G : SignedMeanGain.Geometry)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (alpha : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip alpha (u.thetaResidual c))
    (hz : MeanClass G.strip alpha (u.axialResidual c))
    {Λ I : Type} (K : Λ → ℕ → I → Set FullPoint) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets (HarmonicWaveInteraction.productStrip G.strip)
      (fun _ _ x => G.strip.zeta x.1) (alpha - 1) K
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
  have H' : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner
      G.gauge.radial.outer c u := by simpa only [G.inner_eq, G.outer_eq] using H
  have htheta := H.theta G.patch.a_pos G.patch.a_lt_b
  have haxial := H'.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq
    (congrArg CorrectionState.State.pressure hfixed)
  have haxial' : GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (u.axialResidual c) := by simpa only [G.inner_eq, G.outer_eq] using haxial
  exact ActualSignedControl.physical_fullRequest_localJets G.region G.patch G.left_pos G.right_pos
    G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one c u alpha
    htheta.smooth haxial'.smooth (MeanStateRegularity.MovingField.movingSupport htheta)
    (MeanStateRegularity.MovingField.movingSupport haxial') hθ hz K

/-- The initial cycle invariant gives the request class without assuming
any request derivative or signed output bound. -/
theorem fullRequest_jets_from_invariant {ι : Type} (G : SignedMeanGain.Geometry)
    (c : CorrectionState.Context Point) (primary : ι → CorrectionState.HarmonicBlock Point)
    (P : ι → ℕ → Point → ℝ) (labelCarrier : ι → ℕ → Set Point)
    (sigma : ℝ) (u : CorrectionStep.CycleState ι)
    (H : CorrectionStep.CycleAnalyticInvariant G c primary P labelCarrier sigma u)
    {Λ I : Type} (K : Λ → ℕ → I → Set FullPoint) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets (HarmonicWaveInteraction.productStrip G.strip)
      (fun _ _ x => G.strip.zeta x.1) sigma K
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u.state n x q) := by
  have hh := fullRequest_jets_from_residuals G c u.state (1 + sigma) H.primitives H.reconstructed
    H.raw_mean_bounds.1 H.raw_mean_bounds.2 K
  simpa only [show (1 : ℝ) + sigma - 1 = sigma by ring] using hh

/-! ## Native input jets on a neighborhood of the closed band -/

open PhaseJetBounds PrimaryCopyBounds

/-- Pulse label: an abbreviation for `Fin 2 × ActualPrimary.Label B N0`. -/
abbrev PulseLabel (B N0 : ℕ) := Fin 2 × ActualPrimary.Label B N0

/-- Slow jet domain, bundling `toDomain`, `growth`, `scale_le_growth`. -/
noncomputable def slowJetDomain (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    JetDomain (PulseLabel B N0) PhaseCalculus.Slow where
  toDomain := ActualPhaseDefect.reducedSlowDomain U
  growth l p := (BaseContextAssembly.nativeStrip ActualPrimary.nominal U).growth
    (BaseChartJets.cellBand l.2) (BaseContextAssembly.insertSlow p)
  scale_le_growth l _ _ := (le_max_right 1 (ChartScales.S (BaseChartJets.cellBand l.2))).trans
    ((BaseContextAssembly.nativeStrip ActualPrimary.nominal U).slow_le_growth _ _)

theorem slow_geometry (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    BaseChartJets.GeometryBounds (slowJetDomain (B := B) (N0 := N0) U).toDomain ActualPrimary.h
      (BaseContextAssembly.geometryRadius ActualPrimary.nominal U)
      (BaseContextAssembly.geometryBound ActualPrimary.nominal U)
      (U.qlo / 2) (BaseContextAssembly.geometryUpper U)
      (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
  have h := BaseContextAssembly.native_geometry ActualPrimary.nominal U (PulseLabel B N0)
  exact ⟨fun l p hp => h.time l p hp.2, fun l p hp => h.radius l p hp.2,
    fun l p hp => h.bounded l p hp.2, fun l p hp => h.q_range l p hp.2,
    fun l p hp => h.x_range l p hp.2⟩

theorem slow_inverse_edge (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h))
    (l : PulseLabel B N0) {p : PhaseCalculus.Slow}
    (hp : p ∈ (slowJetDomain U).carrier l) :
    (FinalSlowBase.edgeDistance ActualPrimary.nominal
      (BaseChartJets.normalizedCoordinates ActualPrimary.h p).2)⁻¹ ≤ (slowJetDomain U).growth l p
          := by
  let st := BaseContextAssembly.nativeStrip ActualPrimary.nominal U
  have hm := (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal U _).mp hp.2
  have ht : 0 < p.2.2 := U.time_pos _ hm.1
  have hδ := st.delta_pos _ hp.2
  have hle := ActualSignedGeometry.radialDelta_le_edge (W := ActualPrimary.nominal) hm.2
    (BaseChartJets.normalizedCoordinates ActualPrimary.h p).2.2
  simp only [BaseContextAssembly.slowCoordinates_insert] at hle
  rw [PrimaryTargetBounds.profileRadius_sq (F := ActualPrimary.outgoing) ht] at hle
  have heq : PrimaryTargetBounds.profileRadius ActualPrimary.h p =
      (LocalSignedRequest.profileMap (2 * ActualPrimary.h) (BaseContextAssembly.insertSlow p)).1 :=
          by
    unfold PrimaryTargetBounds.profileRadius
    rw [BaseChartJets.normalizedCoordinates_eq]
    rfl
  rw [heq] at hle
  have hi : (FinalSlowBase.edgeDistance ActualPrimary.nominal
      (BaseChartJets.normalizedCoordinates ActualPrimary.h p).2)⁻¹ ≤
      (st.delta (BaseContextAssembly.insertSlow p))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hδ hle
  exact hi.trans ((le_max_right 1 _).trans
    (le_mul_of_one_le_left (le_trans zero_le_one (le_max_left 1 _)) (st.one_le_slow _)))

theorem native_target_jets (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    NativeJets (slowJetDomain (B := B) (N0 := N0) U)
      (fun _ => PrimaryTargetBounds.movingWeight ActualPrimary.nominal)
      (fun _ => PrimaryTargetBounds.actualTarget ActualPrimary.modulation) :=
  PrimaryCopyBounds.actualTarget_jets ActualPrimary.modulation ActualPrimary.profile.fullTrueCone
    (slowJetDomain U) (BaseContextAssembly.geometryRadius_pos ActualPrimary.nominal U)
    (div_pos U.qlo_pos (by norm_num)) (slow_geometry U) (slow_inverse_edge U)

theorem native_matrix_jets (r c : Fin 2) :
    PolynomialJets (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N)
      (fun l p => ActualPrimary.covariance B N0 l p r c) := by
  rw [ActualPrimary.covariance_eq_integral]
  exact PrimaryPulseBounds.primaryCovariance_entry_polynomial _ ActualPrimary.prefactor
    (fun j => (ActualPrimary.phases B N0 j).frame)
    (fun j => (ActualPrimary.phases B N0 j).lam)
    (fun j => (ActualPrimary.phases B N0 j).u)
    (fun j => (ActualPrimary.phases B N0 j).L)
    (ActualPrimary.nativeReferenceBounds B N0).prefactor_jets
    (fun j => (ActualPrimary.phases B N0 j).pulse_jets)
    (fun j => (ActualPrimary.phases B N0 j).lam_pos)
    (fun j => (ActualPrimary.phases B N0 j).u_pos)
    (fun j => (ActualPrimary.phases B N0 j).L_pos) r c

theorem native_matrix_slot_jets (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) (r c :
    Fin 2) :
    PolynomialJets (ActualPhaseDefect.reducedJetDomain (B := B) (N0 := N0) U)
      (fun l z => ActualPrimary.covariance B N0 l.2 z.1 r c) := by
  have h : PolynomialJets (slowJetDomain (B := B) (N0 := N0) U).toDomain
      (fun l p => ActualPrimary.covariance B N0 l.2 p r c) :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (native_matrix_jets r c) Prod.snd
      (fun _ => rfl) (fun _ _ hp => hp.1)
  exact h.lift_slot _ _

theorem native_mask_jets (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    PolynomialJets (slowJetDomain (B := B) (N0 := N0) U).toDomain
      (fun l => ActualPrimary.spatialMask l.2) := by
  have hcoord := BaseChartJets.polynomial_of_unit (BaseChartJets.normalizedCoordinates_polynomial
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half
    (div_pos U.qlo_pos (by norm_num)) (slow_geometry (B := B) (N0 := N0) U))
  have hq := hcoord.clm (ContinuousLinearMap.fst ℝ ℝ SlowBorelBase.Inner)
  have hdy : PolynomialJets (slowJetDomain (B := B) (N0 := N0) U).toDomain
      (fun _ p => SquaredPartition.dyadicProfile (BaseChartJets.normalizedCoordinates
          ActualPrimary.h p).1) := by
    apply hq.compact_comp isOpen_univ SquaredPartition.dyadicProfile_smooth.contDiffOn
      (isCompact_Icc : IsCompact (Icc (U.qlo / 2) (BaseContextAssembly.geometryUpper U)))
          (subset_univ _)
    intro l p hp
    exact ⟨((slow_geometry U).q_range l p hp).1.le, ((slow_geometry U).q_range l p hp).2.le⟩
  have hm := nativeMask_jets (slowJetDomain (B := B) (N0 := N0) U).toDomain
    (fun l => BaseChartJets.cellBand l.2) (fun l => (PrimaryGeometryAssembly.label
        ActualPrimary.nominal l.2).2)
    (fun l => l.2.val.property.1) (fun _ => rfl)
  apply (hdy.mul hm).congr
  intro l p _
  have he := (ActualPrimary.spatialMask_eq l.2 p).symm
  simp only [BaseChartJets.normalizedCoordinates_eq]
  exact he

/-- Unit domain, bundling `toDomain`, `growth`, `scale_le_growth`. -/
noncomputable def unitDomain : JetDomain (ActualPrimary.Label B N0) (PhaseCalculus.Slow × ℝ) where
  toDomain := PrimaryPulseBounds.productDomain
    (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B N0).prepared.N)
    (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo)
  growth l _ := ChartScales.S (BaseChartJets.cellBand l)
  scale_le_growth _ _ _ := le_rfl

/-- Native unit, constructed using `PrimaryPulseBounds.normalizedPulse`. -/
noncomputable def nativeUnit (l : PulseLabel B N0) : PhaseCalculus.Slow × ℝ → Space :=
  PrimaryPulseBounds.normalizedPulse ((ActualPrimary.phases B N0 l.1).frame l.2)
    ((ActualPrimary.phases B N0 l.1).lam l.2) ((ActualPrimary.phases B N0 l.1).u l.2)
    ((ActualPrimary.phases B N0 l.1).L l.2)

/-- Native envelope, constructed using `PrimaryPulseBounds.referenceP`. -/
noncomputable def nativeEnvelope (l : PulseLabel B N0) (z : PhaseCalculus.Slow × ℝ) : ℝ :=
  PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 l.1).lam l.2)
    ((ActualPrimary.phases B N0 l.1).u l.2) ((ActualPrimary.phases B N0 l.1).L l.2)
    ((ActualPrimary.phases B N0 l.1).L l.2 * z.2)

theorem native_unit_jets : NativeJets (signDomain (unitDomain (B := B) (N0 := N0)))
    nativeEnvelope nativeUnit := by
  change NativeJets (signDomain (unitDomain (B := B) (N0 := N0)))
    (fun l z => PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 l.1).lam l.2)
      ((ActualPrimary.phases B N0 l.1).u l.2) ((ActualPrimary.phases B N0 l.1).L l.2)
      ((ActualPrimary.phases B N0 l.1).L l.2 * z.2))
    (fun l => PrimaryPulseBounds.normalizedPulse ((ActualPrimary.phases B N0 l.1).frame l.2)
      ((ActualPrimary.phases B N0 l.1).lam l.2) ((ActualPrimary.phases B N0 l.1).u l.2)
      ((ActualPrimary.phases B N0 l.1).L l.2))
  exact NativeJets.both_signs (V := unitDomain)
    (w := fun j l z => PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 j).lam l)
      ((ActualPrimary.phases B N0 j).u l) ((ActualPrimary.phases B N0 j).L l)
      ((ActualPrimary.phases B N0 j).L l * z.2))
    (f := fun j l => PrimaryPulseBounds.normalizedPulse ((ActualPrimary.phases B N0 j).frame l)
      ((ActualPrimary.phases B N0 j).lam l) ((ActualPrimary.phases B N0 j).u l)
      ((ActualPrimary.phases B N0 j).L l))
    (fun j => NativeJets.of_envelope (ActualPrimary.phases B N0 j).pulse_jets)

/-- Native phase, bundling `epsilon`, `p`, `pz`, `x0` and the required compatibility proofs. -/
noncomputable def nativePhase : PhaseFamily (PulseLabel B N0) where
  epsilon l := (ActualPrimary.phases B N0 l.1).phase.epsilon l.2
  p l := (ActualPrimary.phases B N0 l.1).phase.p l.2
  pz l := (ActualPrimary.phases B N0 l.1).phase.pz l.2
  x0 l := (ActualPrimary.phases B N0 l.1).phase.x0 l.2
  theta l := (ActualPrimary.phases B N0 l.1).phase.theta l.2
  F l := (ActualPrimary.phases B N0 l.1).phase.F l.2
  G l := (ActualPrimary.phases B N0 l.1).phase.G l.2

theorem native_phase_jets (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    PolynomialJets (ActualPhaseDefect.reducedJetDomain U) (nativePhase (B := B) (N0 := N0)).normal ∧
    PolynomialJets (ActualPhaseDefect.reducedJetDomain U) (nativePhase (B := B) (N0 :=
        N0)).velocity ∧
    PolynomialJets (ActualPhaseDefect.reducedJetDomain U) (nativePhase (B := B) (N0 := N0)).shear
        := by
  let D := ActualPhaseDefect.reducedSlowDomain (B := B) (N0 := N0) U
  let M := (ActualPrimary.phases B N0 0).M + (ActualPrimary.phases B N0 1).M
  let r := min (ActualPrimary.phases B N0 0).r (ActualPrimary.phases B N0 1).r
  have hM0 := (ActualPrimary.phases B N0 0).one_le_M
  have hM1 := (ActualPrimary.phases B N0 1).one_le_M
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMj (j : Fin 2) : (ActualPrimary.phases B N0 j).M ≤ M := by
    fin_cases j <;> dsimp [M] <;> linarith
  have hr : 0 < r := lt_min (ActualPrimary.phases B N0 0).r_pos (ActualPrimary.phases B N0 1).r_pos
  have hrj (j : Fin 2) : r ≤ (ActualPrimary.phases B N0 j).r := by
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hF : PolynomialJets D (nativePhase (B := B) (N0 := N0)).F :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ hx => hx.1)
  have hG : PolynomialJets D (nativePhase (B := B) (N0 := N0)).G :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ hx => hx.1)
  exact (nativePhase (B := B) (N0 := N0)).polynomial_jets D
    (fun l => (ActualPrimary.phases B N0 l.1).V l.2)
    (fun l => (ActualPrimary.phases B N0 l.1).openV l.2) hF hG hr hM
    (fun l => by
      have h := (ActualPrimary.phases B N0 l.1).constants l.2
      exact ⟨h.1.trans (hMj _), h.2.1.trans (hMj _), h.2.2.1.trans (hMj _), h.2.2.2.trans (hMj _)⟩)
    (fun l => (ActualPrimary.phases B N0 l.1).epsilon_ne l.2)
    (fun l p hp => by
      have h := (ActualPrimary.phases B N0 l.1).radius l.2 p hp.1
      exact ⟨(hrj _).trans h.1, h.2.trans (hMj _)⟩)
    (fun l t ht => ((ActualPrimary.phases B N0 l.1).slot l.2 t ht).trans
      (mul_le_mul_of_nonneg_right (hMj _) (zero_le_one.trans (D.one_le_scale l))))

theorem native_action_jets (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h)) :
    PolynomialJets (ActualPhaseDefect.reducedJetDomain (B := B) (N0 := N0) U)
      (fun l z => PrimaryCopyBridge.baseOperator ((nativePhase (B := B) (N0 := N0)).F l z.1)
        ((nativePhase (B := B) (N0 := N0)).shear l z)) := by
  have hF : PolynomialJets (ActualPhaseDefect.reducedSlowDomain (B := B) (N0 := N0) U)
      (nativePhase (B := B) (N0 := N0)).F :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ hx => hx.1)
  exact ((hF.lift_slot _ _).pair (native_phase_jets U).2.2).clm PrimaryCopyBridge.baseOperatorFamily

/-! ## The actual band scalars -/

/-- Coefficient lower as an element of `ℝ`. -/
noncomputable def coefficientLower : ℝ :=
  (1 / ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h)) *
    (1 / ActualSignedGeometry.powerBound (-(ActualPrimary.h / 2)))

/-- Coefficient upper, given by `ActualSignedGeometry.powerBound (CoordinateAlgebra.A
ActualPrimary.h) * ActualSignedGeometry.powerBound (-(ActualPrimary.h / 2))`. -/
noncomputable def coefficientUpper : ℝ :=
  ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h) *
    ActualSignedGeometry.powerBound (-(ActualPrimary.h / 2))

theorem coefficientLower_pos : 0 < coefficientLower := by
  have h₁ := ActualSignedGeometry.powerBound_one (CoordinateAlgebra.A ActualPrimary.h)
  have h₂ := ActualSignedGeometry.powerBound_one (-(ActualPrimary.h / 2))
  unfold coefficientLower
  positivity

theorem coefficientUpper_one : 1 ≤ coefficientUpper :=
  one_le_mul_of_one_le_of_one_le (ActualSignedGeometry.powerBound_one _)
    (ActualSignedGeometry.powerBound_one _)

theorem coefficientScale_bounds (l : SignedLabel B N0) {n : ℕ}
    (hnm : n ≤ BaseChartJets.cellBand l.1 + 4) (hmn : BaseChartJets.cellBand l.1 ≤ n + 4) :
    coefficientLower ≤ coefficientScale l n ∧ coefficientScale l n ≤ coefficientUpper := by
  let hnear : ∀ (_ : Unit) (_ : ℕ), n ≤ BaseChartJets.cellBand l.1 + 4 ∧
      BaseChartJets.cellBand l.1 ≤ n + 4 := fun _ _ => ⟨hnm, hmn⟩
  have h := (ActualSignedGeometry.coefficientScale (fun _ => n)
    (fun (_ : Unit) _ => BaseChartJets.cellBand l.1) hnear ActualPrimary.h).bounds () 0
  rw [ActualSignedGeometry.coefficientScale_value] at h
  exact h

theorem nativePoint_eq_dynamics (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    nativePoint l n k = ActualPrimaryDynamics.copyPoint l.2 l.1 n k := rfl

theorem clockScale_eq_dynamics (l : SignedLabel B N0) (n : ℕ) :
    clockScale l n = ActualPrimaryDynamics.clockScale l.1 n := by
  change ChartScales.Q n ^ (CoordinateAlgebra.A ActualPrimary.h + 1 / 2) /
    ChartScales.Q (BaseChartJets.cellBand l.1) ^ (CoordinateAlgebra.A ActualPrimary.h + 1 / 2) = _
  rw [show CoordinateAlgebra.A ActualPrimary.h + 1 / 2 = 1 + ActualPrimary.h by
    unfold CoordinateAlgebra.A
    ring]
  rfl

theorem normalScale_eq_dynamics (l : SignedLabel B N0) (n : ℕ) :
    normalScale l n = ActualPrimaryDynamics.normalScale l.1 n := by
  simp only [normalScale, PhysicalParticularWave.normalWeight, PhysicalParticularWave.ratioPower,
    ← Real.sqrt_eq_rpow, ActualPrimaryDynamics.normalScale, ActualPrimaryDynamics.radialScale]

/-! ## One family of support cells in every band -/

/-- Absolute native, given by `(ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1),
(ActualPrimary.toAbsolute n x.1).2)`. -/
noncomputable def absoluteNative (l : SignedLabel B N0) (n : ℕ) (x : FullPoint) : Native :=
  (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1), (ActualPrimary.toAbsolute n
      x.1).2)

theorem absoluteNative_smooth (l : SignedLabel B N0) (n : ℕ) :
    ContDiff ℝ ∞ (absoluteNative l n) :=
  ((ActualPrimary.nativeSlow_smooth l.1).comp ((ActualPrimary.toAbsolute_smooth n).comp
      contDiff_fst)).prodMk
    (((ActualPrimary.toAbsolute_smooth n).comp contDiff_fst).snd)

/-- Absolute cells, constructed using `PeriodizedWaveBounds.nativeCells`. -/
noncomputable def absoluteCells (l : SignedLabel B N0) : PeriodizedWaveBounds.Cells Native
    Frequency :=
  PeriodizedWaveBounds.nativeCells (fun _ => ActualPrimary.geometry l.2 l.1)
    (fun _ => (ActualPrimary.clockWindow l.1).core) (fun _ => (ActualPrimary.clockWindow
        l.1).core_compact)
    (fun _ => by
      have hg : ActualPrimary.geometry l.2 l.1 = ActualSignedGeometry.slotGeometry
          ActualPrimary.slots ActualPrimary.vectors_det
          (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label ActualPrimary.nominal
              l.1) l.2)
          (ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1)) := rfl
      have hc : ActualPrimary.clockWindow l.1 = ActualSignedGeometry.clockWindow
          ActualPrimary.slots (BaseChartJets.cellBand l.1) := rfl
      rw [hg, hc]
      exact (ActualSignedGeometry.clockWindow_injective ActualPrimary.slots
          ActualPrimary.vectors_det
        ActualPrimary.outgoing.data.h_pos.le
        (l := PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label
            ActualPrimary.nominal l.1) l.2)
        ((ActualPrimary.choice B N0).prepared.large _ l.1.property).four_le
        (ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1))).mono
          (Set.image_mono (ActualSignedGeometry.clockWindow ActualPrimary.slots
              _).core_subset_outer))

/-- The copy cells use the fixed absolute primary geometry even in bands
where the label is inactive.  No truncated negative cover gap occurs. -/
noncomputable def cells (l : SignedLabel B N0) : PeriodizedWaveBounds.Cells FullPoint Frequency
    where
  carrier n k := absoluteNative l n ⁻¹' (absoluteCells l).carrier n k
  closed n k := ((absoluteCells l).closed n k).preimage (absoluteNative_smooth l n).continuous
  locallyFinite n := by
    intro x
    obtain ⟨V, hV, hfinite⟩ := (absoluteCells l).locallyFinite n (absoluteNative l n x)
    refine ⟨absoluteNative l n ⁻¹' V, (absoluteNative_smooth l n).continuous.continuousAt hV, ?_⟩
    apply hfinite.subset
    rintro k ⟨y, hy, hyV⟩
    exact ⟨absoluteNative l n y, hy, hyV⟩
  unique n i j x hi hj := (absoluteCells l).unique n i j (absoluteNative l n x) hi hj

theorem cells_mem (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    x ∈ (cells l).carrier n k ↔ (nativePoint l n k x).2 ∈ (ActualPrimary.clockWindow l.1).core :=
        Iff.rfl

theorem nativePoint_smooth (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ (nativePoint l n k) := ActualPrimaryDynamics.copyPoint_smooth l.2 l.1 n k

/-- Native time, given by `(ActualPrimary.pulseCoordinates l.1 (nativePoint l n k x)).2`. -/
noncomputable def nativeTime (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) : ℝ :=
  (ActualPrimary.pulseCoordinates l.1 (nativePoint l n k x)).2

theorem nativeTime_smooth (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ (nativeTime l n k) := (nativePoint_smooth l n k).snd.snd.div_const _

theorem cutoff_smooth (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ (cutoff l k n) :=
  ((SquaredPartition.gridMask_smooth ActualPrimary.slots.radius 0).comp
    (nativePoint_smooth l n k).snd.fst).mul
      (GaussianTailFlat.profile_contDiff.comp (nativeTime_smooth l n k))

theorem cutoff_support (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    support (cutoff l k n) ⊆ (cells l).carrier n k := by
  intro x hx
  have hu : PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1 ≠ 0
      := by
    intro hz
    exact hx (by simp only [cutoff, hz, zero_mul])
  have hg : GaussianTailFlat.profile (nativeTime l n k x) ≠ 0 := by
    intro hz
    exact hx (by simp only [cutoff, ActualPrimary.gaussian, nativeTime] at hz ⊢; rw [hz, mul_zero])
  have hdist : |nativeTime l n k x - 1 / 2| < 1 / 3 := by
    by_contra hn
    exact hg (GaussianTailFlat.profile_zero (le_of_not_gt hn))
  obtain ⟨htlo, hthi⟩ := abs_lt.mp hdist
  have htime : nativeTime l n k x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hL := (ActualPrimary.phases B N0 0).L_pos l.1
  apply (cells_mem l n k x).mpr
  have hu' := hu
  change (nativePoint l n k x).2.1 ∈ support (PartitionedCovariance.cutoff
      ActualPrimary.slots.radius) at hu'
  rw [PartitionedCovariance.cutoff_support ActualPrimary.slots.radius_pos] at hu'
  refine ⟨⟨hu'.1.le, hu'.2.le⟩, ?_⟩
  change (nativePoint l n k x).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 0).L l.1)
  exact ⟨((div_pos_iff_of_pos_right hL).mp htime.1).le, ((div_lt_one hL).mp htime.2).le⟩

theorem cutoff_zero_germ_outside_time (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : nativeTime l n k x ∉ Icc (1 / 10 : ℝ) (9 / 10)) :
    cutoff l k n =ᶠ[𝓝 x] fun _ => 0 := by
  have hdist : 1 / 3 < |nativeTime l n k x - 1 / 2| := by
    rcases not_and_or.mp hx with hlo | hhi
    · have hh := lt_of_not_ge hlo
      rw [abs_of_neg (by linarith)]
      linarith
    · have hh := lt_of_not_ge hhi
      rw [abs_of_pos (by linarith)]
      linarith
  have hg := (GaussianTailFlat.profile_eventually_zero hdist).comp_tendsto
    (nativeTime_smooth l n k).continuous.continuousAt
  filter_upwards [hg] with y hy
  change GaussianTailFlat.profile (nativeTime l n k y) = 0 at hy
  change PartitionedCovariance.cutoff _ _ * GaussianTailFlat.profile (nativeTime l n k y) = 0
  rw [hy, mul_zero]

/-! ## Uniform transport on the actual closed control cells -/

/-- Full strip, given by `ActualPrimaryBounds.fullStrip`. -/
noncomputable def fullStrip : StripData FullPoint := ActualPrimaryBounds.fullStrip

/-- Envelope, given by `ActualPrimaryBounds.fullEnvelope (l.2, l.1)`. -/
noncomputable def envelope (l : SignedLabel B N0) : ℕ → FullPoint → ℝ :=
  ActualPrimaryBounds.fullEnvelope (l.2, l.1)

/-- Phase cell, given by `{x | x ∈ ActualPrimaryBounds.controlCell n ((l.2, l.1), k) ∧
nativeTime l n k x ∈ Icc (1 / 10 : ℝ) (9 / 10)}`. -/
noncomputable def phaseCell (l : SignedLabel B N0) (n : ℕ) (k : Frequency) : Set FullPoint :=
  {x | x ∈ ActualPrimaryBounds.controlCell n ((l.2, l.1), k) ∧
    nativeTime l n k x ∈ Icc (1 / 10 : ℝ) (9 / 10)}

theorem nativePoint_eq_fullCopy (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    (hn : ActualPrimaryBounds.near (l.2, l.1) n) :
    nativePoint l n k = ActualPrimaryBounds.fullCopy (l.2, l.1) n k := by
  funext x
  apply Prod.ext
  · exact ActualPrimary.nativeSlow_toAbsolute_eq_slowChange l.1 n x.1
  · change (ActualPrimary.geometry l.2 l.1).coordinates k
      ((CommonCoverSolve.coverPower (CommonWindow.index ActualPrimary.h n)).symm x.1.2.2) =
      (ActualPrimary.chartGeometry n l.2 l.1).coordinates k x.1.2.2
    exact ActualPrimary.chartGeometry_coordinates_active n l.2 l.1 hn.2 k x.1.2.2

theorem phaseCell_time {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hc : x ∈ phaseCell l n k) : nativeTime l n k x ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hc.2.1], by linarith [hc.2.2]⟩

theorem uniform_of_primary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : PulseLabel B N0 → ℕ → FullPoint → ℝ} {α : ℝ}
    {f : ℕ → ActualPrimaryBounds.CopyIndex B N0 → FullPoint → E}
    (hf : LocalizedWaveBounds.LocalClass fullStrip ActualPrimaryBounds.controlCell
      (fun n i => w i.1 n) α f) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun l => w (l.2, l.1)) α phaseCell
      (fun l n k => f n ((l.2, l.1), k)) := by
  refine ⟨fun l n k x hx hc => hf.smooth n ((l.2, l.1), k) x hx hc.1, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun l n k x hx hc j hj => hb n ((l.2, l.1), k) x hx hc.1 j hj⟩

/-- The affine derivative bound is required only on active cells. The
single derivative constant still precedes every label, band and copy. -/
theorem native_jets_on_phaseCell {J D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : JetDomain J D} {w : J → D → ℝ} {f : J → D → E} (hf : NativeJets V w f)
    (index : SignedLabel B N0 → ℕ → J)
    (L : SignedLabel B N0 → ℕ → Frequency → FullPoint →L[ℝ] D)
    (c : SignedLabel B N0 → ℕ → Frequency → D)
    (W : SignedLabel B N0 → ℕ → FullPoint → ℝ)
    {A H : ℝ} (hA : 1 ≤ A) (hH : 1 ≤ H)
    (hmap : ∀ l n k x, x ∈ fullStrip.domain → x ∈ phaseCell l n k →
      L l n k x + c l n k ∈ V.carrier (index l n))
    (hgrowth : ∀ l n k x, x ∈ fullStrip.domain → x ∈ phaseCell l n k →
      V.growth (index l n) (L l n k x + c l n k) ≤ A * fullStrip.growth n x)
    (hlinear : ∀ l n k x, x ∈ fullStrip.domain → x ∈ phaseCell l n k →
      ‖L l n k‖ ≤ H * fullStrip.slow n)
    (hweight : ∀ l n k x, x ∈ fullStrip.domain → x ∈ phaseCell l n k →
      w (index l n) (L l n k x + c l n k) ≤ W l n x) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip W 0 phaseCell
      (fun l n k x => f (index l n) (L l n k x + c l n k)) := by
  refine ⟨?_, ?_⟩
  · intro l n k x hx hc
    exact ((hf.smooth (index l n)).contDiffAt
      ((V.isOpen (index l n)).mem_nhds (hmap l n k x hx hc))).comp x
        (((L l n k).contDiff.add contDiff_const).contDiffAt)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    refine ⟨C * A ^ p * H ^ m, by positivity, p + m, ?_⟩
    intro l n k x hx hc j hj
    have hm := hmap l n k x hx hc
    have hG := fullStrip.one_le_growth n x
    have hS := fullStrip.one_le_slow n
    have hGN := V.one_le_growth (index l n) hm
    have hw := hf.nonneg (index l n) _ hm
    have hW : 0 ≤ W l n x := hw.trans (hweight l n k x hx hc)
    have hlin : ‖L l n k‖ ^ j ≤ H ^ m * fullStrip.growth n x ^ m := by
      calc
        _ ≤ (H * fullStrip.slow n) ^ m :=
          (pow_le_pow_left₀ (norm_nonneg _) (hlinear l n k x hx hc) j).trans
            (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hH hS) hj)
        _ ≤ (H * fullStrip.growth n x) ^ m := by gcongr; exact fullStrip.slow_le_growth n x
        _ = _ := mul_pow _ _ _
    have hu := norm_jet_comp_affine (V.isOpen (index l n)) (hf.smooth (index l n))
      (L l n k) (c l n k) hm j
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (f (index l n)) (L l n k x + c l n k)‖ * ‖L l n k‖ ^ j := hu
      _ ≤ (C * V.growth (index l n) (L l n k x + c l n k) ^ p *
          w (index l n) (L l n k x + c l n k)) * (H ^ m * fullStrip.growth n x ^ m) :=
        mul_le_mul (hb _ _ hm j hj) hlin (by positivity)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
            (pow_nonneg (zero_le_one.trans hGN) _)) hw)
      _ ≤ (C * (A * fullStrip.growth n x) ^ p * W l n x) *
          (H ^ m * fullStrip.growth n x ^ m) := by
        gcongr
        · exact hgrowth l n k x hx hc
        · exact hweight l n k x hx hc
      _ = majorant fullStrip (W l) 0 (C * A ^ p * H ^ m) (p + m) n x := by
        rw [majorant, Real.rpow_zero, mul_pow, pow_add]
        ring

theorem matrix_local_jets (r c : Fin 2) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0 (phaseCell (B := B) (N0 :=
        N0))
      (fun l n k x => matrix l k n x r c) := by
  have hp := uniform_of_primary (w := fun _ _ _ => 1) (ActualPrimaryBounds.polynomial_on_control
    (native_matrix_slot_jets (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion r c))
  apply ActualSignedControl.uniform_local_congr hp
  intro l n k x _ hc
  dsimp only [matrix]
  rw [nativePoint_eq_fullCopy l n k hc.1.1]

/-- Slow linear, given by `(ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ).comp
(ActualPrimaryBounds.slotLinear (l.2, l.1) n)`. -/
noncomputable def slowLinear (l : SignedLabel B N0) (n : ℕ) : FullPoint →L[ℝ] PhaseCalculus.Slow :=
  (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ).comp (ActualPrimaryBounds.slotLinear (l.2, l.1)
      n)

theorem slowLinear_bound {l : SignedLabel B N0} {n : ℕ}
    (hn : ActualPrimaryBounds.near (l.2, l.1) n) :
    ‖slowLinear l n‖ ≤ ActualPrimaryBounds.copyCost * fullStrip.slow n := by
  have hp : ‖ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [ContinuousLinearMap.coe_fst', one_mul] using norm_fst_le x
  calc
    _ ≤ ‖ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ‖ *
        ‖ActualPrimaryBounds.slotLinear (l.2, l.1) n‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (ActualPrimaryBounds.copyCost * fullStrip.slow n) :=
      mul_le_mul hp (ActualPrimaryBounds.slotLinear_bound hn) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem slowCopy_affine (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    (ActualPrimaryBounds.fullCopy (l.2, l.1) n k x).1 =
      slowLinear l n x + (ActualPrimaryBounds.fullCopy (l.2, l.1) n k 0).1 := by
  have he := congrArg Prod.fst (ActualPrimaryBounds.slotCopy_affine (l.2, l.1) n k x)
  exact he

theorem slow_growth_eq (U : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h))
    (l : PulseLabel B N0) (x : Native) :
    (slowJetDomain U).growth l x.1 =
      (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared).growth l.2 x := rfl

theorem copied_target_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ x => fullStrip.zeta x) 0
      (phaseCell (B := B) (N0 := N0))
      (fun l n k x => PrimaryTargetBounds.actualTarget ActualPrimary.modulation (nativePoint l n k
          x).1) := by
  have hh := native_jets_on_phaseCell (native_target_jets (B := B) (N0 := N0)
      ActualPhaseDefect.paddedRegion)
    (fun l _ => (l.2, l.1)) (fun l n _ => slowLinear l n)
    (fun l n k => (ActualPrimaryBounds.fullCopy (l.2, l.1) n k 0).1)
    (fun _ _ x => fullStrip.zeta x) (A := 25) (H := ActualPrimaryBounds.copyCost)
    (by norm_num) ActualPrimaryBounds.copyCost_one
    (fun l n k x hx hc => by
      rw [← slowCopy_affine]
      exact (ActualPrimaryBounds.control_maps hx hc.1).1)
    (fun l n k x hx hc => by
      rw [← slowCopy_affine, slow_growth_eq]
      exact ActualPrimaryBounds.copyPoint_growth hc.1.1 k hx)
    (fun _ _ _ _ _ hc => slowLinear_bound hc.1.1)
    (fun l n k x hx _ => by
      rw [← slowCopy_affine]
      exact le_of_eq (ActualPrimaryBounds.copyPoint_weight (l.2, l.1) n k hx))
  apply ActualSignedControl.uniform_local_congr hh
  intro l n k x _ hc
  rw [nativePoint_eq_fullCopy l n k hc.1.1]
  exact Filter.Eventually.of_forall (fun y => by dsimp only; rw [← slowCopy_affine])

theorem uniform_scalar_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : SignedLabel B N0 → ℕ → FullPoint → ℝ} {α : ℝ}
    {r : SignedLabel B N0 → ℕ → Frequency → FullPoint → ℝ}
    {f : SignedLabel B N0 → ℕ → Frequency → FullPoint → E}
    (hr : PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0 phaseCell r)
    (hf : PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell f)
    (hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ w l n x) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell
      (fun l n k x => r l n k x • f l n k x) := by
  have ha := LocalizedWaveBounds.LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hr
  have hb := LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw hf
  apply LocalizedWaveBounds.LocalClass.to_uniformLocalJets
  simpa only [one_mul, zero_add] using ha.smul hb

theorem uniform_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : SignedLabel B N0 → ℕ → FullPoint → ℝ} {α : ℝ}
    {f : SignedLabel B N0 → ℕ → Frequency → FullPoint → E}
    (hf : PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell f)
    (hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ w l n x) (L : E →L[ℝ] F) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell (fun l n k x => L (f l n k x)) :=
  ((LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw hf).map L).to_uniformLocalJets

theorem coefficientSquare_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n _ (_ : FullPoint) => coefficientScale l n ^ 2) := by
  have hh : LocalizedWaveBounds.LocalUnweighted fullStrip ActualPrimaryBounds.controlCell 0
      (fun n (i : ActualPrimaryBounds.CopyIndex B N0) (_ : FullPoint) => coefficientScale (i.1.2,
          i.1.1) n ^ 2) := by
    apply ActualPrimaryBounds.local_constant (sq_nonneg coefficientUpper)
    intro n i x _ hx
    have hh := coefficientScale_bounds (i.1.2, i.1.1)
      (ActualPrimaryBounds.near_distance hx.1).1 (ActualPrimaryBounds.near_distance hx.1).2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (coefficientScale_pos _ _).le hh.2 2
  exact uniform_of_primary (w := fun _ _ _ => 1) hh

theorem target_local_jets (q : Fin 2) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ x => fullStrip.zeta x) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k x => target l k n x q) := by
  have ht := uniform_map (copied_target_jets (B := B) (N0 := N0))
    (fun _ _ x hx => fullStrip.zeta_nonneg x hx) (PiLp.proj 2 (fun _ : Fin 2 => ℝ) q)
  have hh := uniform_scalar_mul coefficientSquare_local_jets ht
    (fun _ _ x hx => fullStrip.zeta_nonneg x hx)
  exact hh

theorem mask_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k => mask l k n) := by
  have hm := (native_mask_jets (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion).lift_slot
    (fun i => (ActualPrimary.phases B N0 i.1).V i.2)
    (fun i => (ActualPrimary.phases B N0 i.1).openV i.2)
  have hp := uniform_of_primary (w := fun _ _ _ => 1) (ActualPrimaryBounds.polynomial_on_control hm)
  apply ActualSignedControl.uniform_local_congr hp
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change ActualPrimary.spatialMask l.1 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k y).1 =
    ActualPrimary.spatialMask l.1 (nativePoint l n k y).1
  rw [nativePoint_eq_fullCopy l n k hc.1.1]

theorem fullStrip_zeta_pos {x : FullPoint} (hx : x ∈ fullStrip.domain) : 0 < fullStrip.zeta x := by
  have hr := (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimaryBounds.region
      x.1).mp hx
  have hT := BaseContextAssembly.nativeStrip_time ActualPrimary.nominal ActualPrimaryBounds.region
      hx
  have hi : (ActualSignedGeometry.meanEquiv.symm x.1) ∈
      NativeBandExtension.radialInterior ActualPrimary.nominal := ⟨hT, hr.2⟩
  have hp := (NativeBandExtension.radialInterior_spec ActualPrimary.nominal hi).2.2.2
  have he := ActualSignedGeometry.viewStrip_zeta ActualPrimary.nominal ActualPrimaryBounds.region id
    (ActualSignedGeometry.meanEquiv.symm x.1)
  change fullStrip.zeta x = PrimaryTargetBounds.movingWeight ActualPrimary.nominal
    (ActualSignedGeometry.meanEquiv.symm x.1).1 at he
  rw [he]
  exact hp

theorem covariance_margins {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (1 / 5 : ℝ) ^ 2 * (ActualPrimary.choice B N0).detGap ≤
      |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (fullStrip.slow n)) (matrix l k n x)).det| ∧
    (∀ r c, |Real.sqrt (fullStrip.slow n) * matrix l k n x r c| ≤
      5 * (ActualPrimary.choice B N0).entryBound) ∧
    (∀ j, (coefficientLower ^ 2 * (ActualPrimary.choice B N0).inverseLower) * fullStrip.zeta x ≤
      SmoothCovariance.weights (matrix l k n x) (target l k n x) j) := by
  have hrad := ActualPrimaryBounds.copyPoint_radial (l.2, l.1) n k
    (x := ActualSignedGeometry.meanEquiv.symm x.1) hx
  have hi : ActualPrimaryBounds.fullCopy (l.2, l.1) n k x ∈
      NativeBandExtension.radialInterior ActualPrimary.nominal := ⟨hrad.1, hrad.2⟩
  have hq : NativeBandExtension.nativeQ ActualPrimary.h (ActualPrimaryBounds.fullCopy (l.2, l.1) n
      k x) ∈
      Icc (1 / 2 : ℝ) 2 := hc.1.2.2.2
  have hz := ActualPrimary.covariance_bounds B N0 l.1 _
    (NativeBandExtension.reference_of_closed_band ActualPrimary.nominal hi hq) hc.1.2.1
  have hw : PrimaryTargetBounds.movingWeight ActualPrimary.nominal
      (ActualPrimaryBounds.fullCopy (l.2, l.1) n k x).1 = fullStrip.zeta x :=
    ActualPrimaryBounds.copyPoint_weight (l.2, l.1) n k hx
  rw [hw] at hz
  have hn := hc.1.1
  have hband : 1 ≤ BaseChartJets.cellBand l.1 :=
    le_trans (by norm_num) (ActualPrimaryBounds.label_large (l.2, l.1))
  have hS : fullStrip.slow n = ChartScales.S n :=
    max_eq_right (PhysicalGraphBounds.S_ge_one hn.1)
  have hrat := ActualSignedGeometry.sqrt_S_window hn.1 hband
    (ActualPrimaryBounds.near_distance hn).1 (ActualPrimaryBounds.near_distance hn).2
  rw [← hS] at hrat
  have hs := coefficientScale_bounds l (ActualPrimaryBounds.near_distance hn).1
    (ActualPrimaryBounds.near_distance hn).2
  have hh := ActualSignedControl.rescale_margins (R := Real.sqrt (fullStrip.slow n))
    (c := coefficientScale l n) (clo := coefficientLower) (rlo := 1 / 5) (rhi := 5) hz
    (Real.one_le_sqrt.mpr (PhysicalGraphBounds.S_ge_one hband))
    (ActualPrimary.choice B N0).detGap_pos.le (ActualPrimary.choice B N0).inverseLower_pos.le
    (fullStrip.zeta_nonneg x hx) coefficientLower_pos hs.1 (by norm_num) hrat.1 hrat.2
  simpa only [matrix, target, nativePoint_eq_fullCopy l n k hn] using hh

/-- The uniform covariance record is constructed from the actual selected
matrix and leading target, including both closed dyadic endpoints. -/
noncomputable def nativeCovariance (B N0 : ℕ) :
    SignedCopyBounds.UniformNativeCovariance fullStrip (phaseCell (B := B) (N0 := N0)) matrix
        target where
  matrix_jets := matrix_local_jets
  target_jets := target_local_jets
  zeta_pos := fun _ hx => fullStrip_zeta_pos hx
  determinantGap := (1 / 5 : ℝ) ^ 2 * (ActualPrimary.choice B N0).detGap
  entryBound := 5 * (ActualPrimary.choice B N0).entryBound
  primaryLower := coefficientLower ^ 2 * (ActualPrimary.choice B N0).inverseLower
  gap_pos := mul_pos (by norm_num) (ActualPrimary.choice B N0).detGap_pos
  entry_one := one_le_mul_of_one_le_of_one_le (by
      norm_num) (ActualPrimary.choice B N0).entryBound_ge_one
  lower_pos := mul_pos (sq_pos_of_pos coefficientLower_pos) (ActualPrimary.choice B
      N0).inverseLower_pos
  determinant := fun _ _ _ _ hx hc => (covariance_margins hx hc).1
  entries := fun _ _ _ _ hx hc => (covariance_margins hx hc).2.1
  lower := fun _ _ _ _ hx hc => (covariance_margins hx hc).2.2

/-- Normalize native, given by `(ContinuousLinearMap.fst ℝ PhaseCalculus.Slow Plane).prod
(ActualPrimaryBounds.timeProjection L)`. -/
noncomputable def normalizeNative (L : ActualPrimary.Label B N0) :
    Native →L[ℝ] (PhaseCalculus.Slow × ℝ) :=
  (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow Plane).prod
    (ActualPrimaryBounds.timeProjection L)

theorem normalizeNative_apply (L : ActualPrimary.Label B N0) (x : Native) :
    normalizeNative L x = ActualPrimary.pulseCoordinates L x := by
  change (x.1, ((ActualPrimary.phases B N0 0).L L)⁻¹ * x.2.2) =
    (x.1, x.2.2 / (ActualPrimary.phases B N0 0).L L)
  rw [div_eq_mul_inv, mul_comm]

theorem normalizeNative_norm (L : ActualPrimary.Label B N0) :
    ‖normalizeNative L‖ ≤ (ActualPrimary.choice B N0).prepared.M := by
  have hM := (ActualPrimary.choice B N0).prepared.one_le_M
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hM)
  intro x
  change max ‖x.1‖ ‖ActualPrimaryBounds.timeProjection L x‖ ≤ _
  apply max_le
  · exact (norm_fst_le x).trans (le_mul_of_one_le_left (norm_nonneg x) hM)
  · exact (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (ActualPrimaryBounds.timeProjection_norm L) (norm_nonneg x))

/-- Pulse linear, given by `(normalizeNative l.1).comp ((ActualPrimaryBounds.copyLinear (l.2,
l.1) n).comp ActualPrimaryBounds.nativeOfFull)`. -/
noncomputable def pulseLinear (l : SignedLabel B N0) (n : ℕ) :
    FullPoint →L[ℝ] (PhaseCalculus.Slow × ℝ) :=
  (normalizeNative l.1).comp
    ((ActualPrimaryBounds.copyLinear (l.2, l.1) n).comp ActualPrimaryBounds.nativeOfFull)

theorem pulseLinear_bound {l : SignedLabel B N0} {n : ℕ}
    (hn : ActualPrimaryBounds.near (l.2, l.1) n) :
    ‖pulseLinear l n‖ ≤
      ((ActualPrimary.choice B N0).prepared.M * ActualPrimaryBounds.copyCost) * fullStrip.slow n :=
          by
  calc
    _ ≤ ‖normalizeNative l.1‖ *
        (‖ActualPrimaryBounds.copyLinear (l.2, l.1) n‖ * ‖ActualPrimaryBounds.nativeOfFull‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (ActualPrimary.choice B N0).prepared.M *
        ((ActualPrimaryBounds.copyCost * fullStrip.slow n) * 1) :=
      mul_le_mul (normalizeNative_norm l.1)
        (mul_le_mul (ActualPrimaryBounds.copyLinear_bound hn) ActualPrimaryBounds.nativeOfFull_norm
          (norm_nonneg _) (mul_nonneg (zero_le_one.trans ActualPrimaryBounds.copyCost_one)
            (zero_le_one.trans (fullStrip.one_le_slow n))))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (zero_le_one.trans (ActualPrimary.choice B N0).prepared.one_le_M)
    _ = _ := by ring

theorem pulseCopy_affine (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    ActualPrimary.pulseCoordinates l.1 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k x) =
      pulseLinear l n x +
        ActualPrimary.pulseCoordinates l.1 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k 0) := by
  rw [← normalizeNative_apply, ← normalizeNative_apply]
  change normalizeNative l.1 (ActualPrimaryBounds.copyPoint (l.2, l.1) n k
    (ActualPrimaryBounds.nativeOfFull x)) = _
  rw [ActualPrimaryBounds.copyPoint_affine, map_add]
  rfl

theorem nativeEnvelope_copy (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    nativeEnvelope (l.2, l.1)
      (ActualPrimary.pulseCoordinates l.1 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k x)) =
      ActualPrimaryBounds.pulseEnvelope (l.2, l.1) (ActualPrimaryBounds.fullCopy (l.2, l.1) n k
          x).2.2 := by
  change PrimaryPulseBounds.referenceP _ _ _
    (((ActualPrimary.phases B N0 l.2).L l.1) *
      ((ActualPrimaryBounds.fullCopy (l.2, l.1) n k x).2.2 / (ActualPrimary.phases B N0 0).L l.1)) =
    PrimaryPulseBounds.referenceP _ _ _ (ActualPrimaryBounds.fullCopy (l.2, l.1) n k x).2.2
  congr 1
  rw [ActualPrimary.length_sign l.2 l.1,
    mul_div_cancel₀ _ ((ActualPrimary.phases B N0 0).L_pos l.1).ne']

theorem fundamental_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (envelope (B := B) (N0 := N0)) 0 phaseCell
      (fun l n k => fundamental l k n) := by
  have hh := native_jets_on_phaseCell (native_unit_jets (B := B) (N0 := N0))
    (fun l _ => (l.2, l.1)) (fun l n _ => pulseLinear l n)
    (fun l n k => ActualPrimary.pulseCoordinates l.1 (ActualPrimaryBounds.fullCopy (l.2, l.1) n k
        0))
    envelope (A := 25) (H := (ActualPrimary.choice B N0).prepared.M * ActualPrimaryBounds.copyCost)
    (by norm_num) (one_le_mul_of_one_le_of_one_le (ActualPrimary.choice B N0).prepared.one_le_M
      ActualPrimaryBounds.copyCost_one)
    (fun l n k x _ hc => by
      rw [← pulseCopy_affine]
      refine ⟨hc.1.2.1, ?_⟩
      have ht := phaseCell_time hc
      simpa only [nativeTime, nativePoint_eq_fullCopy l n k hc.1.1] using ht)
    (fun l n k x _ hc => by
      change ChartScales.S (BaseChartJets.cellBand l.1) ≤ _
      exact (ActualSignedGeometry.S_window_le hc.1.1.1
        (ActualPrimaryBounds.near_distance hc.1.1).2).trans
        (mul_le_mul_of_nonneg_left ((le_max_right 1 (ChartScales.S n)).trans
          (fullStrip.slow_le_growth n x)) (by norm_num)))
    (fun _ _ _ _ _ hc => pulseLinear_bound hc.1.1)
    (fun l n k x _ hc => by
      rw [← pulseCopy_affine, nativeEnvelope_copy]
      exact le_of_eq (ActualPrimaryBounds.envelope_copy (l.2, l.1) n k hc.1.2.2.1).symm)
  apply ActualSignedControl.uniform_local_congr hh
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change nativeUnit (l.2, l.1) (pulseLinear l n y + _) =
    nativeUnit (l.2, l.1) (ActualPrimary.pulseCoordinates l.1 (nativePoint l n k y))
  rw [← pulseCopy_affine, nativePoint_eq_fullCopy l n k hc.1.1]

theorem normalScale_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n _ (_ : FullPoint) => normalScale l n) :=
  uniform_of_primary (w := fun _ _ _ => 1) ActualPrimaryBounds.normalScale_local

theorem clockScale_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n _ (_ : FullPoint) => clockScale l n) := by
  have hh : LocalizedWaveBounds.LocalUnweighted fullStrip ActualPrimaryBounds.controlCell 0
      (fun n (i : ActualPrimaryBounds.CopyIndex B N0) (_ : FullPoint) => clockScale (i.1.2, i.1.1)
          n) := by
    apply ActualPrimaryBounds.local_constant
      (zero_le_one.trans (ActualSignedGeometry.powerBound_one (CoordinateAlgebra.A ActualPrimary.h
          + 1 / 2)))
    intro n i x _ hc
    change |PhysicalParticularWave.ratioPower (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand i.1.2)) (CoordinateAlgebra.A ActualPrimary.h + 1 / 2)|
          ≤ _
    rw [abs_of_pos (PhysicalParticularWave.ratioPower_pos
      (ChartScales.Q_pos n) (ChartScales.Q_pos _) _)]
    exact ActualSignedGeometry.dyadic_ratioPower_le
      (ActualPrimaryBounds.near_distance hc.1).1 (ActualPrimaryBounds.near_distance hc.1).2 _
  exact uniform_of_primary (w := fun _ _ _ => 1) hh

theorem normal_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0))
      (fun l n _ => (ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n) :=
  uniform_of_primary (w := fun _ _ _ => 1) ActualPrimaryBounds.chart_normal_local

theorem normal_range {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    ActualPrimaryBounds.normalFloor B N0 ≤
        ‖(ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n x‖ ∧
      ‖(ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n x‖ ≤
        ActualPrimaryBounds.normalCeiling B N0 :=
  ActualPrimaryBounds.chart_normal_range (i := ((l.2, l.1), k)) (n := n) (x := x) hx hc.1

theorem normalMotion_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k => normalMotion l k n) := by
  have hs := uniform_scalar_mul (normalScale_local_jets (B := B) (N0 := N0))
    clockScale_local_jets (fun _ _ _ _ => zero_le_one)
  have hv := uniform_of_primary (w := fun _ _ _ => 1) (ActualPrimaryBounds.polynomial_on_control
    (native_phase_jets (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion).2.1)
  have hh := uniform_scalar_mul hs hv (fun _ _ _ _ => zero_le_one)
  apply ActualSignedControl.uniform_local_congr hh
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change (normalScale l n * clockScale l n) •
      (nativePhase (B := B) (N0 := N0)).velocity (l.2, l.1)
        ((ActualPrimaryBounds.fullCopy (l.2, l.1) n k y).1,
          (ActualPrimaryBounds.fullCopy (l.2, l.1) n k y).2.2) =
    (normalScale l n * clockScale l n) • (ActualPrimary.phases B N0 l.2).phase.velocity l.1
      (ActualPrimary.phasePoint l.1 (nativePoint l n k y))
  rw [nativePoint_eq_fullCopy l n k hc.1.1]
  rfl

theorem action_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k => action l k n) := by
  have hv := uniform_of_primary (w := fun _ _ _ => 1) (ActualPrimaryBounds.polynomial_on_control
    (native_action_jets (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion))
  have hh := uniform_scalar_mul clockScale_local_jets hv (fun _ _ _ _ => zero_le_one)
  apply ActualSignedControl.uniform_local_congr hh
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change clockScale l n •
      PrimaryCopyBridge.baseOperator
        ((nativePhase (B := B) (N0 := N0)).F (l.2, l.1) (ActualPrimaryBounds.fullCopy (l.2, l.1) n
            k y).1)
        ((nativePhase (B := B) (N0 := N0)).shear (l.2, l.1)
          ((ActualPrimaryBounds.fullCopy (l.2, l.1) n k y).1,
            (ActualPrimaryBounds.fullCopy (l.2, l.1) n k y).2.2)) = action l k n y
  unfold action
  rw [nativePoint_eq_fullCopy l n k hc.1.1]
  rfl

/-- Transverse projection, given by `(ContinuousLinearMap.fst ℝ ℝ ℝ).comp
(ContinuousLinearMap.snd ℝ PhaseCalculus.Slow Plane)`. -/
noncomputable def transverseProjection : Native →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow Plane)

theorem transverseProjection_norm : ‖transverseProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [transverseProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_mul] using
      (norm_fst_le x.2).trans (norm_snd_le x)

theorem native_cutoff_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (fun _ _ => 1)
      (fun l : PulseLabel B N0 => fun x : Native =>
        PartitionedCovariance.cutoff ActualPrimary.slots.radius x.2.1 * ActualPrimary.gaussian l.2
            x) := by
  have ht := affine_profile_jets
    (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)).toDomain
    (PartitionedCovariance.cutoff ActualPrimary.slots.radius)
    (SquaredPartition.gridMask_smooth ActualPrimary.slots.radius 0)
    (fun m => by
      obtain ⟨C, hC, hb⟩ := SquaredPartition.exists_uniform_jet_bound
        (SquaredPartition.gridMask_smooth ActualPrimary.slots.radius 0)
        (SquaredPartition.gridMask_compactSupport ActualPrimary.slots.radius
            ActualPrimary.slots.radius_pos 0) m
      exact ⟨C, hC.le, hb⟩)
    (fun _ : PulseLabel B N0 => transverseProjection) (fun _ => 0) (K := 1) le_rfl 0
    (fun _ => by simpa only [pow_zero, mul_one] using transverseProjection_norm)
  have ht' : PolynomialJets
      (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
        ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)).toDomain
      (fun _ : PulseLabel B N0 => fun x : Native => PartitionedCovariance.cutoff
          ActualPrimary.slots.radius x.2.1) := by
    simpa only [transverseProjection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', add_zero] using ht
  exact NativeJets.of_polynomial (ht'.mul ActualPrimaryBounds.gaussian_polynomial)

/-- Full copy linear, given by `(ActualPrimaryBounds.copyLinear (l.2, l.1) n).comp
ActualPrimaryBounds.nativeOfFull`. -/
noncomputable def fullCopyLinear (l : SignedLabel B N0) (n : ℕ) : FullPoint →L[ℝ] Native :=
  (ActualPrimaryBounds.copyLinear (l.2, l.1) n).comp ActualPrimaryBounds.nativeOfFull

theorem fullCopyLinear_bound {l : SignedLabel B N0} {n : ℕ}
    (hn : ActualPrimaryBounds.near (l.2, l.1) n) :
    ‖fullCopyLinear l n‖ ≤ ActualPrimaryBounds.copyCost * fullStrip.slow n := by
  calc
    _ ≤ ‖ActualPrimaryBounds.copyLinear (l.2, l.1) n‖ * ‖ActualPrimaryBounds.nativeOfFull‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖ActualPrimaryBounds.copyLinear (l.2, l.1) n‖ * 1 :=
      mul_le_mul_of_nonneg_left ActualPrimaryBounds.nativeOfFull_norm (norm_nonneg _)
    _ ≤ _ := by simp only [mul_one]; exact ActualPrimaryBounds.copyLinear_bound hn

theorem fullCopy_affine (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    ActualPrimaryBounds.fullCopy (l.2, l.1) n k x = fullCopyLinear l n x +
      ActualPrimaryBounds.fullCopy (l.2, l.1) n k 0 :=
  ActualPrimaryBounds.copyPoint_affine (l.2, l.1) n k (ActualPrimaryBounds.nativeOfFull x)

theorem cutoff_local_jets :
    PeriodizedWaveBounds.UniformLocalJets fullStrip (fun _ _ _ => 1) 0
      (phaseCell (B := B) (N0 := N0)) (fun l n k => cutoff l k n) := by
  have hh := native_jets_on_phaseCell (native_cutoff_jets (B := B) (N0 := N0))
    (fun l _ => (l.2, l.1)) (fun l n _ => fullCopyLinear l n)
    (fun l n k => ActualPrimaryBounds.fullCopy (l.2, l.1) n k 0)
    (fun _ _ _ => 1) (A := 25) (H := ActualPrimaryBounds.copyCost)
    (by norm_num) ActualPrimaryBounds.copyCost_one
    (fun l n k x hx _ => by
      rw [← fullCopy_affine]
      exact ActualPrimaryBounds.copyPoint_radial (l.2, l.1) n k hx)
    (fun l n k x hx hc => by
      rw [← fullCopy_affine]
      exact ActualPrimaryBounds.copyPoint_growth hc.1.1 k hx)
    (fun _ _ _ _ _ hc => fullCopyLinear_bound hc.1.1)
    (fun _ _ _ _ _ _ => le_rfl)
  apply ActualSignedControl.uniform_local_congr hh
  intro l n k x _ hc
  apply Filter.Eventually.of_forall
  intro y
  change PartitionedCovariance.cutoff _ (fullCopyLinear l n y + _).2.1 *
    ActualPrimary.gaussian l.1 (fullCopyLinear l n y + _) = cutoff l k n y
  unfold cutoff
  rw [← fullCopy_affine, nativePoint_eq_fullCopy l n k hc.1.1]

theorem uniform_select_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : SignedLabel B N0 → ℕ → FullPoint → ℝ} {α : ℝ}
    {f : Fin 2 → SignedLabel B N0 → ℕ → Frequency → FullPoint → E}
    (hf : ∀ j, PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell (f j))
    (hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ w l n x) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip w α phaseCell
      (fun l => f l.2 l) := by
  refine ⟨fun l => (hf l.2).smooth l, ?_⟩
  intro m
  obtain ⟨C, hC, p, h0⟩ := (hf 0).bounds m
  obtain ⟨D, hD, q, h1⟩ := (hf 1).bounds m
  refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
  intro l n k x hx hc j hj
  have hs : l.2 = 0 ∨ l.2 = 1 := by omega
  rcases hs with hs | hs
  · rw [hs]
    exact (h0 l n k x hx hc j hj).trans
      ((majorant_mono_degree fullStrip (w l) α hC (Nat.le_add_right p q) n x (hw l n x hx)).trans
        (PeriodizedWaveBounds.majorant_mono_constant fullStrip (w l) α (le_add_of_nonneg_right hD)
          (p + q) n x (hw l n x hx)))
  · rw [hs]
    exact (h1 l n k x hx hc j hj).trans
      ((majorant_mono_degree fullStrip (w l) α hD (Nat.le_add_left q p) n x (hw l n x hx)).trans
        (PeriodizedWaveBounds.majorant_mono_constant fullStrip (w l) α (le_add_of_nonneg_left hC)
          (p + q) n x (hw l n x hx)))

theorem inverse_frequency_uniform :
    UniformPrimaryWeights.UniformBandBound fullStrip (1 / 2)
      (fun i : SignedLabel B N0 × Frequency => fun n =>
        1 / (ActualPrimary.chartCoefficients i.1.2 i.1.1).frequency n) := by
  obtain ⟨C, hC, p, hb⟩ := ActualPrimaryBounds.inverse_carrier_band
  exact ⟨C, hC, p, fun _ n => hb n⟩

/-- The selected column is estimated uniformly before the physical label,
band, and copy.  Every matrix and unit in this theorem is the actual fixed
primary construction; only the new signed request varies. -/
theorem raw_coefficients_jets {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : SignedLabel B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1 / 2)
          phaseCell
      (fun l n k => (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).amplitude
          n) ∧
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : SignedLabel B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1)
          phaseCell
      (fun l n k => (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).pressure n)
          := by
  classical
  cases isEmpty_or_nonempty (SignedLabel B N0) with
  | inl h =>
      let := h
      constructor <;> refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim
          l⟩⟩
  | inr h =>
      let := h
      have hw : ∀ l n x, x ∈ fullStrip.domain → 0 ≤ envelope (B := B) (N0 := N0) l n x :=
        fun l n x _ => ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n x
      have hh (j : Fin 2) := SignedCopyBounds.uniform_coefficients_jets
        (a := fun (l : SignedLabel B N0) (_ : Frequency) => ActualPrimary.chartCoefficients l.2 l.1)
        (d := fun (_ : SignedLabel B N0) (_ : Frequency) => directions B)
        (R := fun (_ : SignedLabel B N0) (_ : Frequency) => request)
        (H := matrix) (T := target) (mask := mask) (v := fundamental)
        (Ndot := normalMotion) (A := action) (W := envelope)
        (nativeCovariance B N0) hR mask_local_jets fundamental_local_jets hw
        normal_local_jets normalMotion_local_jets action_local_jets
        (ActualPrimaryBounds.normalFloor_pos B N0)
        (fun l n k x hx hc => (normal_range (l := l) (n := n) (k := k) (x := x) hx hc).1)
        (fun l n k x hx hc => (normal_range (l := l) (n := n) (k := k) (x := x) hx hc).2)
        inverse_frequency_uniform j
      have hweight l n x hx := mul_nonneg (Real.sqrt_nonneg (fullStrip.zeta x)) (hw l n x hx)
      constructor
      · exact uniform_select_two (fun j => (hh j).1) hweight
      · exact uniform_select_two (fun j => (hh j).2) hweight

/-- The actual full request is derived from the current residuals.  No
request-output class or signed-output estimate is an input. -/
theorem actual_raw_coefficients_jets (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : SignedLabel B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (α - 1 / 2)
      (phaseCell (B := B) (N0 := N0))
      (fun l n k => (((parameters l).copyData ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)).raw k).amplitude n) ∧
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun (l : SignedLabel B N0) n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) α phaseCell
      (fun l n k => (((parameters l).copyData ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)).raw k).pressure n) := by
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  simpa only [show α - 1 + 1 / 2 = α - 1 / 2 by ring, sub_add_cancel] using
    raw_coefficients_jets hr'

/-- Covariance at label, bundling `matrix_jets`, `target_jets`, `zeta_pos`, `determinantGap` and
the required compatibility proofs. -/
noncomputable def covarianceAtLabel (l : SignedLabel B N0) :
    SignedCopyBounds.NativeCovariance fullStrip (phaseCell l) (matrix l) (target l) where
  matrix_jets a b := ((nativeCovariance B N0).matrix_jets a b).each l
  target_jets a := ((nativeCovariance B N0).target_jets a).each l
  zeta_pos := (nativeCovariance B N0).zeta_pos
  determinantGap := (nativeCovariance B N0).determinantGap
  entryBound := (nativeCovariance B N0).entryBound
  primaryLower := (nativeCovariance B N0).primaryLower
  gap_pos := (nativeCovariance B N0).gap_pos
  entry_one := (nativeCovariance B N0).entry_one
  lower_pos := (nativeCovariance B N0).lower_pos
  determinant := (nativeCovariance B N0).determinant l
  entries := (nativeCovariance B N0).entries l
  lower := (nativeCovariance B N0).lower l

theorem primary_weight_pos {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) (j : Fin 2) :
    0 < SmoothCovariance.weights (matrix l k n x) (target l k n x) j :=
  (mul_pos (nativeCovariance B N0).lower_pos (fullStrip_zeta_pos hx)).trans_le
    ((nativeCovariance B N0).lower l n k x hx hc j)

open scoped InnerProductSpace
open HarmonicCalculus

theorem fundamental_eq_unitPulse (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    fundamental l k n = ActualSignedDynamics.unitPulse l.2 l.1 n k := rfl

theorem normalMotion_eq_unitMotion (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    normalMotion l k n = ActualSignedDynamics.unitMotion l.2 l.1 n k := by
  funext x
  unfold normalMotion ActualSignedDynamics.unitMotion
  rw [normalScale_eq_dynamics, clockScale_eq_dynamics]
  rfl

theorem action_eq_unitAction (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    action l k n = ActualSignedDynamics.unitAction l.2 l.1 n k := by
  funext x
  unfold action ActualSignedDynamics.unitAction
  rw [clockScale_eq_dynamics]
  rfl

theorem phaseCell_slow {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hc : x ∈ phaseCell l n k) :
    (nativePoint l n k x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.1 := by
  rw [nativePoint_eq_fullCopy l n k hc.1.1]
  exact hc.1.2.1

theorem phaseCell_slot {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hc : x ∈ phaseCell l n k) :
    (nativePoint l n k x).2 ∈ (ActualPrimary.clockWindow l.1).core := by
  rw [nativePoint_eq_fullCopy l n k hc.1.1]
  exact hc.1.2.2.1

theorem phaseCell_unitTime {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hc : x ∈ phaseCell l n k) :
    (nativePoint l n k x).2.2 / (ActualPrimary.phases B N0 l.2).L l.1 ∈ Ioo (0 : ℝ) 1 := by
  simpa only [nativeTime, ActualPrimary.pulseCoordinates, ActualPrimary.length_sign] using
      phaseCell_time hc

theorem actual_unit_ode {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    along ((directions B).fastField n) (fundamental l k n) x =
      TangentProjection.projectedRhs
        ((ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n x)
        (normalMotion l k n x) (fundamental l k n x)
        (action l k n x (fundamental l k n x)) 0
        (fullStrip.epsilon n * (ActualPrimary.chartCoefficients l.2 l.1).frequency n ^ 2 *
          ‖(ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n x‖ ^ 2) := by
  rw [fundamental_eq_unitPulse, normalMotion_eq_unitMotion, action_eq_unitAction]
  exact ActualSignedDynamics.unitPulse_ode l.2 l.1 n ActualPrimaryBounds.region k
    (BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal ActualPrimaryBounds.region hx)
    (BaseContextAssembly.nativeStrip_time ActualPrimary.nominal ActualPrimaryBounds.region hx)
    (phaseCell_slow hc) (phaseCell_unitTime hc) (phaseCell_slot hc)

theorem actual_unit_action {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) :
    CurlClassBounds.complexify (action l k n x (fundamental l k n x)) =
      LinearWaveResidual.shear ((ActualPrimary.chartCoefficients l.2 l.1).radius n)
        ((ActualPrimary.chartCoefficients l.2 l.1).frequencyBase n)
        ((ActualPrimary.chartCoefficients l.2 l.1).axialBase n)
        ((directions B).radialField n) (fun y => CurlClassBounds.complexify (fundamental l k n y))
            x := by
  rw [fundamental_eq_unitPulse, action_eq_unitAction]
  exact ActualSignedDynamics.unitPulse_action l.2 l.1 n k
    (BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal ActualPrimaryBounds.region hx)
    (BaseContextAssembly.nativeStrip_time ActualPrimary.nominal ActualPrimaryBounds.region hx)

theorem actual_unit_tangent_germ {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (fun y => ⟪(ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n y,
      fundamental l k n y⟫_ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
  rw [fundamental_eq_unitPulse]
  exact ActualSignedDynamics.unitPulse_tangent_germ l.2 l.1 n ActualPrimaryBounds.region k
    (BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal ActualPrimaryBounds.region hx)
    (BaseContextAssembly.nativeStrip_time ActualPrimary.nominal ActualPrimaryBounds.region hx)
    (phaseCell_slow hc) (phaseCell_unitTime hc) (phaseCell_slot hc)

/-- A genuine ambient tangency germ for the actual signed amplitude.
It remains valid at the closed transverse and dyadic boundaries. -/
theorem raw_tangent_germ (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (fun y => normalDot ((ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B)
        n y)
      ((((parameters l).copyData ActualPrimaryBounds.strip request).raw k).amplitude n y))
      =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [actual_unit_tangent_germ hx hc] with y hy
  change normalDot _ (CurlClassBounds.complexify
    (SignedWaveUpdate.signedScalar fullStrip (matrix l k) (target l k) request (mask l k) l.2 n y •
      fundamental l k n y)) = 0
  rw [SignedWaveUpdate.normalDot_complexify, inner_smul_right, hy, mul_zero, Complex.ofReal_zero]

/-- The literal signed quotient satisfies its homogeneous principal
equation, with no global covariance-control premise. -/
theorem raw_principal_zero {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hfrozen : SignedWaveUpdate.FrozenAlong (directions B).fast request)
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (((parameters l).copyData ActualPrimaryBounds.strip request).raw k).principal
      fullStrip (directions B) n x = 0 := by
  exact NativePrincipalEquations.signed_coefficients_principal_at
    (a := fun _ : Frequency => ActualPrimary.chartCoefficients l.2 l.1)
    (dirs := fun _ : Frequency => directions B)
    (R := fun _ : Frequency => request) (v := fundamental l)
    (Ndot := normalMotion l) (A := action l)
    (covarianceAtLabel l) (fun q => (hR q).each l) (mask_local_jets.each l)
    (fundamental_local_jets.each l) l.2 n k hx hc
    (matrix_frozen l k) (target_frozen l k) hfrozen (mask_frozen l k)
    (Scaling.carrier_frequency_pos (fullStrip.epsilon_pos n)).ne'
    (actual_unit_ode hx hc) (actual_unit_action hx)

theorem fullRequest_principal_zero {β : ℝ} (s : StripData Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest s P coord c u n x q))
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (((parameters l).copyData ActualPrimaryBounds.strip
      (LocalSignedRequest.fullRequest s P coord c u)).raw k).principal fullStrip (directions B) n x
          = 0 :=
  raw_principal_zero hR (request_frozen s P coord c u) hx hc

/-- The current residuals provide every request estimate needed by the
actual homogeneous signed equation. -/
theorem actual_principal_zero (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c))
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    (((parameters l).copyData ActualPrimaryBounds.strip
      (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)).raw k).principal
        fullStrip (directions B) n x = 0 := by
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  exact fullRequest_principal_zero G.strip G.patch G.coord c u hr' hx hc

end NavierStokes.ActualSignedStageControls
