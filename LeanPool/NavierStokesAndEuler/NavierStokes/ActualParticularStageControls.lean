/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledActualParticularControl
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledParticularFrameJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularBackground
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierTransportBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScalarParticularSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.NativeCutoffJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularPaddedBackground

@[expose] public section

/-!
# Actual particular-wave data on the active label-band pairs

The reference phase and native slot are those of the existing initializer
choice.  The forced fields use the literal current harmonic residual.  Active
pair estimates do not impose polynomial clock bounds on inactive bands.
The actual source support and transported cutoff then globalize the native
estimates. The final theorems give uniform bounds for the literal common
and finite-harmonic fields from the current analytic invariant.
-/

noncomputable section

namespace NavierStokes.ActualParticularStageControls

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CorrectionState CorrectionStep CommonCoverSolve TorusInverse
open scoped ContDiff Topology BigOperators


abbrev Slow := PhaseCalculus.Slow
abbrev Parameter := PhysicalParticularWave.Parameter
abbrev Plane := TorusInverse.Plane
abbrev Native := (Parameter × ℝ) × Plane
abbrev AP := CorrectionInitialization.ActualPrimary.FullPoint
abbrev Label (B N0 : ℕ) := Fin 2 × CorrectionInitialization.ActualPrimary.Label B N0

/-! Reindexing retains the selected phase, its frame, and all uniform constants. -/

noncomputable def reindexDomain {ι κ : Type} (D : Domain ι Slow) (e : κ → ι) : Domain κ Slow where
  scale i := D.scale (e i)
  carrier i := D.carrier (e i)
  isOpen i := D.isOpen (e i)
  one_le_scale i := D.one_le_scale (e i)

noncomputable def reindexPhase {ι κ : Type} (F : PhaseFamily ι) (e : κ → ι) : PhaseFamily κ where
  epsilon i := F.epsilon (e i)
  p i := F.p (e i)
  pz i := F.pz (e i)
  x0 i := F.x0 (e i)
  theta i := F.theta (e i)
  F i := F.F (e i)
  G i := F.G (e i)

noncomputable def reindexConstruction {ι κ : Type} {D : Domain ι Slow}
    (F : PhaseConstruction D) (e : κ → ι) : PhaseConstruction (reindexDomain D e) where
  phase := reindexPhase F.phase e
  V i := F.V (e i)
  openV i := F.openV (e i)
  lam i := F.lam (e i)
  c0 i := F.c0 (e i)
  u i := F.u (e i)
  L i := F.L (e i)
  viscosity i := F.viscosity (e i)
  B i := F.B (e i)
  K i := F.K (e i)
  slope i := F.slope (e i)
  error i := F.error (e i)
  r := F.r
  b := F.b
  M := F.M
  C := F.C
  E := F.E
  r_pos := F.r_pos
  b_pos := F.b_pos
  one_le_M := F.one_le_M
  C_nonneg := F.C_nonneg
  E_nonneg := F.E_nonneg
  baseF := PrimaryGeometryAssembly.polynomial_restrict_reindex F.baseF e (fun _ => rfl) (fun _ _ h
    => h)
  baseG := PrimaryGeometryAssembly.polynomial_restrict_reindex F.baseG e (fun _ => rfl) (fun _ _ h
    => h)
  constants i := F.constants (e i)
  epsilon_ne i := F.epsilon_ne (e i)
  radius i := F.radius (e i)
  slot i := F.slot (e i)
  lam_bound i := F.lam_bound (e i)
  c0_bound i := F.c0_bound (e i)
  u_bound i := F.u_bound (e i)
  rate_bound i := F.rate_bound (e i)
  viscosity_bound i := F.viscosity_bound (e i)
  B_bound i := F.B_bound (e i)
  K_unit i := F.K_unit (e i)
  slope_bound i := F.slope_bound (e i)
  error_small i := F.error_small (e i)
  normal_close i := F.normal_close (e i)
  lam_pos i := F.lam_pos (e i)
  u_pos i := F.u_pos (e i)
  L_pos i := F.L_pos (e i)
  interval i := F.interval (e i)
  viscosity_nonneg i := F.viscosity_nonneg (e i)
  damping_error i := F.damping_error (e i)
  modal_errors i := F.modal_errors (e i)

@[simp] theorem reindex_frame {ι κ : Type} {D : Domain ι Slow}
    (F : PhaseConstruction D) (e : κ → ι) (i : κ) :
    (reindexConstruction F e).frame i = F.frame (e i) := rfl

/-! The original physical slot, Gaussian cutoff, and actual current-state data. -/

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

noncomputable def spatialLabel (l : Label B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.2) l.1

noncomputable def referenceGeometry (l : Label B N0) : Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

noncomputable def gap (l : Label B N0) (n : ℕ) : ℕ :=
  ChartScales.nativeIndex h (BaseChartJets.cellBand l.2) - CommonWindow.index h n

theorem reference_refine (l : Label B N0) (n : ℕ) :
    CopySolveCompatibility.refineGeometry (referenceGeometry l) (gap l n) =
      chartGeometry n l.1 l.2 := by
  simp only [CopySolveCompatibility.refineGeometry, referenceGeometry,
    ActualSignedGeometry.slotGeometry, CommonCoverClass.bandGeometry, Nat.zero_add,
    chartGeometry, geometry, spatialLabel, gap]
  rfl

noncomputable def referenceCutoff (l : Label B N0) (z : Plane) : ℝ :=
  (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff ((phases B N0 l.1).L l.2) z.2

theorem referenceCutoff_compact (l : Label B N0) : HasCompactSupport (referenceCutoff l) :=
  (clockWindow l.2).cutoff_compact.mul_right

noncomputable def reference (l : Label B N0) : ParticularWaveAssembly.Reference Parameter where
  band := BaseChartJets.cellBand l.2
  geometry := referenceGeometry l
  length := (phases B N0 l.1).L l.2
  length_pos := (phases B N0 l.1).L_pos l.2
  tangent j := PrimaryCopyBridge.frameTangentData
    (ActualParticularControl.nativeFrame ((phases B N0 l.1).frame l.2)
      ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap)
    j (fun _ => 0)
  cutoff := referenceCutoff l
  cutoff_compact := referenceCutoff_compact l

noncomputable def nativeToFull : Native ≃ₗᵢ[ℝ] AP :=
  ParticularWaveAssembly.angleShuffle.symm.trans (StateReindex.cylinder cycleAssoc.symm)

noncomputable def background (l : Label B N0) : LinearWaveBounds.WaveCoefficients Native :=
  ParticularWaveBounds.reindexCoefficients nativeToFull (chartCoefficients l.1 l.2)

noncomputable def directions : LinearWaveBounds.GraphDirections Native :=
  ParticularWaveBounds.reindexDirections nativeToFull (PrimaryResidualClass.directions
    (commonContext B))

noncomputable def associatedContext : Context (Parameter × Plane) :=
  StateReindex.context cycleAssoc.symm (commonContext B)

noncomputable def associatedStrip : StripData (Parameter × Plane) :=
  ParticularWaveBounds.reindexStrip cycleAssoc.symm (BaseContextAssembly.nativeStrip nominal
    standardRegion)

noncomputable def assembly (x : CycleState (Label B N0)) (l : Label B N0) :
    ParticularWaveAssembly.AssemblyData Parameter where
  reference := reference l
  charts := {
    parameter n := PhysicalParticularWave.parameterChange h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
    gap := gap l
    amplitude n := PhysicalParticularWave.velocityWeight h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) }
  context := associatedContext (B := B)
  state := StateReindex.state cycleAssoc.symm x.state
  carrierBlock := StateReindex.block cycleAssoc.symm (x.coefficients.blocks l)
  gaussianInput := StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l)
  aliasInput := StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)
  background := background l
  copy := fun _ => 0
  strip := ParticularParameters.nativeStrip associatedStrip
  directions := directions (B := B)

noncomputable def parameters (x : CycleState (Label B N0)) (l : Label B N0) :
    ParticularParameters Parameter :=
  ParticularParameters.fromReference (assembly x l) h (gap l)

theorem parameters_source (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    ((parameters x l).copyData (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j).source =
      ParticularWaveAssembly.sourceFamily (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j := rfl

theorem parameters_length (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    (parameters x l).length n = (phases B N0 l.1).L l.2 /
      PhysicalParticularWave.clockWeight h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) := rfl

/-- Fixed primitive data for all iterations of the same labeled construction. -/
noncomputable def canonicalParameters (l : Label B N0) : ParticularParameters Parameter where
  tangent j n := ScaledTangentTransport.transportTangent ((reference l).tangent j)
    (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (gap l n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (reference l).band)
      ((j:ℝ)*ChartScales.carrier h n) ((j:ℝ)*ChartScales.carrier h (reference l).band))
  geometry n := CopySolveCompatibility.transportGeometry (reference l).geometry (gap l n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n)
      (ChartScales.Q_pos (reference l).band) _).ne'
  length n := (reference l).length /
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band)
  length_pos n := div_pos (reference l).length_pos
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n)
      (ChartScales.Q_pos (reference l).band) _)
  cutoff n := (reference l).cutoff ∘ CopySolveCompatibility.nativeTimeMap 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
  background := background l
  directions := directions (B := B)

theorem parameters_eq_canonical (x : CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n) :
    parameters x l = canonicalParameters l := by
  have he : (assembly x l).carrierBlock.frequency = fun n => (ChartScales.carrier h n : ℝ) :=
    funext hfrequency
  dsimp only [parameters, canonicalParameters, ParticularParameters.fromReference,
    PhysicalParticularWave.referenceFrequency]
  rw [he]
  rfl

/-! The sign combination is proved before specializing the constructed profile. -/

noncomputable def signedPhase {ι : Type} {D : Domain ι Slow}
    (F : Fin 2 → PhaseConstruction D) : PhaseFamily (Fin 2 × ι) where
  epsilon l := (F l.1).phase.epsilon l.2
  p l := (F l.1).phase.p l.2
  pz l := (F l.1).phase.pz l.2
  x0 l := (F l.1).phase.x0 l.2
  theta l := (F l.1).phase.theta l.2
  F l := (F l.1).phase.F l.2
  G l := (F l.1).phase.G l.2

noncomputable def signedConstruction {ι : Type} {D : Domain ι Slow}
    (F : Fin 2 → PhaseConstruction D)
    (hr : ∀ j, (F j).r = (F 0).r) (hb : ∀ j, (F j).b = (F 0).b)
    (hM : ∀ j, (F j).M = (F 0).M) (hC : ∀ j, (F j).C = (F 0).C)
    (hE : ∀ j, (F j).E = (F 0).E)
    (hF : ∀ j, (F j).phase.F = (F 0).phase.F)
    (hG : ∀ j, (F j).phase.G = (F 0).phase.G) :
    PhaseConstruction (reindexDomain D (Prod.snd : Fin 2 × ι → ι)) where
  phase := signedPhase F
  V l := (F l.1).V l.2
  openV l := (F l.1).openV l.2
  lam l := (F l.1).lam l.2
  c0 l := (F l.1).c0 l.2
  u l := (F l.1).u l.2
  L l := (F l.1).L l.2
  viscosity l := (F l.1).viscosity l.2
  B l := (F l.1).B l.2
  K l := (F l.1).K l.2
  slope l := (F l.1).slope l.2
  error l := (F l.1).error l.2
  r := (F 0).r
  b := (F 0).b
  M := (F 0).M
  C := (F 0).C
  E := (F 0).E
  r_pos := (F 0).r_pos
  b_pos := (F 0).b_pos
  one_le_M := (F 0).one_le_M
  C_nonneg := (F 0).C_nonneg
  E_nonneg := (F 0).E_nonneg
  baseF := by
    have he : (signedPhase F).F = fun l => (F 0).phase.F l.2 := by
      funext l
      exact congrFun (hF l.1) l.2
    rw [he]
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (F 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ h => h)
  baseG := by
    have he : (signedPhase F).G = fun l => (F 0).phase.G l.2 := by
      funext l
      exact congrFun (hG l.1) l.2
    rw [he]
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (F 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ h => h)
  constants l := by
    have h := (F l.1).constants l.2
    simp only [hM] at h
    exact h
  epsilon_ne l := (F l.1).epsilon_ne l.2
  radius l := by
    have h := (F l.1).radius l.2
    simp only [hr, hM] at h
    exact h
  slot l := by
    have h := (F l.1).slot l.2
    simp only [hM] at h
    exact h
  lam_bound l := by simpa only [hM] using (F l.1).lam_bound l.2
  c0_bound l := by simpa only [hb, hM] using (F l.1).c0_bound l.2
  u_bound l := by simpa only [hM] using (F l.1).u_bound l.2
  rate_bound l := by
    have h := (F l.1).rate_bound l.2
    simp only [hM] at h
    exact h
  viscosity_bound l := by simpa only [hM] using (F l.1).viscosity_bound l.2
  B_bound l := by simpa only [hb, hM] using (F l.1).B_bound l.2
  K_unit l := (F l.1).K_unit l.2
  slope_bound l := by
    have h := (F l.1).slope_bound l.2
    simp only [hM] at h
    exact h
  error_small l := (F l.1).error_small l.2
  normal_close l := (F l.1).normal_close l.2
  lam_pos l := (F l.1).lam_pos l.2
  u_pos l := (F l.1).u_pos l.2
  L_pos l := (F l.1).L_pos l.2
  interval l := (F l.1).interval l.2
  viscosity_nonneg l := (F l.1).viscosity_nonneg l.2
  damping_error l := by
    have h := (F l.1).damping_error l.2
    simp only [hE] at h
    exact h
  modal_errors l := by
    have h := (F l.1).modal_errors l.2
    simp only [hC] at h
    exact h

noncomputable def jointDomain : Domain (Label B N0) Slow :=
  reindexDomain (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N) Prod.snd

noncomputable def jointPhase : PhaseFamily (Label B N0) := signedPhase (phases B N0)

theorem phase_common_bounds (j : Fin 2) :
    (phases B N0 j).r = (phases B N0 0).r ∧
    (phases B N0 j).b = (phases B N0 0).b ∧
    (phases B N0 j).M = (phases B N0 0).M ∧
    (phases B N0 j).C = (phases B N0 0).C ∧
    (phases B N0 j).E = (phases B N0 0).E :=
  PrimaryGeometryAssembly.common_bounds certificate modulation (choice B N0).prepared
    slots.radius_pos j 0

theorem phase_frequency_eq (j : Fin 2) : (phases B N0 j).phase.F = (phases B N0 0).phase.F := by
  funext L
  exact (PrimaryGeometryAssembly.construction_frequency certificate modulation
    (choice B N0).prepared slots.radius_pos j L).trans
    (PrimaryGeometryAssembly.construction_frequency certificate modulation
      (choice B N0).prepared slots.radius_pos 0 L).symm

theorem phase_axial_eq (j : Fin 2) : (phases B N0 j).phase.G = (phases B N0 0).phase.G := by
  funext L
  exact (PrimaryGeometryAssembly.construction_axial certificate modulation
    (choice B N0).prepared slots.radius_pos j L).trans
    (PrimaryGeometryAssembly.construction_axial certificate modulation
      (choice B N0).prepared slots.radius_pos 0 L).symm

noncomputable def jointConstruction : PhaseConstruction (jointDomain (B := B) (N0 := N0)) :=
  signedConstruction (phases B N0)
    (fun j => (phase_common_bounds j).1)
    (fun j => (phase_common_bounds j).2.1)
    (fun j => (phase_common_bounds j).2.2.1)
    (fun j => (phase_common_bounds j).2.2.2.1)
    (fun j => (phase_common_bounds j).2.2.2.2)
    phase_frequency_eq phase_axial_eq

@[simp] theorem joint_frame (l : Label B N0) :
    (jointConstruction (B := B) (N0 := N0)).frame l = (phases B N0 l.1).frame l.2 := rfl

/-! Changing the native clock preserves the same grouped Gaussian exactly. -/

theorem copyEnvelope_time (g : Geometry) (r L rate : ℝ) (hrate : 0 < rate)
    (W : ℝ → ℝ) (Y : Plane) :
    WaveEnvelopeTransport.copyEnvelope (CopySolveCompatibility.timeGeometry g 0 rate hrate.ne')
      r (L / rate) (fun t => W (rate*t)) Y =
      WaveEnvelopeTransport.copyEnvelope g r L W Y := by
  classical
  apply tsum_congr
  intro k
  have he := CopySolveCompatibility.coordinates_timeGeometry g 0 rate hrate.ne' k Y
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [CopySolveCompatibility.nativeTimeMap, zero_add] at h1 h2
  have hm : (CopySolveCompatibility.timeGeometry g 0 rate hrate.ne').coordinates k Y ∈
      WaveEnvelopeTransport.rectangle r (L/rate) ↔
      g.coordinates k Y ∈ WaveEnvelopeTransport.rectangle r L := by
    change (_ ∈ Icc (-r) r ∧ 0 ≤ _ ∧ _ ≤ L/rate) ↔
      (_ ∈ Icc (-r) r ∧ 0 ≤ _ ∧ _ ≤ L)
    rw [h1, ← h2]
    constructor
    · rintro ⟨hu, h0, hL⟩
      exact ⟨hu, mul_nonneg hrate.le h0, by
        simpa only [mul_comm] using (le_div_iff₀ hrate).mp hL⟩
    · rintro ⟨hu, h0, hL⟩
      exact ⟨hu, (mul_nonneg_iff_of_pos_left hrate).mp h0,
        (le_div_iff₀ hrate).mpr (by simpa only [mul_comm] using hL)⟩
  change (if _ then W _ else 0) = (if _ then W _ else 0)
  simp only [hm, h2]

theorem copyEnvelope_transport (g : Geometry) (gap : ℕ) (r L rate : ℝ)
    (hrate : 0 < rate) (W : ℝ → ℝ) (Y : Plane) :
    WaveEnvelopeTransport.copyEnvelope
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne')
      r (L/rate) (fun t => W (rate*t)) Y =
    WaveEnvelopeTransport.copyEnvelope (CopySolveCompatibility.refineGeometry g gap) r L W Y :=
  copyEnvelope_time (CopySolveCompatibility.refineGeometry g gap) r L rate hrate W Y

/-! The slow/fast association keeps the full moving weight unchanged. -/

noncomputable def slowInsert : Parameter →L[ℝ] CyclePoint where
  toFun p := (p.1,(p.2,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)

noncomputable def slowStrip : StripData Parameter :=
  HarmonicWaveInteraction.pullbackStrip (BaseContextAssembly.nativeStrip nominal standardRegion)
    slowInsert

theorem sourceStrip_eq : CommonCoverClass.sourceStrip slowStrip = associatedStrip := by
  rfl

theorem nativeStrip_eq :
    CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip) =
      ParticularParameters.nativeStrip associatedStrip := by
  rfl

noncomputable def pulseEnvelope (l : Label B N0) : ℝ → ℝ :=
  PrimaryPulseBounds.referenceP ((phases B N0 l.1).lam l.2) ((phases B N0 l.1).u l.2)
    ((phases B N0 l.1).L l.2)

noncomputable def envelope (l : Label B N0) (n : ℕ) (z : Parameter × Plane) : ℝ :=
  WaveEnvelopeTransport.copyEnvelope (chartGeometry n l.1 l.2) slots.radius
    ((phases B N0 l.1).L l.2) (pulseEnvelope l) z.2

noncomputable def meanEnvelope (l : Label B N0) (n : ℕ) (z : CyclePoint) : ℝ :=
  envelope l n (cycleAssoc z)

noncomputable def nativeEnvelope (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  envelope l n (z.1.1,z.2)

theorem envelope_nonneg (l : Label B N0) (n : ℕ) (z : Parameter × Plane) : 0 ≤ envelope l n z :=
  WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _
    (fun t => (PrimaryPulseBounds.referenceP_pos _ _ _ t).le) _

noncomputable def Active (l : Label B N0) (n : ℕ) : Prop :=
  1 ≤ n ∧ BaseChartJets.cellBand l.2 ∈ CommonWindow.levels n

abbrev ActivePair (B N0 : ℕ) := {i : Label B N0 × ℕ // Active i.1 i.2}

section Selected

variable (e : ℕ → ActivePair B N0)

noncomputable def selectedLabel (n : ℕ) : Label B N0 := (e n).val.1

noncomputable def selectedBand (n : ℕ) : ℕ := (e n).val.2

noncomputable def selectedConstruction :=
  reindexConstruction (jointConstruction (B := B) (N0 := N0))
    (fun i : Unit × ℕ => selectedLabel e i.2)

noncomputable def selectedStrip : StripData Parameter :=
  UniformPrimaryWeights.reindexedStrip slowStrip (fun n => (selectedBand e n, ()))

noncomputable def selectedSlot (_ : Unit) (n : ℕ) : SlotColoring.Label :=
  spatialLabel (selectedLabel e n)

theorem selected_near (u : Unit) (n : ℕ) :
    selectedBand e n ≤ (selectedSlot e u n).1 + 4 ∧
      (selectedSlot e u n).1 ≤ selectedBand e n + 4 :=
  CommonWindow.distance (e n).property.2

noncomputable def selectedClock :=
  ActualSignedGeometry.clockScale (selectedBand e) (fun u n => (selectedSlot e u n).1)
    (selected_near e) h

noncomputable def selectedNormal :=
  ActualSignedGeometry.normalScale (selectedBand e) (fun u n => (selectedSlot e u n).1)
    (selected_near e) outgoing.data.h_pos.le

noncomputable def selectedGap (_ : Unit) (n : ℕ) : ℕ := gap (selectedLabel e n) (selectedBand e n)

noncomputable def selectedGeometry :=
  ScaledActualParticularControl.geometry
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (selectedClock e)

noncomputable def selectedLength :=
  ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e)

noncomputable def selectedPulseEnvelope :=
  ScaledActualParticularControl.envelope (selectedConstruction e) (selectedClock e)

theorem selected_geometry_eq (x : CycleState (Label B N0)) (n : ℕ) :
    selectedGeometry e () n = (parameters x (selectedLabel e n)).geometry (selectedBand e n) := rfl

theorem selected_length_eq (x : CycleState (Label B N0)) (n : ℕ) :
    selectedLength e () n = (parameters x (selectedLabel e n)).length (selectedBand e n) := rfl

theorem selected_gap_bound (u : Unit) (n : ℕ) :
    selectedGap e u n ≤ CommonWindow.gap h + SlotColoring.nativeGap h :=
  ActualSignedGeometry.common_native_gap outgoing.data.h_pos.le
    (CommonWindow.indexBounds h outgoing.data.h_pos.le)
    (e n).property.1 (by
      have := ((choice B N0).prepared.large _ (selectedLabel e n).2.property).four_le
      exact le_trans (by norm_num) this)
    (selected_near e u n).1 (selected_near e u n).2

theorem selected_slot_large (u : Unit) (n : ℕ) : 4 ≤ (selectedSlot e u n).1 :=
  ((choice B N0).prepared.large _ (selectedLabel e n).2.property).four_le

theorem selected_scale (i : Unit × ℕ) :
    (reindexDomain (jointDomain (B := B) (N0 := N0))
      (fun z : Unit × ℕ => selectedLabel e z.2)).scale i =
      ChartScales.S (selectedSlot e i.1 i.2).1 := rfl

theorem selected_length (i : Unit × ℕ) :
    (selectedConstruction e).L i = ChartScales.slotLength slots.radius h (selectedSlot e i.1 i.2).1
      := rfl

theorem selected_envelope_eq (n : ℕ) (z : Parameter × Plane) :
    ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
      (selectedLength e) (selectedPulseEnvelope e) () n z =
      envelope (selectedLabel e n) (selectedBand e n) z := by
  have he := copyEnvelope_transport (referenceGeometry (selectedLabel e n)) (selectedGap e () n)
    slots.radius ((selectedConstruction e).L ((),n)) ((selectedClock e).value () n)
    ((selectedClock e).value_pos () n) (pulseEnvelope (selectedLabel e n)) z.2
  rw [show selectedGap e () n = gap (selectedLabel e n) (selectedBand e n) from rfl,
    reference_refine] at he
  exact he

end Selected

/-! The input class is exactly the residual component of the cycle invariant. -/

theorem select_uniform {ι X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData X} {w : ι → ℕ → X → ℝ} {f : ι → ℕ → X → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass s w α f) (e : ℕ → ι × ℕ) :
    LabelSumBounds.UniformClass (UniformPrimaryWeights.reindexedStrip s (fun n => ((e n).2, ())))
      (fun (_ : Unit) n => w (e n).1 (e n).2) α (fun (_ : Unit) n => f (e n).1 (e n).2) := by
  refine ⟨fun _ n => hf.weight_nonneg (e n).1 (e n).2,
    fun _ n => hf.smooth (e n).1 (e n).2, ?_⟩
  intro m
  obtain ⟨C,hC,p,hp⟩ := hf.bounds m
  exact ⟨C,hC,p,fun _ n => hp (e n).1 (e n).2⟩

theorem associated_residual_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
      (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
          l))) :
    UniformHarmonicInteraction.UniformVelocity associatedStrip envelope α
      (fun l => HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput) := by
  exact MeanBoundsReindex.residualBlock_uniform_pull cycleAssoc.symm (commonContext B) x.state
    x.coefficients.blocks x.coefficients.gaussian x.coefficients.aliasCoefficients H

noncomputable def currentSource (x : CycleState (Label B N0)) (j : ℤ)
    (l : Label B N0) : ℕ → Native → HarmonicCalculus.ComplexVector :=
  ParticularWaveAssembly.sourceFamily (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

theorem current_source_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
      (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)))
    (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass (CommonCoverClass.sourceStrip
      (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j) := by
  have hs := ActualParticularControl.residualSource_uniform associatedStrip envelope α
    (associatedContext (B := B)) (StateReindex.state cycleAssoc.symm x.state)
    (fun l => (assembly x l).carrierBlock) (fun l => (assembly x l).gaussianInput)
    (fun l => (assembly x l).aliasInput) (fun _ => j)
    (fun i => associated_residual_class x H i j hj)
  have ht := ActualParticularControl.uniform_parameter_pull hs
    (ActualParticularControl.forgetAngle (P := Parameter))
  have he : CommonCoverClass.parameterStrip associatedStrip
      (ActualParticularControl.forgetAngle (P := Parameter)) =
      CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip) := rfl
  rw [he] at ht
  exact ht

theorem invariant_current_source_class (x : CycleState (Label B N0))
    {G : SignedMeanGain.Geometry} {primary : Label B N0 → HarmonicBlock CyclePoint} {σ : ℝ}
    {labelCarrier : Label B N0 → ℕ → Set CyclePoint}
    (H : CycleAnalyticInvariant G (commonContext B) primary meanEnvelope labelCarrier σ x)
    (hstrip : G.strip = BaseContextAssembly.nativeStrip nominal standardRegion)
    (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass (CommonCoverClass.sourceStrip
      (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope (1/2+σ) (currentSource x j) := by
  apply current_source_class x _ j hj
  simpa only [hstrip] using H.residual

theorem source_angle_reindex (s : StripData Parameter) (index : ℕ → ℕ) :
    CommonCoverClass.sourceStrip
      (ActualParticularControl.angleStrip
        (UniformPrimaryWeights.reindexedStrip s (fun n => (index n, ())))) =
    UniformPrimaryWeights.reindexedStrip
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun n => (index n, ())) := rfl

theorem selected_source_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) (e : ℕ → ActivePair B N0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
        (selectedLength e) (selectedPulseEnvelope e)) α
      (fun (_ : Unit) n => currentSource x j (selectedLabel e n) (selectedBand e n)) := by
  rw [show CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)) =
    UniformPrimaryWeights.reindexedStrip
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n => (selectedBand e n, ())) from source_angle_reindex slowStrip (selectedBand e)]
  have hw : ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
      (selectedLength e) (selectedPulseEnvelope e) =
      (fun (_ : Unit) n (z : Native) => nativeEnvelope (selectedLabel e n) (selectedBand e n) z) :=
        by
    funext u n z
    exact selected_envelope_eq e n (z.1.1,z.2)
  rw [hw]
  exact select_uniform H (fun n => (e n).val)

section ModalConstruction

variable (e : ℕ → ActivePair B N0)

noncomputable def selectedPhi := ScaledActualParticularControl.physicalPhi h
  (selectedBand e) (fun u n => (selectedSlot e u n).1)

noncomputable def selectedChi : (Parameter × ℝ) →L[ℝ] Slow :=
  ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ Parameter ℝ)

noncomputable def selectedFrame (n : ℕ) : PrimaryODE.FrameData ((Parameter × ℝ) × ℝ) :=
  ActualParticularControl.nativeFrame
    (ScaledActualParticularControl.frame (selectedConstruction e) (selectedPhi e)
      (selectedClock e) (selectedNormal e) ((),n)) selectedChi

noncomputable def selectedPatch : Unit → ℕ → Frequency → Set Native :=
  ScaledActualParticularControl.patch (ActualParticularControl.angleStrip (selectedStrip e))
    (selectedConstruction e) selectedChi (selectedPhi e) (selectedClock e) (selectedGeometry e)
    (fun _ _ => slots.radius)

theorem selected_scale_le (i : Unit × ℕ) :
    (reindexDomain (jointDomain (B := B) (N0 := N0))
      (fun z : Unit × ℕ => selectedLabel e z.2)).scale i ≤ 25*(selectedStrip e).slow i.2 := by
  rw [selected_scale]
  exact ScaledActualParticularControl.active_scale_bound (selectedStrip e)
    (selectedBand e) (fun u n => (selectedSlot e u n).1) (fun n => (e n).property.1)
    (selected_near e) (fun n => le_max_right _ _) i.1 i.2

theorem selected_geometry_bound (u : Unit) (n : ℕ) :
    CommonCoverClass.argumentCost (selectedGeometry e u n) ≤
      ScaledActualParticularControl.slotCost vectors_det (selectedClock e)
        (CommonWindow.gap h + SlotColoring.nativeGap h) * (selectedStrip e).slow n^2 :=
  ScaledActualParticularControl.slot_geometry_cost slots vectors_det (selectedSlot e)
    (selectedStrip e) outgoing.data.h_pos.le (selectedClock e) (selectedGap e)
    (CommonWindow.gap h + SlotColoring.nativeGap h) (selected_gap_bound e)
    (selected_slot_large e) (fun u n => selected_scale_le e (u,n)) u n

/-- The real or imaginary control is constructed from the selected phase,
the exact clock and slot geometry, and the current residual class. -/
noncomputable def selectedControl (x : CycleState (Label B N0)) {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :=
  ScaledActualParticularControl.scaledControl
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e)
    selectedChi (selectedPhi e) (selectedClock e) (selectedNormal e)
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (fun _ _ => slots.radius)
    (ActualSignedGeometry.slowChangeCost_one h) (by norm_num : (1:ℝ) ≤ 25)
    (ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h))
    (ScaledActualParticularControl.physicalPhi_bound h (selectedBand e)
      (fun u n => (selectedSlot e u n).1) (selected_near e))
    (selected_scale_le e)
    (fun u n => by
      rw [selected_length]
      exact ActualSignedGeometry.slotGeometry_separated slots vectors_det
        outgoing.data.h_pos.le (selected_slot_large e u n) 0)
    (selected_geometry_bound e) j hj
    (fun (_ : Unit) n z => part (currentSource x j (selectedLabel e n) (selectedBand e n) z))
    ((selected_source_class x H e).map part)

theorem selected_tangent_eq (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (f : Native → ProblemStatement.Space) :
    ScaledActualParticularControl.withSource
      ((parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n)) f =
      PrimaryCopyBridge.frameTangentData (selectedFrame e n) j f := by
  have he := ScaledActualParticularControl.angle_transport_withSource
    ((selectedConstruction e).frame ((),n))
    ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
    (selectedPhi e ((),n))
    (ScaledActualParticularControl.physicalPsi h (selectedBand e)
      (fun u q => (selectedSlot e u q).1) ((),n))
    (ScaledActualParticularControl.physical_commute h (selectedBand e)
      (fun u q => (selectedSlot e u q).1) ((),n))
    (fun _ => 0) f j (selectedGap e () n) ((selectedClock e).value () n)
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q (selectedBand e n))
      (ChartScales.Q (selectedSlot e () n).1)) ((selectedNormal e).value () n)
  have ht := ScaledActualParticularControl.actualSlot_tangent_eq (selectedSlot e)
    (selectedConstruction e) outgoing.data.h_pos.le (selectedBand e) (selected_near e)
    (fun _ _ _ => 0) (selectedGap e) j hj () n
  have ha : (parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n) =
      ScaledActualParticularControl.transportedTangent (selectedConstruction e)
        ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
        (ScaledActualParticularControl.physicalPsi h (selectedBand e)
          (fun u q => (selectedSlot e u q).1)) (selectedClock e) (selectedNormal e)
        (fun _ _ _ => 0) (selectedGap e)
        (fun u q => PhysicalParticularWave.velocityWeight h (ChartScales.Q (selectedBand e q))
          (ChartScales.Q (selectedSlot e u q).1)) j () n := by
    dsimp only [selectedClock, selectedNormal]
    rw [ht]
    dsimp only [parameters, ParticularParameters.nativeTangent, ParticularParameters.fromReference,
      assembly, reference, PhysicalParticularWave.referenceFrequency, StateReindex.block]
    rw [hfrequency, hfrequency]
    rfl
  rw [ha]
  exact he

noncomputable def selectedSource (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) (n : ℕ) :=
  currentSource x j (selectedLabel e n) (selectedBand e n)

noncomputable def selectedTangent (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) (n : ℕ) :=
  (parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n)

noncomputable def selectedBackground (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) :=
  ParticularCopyBounds.reindexedBase
    (fun l => ((parameters x l).copyData (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput
        j).background)
    (fun n => (selectedBand e n, selectedLabel e n))

/-- This is the control of the literal selected `fromReference` tangent,
after its source is overwritten by the corresponding part of the current HR source. -/
noncomputable def selectedActualControl (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :
    ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) α
      (fun (_ : Unit) n => selectedFrame e n)
      (fun u n => ScaledActualParticularControl.withSource (selectedTangent e x j u n)
        (fun z => part (selectedSource e x j u n z)))
      j (selectedGeometry e) (selectedLength e) (selectedPulseEnvelope e) (selectedPatch e) := by
  have he : (fun u n => ScaledActualParticularControl.withSource (selectedTangent e x j u n)
      (fun z => part (selectedSource e x j u n z))) =
      (fun (_ : Unit) n => PrimaryCopyBridge.frameTangentData (selectedFrame e n) j
        (fun z => part (selectedSource e x j () n z))) := by
    funext u n
    exact selected_tangent_eq e x hfrequency j hj n _
  rw [he]
  exact selectedControl e x j hj H part

theorem selected_inverse_frequency (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) :
    UniformPrimaryWeights.UniformBandBound
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) (1/2)
      (fun u n => 1 / (selectedBackground e x j u).frequency n) := by
  have hb := UniformPrimaryWeights.harmonic_inverse_bandBound
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
    (fun (_ : Unit) _ => j) (fun _ _ => hj)
  have he (u : Unit) (n : ℕ) : (selectedBackground e x j u).frequency n =
      (j:ℝ) * CurlClassBounds.carrierFrequency
        (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) n :=
          by
    change (j:ℝ) * (x.coefficients.blocks (selectedLabel e n)).frequency (selectedBand e n) = _
    rw [hfrequency]
    rfl
  simpa only [he, mul_comm] using hb

end ModalConstruction

theorem uniform_to_local {ι I X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData X} {w : ι → ℕ → X → ℝ} {f : ι → ℕ → X → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass s w α f) (C : ι → ℕ → I → Set X) :
    PeriodizedWaveBounds.UniformLocalJets s w α C (fun l n _ => f l n) := by
  refine ⟨fun l n _ z hz _ => (hf.smooth l n).contDiffAt (s.isOpen_domain.mem_nhds hz), ?_⟩
  intro m
  obtain ⟨K,hK,p,hp⟩ := hf.bounds m
  exact ⟨K,hK,p,fun l n _ z hz _ => hp l n z hz⟩

/-- The actual computed copy data, with the current residual as source. -/
noncomputable def data (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :=
  (parameters x l).copyData (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

/-- The active phase patch includes the transverse boundary. Its time
coordinate is the actual transported clock. -/
noncomputable def controlPatch (l : Label B N0) (n : ℕ) (k : Frequency) : Set Native :=
  {z | Active l n ∧
    (z.1.1 ∈ slowStrip.domain ∧
      ActualSignedGeometry.slowChange h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2))
        (ActualSignedGeometry.swapParameter z.1.1) ∈ jointDomain.carrier l ∧
      (((canonicalParameters l).geometry n).coordinates k z.2).2 ∈
        Ioo 0 ((canonicalParameters l).length n)) ∧
    (((canonicalParameters l).geometry n).coordinates k z.2).1 ∈
      Icc (-slots.radius) slots.radius}

theorem selected_controlPatch (e : ℕ → ActivePair B N0) (u : Unit) (q : ℕ) (k : Frequency) :
    controlPatch (selectedLabel e q) (selectedBand e q) k = selectedPatch e u q k := by
  ext z
  change (Active (selectedLabel e q) (selectedBand e q) ∧ _) ↔ _
  have ha : Active (selectedLabel e q) (selectedBand e q) := (e q).property
  rw [and_iff_right ha]
  rfl

theorem selected_data_amplitude (e : ℕ → ActivePair B N0)
    (x : CycleState (Label B N0)) (j : ℤ) (u : Unit) (q : ℕ) (k : Frequency) :
    (data x (selectedLabel e q) j).amplitude (selectedBand e q) k =
      (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).amplitude q := rfl

theorem selected_data_pressure (e : ℕ → ActivePair B N0)
    (x : CycleState (Label B N0)) (j : ℤ) (u : Unit) (q : ℕ) (k : Frequency) :
    (data x (selectedLabel e q) j).pressure (selectedBand e q) k =
      (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).pressure q := rfl

section RawSelected

variable (e : ℕ → ActivePair B N0)

noncomputable def selectedWeight : Unit → ℕ → Native → ℝ :=
  ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
    (selectedLength e) (selectedPulseEnvelope e)

theorem selectedWeight_nonneg (u : Unit) (n : ℕ) (z : Native) : 0 ≤ selectedWeight e u n z := by
  change 0 ≤ WaveEnvelopeTransport.copyEnvelope (selectedGeometry e u n) slots.radius
    (selectedLength e u n) (selectedPulseEnvelope e u n) z.2
  exact WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _
    (fun t => (PrimaryPulseBounds.referenceP_pos ((selectedConstruction e).lam (u,n))
      ((selectedConstruction e).u (u,n)) ((selectedConstruction e).L (u,n))
      ((selectedClock e).value u n*t)).le) _

theorem selectedWeight_eq (u : Unit) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ selectedPatch e u n k) :
    selectedWeight e u n z = selectedPulseEnvelope e u n ((selectedGeometry e u n).coordinates k
      z.2).2 :=
  ScaledActualParticularControl.patch_envelope
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e)
    selectedChi (selectedPhi e) (selectedClock e)
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (fun _ _ => slots.radius)
    (fun u n => by
      rw [selected_length]
      exact ActualSignedGeometry.slotGeometry_separated slots vectors_det
        outgoing.data.h_pos.le (selected_slot_large e u n) 0) hz

theorem selected_raw_jets (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun u n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip (selectedStrip e))).zeta z) * selectedWeight e u n z)
      α (selectedPatch e)
      (fun u n k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).amplitude n) ∧
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun u n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip (selectedStrip e))).zeta z) * selectedWeight e u n z)
      (α+1/2) (selectedPatch e)
      (fun u n k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).pressure n) := by
  let f := fun u n z => ParticularWaveBounds.realPart (selectedSource e x j u n z)
  have he : ScaledParticularFrameJets.tangent (selectedConstruction e) selectedChi
      (selectedPhi e) (selectedClock e) (selectedNormal e) f j =
      fun u n => ParticularWaveBounds.realData (selectedTangent e x j u n) (selectedSource e x j u
        n) := by
    funext u n
    exact (selected_tangent_eq e x hfrequency j hj n _).symm
  have hgeo := ScaledParticularFrameJets.native_geometry_jets
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e) selectedChi
    (selectedPhi e) (selectedClock e) (selectedNormal e) (selectedGeometry e) (fun _ _ =>
      slots.radius)
    f j (ActualSignedGeometry.slowChangeCost_one h) (by norm_num : (1:ℝ) ≤ 25)
    (ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h))
    (ScaledActualParticularControl.physicalPhi_bound h (selectedBand e)
      (fun u n => (selectedSlot e u n).1) (selected_near e))
    (selected_scale_le e) (selected_geometry_bound e)
  rw [he] at hgeo
  have hrange (u n k z) (hz : z ∈ selectedPatch e u n k) :=
    ScaledParticularFrameJets.native_normal_bounds
      (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e) selectedChi
      (selectedPhi e) (selectedClock e) (selectedNormal e) (selectedGeometry e) (fun _ _ =>
        slots.radius)
      f j hz
  simp only [he] at hrange
  exact ParticularCopyBounds.uniform_coefficients_jets
    (selectedBackground e x j) (selectedTangent e x j) (selectedSource e x j)
    (selectedGeometry e) (selectedLength e)
    (fun u n => ScaledActualParticularControl.length_pos (selectedConstruction e) (selectedClock e)
      u n)
    (selectedPulseEnvelope e) (selectedWeight e) (fun (_ : Unit) n => selectedFrame e n) j
      (selectedPatch e)
    (selectedActualControl e x hfrequency j hj H ParticularWaveBounds.realPart)
    (selectedActualControl e x hfrequency j hj H ParticularWaveBounds.imagPart)
    (fun u n z _ => selectedWeight_nonneg e u n z)
    (fun u n k z _ hz => (selectedWeight_eq e u n k hz).ge)
    hgeo.1 hgeo.2.1 hgeo.2.2
    (uniform_to_local (selected_source_class x H e) (selectedPatch e))
    (ScaledParticularFrameJets.normal_lower_pos (selectedConstruction e) (selectedNormal e))
    (fun u n k z _ hz => (hrange u n k z hz).1)
    (fun u n k z _ hz => (hrange u n k z hz).2)
    (selected_inverse_frequency e x hfrequency j hj)

end RawSelected

/-- The selector is only an indexing device. Both actual raw fields have
one bound before the original spatial label, active band, and lattice copy. -/
theorem raw_jets (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun l n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z) * nativeEnvelope l n z)
      α controlPatch (fun l => (data x l j).amplitude) ∧
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun l n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z) * nativeEnvelope l n z)
      (α+1/2) controlPatch (fun l => (data x l j).pressure) := by
  classical
  by_cases hne : Nonempty (ActivePair B N0)
  · let : Nonempty (ActivePair B N0) := hne
    let e : ℕ → ActivePair B N0 := Classical.choose (exists_surjective_nat (ActivePair B N0))
    have he : Surjective e := Classical.choose_spec (exists_surjective_nat (ActivePair B N0))
    have hs := selected_raw_jets e x hfrequency j hj H
    have hp : (fun (_ : Unit) q k => controlPatch (selectedLabel e q) (selectedBand e q) k) =
        selectedPatch e := by
      funext u q k
      exact selected_controlPatch e u q k
    have hw : selectedWeight e =
        (fun (_ : Unit) q (z : Native) => nativeEnvelope (selectedLabel e q) (selectedBand e q) z)
          := by
      funext u q z
      exact selected_envelope_eq e q (z.1.1,z.2)
    have hstrip : CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip
      e)) =
        UniformPrimaryWeights.reindexedStrip
          (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
          (fun q => (selectedBand e q, ())) := source_angle_reindex slowStrip (selectedBand e)
    have ha : (fun (_ : Unit) q k => (data x (selectedLabel e q) j).amplitude (selectedBand e q) k)
      =
        (fun u q k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
          (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
          (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
            (selectedConstruction e) (selectedClock e) u n)).amplitude q) := by
      funext u q k
      exact selected_data_amplitude e x j u q k
    have hb : (fun (_ : Unit) q k => (data x (selectedLabel e q) j).pressure (selectedBand e q) k) =
        (fun u q k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
          (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
          (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
            (selectedConstruction e) (selectedClock e) u n)).pressure q) := by
      funext u q k
      exact selected_data_pressure e x j u q k
    rw [hstrip, hw, ← hp, ← ha, ← hb] at hs
    exact ⟨ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
      (fun _ _ _ _ _ hcell => hcell.1) hs.1,
      ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
        (fun _ _ _ _ _ hcell => hcell.1) hs.2⟩
  · have hempty (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native)
        (hz : z ∈ controlPatch l n k) : False := hne ⟨⟨(l,n),hz.1⟩⟩
    constructor <;> constructor
    · intro l n k z _ hz
      exact (hempty l n k z hz).elim
    · intro N
      exact ⟨0, le_rfl, 0, fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩
    · intro l n k z _ hz
      exact (hempty l n k z hz).elim
    · intro N
      exact ⟨0, le_rfl, 0, fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩

/-! The support geometry is the same canonical scalar-clock geometry. -/

noncomputable def supportLabel (l : Label B N0) : ActualCarrierTransportBase.Index B N0 :=
  (l.2,l.1)

theorem support_geometry_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.geometry (supportLabel l) n = (parameters x l).geometry n := rfl

theorem support_length_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.referenceLength (supportLabel l) /
      ActualCarrierTransportBase.clock (supportLabel l) n = (parameters x l).length n := rfl

theorem support_cutoff_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.cutoff (supportLabel l) n = (parameters x l).cutoff n := rfl

theorem copyData_ext {D I : Type} {a b : PeriodizedWaveBounds.CopyData D I}
    (hb : a.background = b.background) (ha : a.amplitude = b.amplitude)
    (hp : a.pressure = b.pressure) (hc : a.cutoff = b.cutoff) (hs : a.source = b.source) : a = b :=
      by
  cases a
  cases b
  cases hb
  cases ha
  cases hp
  cases hc
  cases hs
  rfl

theorem data_scalar_eq (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    data x l j = ScalarParticularSupport.scalarData (data x l j).background
      ((parameters x l).nativeTangent j) (currentSource x j l)
      (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
      (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
      (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
      (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l)) := by
  apply copyData_ext
  · rfl
  · rfl
  · rfl
  · funext n k z
    exact congrFun (ActualCarrierTransportBase.cutoff_eq_native (supportLabel l) n)
      ((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2)
  · rfl

noncomputable def carrierCells (l : Label B N0) : PeriodizedWaveBounds.Cells Native Frequency :=
  ScalarParticularSupport.scalarCells (P := Parameter)
    (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
    (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
    (ActualCarrierTransportBase.clock (supportLabel l))
    (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l))

theorem data_cutoff_support (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) (k : Frequency) :
    Function.support ((data x l j).cutoff n k) ⊆ (carrierCells l).carrier n k := by
  rw [data_scalar_eq x l j]
  exact ScalarParticularSupport.scalarData_cutoff_support (data x l j).background
    ((parameters x l).nativeTangent j) (currentSource x j l)
    (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
    (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
    (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
    (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l))
    (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l)) n k

abbrev InputSupport (x : CycleState (Label B N0)) : Prop :=
  ∀ l, HarmonicSourceSupport.InputSupportOn ActualCarrierTransportBase.domain
    (ActualCarrierTransportBase.labelCarrier (supportLabel l))
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)

theorem currentSource_pull (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n : ℕ) :
    currentSource x j l n = fun z =>
      ParticularWaveAssembly.residualSource (commonContext B) x.state (x.coefficients.blocks l)
        (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j n (nativeToFull z).1 :=
          by
  funext z
  change ParticularWaveAssembly.residualSource
      (StateReindex.context cycleAssoc.symm (commonContext B)) (StateReindex.state cycleAssoc.symm
        x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
      j n (z.1.1,z.2) = _
  unfold ParticularWaveAssembly.residualSource
  rw [StateReindex.residualBlock_pull]
  rfl

/-- Actual incoming coefficient support supplies the source's zero germ
on the full slow domain; no zero-germ conclusion about the solved field is assumed. -/
theorem currentSource_zero_germ (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : Native}
    (hz : z.1.1 ∈ ActualCarrierTransportBase.parameterDomain)
    (hout : (z.1.1,z.2) ∉ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n) :
    currentSource x j l n =ᶠ[𝓝 z] fun _ => 0 := by
  have hnot : (nativeToFull z).1 ∉ ActualCarrierTransportBase.labelCarrier (supportLabel l) n := by
    intro hc
    exact hout ((ActualCarrierTransportBase.labelCarrier_iff_canonicalSourceRegion hN
      (supportLabel l) n hz z.2).mp hc)
  have he := HarmonicSourceSupport.residualSource_zero_germ_on (commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    (PhysicalMeanDomain.slowDomain_open standardRegion.isOpen)
    (fun n => ActualInitialExcluded.labelCarrier_closed l n) (hs l) j n
    (x := (nativeToFull z).1) hz hnot
  rw [currentSource_pull]
  exact he.comp_tendsto (continuous_fst.comp nativeToFull.continuous).continuousAt


/-! Actual source-carrier coverage of the analytic patch. -/

theorem native_parameter_domain {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
      :
    z.1.1 ∈ ActualCarrierTransportBase.parameterDomain :=
  ((BaseContextAssembly.nativeStrip_mem nominal standardRegion (nativeToFull z).1).mp hz).1

theorem sourceRegion_mem_controlPatch (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k)
    (hs : (z.1.1,z.2) ∈ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n) :
    z ∈ controlPatch l n k := by
  have hc : (nativeToFull z).1 ∈ ActualInitialExcluded.labelCarrier l n :=
    (ActualCarrierTransportBase.labelCarrier_iff_canonicalSourceRegion hN
      (supportLabel l) n (native_parameter_domain hz) z.2).mpr hs
  obtain ⟨q, hnear, hphase, _⟩ := ActualCarrierGeometry.labelCarrier_phaseCell hN l n
    (x := nativeToFull z) hz hc
  have hphase' : ActualSignedGeometry.slowChange h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
      (ActualSignedGeometry.swapParameter z.1.1) ∈ jointDomain.carrier l := hphase
  rcases hs with ⟨_, hfast⟩
  obtain ⟨k', hcoord⟩ := Set.mem_iUnion.mp hfast
  have houter : z ∈ (carrierCells l).carrier n k' :=
    ActualGaussianCoverage.sourceCell_subset_outer slots.radius_pos
      (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hcoord
  have heq : k = k' := (carrierCells l).unique n k k' z hk houter
  subst k'
  exact ⟨hnear, ⟨hz, hphase', ActualGaussianCoverage.sourceCell_time
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hcoord⟩, hcoord.1⟩

/-- Every native cell is either controlled, killed by the actual cutoff,
or has both a zero raw solve and a zero current forcing germ. -/
theorem data_control_alternative (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k) :
    z ∈ controlPatch l n k ∨
      ((data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∨
      ((data x l j).amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).pressure n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0) := by
  by_cases hsource : (z.1.1,z.2) ∈
      ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n
  · exact Or.inl (sourceRegion_mem_controlPatch hN l n k hz hk hsource)
  · right
    have he := ScalarParticularSupport.scalarData_native_zero_alternative (data x l j).background
      ((parameters x l).nativeTangent j) (currentSource x j l)
      (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
      (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
      (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
      (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l))
      (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l))
      ActualCarrierTransportBase.parameterDomain
      (ActualCarrierTransportBase.activeSlowCore (supportLabel l))
      (fun n z hz hn => currentSource_zero_germ x hs hN l j n hz hn)
      n k (native_parameter_domain hz) hk hsource
    rw [← data_scalar_eq x l j] at he
    rcases he with hcut | ⟨ha,hp⟩
    · exact Or.inl hcut
    · exact Or.inr ⟨ha,hp,currentSource_zero_germ x hs hN l j n
        (native_parameter_domain hz) hsource⟩

theorem data_control_cover (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k) :
    z ∈ controlPatch l n k ∨
      (((data x l j).localized k).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
      (((data x l j).localized k).pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  rcases data_control_alternative x hs hN l j n k hz hk with h | hcut | ⟨ha,hp,_⟩
  · exact Or.inl h
  · exact Or.inr ((data x l j).localized_zero_germs hcut)
  · right
    refine ⟨?_, LabelSupportPreservation.localized_pressure_zero_of_raw (data x l j) hp⟩
    filter_upwards [ha] with y hy
    change (data x l j).cutoff n k y • (data x l j).amplitude n k y = 0
    rw [hy, smul_zero]

/-! The literal transported window/Gaussian product has uniform jets. -/

theorem selected_u (e : ℕ → ActivePair B N0) (u : Unit) (n : ℕ) :
    (selectedConstruction e).u (u,n) = (choice B N0).prepared.u :=
  PrimaryGeometryAssembly.construction_u certificate modulation
    (choice B N0).prepared slots.radius_pos (selectedLabel e n).1 (selectedLabel e n).2

theorem selected_cutoff_eq (e : ℕ → ActivePair B N0) (x : CycleState (Label B N0)) (j : ℤ)
    (u : Unit) (n : ℕ) (k : Frequency) :
    (data x (selectedLabel e n) j).cutoff (selectedBand e n) k =
      NativeCutoffJets.literalCutoff (selectedConstruction e) (selectedClock e) (selectedGeometry e)
        (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos) u n k := rfl

theorem selected_cutoff_jets (e : ℕ → ActivePair B N0) (x : CycleState (Label B N0)) (j : ℤ) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun _ _ _ => 1) 0 (selectedPatch e)
      (fun (_ : Unit) n k => (data x (selectedLabel e n) j).cutoff (selectedBand e n) k) := by
  have he : (fun (_ : Unit) n k => (data x (selectedLabel e n) j).cutoff (selectedBand e n) k) =
      NativeCutoffJets.literalCutoff (selectedConstruction e) (selectedClock e) (selectedGeometry e)
        (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos) := by
    funext u n k
    exact selected_cutoff_eq e x j u n k
  rw [he]
  exact NativeCutoffJets.literalCutoff_uniformLocalJets (selectedConstruction e) (selectedClock e)
    (selectedGeometry e) (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos)
    (ActualParticularControl.angleStrip (selectedStrip e)) selectedChi (selectedPhi e)
    (choice B N0).prepared.u_pos (selected_u e)
    ⟨_, ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h), 2, selected_geometry_bound e⟩

theorem cutoff_jets (x : CycleState (Label B N0)) (j : ℤ) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun _ _ _ => 1) 0 controlPatch (fun l => (data x l j).cutoff) := by
  classical
  by_cases hne : Nonempty (ActivePair B N0)
  · let : Nonempty (ActivePair B N0) := hne
    let e : ℕ → ActivePair B N0 := Classical.choose (exists_surjective_nat (ActivePair B N0))
    have he : Surjective e := Classical.choose_spec (exists_surjective_nat (ActivePair B N0))
    have hj := selected_cutoff_jets e x j
    have hp : (fun (_ : Unit) q k => controlPatch (selectedLabel e q) (selectedBand e q) k) =
        selectedPatch e := by
      funext u q k
      exact selected_controlPatch e u q k
    have hstrip : CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip
      e)) =
        UniformPrimaryWeights.reindexedStrip
          (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
          (fun q => (selectedBand e q, ())) := source_angle_reindex slowStrip (selectedBand e)
    rw [hstrip, ← hp] at hj
    exact ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
      (fun _ _ _ _ _ hcell => hcell.1) hj
  · have hempty (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native)
        (hz : z ∈ controlPatch l n k) : False := hne ⟨⟨(l,n),hz.1⟩⟩
    refine ⟨fun l n k z _ hz => (hempty l n k z hz).elim, fun _ => ?_⟩
    exact ⟨0,le_rfl,0,fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩

/-! Derived local background bounds and actual common-field estimates. -/

theorem canonical_geometry_eq (l : Label B N0) (n : ℕ) :
    (canonicalParameters l).geometry n =
      ActualCarrierTransportBase.geometry (supportLabel l) n := rfl

theorem control_clock (l : Label B N0) (n : ℕ) (k : Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 (ActualCarrierTransportBase.clock (supportLabel l) n)
      (((canonicalParameters l).geometry n).coordinates k Y) =
        (chartGeometry n l.1 l.2).coordinates k Y := by
  rw [canonical_geometry_eq]
  simpa only [supportLabel] using
    ActualCarrierTransportBase.coordinates_clock (supportLabel l) n k Y

theorem controlPatch_subset_padded (l : Label B N0) (n : ℕ) (k : Frequency) :
    controlPatch l n k ⊆ ParticularPaddedBackground.cells n (l,k) := by
  intro z hz
  refine ⟨hz.1, hz.2.1.2.1, ?_⟩
  simp only [ActualPrimaryBounds.fullCopy, ActualPrimaryBounds.copyPoint,
    ActualSignedGeometry.copyPoint]
  change (chartGeometry n l.1 l.2).coordinates k z.2 ∈ (clockWindow l.2).core
  rw [← control_clock]
  change _ ∈ Icc (-slots.radius) slots.radius ∧
    0 + ActualCarrierTransportBase.clock (supportLabel l) n *
      (((canonicalParameters l).geometry n).coordinates k z.2).2 ∈
        Icc 0 ((phases B N0 0).L l.2)
  refine ⟨hz.2.2, ?_⟩
  have hc := ActualCarrierTransportBase.clock_pos (supportLabel l) n
  have ht := hz.2.1.2.2
  change 0 < _ ∧ _ < ((phases B N0 l.1).L l.2) /
    ActualCarrierTransportBase.clock (supportLabel l) n at ht
  rw [length_sign l.1 l.2] at ht
  exact ⟨by simpa only [zero_add] using (mul_pos hc ht.1).le,
    by simpa only [zero_add, mul_comm] using ((lt_div_iff₀ hc).mp ht.2).le⟩

theorem local_restrict {D I E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {C K : ℕ → I → Set D} {w : ℕ → I → D → ℝ}
    {α : ℝ} {f : ℕ → I → D → E}
    (hf : LocalizedWaveBounds.LocalClass s C w α f)
    (hsub : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∈ C n i) :
    LocalizedWaveBounds.LocalClass s K w α f :=
  hf.enlarge (fun n i x hx hi => Or.inl (hsub n i x hx hi))

theorem inputs_restrict {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {C K : ℕ → I → Set D} {W : ℕ → I → D → ℝ}
    {α κ : ℝ} {d : LinearWaveBounds.GraphDirections D}
    {a : LocalizedWaveBounds.WaveFamily D I}
    (hf : LocalizedWaveBounds.InputBounds s C W α κ d a)
    (hsub : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∈ C n i) :
    LocalizedWaveBounds.InputBounds s K W α κ d a where
  loss_nonneg := hf.loss_nonneg
  radial_profile := local_restrict hf.radial_profile hsub
  radial_scale := hf.radial_scale
  fast_scale := hf.fast_scale
  frequency_scale := local_restrict hf.frequency_scale hsub
  radius := local_restrict hf.radius hsub
  inverse_radius := local_restrict hf.inverse_radius hsub
  radial_base := local_restrict hf.radial_base hsub
  frequency_base := local_restrict hf.frequency_base hsub
  axial_base := local_restrict hf.axial_base hsub
  radial_base_aux n i x hx hi := hf.radial_base_aux n i x hx (hsub n i x hx hi)
  frequency_base_aux n i x hx hi := hf.frequency_base_aux n i x hx (hsub n i x hx hi)
  axial_base_aux n i x hx hi := hf.axial_base_aux n i x hx (hsub n i x hx hi)
  normal := local_restrict hf.normal hsub
  defect := local_restrict hf.defect hsub
  amplitude j := local_restrict (hf.amplitude j) hsub
  pressure := local_restrict hf.pressure hsub

abbrev PreservesCarriers (x : CycleState (Label B N0)) : Prop :=
  ∀ l, SameCarrier (x.coefficients.blocks l) (ActualParticularBackground.primaryBlock l)

theorem preserves_frequency {x : CycleState (Label B N0)} (hx : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) :
    (x.coefficients.blocks l).frequency n = ChartScales.carrier h n :=
  (congrFun (hx l).frequency n).symm

theorem data_background_eq (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    (data x l j).background =
      ActualParticularBackground.carrier (fun l => x.coefficients.blocks l) j l := rfl

theorem native_background_eq (x : CycleState (Label B N0)) (j : ℤ) :
    jointRawBackground (fun l => data x l j) =
      ActualParticularBackground.backgroundFamily (fun l => x.coefficients.blocks l) j := rfl

theorem actual_background_inputs (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) :
    LocalizedWaveBounds.InputBounds
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n (i : Label B N0 × Frequency) => controlPatch i.1 n i.2)
      (fun n i z => nativeEnvelope i.1 n z) 0 ChartScales.kappa (directions (B := B))
      (jointRawBackground (fun l => data x l j)) := by
  rw [native_background_eq]
  exact inputs_restrict
    (ParticularPaddedBackground.actual_background_inputs hN
      (fun l => x.coefficients.blocks l) hx j (fun n i z => nativeEnvelope i.1 n z)
      (fun n i z _ => envelope_nonneg i.1 n (z.1.1,z.2)))
    (fun n i z _ hz => controlPatch_subset_padded i.1 n i.2 hz)

theorem actual_normal_range (x : CycleState (Label B N0)) (hx : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ controlPatch l n k) :
    ActualPrimaryBounds.normalFloor B N0 ≤ ‖(data x l j).background.normal
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) (directions (B
        := B)) n z‖ ∧
    ‖(data x l j).background.normal
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) (directions (B
        := B)) n z‖ ≤
        ActualPrimaryBounds.normalCeiling B N0 := by
  exact ParticularPaddedBackground.background_normal_range
    (fun l => x.coefficients.blocks l) hx j (n := n) (i := (l,k)) (x := z)
    hz (controlPatch_subset_padded l n k hk)

theorem actual_inverse_frequency (x : CycleState (Label B N0)) (hx : PreservesCarriers x) (j : ℤ) :
    LocalizedWaveBounds.LocalUnweighted
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n (i : Label B N0 × Frequency) => controlPatch i.1 n i.2) (1/2)
      (fun n i (_ : Native) => 1/(data x i.1 j).background.frequency n) := by
  exact local_restrict
    (ParticularPaddedBackground.background_inverse_frequency (fun l => x.coefficients.blocks l) hx
      j)
    (fun n i z _ hz => controlPatch_subset_padded i.1 n i.2 hz)

theorem common_bounds (x : CycleState (Label B N0)) (hx : PreservesCarriers x)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    let s := CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)
    LabelSumBounds.UniformWaveClass s nativeEnvelope α (fun l => (data x l j).common.amplitude) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope α
      (fun l => ((data x l j).commonCorrected s (directions (B := B))).amplitude) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2) (fun l => (data x l
      j).common.pressure) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2-ChartScales.kappa)
      (fun l => (data x l j).common.curlCorrection s (directions (B := B))) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2-3*ChartScales.kappa)
      (fun l => (data x l j).globalGood s (directions (B := B))) := by
  have hr := raw_jets x (preserves_frequency hx) j hj H
  exact uniform_common_bounds_from_raw (fun l => data x l j) carrierCells
    (fun l n k => data_cutoff_support x l j n k)
    (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (actual_background_inputs x hx hN j) hr.1 hr.2 (cutoff_jets x j)
    (by norm_num [ChartScales.kappa]) (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun l n k z hz hk => (actual_normal_range x hx l j n k hz hk).1)
    (fun l n k z hz hk => (actual_normal_range x hx l j n k hz hk).2)
    (actual_inverse_frequency x hx j)
    (fun l n k z hz hk => data_control_cover x hs hN l j n k hz hk)

/-! The exact moving weight, finite harmonic assembly, and invariant interface. -/

theorem meanEnvelope_eq_primary (l : Label B N0) (n : ℕ) (z : CyclePoint) :
    meanEnvelope l n z = ActualPrimaryBounds.meanEnvelope l n z := rfl

theorem nativeEnvelope_le_one (l : Label B N0) (n : ℕ) (z : Native) :
    nativeEnvelope l n z ≤ 1 :=
  ActualPrimaryBounds.fullEnvelope_le_one l n (nativeToFull z)

theorem native_wave_to_weighted {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : Label B N0 → ℕ → Native → E}
    (hf : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) nativeEnvelope
        α f) :
    LabelSumBounds.UniformClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun _ _ z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z)) α f :=
  hf.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun l n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (nativeEnvelope_le_one l n z))

abbrev ResidualBounds (x : CycleState (Label B N0)) (α : ℝ) : Prop :=
  UniformHarmonicInteraction.UniformVelocity
    (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
    (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))

noncomputable def associatedUpdate (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock (Parameter × Plane) :=
  (parameters x l).updateBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

noncomputable def associatedGood (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock (Parameter × Plane) :=
  (parameters x l).goodBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

theorem associated_assembled_bounds (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (H : ResidualBounds x α) (N : ℕ) :
    (∀ i j, LabelSumBounds.UniformWaveClass associatedStrip envelope α
      (fun l n z => (associatedUpdate x N l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass associatedStrip envelope (α+1/2)
      (fun l n z => (associatedUpdate x N l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass associatedStrip envelope (α+1/2-3*ChartScales.kappa)
      (fun l n z => (associatedGood x N l).velocity n i j z)) := by
  have hm (j : ℤ) (hj : j ∈ ParticularWaveAssembly.modes N) :=
    common_bounds x hx hs hN j ((ParticularWaveAssembly.mem_modes N j).mp hj).1
      (current_source_class x H j ((ParticularWaveAssembly.mem_modes N j).mp hj).1)
  exact ParticularParameters.uniform_assembled_bounds (fun l => parameters x l)
    associatedStrip (associatedContext (B := B)) (StateReindex.state cycleAssoc.symm x.state)
    (fun l => StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (fun l => StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (fun l => StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
    N (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (fun j hj => (hm j hj).2.1) (fun j hj => (hm j hj).2.2.1)
    (fun j hj => (hm j hj).2.2.2.2)

noncomputable def outputBlock (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock CyclePoint := StateReindex.block cycleAssoc (associatedUpdate x N l)

noncomputable def outputGood (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock CyclePoint := StateReindex.block cycleAssoc (associatedGood x N l)

theorem associated_wave_return {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : Label B N0 → ℕ → Parameter × Plane → E}
    (hf : LabelSumBounds.UniformWaveClass associatedStrip envelope α f) :
    LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope α (fun l n z => f l n (cycleAssoc z)) := by
  exact MeanBoundsReindex.uniformClass_return cycleAssoc hf

/-- The finite harmonic assembly and coordinate association retain
constants chosen before the spatial label and band. -/
theorem assembled_bounds (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (H : ResidualBounds x α) (N : ℕ) :
    (∀ i j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope α (fun l n z => (outputBlock x N l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope (α+1/2) (fun l n z => (outputBlock x N l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope (α+1/2-3*ChartScales.kappa)
      (fun l n z => (outputGood x N l).velocity n i j z)) := by
  obtain ⟨ha,hp,hg⟩ := associated_assembled_bounds x hx hs hN H N
  exact ⟨fun i j => associated_wave_return (ha i j),
    fun j => associated_wave_return (hp j), fun i j => associated_wave_return (hg i j)⟩

/-- The quantitative inputs are precisely fields of the current analytic
invariant. The geometric equalities identify its actual strip and carrier. -/
theorem invariant_assembled_bounds (x : CycleState (Label B N0))
    {G : SignedMeanGain.Geometry} {σ : ℝ}
    (H : CycleAnalyticInvariant G (commonContext B) ActualParticularBackground.primaryBlock
      meanEnvelope (fun l => ActualCarrierTransportBase.labelCarrier (supportLabel l)) σ x)
    (hstrip : G.strip = BaseContextAssembly.nativeStrip nominal standardRegion)
    (hdomain : G.domain = ActualCarrierTransportBase.domain)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    (∀ i j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1/2+σ)
      (fun l n z => (outputBlock x x.coefficients.residualBand l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1+σ)
      (fun l n z => (outputBlock x x.coefficients.residualBand l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1+σ-3*ChartScales.kappa)
      (fun l n z => (outputGood x x.coefficients.residualBand l).velocity n i j z)) := by
  have hs : InputSupport x := by
    intro l
    simpa only [hdomain] using H.inputSupport l
  have hr : ResidualBounds x (1/2+σ) := by
    simpa only [hstrip] using H.residual
  have hout := assembled_bounds x H.carrier hs hN hr x.coefficients.residualBand
  have hα : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  simpa only [hstrip, hα] using hout

end NavierStokes.ActualParticularStageControls
