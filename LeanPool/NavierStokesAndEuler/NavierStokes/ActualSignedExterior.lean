/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalBinding
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
public import LeanPool.NavierStokesAndEuler.NavierStokes.DependentSignedPhysicalFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage

@[expose] public section

/-!
# Exact exterior support of the actual signed physical fields

The original spatial mask and leading target force every signed copy to
vanish outside the fixed nominal active annulus. The argument retains the
normalized radial coordinate exactly and is independent of the request.
-/

noncomputable section

namespace NavierStokes.ActualSignedExterior

open Set Function Filter ProblemStatement CorrectionInitialization
open CorrectionInitialization.ActualPrimary PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff BigOperators

abbrev Label := ActualSignedPhysicalBinding.Label

variable {B N0 : ℕ}

noncomputable def active : Set SpaceTime := ActualPolarCoverage.active

/-! ## The normalized radial coordinate does not depend on the band -/

theorem normalizedX_graph (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    (BaseChartJets.normalizedCoordinates h
      (ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph h n d w))).2.1 =
        (SlowBorelBase.cartesianChart h w).2.1 := by
  have ht := PhysicalMeanJetBounds.graph_time_pos h n d hw
  rw [← PrimaryTargetBounds.profileRadius_sq (F := outgoing)
    (p := ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph h n d w)) ht]
  simpa only [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq,
    SimilarityHomogeneity.chartQ, ActualSignedPhysicalData.nativeSlow,
    VariableGaugeMean.qLength] using
      ActualPolarCoverage.graph_profileRadius_sq outgoing.data.h_pos
        outgoing.data.h_lt_half n d hw

theorem physicalLift_slow (n : ℕ) (w : SpaceTime) :
    ((ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.1,
      (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.2.1) =
        ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph h n 0 w) := by
  rw [PhysicalMeanJetBounds.graph, Function.comp_apply, ActualSignedPhysicalData.commonLift_zero]
  rfl

/-- This is a statement about the literal primary mask and target. No
property of the signed output or of the current request is assumed. -/
theorem primary_mask_or_target_zero (l : Label B N0) (n m : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    (ActualSignedPhysicalBinding.primary l).mask n
        (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h m w)) = 0 ∨
      (ActualSignedPhysicalBinding.primary l).target n
        (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h m w)) = 0 := by
  let p := ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph h m 0 w)
  have ht : 0 < p.2.2 := PhysicalMeanJetBounds.graph_time_pos h m 0 hw
  by_cases hm : spatialMask l.1 p = 0
  · left
    change spatialMask l.1 _ = 0
    rwa [physicalLift_slow]
  · right
    have hc := spatialMask_carrier l.1 ht hm
    have hr := (choice B N0).prepared.radius_pos l.1 p hc
    have hn : (BaseChartJets.normalizedCoordinates h p).2.1 ∉
        Ioo (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal) := by
      intro hi
      apply hout
      change (SlowBorelBase.cartesianChart h w).2.1 ∈
        Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal)
      have he := normalizedX_graph m 0 hw
      change (BaseChartJets.normalizedCoordinates h p).2.1 = _ at he
      rw [← he]
      exact ⟨hi.1.le, hi.2.le⟩
    have hz := PrimaryTargetBounds.stress_zero_of_not_active modulation
      (ProfileSpectralCone.normalized_X_pos outgoing.data.h_pos outgoing.data.h_lt_half ht hr)
      (abs_le.mp (BaseChartJets.normalizedCoordinates_eta outgoing.data.h_pos
        outgoing.data.h_lt_half ht).le) hn
    have htarget : PrimaryTargetBounds.actualTarget modulation p = 0 := by
      simp only [PrimaryTargetBounds.actualTarget, hz, smul_zero]
    change (fun j => PrimaryTargetBounds.actualTarget modulation _ j) = 0
    rw [physicalLift_slow]
    change (fun j => PrimaryTargetBounds.actualTarget modulation p j) = 0
    simp only [htarget, WithLp.ofLp_zero, Pi.zero_apply]
    rfl

/-! ## All actual labels, with their original dependent data -/

noncomputable def bandLabel (l : Label B N0) : BandLabel :=
  ⟨ActualSignedPhysicalBinding.spatialLabel l, ActualPrimaryBounds.label_large (l.2, l.1)⟩

theorem bandLabel_injective : Injective (bandLabel (B := B) (N0 := N0)) := by
  intro l k hlk
  have he : ActualSignedPhysicalBinding.spatialLabel l =
      ActualSignedPhysicalBinding.spatialLabel k := congrArg Subtype.val hlk
  have hu : PrimaryGeometryAssembly.label nominal l.1 =
      PrimaryGeometryAssembly.label nominal k.1 := by
    apply Prod.ext
    · exact congrArg (fun L : SlotColoring.Label => L.1) he
    · exact congrArg (fun L : SlotColoring.Label => L.2.1) he
  have hfirst := PrimaryGeometryAssembly.label_injective nominal hu
  apply Prod.ext hfirst
  apply PartitionedCovariance.signedLabel_injective (PrimaryGeometryAssembly.label nominal k.1)
  simpa only [bandLabel, ActualSignedPhysicalBinding.spatialLabel, hfirst] using he

noncomputable def labels (B N0 : ℕ) : Set BandLabel := range (bandLabel (B := B) (N0 := N0))

noncomputable def nativeLabel (l : Label B N0) :
    ActualSignedPhysicalData.NativeLabel (labels B N0) :=
  ⟨ActualSignedPhysicalBinding.spatialLabel l, ActualPrimaryBounds.label_large (l.2, l.1),
    Set.mem_range_self l⟩

noncomputable def actualLabel (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    Label B N0 := Classical.choose L.mem

theorem bandLabel_actualLabel (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    bandLabel (actualLabel L) = (L : BandLabel) := Classical.choose_spec L.mem

@[simp] theorem actualLabel_nativeLabel (l : Label B N0) :
    actualLabel (nativeLabel l) = l :=
  bandLabel_injective (bandLabel_actualLabel (nativeLabel l))

theorem nativeLabel_ext {S : Set BandLabel}
    {L M : ActualSignedPhysicalData.NativeLabel S} (he : L.val = M.val) : L = M := by
  cases L
  cases M
  cases he
  rfl

@[simp] theorem nativeLabel_actualLabel
    (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    nativeLabel (actualLabel L) = L :=
  nativeLabel_ext (congrArg Subtype.val (bandLabel_actualLabel L))

noncomputable def labelEquiv : Label B N0 ≃ ActualSignedPhysicalData.NativeLabel (labels B N0) where
  toFun := nativeLabel
  invFun := actualLabel
  left_inv := actualLabel_nativeLabel
  right_inv := nativeLabel_actualLabel

theorem actualLabel_reference (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    ActualSignedPhysicalBinding.reference (actualLabel L) = L.val.1 :=
  congrArg (fun L : BandLabel => L.val.1) (bandLabel_actualLabel L)

noncomputable def rebandPayload {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    {P : PhysicalSignedWave.PrimaryData U} {n m : ℕ} (he : n = m)
    (V : P.Views n) (s : V.StateData) : Σ W : P.Views m, W.StateData :=
  he ▸ ⟨V, s⟩

theorem rebandPayload_referenceRequest {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    {P : PhysicalSignedWave.PrimaryData U} {n m : ℕ} (he : n = m)
    (V : P.Views n) (s : V.StateData) :
    (rebandPayload he V s).2.referenceRequest = s.referenceRequest := by
  cases he
  rfl

noncomputable def payload (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews
  l).StateData)
    (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    Σ V : (ActualSignedPhysicalBinding.primary (actualLabel L)).Views L.val.1, V.StateData :=
  rebandPayload (actualLabel_reference L) (ActualSignedPhysicalBinding.nativeViews (actualLabel L))
    (s (actualLabel L))

/-- Both signs and every actual primary label are retained. Only proof
transport of the reference index is used in the view/state fields. -/
noncomputable def family (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews
  l).StateData) :
    DependentSignedPhysicalFamily.Family where
  active := labels B N0
  domain L := ActualSignedPhysicalBinding.domain (actualLabel L)
  primary L := ActualSignedPhysicalBinding.primary (actualLabel L)
  view L := (payload s L).1
  state L := (payload s L).2
  column L := (actualLabel L).2

@[simp] theorem family_referenceRequest
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (L : ActualSignedPhysicalData.NativeLabel (labels B N0)) :
    ((family s).state L).referenceRequest = (s (actualLabel L)).referenceRequest :=
  rebandPayload_referenceRequest _ _ _

@[simp] theorem family_referenceRequest_nativeLabel
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) :
    ((family s).state (nativeLabel l)).referenceRequest = (s l).referenceRequest := by
  rw [family_referenceRequest, actualLabel_nativeLabel]

/-! ## Every physical copy vanishes on the exact exterior -/

section Fields

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

theorem potential_gap (i : Fin 3) (L : BandLabel) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).gap L = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.potentialFamily
    slots outgoing.data.h_pos.le ((family s).singleton L) i) L).gap L = 0
  by_cases hL : L ∈ (family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hL]
    rfl
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL]
    rfl

theorem pressure_gap (L : BandLabel) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).gap L = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.pressureFamily
    slots outgoing.data.h_pos.le ((family s).singleton L)) L).gap L = 0
  by_cases hL : L ∈ (family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hL]
    rfl
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL]
    rfl

theorem potential_amplitude_zero (i : Fin 3) (I : WaveIndex 1) (k : TorusInverse.Frequency)
    {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k I
      (PhysicalGraphBounds.physicalLift h I.1.val.1 w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.potentialFamily
    slots outgoing.data.h_pos.le ((family s).singleton L) i) I.1).amplitude k I _ = 0
  by_cases hL : I.1 ∈ (family s).active
  · let L : ActualSignedPhysicalData.NativeLabel (family s).active :=
      ⟨I.1.val, I.1.property, hL⟩
    change ((family s).copyAt _ (L : BandLabel)).amplitude k I _ = 0
    rw [DependentSignedPhysicalFamily.Family.copyAt_active]
    by_contra hn
    obtain ⟨hL', _, hm, ht⟩ := ActualSignedPhysicalData.potential_amplitude_inputs
      slots outgoing.data.h_pos.le ((family s).singleton L) i k I _ hn
    rcases primary_mask_or_target_zero (actualLabel L) I.1.val.1 I.1.val.1 hw hout with hz | hz
    · exact hm hz
    · exact ht hz
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL]
    rfl

theorem pressure_amplitude_zero (I : WaveIndex 1) (k : TorusInverse.Frequency)
    {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k I
      (PhysicalGraphBounds.physicalLift h I.1.val.1 w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.pressureFamily
    slots outgoing.data.h_pos.le ((family s).singleton L)) I.1).amplitude k I _ = 0
  by_cases hL : I.1 ∈ (family s).active
  · let L : ActualSignedPhysicalData.NativeLabel (family s).active :=
      ⟨I.1.val, I.1.property, hL⟩
    change ((family s).copyAt _ (L : BandLabel)).amplitude k I _ = 0
    rw [DependentSignedPhysicalFamily.Family.copyAt_active]
    by_contra hn
    obtain ⟨hL', _, hm, ht⟩ := ActualSignedPhysicalData.pressure_amplitude_inputs
      slots outgoing.data.h_pos.le ((family s).singleton L) k I _ hn
    rcases primary_mask_or_target_zero (actualLabel L) I.1.val.1 I.1.val.1 hw hout with hz | hz
    · exact hm hz
    · exact ht hz
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL]
    rfl

theorem potential_term_zero (i : Fin 3) (I : WaveIndex 1) (k : TorusInverse.Frequency)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k I
    (commonLift h I.1.val.1
      (((family s).potentialCopies slots outgoing.data.h_pos.le i).gap I.1) w) = 0
  rw [potential_gap, ActualSignedPhysicalData.commonLift_zero]
  exact potential_amplitude_zero s i I k hw hout

theorem pressure_term_zero (I : WaveIndex 1) (k : TorusInverse.Frequency)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k I
    (commonLift h I.1.val.1
      (((family s).pressureCopies slots outgoing.data.h_pos.le).gap I.1) w) = 0
  rw [pressure_gap, ActualSignedPhysicalData.commonLift_zero]
  exact pressure_amplitude_zero s I k hw hout

theorem potential_sum_zero (i : Fin 3) (a r0 : ℝ) {w : SpaceTime}
    (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).sum a h r0 w = 0 := by
  have hz := fun I k => potential_term_zero s i I k a r0 hw hout
  simp only [CopyFamily.sum, CopyFamily.periodized, hz, tsum_zero, finsum_zero]

theorem pressure_sum_zero (a r0 : ℝ) {w : SpaceTime}
    (hw : w ∈ preterminal) (hout : w ∉ active) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).sum a h r0 w = 0 := by
  have hz := fun I k => pressure_term_zero s I k a r0 hw hout
  simp only [CopyFamily.sum, CopyFamily.periodized, hz, tsum_zero, finsum_zero]

/-- The literal dependent-family potential, at the fixed physical chart radius. -/
noncomputable def potential : VelocityField :=
  PhysicalCopyBounds.vectorSum ((family s).potentialCopies slots outgoing.data.h_pos.le)
    ActualPolarCoverage.inner h slots.radius

noncomputable def pressure : PressureField :=
  fun w => (((family s).pressureCopies slots outgoing.data.h_pos.le).sum
    ActualPolarCoverage.inner h slots.radius w).re

theorem potential_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    potential s w = 0 := by
  have hz := fun i => potential_sum_zero s i ActualPolarCoverage.inner slots.radius hw hout
  simp only [potential, PhysicalCopyBounds.vectorSum, hz, map_zero, Finset.sum_const_zero]

theorem pressure_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    pressure s w = 0 := by
  rw [pressure, pressure_sum_zero s _ _ hw hout]
  rfl

theorem exterior_open : IsOpen {w : SpaceTime | w ∈ preterminal ∧ w ∉ active} :=
  BaseResidual.chartedDomain_isOpen outgoing.data.h_pos outgoing.data.h_lt_half
    (show IsOpen {p : ℝ × ℝ | p.1 ∉ Icc (NominalConeAssembly.activeLeft nominal)
      (NominalConeAssembly.activeRight nominal)} from
      (isClosed_Icc.preimage continuous_fst).isOpen_compl)

theorem potential_zero_germ {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    potential s =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [exterior_open.mem_nhds ⟨hw, hout⟩] with y hy
  exact potential_zero s hy.1 hy.2

theorem pressure_zero_germ {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    pressure s =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [exterior_open.mem_nhds ⟨hw, hout⟩] with y hy
  exact pressure_zero s hy.1 hy.2

theorem velocity_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    SpatialCurl.spatialCurl (potential s) w = 0 :=
  PhysicalCurlCovariance.spatialCurl_zero_of_zero_near (potential_zero_germ s hw hout)

/-- Any fixed residual floor is allowed, since the stronger exterior
identity above holds on the whole preterminal set. -/
theorem exterior_below (Nres : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (_hq : physicalQ h w < ChartScales.Q Nres) (hout : w ∉ active) :
    potential s w = 0 ∧ pressure s w = 0 :=
  ⟨potential_zero s hw hout, pressure_zero s hw hout⟩

end Fields

/-! ## The same state and request as the actual correction cycle -/

section Cycle

variable (x : CorrectionStep.CycleState (Label B N0))
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B)
      ((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (commonContext B) x.state))
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b
      ((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (commonContext B) x.state).pressure)

noncomputable def cycleNativeStates (l : Label B N0) :
    (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  ActualSignedPhysicalBinding.nativeStateData l ActualInitialization.patch
    ((ActualCycleParameters.fixedParameters B N0).afterParticular
      x.coefficients (commonContext B) x.state) H hp

noncomputable def cycleFamily : DependentSignedPhysicalFamily.Family :=
  family (cycleNativeStates x H hp)

noncomputable def cyclePotential : VelocityField := potential (cycleNativeStates x H hp)

noncomputable def cyclePressure : PressureField := pressure (cycleNativeStates x H hp)

/-- The exterior statement concerns the signed request of the literal
cycle after its particular update, without replacing the incoming state. -/
theorem cycle_referenceRequest (l : Label B N0) (z : ActualSignedPhysicalBinding.Cylinder) :
    ((cycleFamily x H hp).state (nativeLabel l)).referenceRequest
        (ActualSignedPhysicalBinding.reference l) z =
      (ActualCycleParameters.fixedParameters B N0).signedRequest
        x.coefficients (commonContext B) x.state (ActualSignedPhysicalBinding.reference l)
          (ActualSignedPhysicalBinding.toCommonCylinder l z) := by
  change ((family (cycleNativeStates x H hp)).state (nativeLabel l)).referenceRequest _ _ = _
  rw [family_referenceRequest_nativeLabel]
  exact ActualSignedPhysicalBinding.nativeStateData_referenceRequest l ActualInitialization.patch
    ((ActualCycleParameters.fixedParameters B N0).afterParticular
      x.coefficients (commonContext B) x.state) H hp z

theorem cycle_potential_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    cyclePotential x H hp w = 0 := potential_zero (cycleNativeStates x H hp) hw hout

theorem cycle_pressure_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    cyclePressure x H hp w = 0 := pressure_zero (cycleNativeStates x H hp) hw hout

theorem cycle_zero_germs {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    (cyclePotential x H hp =ᶠ[𝓝 w] fun _ => 0) ∧
      (cyclePressure x H hp =ᶠ[𝓝 w] fun _ => 0) :=
  ⟨potential_zero_germ (cycleNativeStates x H hp) hw hout,
    pressure_zero_germ (cycleNativeStates x H hp) hw hout⟩

theorem cycle_velocity_zero {w : SpaceTime} (hw : w ∈ preterminal) (hout : w ∉ active) :
    SpatialCurl.spatialCurl (cyclePotential x H hp) w = 0 :=
  velocity_zero (cycleNativeStates x H hp) hw hout

theorem cycle_exterior (Nres : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w < ChartScales.Q Nres) (hout : w ∉ active) :
    cyclePotential x H hp w = 0 ∧ cyclePressure x H hp w = 0 :=
  exterior_below (cycleNativeStates x H hp) Nres hw hq hout

end Cycle

end NavierStokes.ActualSignedExterior
