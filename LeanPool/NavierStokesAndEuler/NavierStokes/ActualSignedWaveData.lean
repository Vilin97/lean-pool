/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeProfiles
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeCopyFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeSignedData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedReferenceGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedFamilySupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.GluedStageEstimates

@[expose] public section

/-!
# Physical wave data for the actual signed cycle fields

The native family is the family in `ActualSignedExterior`. Geometry,
profiles and native source bounds are assembled before any physical
estimate is applied.
-/

noncomputable section

namespace NavierStokes.ActualSignedWaveData

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff BigOperators

abbrev Label := ActualSignedPhysicalBinding.Label
abbrev Native := ActualSignedPhysicalData.Native
abbrev SourceIndex := Σ (_ : BandLabel), ActualSignedPhysicalData.SourceIndex

variable {B N0 : ℕ}

noncomputable def nativeStates (P : SignedStressPrimitive.Patch) (u : State
  LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)
    (l : Label B N0) : (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  ActualSignedPhysicalBinding.nativeStateData l P u H hp

noncomputable def family (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    DependentSignedPhysicalFamily.Family :=
  ActualSignedExterior.family (nativeStates (N0 := N0) P u H hp)

section Geometry

variable (P : SignedStressPrimitive.Patch) (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

/-- The physical geometry is derived from the same actual primary, views,
and current-state request; no representation assertion is assumed. -/
noncomputable def singletonGeometry
    (L : ActualSignedPhysicalData.NativeLabel (family (N0 := N0) P u H hp).active) :
    ActualSignedPhysicalData.ReferenceGeometry slots ((family P u H hp).singleton L) :=
  ActualSignedReferenceGeometry.singletonGeometry P u H hp L

/-- One actual bound works for every native label and both signs. -/
theorem singleton_frequencies
    (L : ActualSignedPhysicalData.NativeLabel (family (N0 := N0) P u H hp).active)
    (K : ActualSignedPhysicalData.NativeLabel ((family P u H hp).singleton L).active) :
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.p K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 ∧
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.pz K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 ∧
    |((((family P u H hp).singleton L).primary K).pulse
        (((family P u H hp).singleton L).column K)).phase.x0 K.val.1| ≤
        ActualPhaseJetBounds.phaseSize B N0 := by
  rw [ActualSignedReferenceGeometry.singleton_index_eq (family P u H hp) L K]
  exact ActualPhaseJetBounds.phase_constants_bound
    ((ActualSignedExterior.actualLabel L).2, (ActualSignedExterior.actualLabel L).1)

end Geometry

private theorem cells_mpr {H : ℕ} {K : Type*} {f g : CopyFamily H K}
    (he : f = g) (c : SupportCells g) (L : BandLabel) :
    (Eq.mpr (congrArg SupportCells he) c).cells L = c.cells L := by
  cases he
  rfl

private theorem branchCells_active (f : DependentSignedPhysicalFamily.Family)
    {H : ℕ} {K : Type*}
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (c : ∀ L, SupportCells (copies L))
    (L : ActualSignedPhysicalData.NativeLabel f.active) (M : BandLabel) :
    (f.branchCells copies c L).cells M = (c L).cells M := by
  classical
  simp only [DependentSignedPhysicalFamily.Family.branchCells, dite_eq_left L.mem]
  exact cells_mpr (f.copyAt_active copies L) (c L) M

private theorem branchCells_inactive (f : DependentSignedPhysicalFamily.Family)
    {H : ℕ} {K : Type*}
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (c : ∀ L, SupportCells (copies L)) (L M : BandLabel) (hL : L ∉ f.active) :
    (f.branchCells copies c L).cells M =
      (DependentSignedPhysicalFamily.zeroCells (H := H) (K := K)).cells M := by
  classical
  simp only [DependentSignedPhysicalFamily.Family.branchCells, dite_eq_right hL]
  exact cells_mpr (f.copyAt_inactive copies hL) DependentSignedPhysicalFamily.zeroCells M

section CopyFamilies

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

noncomputable def originalPotentialCells (i : Fin 3) :
    SupportCells ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i) :=
  DependentSignedPhysicalFamily.diagonalCells _
    ((ActualSignedExterior.family s).branchCells
      (fun L => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i)
      (fun L => ActualSignedPhysicalData.localizedPotentialCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i))

noncomputable def originalPressureCells :
    SupportCells ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le) :=
  DependentSignedPhysicalFamily.diagonalCells _
    ((ActualSignedExterior.family s).branchCells
      (fun L => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L))
      (fun L => ActualSignedPhysicalData.localizedPressureCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L)))

theorem potentialCells_active (i : Fin 3)
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)) :
    (originalPotentialCells s i).cells L =
      (ActualSignedPhysicalData.localizedPotentialCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L) i).cells L := by
  exact branchCells_active (ActualSignedExterior.family s) _ _ L L

theorem pressureCells_active
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)) :
    (originalPressureCells s).cells L =
      (ActualSignedPhysicalData.localizedPressureCells slots outgoing.data.h_pos.le
        ((ActualSignedExterior.family s).singleton L)).cells L := by
  exact branchCells_active (ActualSignedExterior.family s) _ _ L L

theorem potentialCells_inactive (i : Fin 3) {L : BandLabel}
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    (originalPotentialCells s i).cells L =
      (DependentSignedPhysicalFamily.zeroCells (H := 1)).cells L := by
  exact branchCells_inactive (ActualSignedExterior.family s) _ _ L L hL

theorem pressureCells_inactive {L : BandLabel}
    (hL : L ∉ ActualSignedExterior.labels B N0) :
    (originalPressureCells s).cells L =
      (DependentSignedPhysicalFamily.zeroCells (H := 1)).cells L := by
  exact branchCells_inactive (ActualSignedExterior.family s) _ _ L L hL

noncomputable def originalPotentialCarrier (i : Fin 3) :
    CarrierBounds ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)
      (originalPotentialCells s i) ActualPolarCoverage.inner ActualPolarCoverage.outer h
        slots.radius where
  region _ L := ActualSignedNativeProfiles.region B N0 L
  open_region _ := ActualSignedNativeProfiles.region_open B N0
  jets := ActualSignedNativeProfiles.potential_profiles_jets s i
  contains k I w hw _ _ hc j hj := by
    classical
    change LocalPhysicalCopyBounds.slotSlow
      (((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).carrier k
        I.1
        |>.withChart j) ActualPolarCoverage.inner h I.1.val.1 slots.radius w ∈ _
    rw [ActualSignedPhysicalData.slotSlow_eq_nativeSlow ActualPolarCoverage.inner_pos]
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · let L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0) :=
        ⟨I.1.val,I.1.property,hL⟩
      have he := potentialCells_active s i L
      change (originalPotentialCells s i).cells I.1 = _ at he
      rw [he, ActualSignedExterior.potential_gap, ActualSignedPhysicalData.commonLift_zero] at hc
      exact ActualSignedNativeProfiles.closure_covers s L I.1 w hw hc.2
    · rw [potentialCells_inactive s i hL] at hc
      exact hc.elim
    exact hj

noncomputable def originalPressureCarrier :
    CarrierBounds ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)
      (originalPressureCells s) ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius
        where
  region _ L := ActualSignedNativeProfiles.region B N0 L
  open_region _ := ActualSignedNativeProfiles.region_open B N0
  jets := ActualSignedNativeProfiles.pressure_profiles_jets s
  contains k I w hw _ _ hc j hj := by
    classical
    change LocalPhysicalCopyBounds.slotSlow
      (((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).carrier k I.1
        |>.withChart j) ActualPolarCoverage.inner h I.1.val.1 slots.radius w ∈ _
    rw [ActualSignedPhysicalData.slotSlow_eq_nativeSlow ActualPolarCoverage.inner_pos]
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · let L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0) :=
        ⟨I.1.val,I.1.property,hL⟩
      have he := pressureCells_active s L
      change (originalPressureCells s).cells I.1 = _ at he
      rw [he, ActualSignedExterior.pressure_gap, ActualSignedPhysicalData.commonLift_zero] at hc
      exact ActualSignedNativeProfiles.closure_covers s L I.1 w hw hc.2
    · rw [pressureCells_inactive s hL] at hc
      exact hc.elim
    exact hj

/-- The actual assembled copies, extended by zero outside positive lift
time. Their fields agree with the original signed fields before t=1. -/
noncomputable def potentialCopies (i : Fin 3) : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)

noncomputable def pressureCopies : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)

noncomputable def potentialCells (i : Fin 3) : SupportCells (potentialCopies s i) :=
  PositiveTimeCopyFamily.gateCells (originalPotentialCells s i)

noncomputable def pressureCells : SupportCells (pressureCopies s) :=
  PositiveTimeCopyFamily.gateCells (originalPressureCells s)

noncomputable def potentialCarrier (i : Fin 3) :
    CarrierBounds (potentialCopies s i) (potentialCells s i)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius :=
  PositiveTimeCopyFamily.gateCarrier (originalPotentialCells s i) (originalPotentialCarrier s i)

noncomputable def pressureCarrier :
    CarrierBounds (pressureCopies s) (pressureCells s)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius :=
  PositiveTimeCopyFamily.gateCarrier (originalPressureCells s) (originalPressureCarrier s)

theorem potential_field_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    vectorSum (potentialCopies s) ActualPolarCoverage.inner h slots.radius w =
      ActualSignedExterior.potential s w :=
  PositiveTimeCopyFamily.vectorSum_eq _ _ _ _ hw

theorem pressure_field_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    ((pressureCopies s).sum ActualPolarCoverage.inner h slots.radius w).re =
      ActualSignedExterior.pressure s w :=
  congrArg Complex.re (PositiveTimeCopyFamily.sum_eq _ _ _ _ hw)

theorem potential_field_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    vectorSum (potentialCopies s) ActualPolarCoverage.inner h slots.radius =ᶠ[𝓝 w]
      ActualSignedExterior.potential s :=
  PositiveTimeCopyFamily.vectorSum_germ _ _ _ _ hw

theorem pressure_field_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (fun w => ((pressureCopies s).sum ActualPolarCoverage.inner h slots.radius w).re) =ᶠ[𝓝 w]
      ActualSignedExterior.pressure s := by
  filter_upwards [PositiveTimeCopyFamily.sum_germ
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)
    ActualPolarCoverage.inner h slots.radius hw] with y hy
  exact congrArg Complex.re hy


/-- The carrier coefficients remain jointly bounded after label selection
and the positive-time extension. -/
theorem singleton_frequencies_of_states
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active)
    (K : ActualSignedPhysicalData.NativeLabel
      ((ActualSignedExterior.family s).singleton L).active) :
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.p K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 ∧
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.pz K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 ∧
    |(((((ActualSignedExterior.family s).singleton L).primary K).pulse
      (((ActualSignedExterior.family s).singleton L).column K)).phase.x0 K.val.1)| ≤
      ActualPhaseJetBounds.phaseSize B N0 := by
  rw [ActualSignedReferenceGeometry.singleton_index_eq (ActualSignedExterior.family s) L K]
  exact ActualPhaseJetBounds.phase_constants_bound
    ((ActualSignedExterior.actualLabel L).2, (ActualSignedExterior.actualLabel L).1)

theorem potential_frequencies (i : Fin 3) (k : TorusInverse.Frequency) (L : BandLabel) :
    |((potentialCopies s i).carrier k L).angular| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((potentialCopies s i).carrier k L).axial| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((potentialCopies s i).carrier k L).radial| ≤ ActualPhaseJetBounds.phaseSize B N0 := by
  classical
  have he : (potentialCopies s i).carrier k L =
      ((ActualSignedExterior.family s).copyAt
        (fun M => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
          ((ActualSignedExterior.family s).singleton M) i) L).carrier k L := rfl
  rw [he]
  by_cases hL : L ∈ (ActualSignedExterior.family s).active
  · let M : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active :=
      ⟨L.val, L.property, hL⟩
    rw [DependentSignedPhysicalFamily.Family.copyAt_active _ _ M]
    exact ActualSignedPhysicalData.carrier_frequencies
      ((ActualSignedExterior.family s).singleton M) ActualPhaseJetBounds.one_le_phaseSize
      (singleton_frequencies_of_states s M) k L
  · rw [DependentSignedPhysicalFamily.Family.copyAt_inactive _ _ hL]
    have hP := zero_le_one.trans (ActualPhaseJetBounds.one_le_phaseSize (B := B) (N0 := N0))
    exact ⟨by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP⟩

theorem pressure_frequencies (k : TorusInverse.Frequency) (L : BandLabel) :
    |((pressureCopies s).carrier k L).angular| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((pressureCopies s).carrier k L).axial| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |((pressureCopies s).carrier k L).radial| ≤ ActualPhaseJetBounds.phaseSize B N0 := by
  classical
  have he : (pressureCopies s).carrier k L =
      ((ActualSignedExterior.family s).copyAt
        (fun M => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
          ((ActualSignedExterior.family s).singleton M)) L).carrier k L := rfl
  rw [he]
  by_cases hL : L ∈ (ActualSignedExterior.family s).active
  · let M : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active :=
      ⟨L.val, L.property, hL⟩
    rw [DependentSignedPhysicalFamily.Family.copyAt_active _ _ M]
    exact ActualSignedPhysicalData.carrier_frequencies
      ((ActualSignedExterior.family s).singleton M) ActualPhaseJetBounds.one_le_phaseSize
      (singleton_frequencies_of_states s M) k L
  · rw [DependentSignedPhysicalFamily.Family.copyAt_inactive _ _ hL]
    have hP := zero_le_one.trans (ActualPhaseJetBounds.one_le_phaseSize (B := B) (N0 := N0))
    exact ⟨by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP,
      by simpa [DependentSignedPhysicalFamily.zeroCopies] using hP⟩

/-! ## The jointly indexed Cartesian sources -/

noncomputable def sourceStrip : WeightedClasses.StripData PhysicalGraphBounds.LiftPoint :=
  CartesianCopySource.pullStrip ActualPrimaryBounds.strip
    ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos

noncomputable def potentialSource :
    (Fin 3 × SourceIndex) → ℕ → PhysicalGraphBounds.LiftPoint → ℂ :=
  fun I n x => CartesianCopySource.rotatedSource
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le)) I.2 n x I.1

noncomputable def pressureSource : SourceIndex → ℕ → PhysicalGraphBounds.LiftPoint → ℂ :=
  fun I n x => DependentSignedPhysicalFamily.jointSource
    ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le) I n
      (PhysicalClassBounds.cylindricalMap x)

noncomputable def sourceWeight (_ : SourceIndex) (_ : ℕ)
    (x : PhysicalGraphBounds.LiftPoint) : ℝ :=
  Real.sqrt (ActualPrimaryBounds.strip.zeta (PhysicalClassBounds.cylindricalMap x))

noncomputable def potentialWeight (I : Fin 3 × SourceIndex) (n : ℕ)
    (x : PhysicalGraphBounds.LiftPoint) : ℝ := sourceWeight I.2 n x

theorem potential_amplitude_eq_source (i : Fin 3) (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k I
      x =
      ChartScales.Q I.1.val.1 ^ (-h) • potentialSource s (i, ⟨I.1, (I, k)⟩) I.1.val.1 x :=
  DependentSignedPhysicalFamily.Family.potential_amplitude_eq_source _ _ _ _ _ _ _

theorem pressure_amplitude_eq_source (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k I x =
      ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) •
        pressureSource s ⟨I.1, (I, k)⟩ I.1.val.1 x :=
  DependentSignedPhysicalFamily.Family.pressure_amplitude_eq_source _ _ _ _ _ _

theorem potential_source_bounds {α : ℝ}
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le))) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip h α potentialWeight (potentialSource s) :=
  ActualSignedPhysicalData.componentSourceBounds
    (CartesianCopySource.sourceBounds_rotated (b := ActualPolarCoverage.outer)
      ActualPolarCoverage.inner_pos hs)

theorem pressure_source_bounds {α : ℝ}
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le))) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip h α sourceWeight (pressureSource s) :=
  CartesianCopySource.sourceBounds_pullback (b := ActualPolarCoverage.outer)
    ActualPolarCoverage.inner_pos hs

end CopyFamilies


section NativeAssembly

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
  (hgeo : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.ReferenceGeometry slots ((ActualSignedExterior.family s).singleton L))
  (hn : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.NativeRegular slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L))
  {α : ℝ}

/-- The physical potential datum is assembled once over all source labels.
The source estimate and profile constants are chosen before those labels. -/
noncomputable def potentialOfNative
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le))) :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) where
  lowerRadius := ActualPolarCoverage.inner
  upperRadius := ActualPolarCoverage.outer
  nativeWidth := slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := α
  shift := -h
  harmonics := 1
  gapBound := 0
  lower_pos := ActualPolarCoverage.inner_pos
  width_nonneg := slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight := potentialWeight
  source := potentialSource s
  source_bounds := potential_source_bounds s hs
  copies := potentialCopies s
  cells := potentialCells s
  chart i := PositiveTimeSignedData.identitySourceChart _ (originalPotentialCells s i)
    ActualPolarCoverage.inner_pos (ActualSignedFamilySupport.potential_support s hgeo i)
    sourceStrip (potentialSource s) (fun k I => (i, ⟨I.1, (I, k)⟩))
    (potential_amplitude_eq_source s i)
    (ActualSignedFamilySupport.potential_source_domain s i)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier := potentialCarrier s
  support := ActualSignedFamilySupport.potential_support s hgeo
  smooth := ActualSignedFamilySupport.potential_smooth s hgeo hn
  frequencies := potential_frequencies s

noncomputable def pressureOfNative
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
      (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
      (DependentSignedPhysicalFamily.jointSource
        ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le))) :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit where
  lowerRadius := ActualPolarCoverage.inner
  upperRadius := ActualPolarCoverage.outer
  nativeWidth := slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := α
  shift := -(2 * CoordinateAlgebra.A h)
  harmonics := 1
  gapBound := 0
  lower_pos := ActualPolarCoverage.inner_pos
  width_nonneg := slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight := sourceWeight
  source := pressureSource s
  source_bounds := pressure_source_bounds s hs
  copies _ := pressureCopies s
  cells _ := pressureCells s
  chart _ := PositiveTimeSignedData.identitySourceChart _ (originalPressureCells s)
    ActualPolarCoverage.inner_pos (ActualSignedFamilySupport.pressure_support s hgeo)
    sourceStrip (pressureSource s) (fun k I => ⟨I.1, (I, k)⟩)
    (pressure_amplitude_eq_source s)
    (ActualSignedFamilySupport.pressure_source_domain s)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier _ := pressureCarrier s
  support _ := ActualSignedFamilySupport.pressure_support s hgeo
  smooth _ := ActualSignedFamilySupport.pressure_smooth s hgeo hn
  frequencies _ := pressure_frequencies s

variable
  (hpotential : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
    (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).potentialSource slots outgoing.data.h_pos.le)))
  (hpressure : LocalPhysicalCopyBounds.LocalSourceBounds ActualPrimaryBounds.strip h α
    (fun (_ : SourceIndex) _ y => Real.sqrt (ActualPrimaryBounds.strip.zeta y))
    (DependentSignedPhysicalFamily.jointSource
      ((ActualSignedExterior.family s).pressureSource slots outgoing.data.h_pos.le)))

@[simp] theorem potentialOfNative_alpha :
    (potentialOfNative s hgeo hn hpotential).alpha = α := rfl

@[simp] theorem pressureOfNative_alpha :
    (pressureOfNative s hgeo hn hpressure).alpha = α := rfl

@[simp] theorem potentialOfNative_shift :
    (potentialOfNative s hgeo hn hpotential).shift = -h := rfl

@[simp] theorem pressureOfNative_shift :
    (pressureOfNative s hgeo hn hpressure).shift = -(2 * CoordinateAlgebra.A h) := rfl

theorem potentialOfNative_vector_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (potentialOfNative s hgeo hn hpotential).vector w = ActualSignedExterior.potential s w :=
  potential_field_eq s hw

theorem pressureOfNative_pressure_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (pressureOfNative s hgeo hn hpressure).pressure w = ActualSignedExterior.pressure s w :=
  pressure_field_eq s hw

theorem potentialOfNative_vector_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (potentialOfNative s hgeo hn hpotential).vector =ᶠ[𝓝 w] ActualSignedExterior.potential s :=
  potential_field_germ s hw

theorem pressureOfNative_pressure_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (pressureOfNative s hgeo hn hpressure).pressure =ᶠ[𝓝 w] ActualSignedExterior.pressure s :=
  pressure_field_germ s hw

end NativeAssembly


section ActualProducers

open WeightedClasses

variable (u : State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)
  (α : ℝ)
  (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) u = u)
  (hθ : MeanClass ActualInitialization.geometry.strip α (u.thetaResidual (commonContext B)))
  (hz : MeanClass ActualInitialization.geometry.strip α (u.axialResidual (commonContext B)))

/-- Genuine primitive and measured residual data produce the entire
potential record. Native regularity and native output bounds are derived. -/
noncomputable def potentialFromResiduals :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) :=
  potentialOfNative (α := α) (nativeStates (N0 := N0) ActualInitialization.patch u H hp)
    (singletonGeometry ActualInitialization.patch u H hp)
    (ActualSignedNativeRegularity.nativeRegular_from_residuals u H hp α hfixed hθ hz)
    (by
      have hb := ActualSignedNativeBounds.source_bounds ActualInitialization.patch u H hp
        (ActualSignedNativeRegularity.request_jets_from_residuals
          (N0 := N0) u α H hfixed hθ hz)
      have he := hb.1
      simp only [sub_add_cancel] at he
      exact he)

noncomputable def pressureFromResiduals :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit :=
  pressureOfNative (α := α) (nativeStates (N0 := N0) ActualInitialization.patch u H hp)
    (singletonGeometry ActualInitialization.patch u H hp)
    (ActualSignedNativeRegularity.nativeRegular_from_residuals u H hp α hfixed hθ hz)
    (by
      have hb := ActualSignedNativeBounds.source_bounds ActualInitialization.patch u H hp
        (ActualSignedNativeRegularity.request_jets_from_residuals
          (N0 := N0) u α H hfixed hθ hz)
      have he := hb.2
      simp only [sub_add_cancel] at he
      exact he)

@[simp] theorem potentialFromResiduals_alpha :
    (potentialFromResiduals (N0 := N0) u H hp α hfixed hθ hz).alpha = α := rfl

@[simp] theorem pressureFromResiduals_alpha :
    (pressureFromResiduals (N0 := N0) u H hp α hfixed hθ hz).alpha = α := rfl

@[simp] theorem potentialFromResiduals_shift :
    (potentialFromResiduals (N0 := N0) u H hp α hfixed hθ hz).shift = -h := rfl

@[simp] theorem pressureFromResiduals_shift :
    (pressureFromResiduals (N0 := N0) u H hp α hfixed hθ hz).shift =
      -(2 * CoordinateAlgebra.A h) := rfl

end ActualProducers

section Cycle

variable {σ : ℝ} (x : CycleState (Label B N0))
  (R : ActualParticularMeanGain.Result x σ)

/-- The post-particular theorem supplies every analytic hypothesis; the
physical copies use its same reconstructed state and pressure primitive. -/
noncomputable def cyclePotentialData :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      (Fin 3 × SourceIndex) TorusInverse.Frequency (Fin 3) :=
  potentialFromResiduals (N0 := N0) (ActualParticularMeanGain.postParticular x) R.primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)
    (1 + σ - ChartScales.kappa) R.reconstructed R.theta R.axial

noncomputable def cyclePressureData :
    PhysicalStageBounds.WaveData h PhysicalGraphBounds.LiftPoint
      SourceIndex TorusInverse.Frequency Unit :=
  pressureFromResiduals (N0 := N0) (ActualParticularMeanGain.postParticular x) R.primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)
    (1 + σ - ChartScales.kappa) R.reconstructed R.theta R.axial

@[simp] theorem cyclePotentialData_alpha :
    (cyclePotentialData x R).alpha = 1 + σ - ChartScales.kappa := rfl

@[simp] theorem cyclePressureData_alpha :
    (cyclePressureData x R).alpha = 1 + σ - ChartScales.kappa := rfl

@[simp] theorem cyclePotentialData_shift : (cyclePotentialData x R).shift = -h := rfl

@[simp] theorem cyclePressureData_shift :
    (cyclePressureData x R).shift = -(2 * CoordinateAlgebra.A h) := rfl

theorem cyclePotentialData_eq : EqOn (cyclePotentialData x R).vector
    (ActualSignedExterior.cyclePotential x R.primitive
      (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) preterminal :=
  fun _ hw => potential_field_eq _ hw

theorem cyclePressureData_eq : EqOn (cyclePressureData x R).pressure
    (ActualSignedExterior.cyclePressure x R.primitive
      (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) preterminal :=
  fun _ hw => pressure_field_eq _ hw

theorem cyclePotentialData_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (cyclePotentialData x R).vector =ᶠ[𝓝 w]
      ActualSignedExterior.cyclePotential x R.primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive) :=
  potential_field_germ _ hw

theorem cyclePressureData_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (cyclePressureData x R).pressure =ᶠ[𝓝 w]
      ActualSignedExterior.cyclePressure x R.primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive) :=
  pressure_field_germ _ hw

/-- A consequence for the original signed potential, including every
ambient time and spatial derivative. -/
theorem cyclePotential_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (ActualSignedExterior.cyclePotential x R.primitive
          (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) w‖ ≤
        C * physicalQ h w ^ (h * (1 + σ - ChartScales.kappa) -
          PhysicalClassBounds.physicalLoss h (-h) m) := by
  obtain ⟨C, hC, hb⟩ := (cyclePotentialData x R).vector_bound
    outgoing.data.h_pos outgoing.data.h_lt_half m
  refine ⟨C, hC, fun w hw hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (cyclePotentialData_germ x R hw) m]
  exact hb w hw hq

theorem cyclePressure_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (ActualSignedExterior.cyclePressure x R.primitive
          (ActualSignedPhysicalBinding.afterParticular_pressure x R.primitive)) w‖ ≤
        C * physicalQ h w ^ (h * (1 + σ - ChartScales.kappa) -
          PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) := by
  obtain ⟨C, hC, hb⟩ := (cyclePressureData x R).pressure_bound
    outgoing.data.h_pos outgoing.data.h_lt_half m
  refine ⟨C, hC, fun w hw hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (cyclePressureData_germ x R hw) m]
  exact hb w hw hq

end Cycle

/-! ## The actual infinite stage sequence -/

theorem stageResult (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularMeanGain.Result (ActualCyclePreservation.state B N0 j)
      (ActualIterationLedger.sigma j) :=
  ActualParticularMeanGain.postParticular_gain
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_particularInputs B N0 hN j)
    (ActualIterationLedger.sigma_admissible j)

/-- The actual signed part of the schedule. There is no input WaveData,
physical bound or native output-regularity hypothesis. -/
noncomputable def signedInputs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    GluedStageEstimates.SignedInputs PhysicalGraphBounds.LiftPoint SourceIndex
      TorusInverse.Frequency where
  potential j := cyclePotentialData (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)
  pressure j := cyclePressureData (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)
  potential_exponent j := by
    change 1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
      1 + ActualIterationLedger.sigma j - ChartScales.kappa
    linarith
  pressure_exponent _ := le_rfl
  potential_shift _ := rfl
  pressure_shift _ := rfl

theorem signedInputs_potential_eq (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((signedInputs B N0 hN).potential j).vector
      (ActualSignedExterior.cyclePotential (ActualCyclePreservation.state B N0 j)
        (stageResult B N0 hN j).primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCyclePreservation.state B N0 j)
          (stageResult B N0 hN j).primitive)) preterminal :=
  cyclePotentialData_eq (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)

theorem signedInputs_pressure_eq (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((signedInputs B N0 hN).pressure j).pressure
      (ActualSignedExterior.cyclePressure (ActualCyclePreservation.state B N0 j)
        (stageResult B N0 hN j).primitive
        (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCyclePreservation.state B N0 j)
          (stageResult B N0 hN j).primitive)) preterminal :=
  cyclePressureData_eq (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)

end NavierStokes.ActualSignedWaveData
