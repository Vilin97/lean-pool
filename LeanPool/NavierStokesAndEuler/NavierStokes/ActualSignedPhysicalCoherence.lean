/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPotentialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalPrefixFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedReferenceGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCurrentSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalZeros
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedPhysicalSumCalculus

@[expose] public section

/-!
# The canonical signed physical family and its current-band realization

The dependent family, both signed labels, and its positive physical harmonic
are retained.  Native faces are treated by the literal zero mask before a
current-band comparison is used.
-/

noncomputable section

namespace NavierStokes.ActualSignedPhysicalCoherence

open Set Function Filter HarmonicCalculus PhysicalWaveSum PhysicalCopyBounds
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

abbrev Label (B N0 : ℕ) := ActualSignedPhysicalBinding.Label B N0
abbrev Point := ActualSignedCoherence.Point
abbrev FullPoint := ActualSignedCoherence.FullPoint
abbrev SpaceTime := ProblemStatement.SpaceTime
abbrev Frequency := TorusInverse.Frequency

variable {B N0 : ℕ}

section FiniteSums

variable {α β V : Type*} [AddCommMonoid V]

theorem finsum_injective_support (e : α → β) (he : Injective e) (f : β → V)
    (hz : ∀ b, b ∉ range e → f b = 0) :
    (∑ᶠ b, f b) = ∑ᶠ a, f (e a) := by
  calc
    _ = ∑ᶠ b ∈ range e, f b := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro b
      by_cases hb : b ∈ range e
      · simp only [indicator_of_mem hb]
      · simp only [indicator_of_notMem hb, hz b hb]
    _ = _ := finsum_mem_range he

theorem finsum_finite_support (s : Finset α) (f : α → V)
    (hz : ∀ a, a ∉ s → f a = 0) : (∑ᶠ a, f a) = ∑ a ∈ s, f a := by
  apply finsum_eq_sum_of_support_subset
  intro a ha
  by_contra hn
  exact ha (hz a hn)

end FiniteSums

noncomputable def physicalIndex (l : Label B N0) : WaveIndex 1 :=
  ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)

theorem physicalIndex_injective : Injective (physicalIndex (B := B) (N0 := N0)) := by
  intro l k he
  apply ActualSignedExterior.bandLabel_injective
  exact congrArg Prod.fst he

theorem mem_range_physicalIndex (I : WaveIndex 1) :
    I ∈ range (physicalIndex (B := B) (N0 := N0)) ↔
      I.1 ∈ ActualSignedExterior.labels B N0 ∧ I.2.val = 1 := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Set.mem_range_self l, rfl⟩
  · rintro ⟨⟨l, hl⟩, hj⟩
    refine ⟨l, Prod.ext hl ?_⟩
    exact Subtype.ext hj.symm

section PositiveHarmonic

variable (f : DependentSignedPhysicalFamily.Family)

theorem potential_amplitude_zero_unless (i : Fin 3) (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (x : PhysicalGraphBounds.LiftPoint) :
    (f.potentialCopies slots outgoing.data.h_pos.le i).amplitude k I x = 0 := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.potentialFamily slots
    outgoing.data.h_pos.le (f.singleton L) i) I.1).amplitude k I x = 0
  by_cases hI : I.1 ∈ f.active
  · rw [f.copyAt_active _ (⟨I.1.val, I.1.property, hI⟩ : ActualSignedPhysicalData.NativeLabel
    f.active)]
    have hj : I.2.val ≠ 1 := hbad.resolve_left (not_not.mpr hI)
    simp [ActualSignedPhysicalData.potentialFamily, hj]
  · rw [f.copyAt_inactive _ hI]
    rfl

theorem pressure_amplitude_zero_unless (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (x : PhysicalGraphBounds.LiftPoint) :
    (f.pressureCopies slots outgoing.data.h_pos.le).amplitude k I x = 0 := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.pressureFamily slots
    outgoing.data.h_pos.le (f.singleton L)) I.1).amplitude k I x = 0
  by_cases hI : I.1 ∈ f.active
  · rw [f.copyAt_active _ (⟨I.1.val, I.1.property, hI⟩ : ActualSignedPhysicalData.NativeLabel
    f.active)]
    have hj : I.2.val ≠ 1 := hbad.resolve_left (not_not.mpr hI)
    simp [ActualSignedPhysicalData.pressureFamily, hj]
  · rw [f.copyAt_inactive _ hI]
    rfl

theorem potential_term_zero_unless (i : Fin 3) (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (a r0 : ℝ) (w : SpaceTime) :
    (f.potentialCopies slots outgoing.data.h_pos.le i).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  exact potential_amplitude_zero_unless f i I hbad k _

theorem pressure_term_zero_unless (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (a r0 : ℝ) (w : SpaceTime) :
    (f.pressureCopies slots outgoing.data.h_pos.le).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  exact pressure_amplitude_zero_unless f I hbad k _

end PositiveHarmonic

section CanonicalSums

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

theorem potential_sum_labels (i : Fin 3) (a r0 : ℝ) (w : SpaceTime) :
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).sum a h r0 w =
      ∑ᶠ l : Label B N0,
        ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).periodized
          a h r0 (physicalIndex l) w := by
  unfold CopyFamily.sum
  apply finsum_injective_support physicalIndex physicalIndex_injective
  intro I hI
  have hbad : I.1 ∉ (ActualSignedExterior.family s).active ∨ I.2.val ≠ 1 := by
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · right
      intro hj
      exact hI ((mem_range_physicalIndex I).mpr ⟨hL, hj⟩)
    · exact Or.inl hL
  change (∑' k, ((ActualSignedExterior.family s).potentialCopies slots
    outgoing.data.h_pos.le i).term a h r0 I k w) = 0
  simp only [potential_term_zero_unless _ i I hbad, tsum_zero]

theorem pressure_sum_labels (a r0 : ℝ) (w : SpaceTime) :
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).sum a h r0 w =
      ∑ᶠ l : Label B N0,
        ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).periodized
          a h r0 (physicalIndex l) w := by
  unfold CopyFamily.sum
  apply finsum_injective_support physicalIndex physicalIndex_injective
  intro I hI
  have hbad : I.1 ∉ (ActualSignedExterior.family s).active ∨ I.2.val ≠ 1 := by
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · right
      intro hj
      exact hI ((mem_range_physicalIndex I).mpr ⟨hL, hj⟩)
    · exact Or.inl hL
  change (∑' k, ((ActualSignedExterior.family s).pressureCopies slots
    outgoing.data.h_pos.le).term a h r0 I k w) = 0
  simp only [pressure_term_zero_unless _ I hbad, tsum_zero]

end CanonicalSums

/-! ## The exact native-to-common physical graph -/

theorem toCommon_nativeGraph (l : Label B N0) (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedPhysicalBinding.toCommonCylinder l
      ((PhysicalResidualBridge.commonGraph
        (ChartScales.Q (ActualSignedPhysicalBinding.reference l)) h
        (ChartScales.nativeIndex h (ActualSignedPhysicalBinding.reference l))).map z) =
      ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z := by
  let m := ActualSignedPhysicalBinding.reference l
  have he (Y : TorusInverse.Plane) :
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h m - CommonWindow.index h m)).symm
        ((SlotGeometry.cover ^ ChartScales.nativeIndex h m) Y) =
          (SlotGeometry.cover ^ CommonWindow.index h m) Y := by
    apply (CommonCoverSolve.coverPower
      (ChartScales.nativeIndex h m - CommonWindow.index h m)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [← CommonCoverSolve.coverPower_apply, ← CommonCoverSolve.coverPower_apply]
    rw [← CopySolveCompatibility.coverPower_add,
      Nat.sub_add_cancel (CommonWindow.index_le_native h m)]
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    ActualSignedPhysicalBinding.toCommonCylinder_apply, PhysicalResidualTZ.swapCylinder_apply]
  exact congrArg (fun Y => ((ChartScales.Q m ^ (-(1 / 2 : ℝ)) * z.2 0,
    (((1 - z.1) / ChartScales.Q m, ChartScales.Q m ^ (-CoordinateAlgebra.D h) * z.2 2), Y)), z.2 1))
      (he _)

theorem nativePoint_radius (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.1 =
      ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0 := by
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]

theorem nativePoint_time (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.2.1.1 = (1 - z.1) / ChartScales.Q n := by
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]

section ReferenceAlgebra

variable (l : Label B N0) (P : SignedStressPrimitive.Patch) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)

theorem reference_cutoff_formula (k : Frequency) (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).cutoff
        (ActualSignedPhysicalBinding.reference l) k x =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
          0).coordinates
          k x.1.2.2) := by
  simp only [ActualSignedPhysicalBinding.referenceCopies, ActualSignedPhysicalData.dynamicCopyData,
    ActualSignedPhysicalBinding.nativeViews_map]
  rfl

theorem reference_raw_amplitude (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.amplitude
        (ActualSignedPhysicalBinding.reference l) x =
      (ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).raw
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l) x := by
  rw [ActualPeriodizedSignedRealization.reference_raw_eq_sum]
  change (∑' k : Frequency, _ •
    (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
      (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.nativeViews l)
      (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2 k).amplitude
        (ActualSignedPhysicalBinding.reference l) x) = _
  apply tsum_congr
  intro k
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  rw [ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_amplitude_at]
  simp only [ActualSignedPhysicalBinding.nativeViews_map,
    ActualPeriodizedSignedRealization.nativeUnit]
  rw [reference_cutoff_formula]
  erw [ActualSignedPhysicalData.waveMask_eq_compact]
  rw [mul_smul]
  rfl

theorem reference_raw_pressure (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.pressure
        (ActualSignedPhysicalBinding.reference l) x =
      (ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).rawPressure
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l) x := by
  let A := ActualSignedPhysicalBinding.primary l
  let L := ActualSignedPhysicalBinding.layout l
  let R := (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest
  let m := ActualSignedPhysicalBinding.reference l
  have hs : SignedWaveUpdate.signedScalar
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).strip
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).matrix
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).target R
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).mask l.2 m x =
        L.mask m x.1.2.2 * ActualPeriodizedSignedRealization.referenceScalar A R l.2 m x :=
    ActualPeriodizedSignedRealization.signedScalar_mul_mask _ _ _ _ _ _ _ _ _
  symm
  change L.gaussian m x.1.2.2 •
    ((ActualPeriodizedSignedRealization.periodizedPrimary A L).coefficients R l.2).pressure m x = _
  rw [PhysicalSignedWave.PrimaryData.coefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at, hs, mul_smul,
    ← L.gaussian_mask_sum]
  change (∑' k : Frequency, _) = ∑' k : Frequency,
    (_ : ℝ) • (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
      A (ActualSignedPhysicalBinding.nativeViews l) R l.2 k).pressure m x
  apply tsum_congr
  intro k
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq,
    ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at]
  simp only [ActualPeriodizedSignedRealization.nativeUnit,
    ActualSignedPhysicalBinding.nativeViews_map, Complex.ofReal_re]
  rw [reference_cutoff_formula]
  change L.nativeGaussian m k x.1.2.2 • (L.nativeMask m k x.1.2.2 •
    (ActualPeriodizedSignedRealization.referenceScalar A R l.2 m x • _)) =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
          0).coordinates
          k x.1.2.2) • (_ : ℂ)
  by_cases hk : L.nativeMask m k x.1.2.2 = 0
  · have hk' : ActualSignedPhysicalData.nativeMask slots (ActualSignedPhysicalBinding.spatialLabel
    l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
          0).coordinates
          k x.1.2.2) = 0 := hk
    erw [ActualSignedPhysicalData.waveMask_eq_compact]
    simp only [hk, zero_smul, smul_zero, hk', zero_mul]
  · rw [ActualPeriodizedSignedRealization.referenceUnit_eq_native A L _ _ _ _ hk]
    erw [ActualSignedPhysicalData.waveMask_eq_compact]
    change L.nativeGaussian m k x.1.2.2 • (L.nativeMask m k x.1.2.2 • (_ : ℂ)) =
      (L.nativeMask m k x.1.2.2 * L.nativeGaussian m k x.1.2.2) • _
    exact (smul_comm (L.nativeGaussian m k x.1.2.2) (L.nativeMask m k x.1.2.2) _).trans
      (mul_smul (L.nativeMask m k x.1.2.2) (L.nativeGaussian m k x.1.2.2) _).symm

theorem reference_vectorMode (x : FullPoint) :
    vectorMode ((ActualSignedPhysicalBinding.primary l).base.frequency
        (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      (fun y => CurlClassBounds.inverseCarrier
          ((ActualSignedPhysicalBinding.primary l).base.frequency
            (ActualSignedPhysicalBinding.reference l)) •
        CurlClassBounds.normalCoefficient
          ((ActualSignedPhysicalBinding.primary l).base.normal
            (ActualSignedPhysicalBinding.primary l).strip (ActualSignedPhysicalBinding.primary
              l).directions
            (ActualSignedPhysicalBinding.reference l) y)
          ((ActualPeriodizedSignedRealization.periodizedPrimary
            (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).raw
              (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
              (ActualSignedPhysicalBinding.reference l) y)) x =
      (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.curlPotential
        (ActualSignedPhysicalBinding.primary l).strip (ActualSignedPhysicalBinding.primary
          l).directions
        (ActualSignedPhysicalBinding.reference l) x := by
  let C := ActualSignedPhysicalBinding.referenceCopies l P u H hp
  let m := ActualSignedPhysicalBinding.reference l
  have hK : C.common.frequency m = (ActualSignedPhysicalBinding.primary l).base.frequency m :=
    congrArg (fun c => c.frequency m) (ActualSignedPhysicalBinding.reference_background l P u H hp)
  have hPhi : C.common.phase m = (ActualSignedPhysicalBinding.primary l).base.phase m :=
    congrArg (fun c => c.phase m) (ActualSignedPhysicalBinding.reference_background l P u H hp)
  change _ = vectorMode (C.common.frequency m) (C.common.phase m)
    (fun y => CurlClassBounds.inverseCarrier (C.common.frequency m) •
      CurlClassBounds.normalCoefficient (C.common.normal (ActualSignedPhysicalBinding.primary
        l).strip
        (ActualSignedPhysicalBinding.primary l).directions m y) (C.common.amplitude m y)) x
  rw [hK, hPhi, ActualSignedPhysicalBinding.reference_common_normal]
  dsimp only [C, m]
  simp_rw [reference_raw_amplitude l P u H hp]

theorem reference_pressureMode (x : FullPoint) :
    mode ((ActualSignedPhysicalBinding.primary l).base.frequency
      (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      ((ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).rawPressure
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l)) x =
      mode ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.frequency
          (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.phase
          (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.pressure
          (ActualSignedPhysicalBinding.reference l)) x := by
  have hK : (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.frequency
      (ActualSignedPhysicalBinding.reference l) =
      (ActualSignedPhysicalBinding.primary l).base.frequency (ActualSignedPhysicalBinding.reference
        l) :=
    congrArg (fun c => c.frequency (ActualSignedPhysicalBinding.reference l))
      (ActualSignedPhysicalBinding.reference_background l P u H hp)
  have hPhi : (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.phase
      (ActualSignedPhysicalBinding.reference l) =
      (ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l)
        :=
    congrArg (fun c => c.phase (ActualSignedPhysicalBinding.reference l))
      (ActualSignedPhysicalBinding.reference_background l P u H hp)
  unfold mode carrier
  rw [reference_raw_pressure, hK, hPhi]

end ReferenceAlgebra

noncomputable def measuredStates (P : SignedStressPrimitive.Patch) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  fun l => ActualSignedPhysicalBinding.nativeStateData l P u H hp

noncomputable def singletonVectorMode
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (x : FullPoint) : ComplexVector :=
  let f := (ActualSignedExterior.family s).singleton (ActualSignedExterior.nativeLabel l)
  let L := (ActualSignedExterior.family s).singletonLabel (ActualSignedExterior.nativeLabel l)
  vectorMode ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
    (ActualSignedPhysicalData.referencePotentialCoefficient slots outgoing.data.h_pos.le f L) x

noncomputable def singletonPressureMode
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (x : FullPoint) : ℂ :=
  let f := (ActualSignedExterior.family s).singleton (ActualSignedExterior.nativeLabel l)
  let L := (ActualSignedExterior.family s).singletonLabel (ActualSignedExterior.nativeLabel l)
  mode ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
    ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
      (ActualSignedPhysicalData.layout slots outgoing.data.h_pos.le L.val L.property 0)).rawPressure
        (f.state L).referenceRequest (f.column L) L.val.1) x

section MeasuredModes

variable (l : Label B N0) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)

theorem singletonVectorMode_eq (x : FullPoint) :
    singletonVectorMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l x =
      ActualSignedPotentialCoherence.potential l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
  have he := (reference_vectorMode l ActualInitialization.patch u H hp x).trans
    (ActualSignedPhysicalBinding.curlPotential_reference l ActualInitialization.patch u H hp x)
  apply Eq.trans ?_ he
  funext i
  dsimp only [singletonVectorMode, vectorMode, mode,
    ActualSignedPhysicalData.referencePotentialCoefficient]
  erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest,
    ActualSignedExterior.family_referenceRequest_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  dsimp only [ActualSignedExterior.family, DependentSignedPhysicalFamily.Family.singletonLabel]
  generalize_proofs
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl

theorem singletonPressureMode_eq (x : FullPoint) :
    singletonPressureMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l x =
      ActualSignedPotentialCoherence.pressureMode l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
  have he : mode ((ActualSignedPhysicalBinding.primary l).base.frequency
      (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      ((ActualPeriodizedSignedRealization.periodizedPrimary (ActualSignedPhysicalBinding.primary l)
        (ActualSignedPhysicalBinding.layout l)).rawPressure
        (ActualSignedPhysicalBinding.nativeStateData l ActualInitialization.patch u H
          hp).referenceRequest l.2
        (ActualSignedPhysicalBinding.reference l)) x =
      ActualSignedPotentialCoherence.pressureMode l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
    rw [reference_pressureMode l ActualInitialization.patch u H hp x]
    unfold mode carrier
    rw [← ActualSignedPhysicalBinding.common_pressure_reference,
      ActualSignedPhysicalBinding.reference_phase]
    rfl
  apply Eq.trans ?_ he
  dsimp only [singletonPressureMode, mode]
  erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest,
    ActualSignedExterior.family_referenceRequest_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  dsimp only [ActualSignedExterior.family, DependentSignedPhysicalFamily.Family.singletonLabel]
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl

end MeasuredModes

noncomputable def canonicalPotential
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (w : SpaceTime) : ComplexVector := fun i =>
  ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).periodized
    ActualPolarCoverage.inner h slots.radius (physicalIndex l) w

noncomputable def canonicalPressure
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (w : SpaceTime) : ℂ :=
  ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).periodized
    ActualPolarCoverage.inner h slots.radius (physicalIndex l) w

section NativeRepresentation

variable (l : Label B N0) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)

theorem canonicalPotential_native (w : SpaceTime) (j : PolarCharts.Index)
    (hw : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PhysicalGraphBounds.annulus ActualPolarCoverage.inner ActualPolarCoverage.outer)
    (hj : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PolarCharts.chartDomain ActualPolarCoverage.inner j) :
    canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPhysicalData.rotateCoefficient
        (PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w)
        (ActualSignedPotentialCoherence.cylindricalPotential l u
          (ActualSignedPhysicalBinding.reference l)
          (PhysicalCurlCovariance.polarCoordinates
            (ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner
              (ActualSignedPhysicalBinding.reference l)) j w)) := by
  let s := measuredStates (N0 := N0) ActualInitialization.patch u H hp
  let f := ActualSignedExterior.family s
  let L := f.singletonLabel (ActualSignedExterior.nativeLabel l)
  let G := ActualSignedReferenceGeometry.nativeSingletonGeometry ActualInitialization.patch u H hp l
  have hr := (ActualSignedPhysicalData.polarCoordinates_valid
    (ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos
      (ActualSignedPhysicalBinding.reference l)) j
        (ActualSignedPhysicalGeometry.physical_chart_mem _ j hj)).1
  ext i
  change (f.potentialCopies slots outgoing.data.h_pos.le i).periodized _ _ _
    (ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)) w = _
  erw [DependentSignedPhysicalFamily.Family.potential_periodized_active]
  change (ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) i).periodized
      ActualPolarCoverage.inner h slots.radius (ActualSignedPhysicalData.positiveIndex L) w = _
  rw [ActualSignedPhysicalData.potential_periodized_of_chart slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) G L i ActualPolarCoverage.inner_pos w hw j
      hj]
  rw [← ActualSignedPhysicalData.rotateCoefficient_vectorMode,
    PhysicalGraphBounds.liftXY_physicalLift]
  change (ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-h) : ℝ) •
    ActualSignedPhysicalData.rotateCoefficient
      (PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w)
      (singletonVectorMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
        (ActualSignedPhysicalData.cylinderAt ActualPolarCoverage.inner j
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w))) i = _
  rw [singletonVectorMode_eq l u H hp,
    ActualSignedPhysicalGeometry.cylinderAt_physical_chart h _ ActualPolarCoverage.inner_pos j hj,
    toCommon_nativeGraph l _ hr]
  change _ = ActualSignedPhysicalData.rotateCoefficient _
    ((ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-h) : ℝ) • _) i
  rw [ActualSignedPhysicalData.rotateCoefficient_real_smul]
  rfl

theorem canonicalPressure_native (w : SpaceTime) (j : PolarCharts.Index)
    (hw : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PhysicalGraphBounds.annulus ActualPolarCoverage.inner ActualPolarCoverage.outer)
    (hj : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PolarCharts.chartDomain ActualPolarCoverage.inner j) :
    canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPotentialCoherence.cylindricalPressureMode l u
        (ActualSignedPhysicalBinding.reference l)
        (PhysicalCurlCovariance.polarCoordinates
          (ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner
            (ActualSignedPhysicalBinding.reference l)) j w) := by
  let s := measuredStates (N0 := N0) ActualInitialization.patch u H hp
  let f := ActualSignedExterior.family s
  let L := f.singletonLabel (ActualSignedExterior.nativeLabel l)
  let G := ActualSignedReferenceGeometry.nativeSingletonGeometry ActualInitialization.patch u H hp l
  have hr := (ActualSignedPhysicalData.polarCoordinates_valid
    (ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos
      (ActualSignedPhysicalBinding.reference l)) j
        (ActualSignedPhysicalGeometry.physical_chart_mem _ j hj)).1
  change (f.pressureCopies slots outgoing.data.h_pos.le).periodized _ _ _
    (ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)) w = _
  erw [DependentSignedPhysicalFamily.Family.pressure_periodized_active]
  change (ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l))).periodized
      ActualPolarCoverage.inner h slots.radius (ActualSignedPhysicalData.positiveIndex L) w = _
  rw [ActualSignedPhysicalData.pressure_periodized_of_chart slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) G L ActualPolarCoverage.inner_pos w hw j hj]
  change (ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-(2 * CoordinateAlgebra.A h))
    : ℝ) •
    singletonPressureMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
      (ActualSignedPhysicalData.cylinderAt ActualPolarCoverage.inner j
        (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w)) = _
  rw [singletonPressureMode_eq l u H hp,
    ActualSignedPhysicalGeometry.cylinderAt_physical_chart h _ ActualPolarCoverage.inner_pos j hj,
    toCommon_nativeGraph l _ hr]
  rfl

end NativeRepresentation

/-! ## The two literal zero cases, including both native dyadic faces -/

theorem canonical_current_zero
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (u : CorrectionState.State Point) (n : ℕ)
    (w z : SpaceTime) (hr : 0 < z.2 0)
    (he : (z.1, CylindricalResidual.chart z.2) = w) (hw : w ∈ preterminal)
    (hbad : w ∉ ActualSignedExterior.active ∨
      physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    canonicalPotential s l w = 0 ∧ canonicalPressure s l w = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  have hwz : (z.1, CylindricalResidual.chart z.2) ∈ preterminal := by rwa [he]
  rcases hbad with hout | hq
  · have houtz : (z.1, CylindricalResidual.chart z.2) ∉ ActualSignedExterior.active := by rwa [he]
    refine ⟨?_, ?_, ActualSignedPhysicalZeros.cylindricalPotential_zero_of_exterior l u n z hr hwz
      houtz,
      ActualSignedPhysicalZeros.cylindricalPressureMode_zero_of_exterior l u n z hr hwz houtz⟩
    · ext i
      change (∑' k : Frequency, ((ActualSignedExterior.family s).potentialCopies
        slots outgoing.data.h_pos.le i).term ActualPolarCoverage.inner h slots.radius
          (physicalIndex l) k w) = 0
      simp only [ActualSignedExterior.potential_term_zero s _ _ _ _ _ hw hout, tsum_zero]
    · change (∑' k : Frequency, ((ActualSignedExterior.family s).pressureCopies
        slots outgoing.data.h_pos.le).term ActualPolarCoverage.inner h slots.radius
          (physicalIndex l) k w) = 0
      simp only [ActualSignedExterior.pressure_term_zero s _ _ _ _ hw hout, tsum_zero]
  · have hqz : physicalQ h (z.1, CylindricalResidual.chart z.2) /
        ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2 := by rwa [he]
    refine ⟨?_, ?_, ActualSignedPhysicalZeros.cylindricalPotential_zero_of_nativeQ l u n z hr hwz
      hqz,
      ActualSignedPhysicalZeros.cylindricalPressureMode_zero_of_nativeQ l u n z hr hwz hqz⟩
    · ext i
      exact ActualSignedPhysicalZeros.canonical_potential_periodized_zero_of_nativeQ
        s l i ActualPolarCoverage.inner slots.radius hw hq
    · exact ActualSignedPhysicalZeros.canonical_pressure_periodized_zero_of_nativeQ
        s l ActualPolarCoverage.inner slots.radius hw hq

theorem current_chart_ratio (n : ℕ) {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2 := by
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have he : (z.1, CylindricalResidual.chart z.2) = w :=
    ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
  have ht : (z.1, CylindricalResidual.chart z.2) ∈ preterminal := by rw [he]; exact hw.1.1
  have hn := ActualSignedCurrentSupport.physicalDomain_of_source n hw.2.2
  have hq : SimilarityCoordinates.coordinateQ (2 * h)
      (ActualSignedPotentialCoherence.nativePoint n z).1.2.1 ∈ Ioo (1 / 2 : ℝ) 2 := hn.2.2
  rw [ActualSignedPhysicalGeometry.nativePoint_slow n 0,
    PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n 0 ht, he] at hq
  exact hq

section CurrentRepresentation

variable (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)
  (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) u).pressure = u.pressure)
  (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
      (ActualInitialCoherence.overlap n m))
      (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
      (GaugeStateCoherence.bandScale n m) u u n m)

include hfixed HS

/-- The physical copy sum has the current-band value.  The last conclusion
is complex-valued: it justifies truncating the original complex sum before
taking real parts. -/
theorem canonical_current_values (l : Label B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    PhysicalCurlCovariance.realVector
        (canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w) =
      CurrentSignedCurl.currentPotential l u n a i w ∧
    (canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w).re =
      CurrentSignedCurl.currentPressure l u n a i w ∧
    (l ∉ activeLabels standardRegion B N0 n →
      canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w = 0 ∧
        canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w = 0) :=
          by
  by_cases hc : w ∈ ActualSignedExterior.active ∧
      physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∈ Ioo (1 / 2 : ℝ) 2
  · let m := ActualSignedPhysicalBinding.reference l
    obtain ⟨j, hj⟩ := ActualSignedPhysicalGeometry.chart_exists_of_ratio m hw.1.1 hc.1 hc.2
    let b := ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner m
    let z := PhysicalCurlCovariance.polarCoordinates b j w
    have hb : 0 < b := ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos m
    have hwb : w ∈ ActualMeanPotentialRealization.cartesianDomain b j :=
      ActualSignedPhysicalGeometry.physical_chart_mem m j hj
    have hm : z ∈ ActualSignedPotentialCoherence.physicalDomain m :=
      ActualSignedPhysicalGeometry.scaledChart_mem_physicalDomain m ActualPolarCoverage.inner_pos j
        hj
        hw.1.1 hc.2
    have hn : z ∈ ActualSignedPotentialCoherence.physicalDomain n :=
      ActualSignedPhysicalGeometry.polarCoordinates_mem_physicalDomain n hb j hwb hw.1.1
        (current_chart_ratio n ha i hw)
    have he := ActualSignedPotentialCoherence.cylindrical_values_eq l u H hfixed HS n m z hn hm
    have hann := ActualSignedPhysicalGeometry.annulus_of_ratio m hw.1.1 hc.1 hc.2
    have hv := canonicalPotential_native l u H hp w j hann hj
    have hpr := canonicalPressure_native l u H hp w j hann hj
    change canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPhysicalData.rotateCoefficient (PhysicalGraphBounds.scaledRadial m w)
        (ActualSignedPotentialCoherence.cylindricalPotential l u m z) at hv
    change canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPotentialCoherence.cylindricalPressureMode l u m z at hpr
    rw [← he.1] at hv
    rw [← he.2] at hpr
    have hangle : (PolarCharts.chart ActualPolarCoverage.inner j
        (PhysicalGraphBounds.scaledRadial m w)).2 = (PhysicalCurlCovariance.polarInput b j w).2 :=
          by
      have hh := congrArg Prod.snd (ActualSignedPhysicalGeometry.physical_chart_scale m
        ActualPolarCoverage.inner_pos j hj)
      exact hh
    have hvr : PhysicalCurlCovariance.realVector
        (canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w) =
        CurrentSignedCurl.currentPotential l u n b j w := by
      ext r
      rw [PhysicalCurlCovariance.realVector_apply, hv,
        ActualSignedPhysicalData.rotateCoefficient_chart_re ActualPolarCoverage.inner_pos j hj,
        hangle]
      rfl
    have hprr : (canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
      w).re =
        CurrentSignedCurl.currentPressure l u n b j w := congrArg Complex.re hpr
    refine ⟨hvr.trans (CurrentSignedCurl.currentPotential_overlap l u n hb ha j i hwb hw.2.1),
      hprr.trans (CurrentSignedCurl.currentPressure_overlap l u n hb ha j i hwb hw.2.1), ?_⟩
    intro hnot
    obtain ⟨hzv, hzp⟩ := ActualSignedCurrentSupport.cylindrical_zero l u n hn hnot
    rw [hzv, ActualSignedPhysicalData.rotateCoefficient_zero] at hv
    rw [hzp] at hpr
    exact ⟨hv, hpr⟩
  · have hbad : w ∉ ActualSignedExterior.active ∨
        physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2
          :=
      not_and_or.mp hc
    let z := PhysicalCurlCovariance.polarCoordinates a i w
    have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw.2.1).1
    have hback : (z.1, CylindricalResidual.chart z.2) = w :=
      ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
    obtain ⟨hv, hpr, hcv, hcp⟩ := canonical_current_zero
      (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l u n w z hr hback hw.1.1 hbad
    dsimp only [z] at hcv hcp
    have hzero : PhysicalCurlCovariance.realVector (0 : ComplexVector) = 0 := by ext r; simp
    refine ⟨?_, ?_, fun _ => ⟨hv, hpr⟩⟩
    · simp only [hv, CurrentSignedCurl.currentPotential, PhysicalCurlCovariance.cartesianPotential,
        hcv, hzero, map_zero]
    · simp only [hpr, CurrentSignedCurl.currentPressure, hcp, Complex.zero_re]

theorem measuredPotential_eq_sum (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.potential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) w =
      ∑ l ∈ v.labels n, CurrentSignedCurl.currentPotential l u n a i w := by
  unfold ActualSignedExterior.potential PhysicalCopyBounds.vectorSum
  simp_rw [potential_sum_labels]
  apply SignedPhysicalSumCalculus.realCoordinate_finsum_eq_sum
    (v.labels n) (fun l => canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch
      u H hp) l w)
  · intro l hn
    have hn' : l ∉ activeLabels standardRegion B N0 n := by simpa only [hlabels] using hn
    exact ((canonical_current_values u H hp hfixed HS l n ha i hw).2.2 hn').1
  · intro l
    exact (canonical_current_values u H hp hfixed HS l n ha i hw).1

theorem measuredPressure_eq_sum (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) w =
      ∑ l ∈ v.labels n, CurrentSignedCurl.currentPressure l u n a i w := by
  unfold ActualSignedExterior.pressure
  rw [pressure_sum_labels]
  apply SignedPhysicalSumCalculus.real_finsum_eq_sum
    (v.labels n) (fun l => canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch
      u H hp) l w)
  · intro l hn
    have hn' : l ∉ activeLabels standardRegion B N0 n := by simpa only [hlabels] using hn
    exact ((canonical_current_values u H hp hfixed HS l n ha i hw).2.2 hn').2
  · intro l
    exact (canonical_current_values u H hp hfixed HS l n ha i hw).2.1

theorem measuredPotential_germ (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.potential (measuredStates (N0 := N0) ActualInitialization.patch u H hp)
      =ᶠ[𝓝 w]
      fun z => ∑ l ∈ v.labels n, CurrentSignedCurl.currentPotential l u n a i z := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hw]
    with z hz
  exact measuredPotential_eq_sum u H hp hfixed HS v hlabels n ha i hz

theorem measuredPressure_germ (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp)
      =ᶠ[𝓝 w]
      fun z => ∑ l ∈ v.labels n, CurrentSignedCurl.currentPressure l u n a i z := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hw]
    with z hz
  exact measuredPressure_eq_sum u H hp hfixed HS v hlabels n ha i hz

theorem measuredPotential_curl (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {α : ℝ}
    (hamp : ∀ l ∈ v.labels n, CurrentSignedCurl.AmplitudeBound l u α)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (ActualSignedExterior.potential
        (measuredStates (N0 := N0) ActualInitialization.patch u H hp)))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ v.labels n, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (ActualSignedCoherence.request B u)).oscillation
              n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact (PhysicalCurlCovariance.spatialCurl_congr
    (measuredPotential_germ u H hp hfixed HS v hlabels n ha i hw)).trans
      (CurrentSignedCurl.currentPotential_sum_curl_map (v.labels n) u hamp n ha i hw)

theorem measuredPressure_eq (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H
      hp))
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ v.labels n, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (ActualSignedCoherence.request B
              u)).oscillatoryPressure n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  rw [measuredPressure_eq_sum u H hp hfixed HS v hlabels n ha i hw]
  simp only [CurrentSignedCurl.currentPressure_eq, map_sum, Finset.sum_apply]

end CurrentRepresentation

/-! ## The literal correction cycle's physical fields -/

noncomputable def cycleInput (x : CorrectionStep.CycleState (Label B N0)) :
    CorrectionState.State Point :=
  (ActualCycleParameters.fixedParameters B N0).afterParticular
    x.coefficients (commonContext B) x.state

section Cycle

variable (x : CorrectionStep.CycleState (Label B N0))
  (Hu : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) (cycleInput x))
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (cycleInput x).pressure)
  (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) (cycleInput x)).pressure = (cycleInput x).pressure)
  (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
      (ActualInitialCoherence.overlap n m))
      (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
      (GaugeStateCoherence.bandScale n m) (cycleInput x) (cycleInput x) n m)
  (hlabels : x.coefficients.labels = activeLabels standardRegion B N0)

include hfixed HS hlabels

/-- Curl is taken only after equality of the canonical physical potential
on an open neighborhood has been proved.  The sole analytic bound concerns
the actual current common amplitude. -/
theorem cyclePotential_curl (n : ℕ) {α : ℝ}
    (hamp : ∀ l ∈ x.coefficients.labels n, CurrentSignedCurl.AmplitudeBound l (cycleInput x) α)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (ActualSignedExterior.cyclePotential x Hu hp))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).signedVelocity
            x.coefficients (commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  have hv : (∑ l ∈ x.coefficients.labels n,
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B (cycleInput x))).oscillation n) =
      (ActualCycleParameters.fixedParameters B N0).signedVelocity
        x.coefficients (commonContext B) x.state n := by
    funext z j
    simp only [Finset.sum_apply, CorrectionStep.CycleParameters.signedVelocity,
      LabelSumBounds.fieldSum]
    rfl
  have hh := measuredPotential_curl (cycleInput x) Hu hp hfixed HS x.coefficients hlabels n hamp
    (qbig := qbig) ha i
  rw [hv] at hh
  exact hh

/-- The canonical physical pressure is the same finite signed pressure
sum used by the current correction state. -/
theorem cyclePressure_eq (n : ℕ) {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (ActualSignedExterior.cyclePressure x Hu hp)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).signedPressure
            x.coefficients (commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  have hv : (∑ l ∈ x.coefficients.labels n,
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B (cycleInput x))).oscillatoryPressure n) =
      (ActualCycleParameters.fixedParameters B N0).signedPressure
        x.coefficients (commonContext B) x.state n := by
    funext z
    simp only [Finset.sum_apply, CorrectionStep.CycleParameters.signedPressure]
    rfl
  have hh := measuredPressure_eq (cycleInput x) Hu hp hfixed HS x.coefficients hlabels n
    (qbig := qbig) ha i
  rw [hv] at hh
  exact hh

end Cycle

end NavierStokes.ActualSignedPhysicalCoherence
