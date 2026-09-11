/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEdgeExtension
import LeanPool.NavierStokesAndEuler.NavierStokes.NativeBandExtension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedUnmaskedBounds

/-! Related estimates used together by the same construction modules. -/

section

/-!
# Reference geometry of the actual signed family

Every singleton retains the original primary label, phase, native view,
and current-state request.  Reindexing its dependent payload changes only
the proof of the reference-band equality.  The seven reference-geometry
fields below come from these primitive identities; no equality of output
physical fields or native regularity is assumed.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedReferenceGeometry

open Set Function CorrectionState CorrectionInitialization
open CorrectionInitialization.ActualPrimary

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label

variable {B N0 : ℕ}

theorem singleton_index_eq (f : DependentSignedPhysicalFamily.Family)
    (L : ActualSignedPhysicalData.NativeLabel f.active)
    (K : ActualSignedPhysicalData.NativeLabel (f.singleton L).active) :
    K = f.singletonLabel L := by
  apply ActualSignedExterior.nativeLabel_ext
  exact f.singleton_label_val L K

theorem reband_exponent {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    {P : PhysicalSignedWave.PrimaryData U} {n m : ℕ} (he : n = m)
    (V : P.Views n) (s : V.StateData) :
    (ActualSignedExterior.rebandPayload he V s).1.exponent = V.exponent := by
  cases he
  rfl

theorem reband_scale {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    {P : PhysicalSignedWave.PrimaryData U} {n m : ℕ} (he : n = m)
    (V : P.Views n) (s : V.StateData) :
    (ActualSignedExterior.rebandPayload he V s).1.referenceScale = V.referenceScale := by
  cases he
  rfl

theorem reband_cover {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    {P : PhysicalSignedWave.PrimaryData U} {n m : ℕ} (he : n = m)
    (V : P.Views n) (s : V.StateData) :
    (ActualSignedExterior.rebandPayload he V s).1.referenceCover = V.referenceCover := by
  cases he
  rfl

/-- The geometric part is uniform over native state families.  The sole
state-dependent primitive here is angular invariance of the request.
`singletonGeometry` below constructs it for the actual measured request. -/
noncomputable def singletonGeometryOfAngular
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (ha : ∀ l, (ActualSignedPhysicalBinding.primary l).Angular
      (s l).referenceRequest (ActualSignedPhysicalBinding.reference l))
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.family s).singleton L) where
  frequency K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.frequency
      L.val.1 = _
    erw [ActualSignedPhysicalBinding.primary_frequency, ActualSignedExterior.actualLabel_reference]
    rfl
  phase K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.phase
      L.val.1 = _
    rw [ActualSignedPhysicalBinding.primary_phase]
    have hl : ActualSignedPhysicalBinding.spatialLabel (ActualSignedExterior.actualLabel L) = L.val
        :=
      congrArg Subtype.val (ActualSignedExterior.bandLabel_actualLabel L)
    erw [hl, ActualSignedExterior.actualLabel_reference]
    rfl
  angular K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).Angular
      (((ActualSignedExterior.family s).singleton L).state
        ((ActualSignedExterior.family s).singletonLabel L)).referenceRequest L.val.1
    erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest,
      ActualSignedExterior.family_referenceRequest, ← ActualSignedExterior.actualLabel_reference L]
    exact ha (ActualSignedExterior.actualLabel L)
  chart K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change PhysicalSignedWave.ChartGeometry
      (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base
      (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).strip
      (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).directions
      L.val.1 h (ChartScales.Q L.val.1) (ChartScales.nativeIndex h L.val.1)
    simpa only [ActualSignedExterior.actualLabel_reference L] using
      ActualSignedPhysicalBinding.primary_chart (ActualSignedExterior.actualLabel L) L.val.1
  exponent K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedExterior.payload s L).1.exponent = h
    erw [ActualSignedExterior.payload, reband_exponent]
    rfl
  scale K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedExterior.payload s L).1.referenceScale = ChartScales.Q L.val.1
    erw [ActualSignedExterior.payload, reband_scale]
    change ChartScales.Q (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel
        L)) = _
    erw [ActualSignedExterior.actualLabel_reference]
  cover K := by
    rw [singleton_index_eq (ActualSignedExterior.family s) L K]
    change (ActualSignedExterior.payload s L).1.referenceCover = ChartScales.nativeIndex h L.val.1
    erw [ActualSignedExterior.payload, reband_cover]
    change ChartScales.nativeIndex h
      (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) = _
    erw [ActualSignedExterior.actualLabel_reference]

/-- All seven fields for the canonical measured-request family, retaining
the actual current state and the same prepared primary choice. -/
noncomputable def singletonGeometry (P : SignedStressPrimitive.Patch)
    (u : State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)
    (L : ActualSignedPhysicalData.NativeLabel
      (ActualSignedExterior.family (fun l : Label B N0 =>
        ActualSignedPhysicalBinding.nativeStateData l P u H hp)).active) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.family (fun l : Label B N0 =>
        ActualSignedPhysicalBinding.nativeStateData l P u H hp)).singleton L) :=
  singletonGeometryOfAngular _
    (fun l => ActualSignedPhysicalBinding.primaryAngular l P u H hp) L

/-- Original-label form, suitable for the per-label current-chart
coherence theorems. -/
noncomputable def nativeSingletonGeometry (P : SignedStressPrimitive.Patch)
    (u : State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)
    (l : Label B N0) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.family (fun k : Label B N0 =>
        ActualSignedPhysicalBinding.nativeStateData k P u H hp)).singleton
          (ActualSignedExterior.nativeLabel l)) :=
  singletonGeometry P u H hp (ActualSignedExterior.nativeLabel l)

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

/-- The actual post-particular cycle family is definitionally the same
family used above, including its state and request. -/
noncomputable def cycleSingletonGeometry
    (L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.cycleFamily x H hp).active) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.cycleFamily x H hp).singleton L) :=
  singletonGeometry ActualInitialization.patch
    ((ActualCycleParameters.fixedParameters B N0).afterParticular
      x.coefficients (commonContext B) x.state) H hp L

/-- Cycle native geometry, given by `cycleSingletonGeometry x H hp
(ActualSignedExterior.nativeLabel l)`. -/
noncomputable def cycleNativeGeometry (l : Label B N0) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.cycleFamily x H hp).singleton (ActualSignedExterior.nativeLabel l)) :=
  cycleSingletonGeometry x H hp (ActualSignedExterior.nativeLabel l)

end Cycle

end NavierStokes.ActualSignedReferenceGeometry

end
end

end

section

/-!
# Native regularity of the actual signed cut sources

The dyadic factor is retained literally.  The estimates below first turn
the actual radial flat-weight classes into bounded jets, including at the
radial edges; no smooth continuation of the unmasked request at a dyadic
face is assumed.
-/

section

/-!
# Exact native-source factorization for the actual signed family

The primitive state, primary choice, request, and lattice copy are unchanged.
The identities retain the one Gaussian already present in the native cutoff.
They hold on the whole native coordinate space, before any smoothness claim
or own-band/harmonic gate is applied.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedUnmaskedBinding

open Set Function Filter CorrectionState CorrectionInitialization
open scoped ContDiff Topology

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native label: an abbreviation for `ActualSignedPhysicalData.NativeLabel
(ActualSignedExterior.labels B N0)`. -/
abbrev NativeLabel (B N0 : ℕ) :=
  ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)
/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Cylinder: an abbreviation for `ActualSignedPhysicalBinding.Cylinder`. -/
abbrev Cylinder := ActualSignedPhysicalBinding.Cylinder
/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native
/-- Copy: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Copy := TorusInverse.Frequency

variable {B N0 : ℕ}

/-- Request, given by `LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P (2 *
ActualPrimary.h) (ActualPrimary.commonContext B) u`. -/
noncomputable def request (P : SignedStressPrimitive.Patch) (u : State Point) :=
  LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P (2 * ActualPrimary.h)
    (ActualPrimary.commonContext B) u

variable (P : SignedStressPrimitive.Patch) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion P.a P.b
      (ActualPrimary.commonContext B) u)
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion P.a P.b u.pressure)

/-- States, given by `ActualSignedPhysicalBinding.nativeStateData l P u H hp`. -/
noncomputable def states (l : Label B N0) : (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  ActualSignedPhysicalBinding.nativeStateData l P u H hp

/-- Branch, given by `(ActualSignedExterior.family (states P u H hp)).singleton L`. -/
noncomputable def branch (L : NativeLabel B N0) :=
  (ActualSignedExterior.family (states P u H hp)).singleton L

/-- Branch label, given by `(ActualSignedExterior.family (states P u H hp)).singletonLabel L`. -/
noncomputable def branchLabel (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeLabel (branch P u H hp L).active :=
  (ActualSignedExterior.family (states P u H hp)).singletonLabel L

theorem branch_request (L : NativeLabel B N0) :
    ((branch P u H hp L).state (branchLabel P u H hp L)).referenceRequest =
      (ActualSignedPhysicalBinding.nativeStateData (ActualSignedExterior.actualLabel L)
        P u H hp).referenceRequest := by
  exact ((ActualSignedExterior.family (states P u H hp)).singleton_referenceRequest L).trans
    (ActualSignedExterior.family_referenceRequest (states P u H hp) L)

omit P u H hp in
theorem layout_eq (L : NativeLabel B N0) :
    ActualSignedPhysicalData.layout ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
      L.val L.property 0 = ActualSignedPhysicalBinding.layout (ActualSignedExterior.actualLabel L)
          := by
  have he : ActualSignedPhysicalBinding.spatialLabel (ActualSignedExterior.actualLabel L) = L.val :=
    congrArg Subtype.val (ActualSignedExterior.bandLabel_actualLabel L)
  unfold ActualSignedPhysicalBinding.layout
  congr 1
  exact he.symm

/- Identity view maps identify the genuine native pulse, without a
support or nonvanishing assumption. -/
omit P u H hp in
theorem unit_reference (l : Label B N0) (k : Copy) (x : Cylinder) :
    ActualPeriodizedSignedRealization.nativeUnit (ActualSignedPhysicalBinding.primary l)
      (ActualSignedPhysicalBinding.layout l) (ActualSignedPhysicalBinding.nativeViews l) l.2 k
      (ActualSignedPhysicalBinding.reference l) x =
    ActualPeriodizedSignedRealization.referenceNativeUnit (ActualSignedPhysicalBinding.primary l)
      (ActualSignedPhysicalBinding.layout l) l.2 (ActualSignedPhysicalBinding.reference l) k x := by
  simp only [ActualPeriodizedSignedRealization.nativeUnit,
    ActualPeriodizedSignedRealization.referenceNativeUnit,
    ActualSignedPhysicalBinding.nativeViews_map]

theorem reference_amplitude_formula (l : Label B N0) (k : Copy) (x : Cylinder) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).amplitude
      (ActualSignedPhysicalBinding.reference l) k x =
    ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
      (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
      (ActualSignedPhysicalBinding.reference l) x • CurlClassBounds.complexify
      (ActualPeriodizedSignedRealization.referenceNativeUnit (ActualSignedPhysicalBinding.primary l)
        (ActualSignedPhysicalBinding.layout l) l.2 (ActualSignedPhysicalBinding.reference l) k x)
            := by
  change (ActualSignedPhysicalData.dynamicCoefficients ActualPrimary.slots
    ActualPrimary.outgoing.data.h_pos.le (ActualSignedPhysicalBinding.spatialLabel l)
    (ActualSignedPhysicalBinding.label_large l) 0 (ActualSignedPhysicalBinding.primary l)
    (ActualSignedPhysicalBinding.nativeViews l)
    (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2 k).amplitude
      (ActualSignedPhysicalBinding.reference l) x = _
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  unfold ActualSignedPhysicalBinding.nativeCoefficients
  rw [ActualPeriodizedSignedRealization.coefficients_amplitude_at, unit_reference]
  rfl

theorem reference_pressure_formula (l : Label B N0) (k : Copy) (x : Cylinder) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).pressure
      (ActualSignedPhysicalBinding.reference l) k x =
    ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
      (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
      (ActualSignedPhysicalBinding.reference l) x •
      ActualPeriodizedSignedRealization.homogeneousPressure
        ((ActualSignedPhysicalBinding.primary l).base.frequency
            (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.primary l).base.normal (ActualSignedPhysicalBinding.primary
            l).strip
          (ActualSignedPhysicalBinding.primary l).directions (ActualSignedPhysicalBinding.reference
              l) x)
        ((ActualSignedPhysicalBinding.primary l).normalMotion
            (ActualSignedPhysicalBinding.reference l) x)
        ((ActualSignedPhysicalBinding.primary l).action (ActualSignedPhysicalBinding.reference l) x)
        (ActualPeriodizedSignedRealization.referenceNativeUnit (ActualSignedPhysicalBinding.primary
            l)
          (ActualSignedPhysicalBinding.layout l) l.2 (ActualSignedPhysicalBinding.reference l) k x)
              := by
  change (ActualSignedPhysicalData.dynamicCoefficients ActualPrimary.slots
    ActualPrimary.outgoing.data.h_pos.le (ActualSignedPhysicalBinding.spatialLabel l)
    (ActualSignedPhysicalBinding.label_large l) 0 (ActualSignedPhysicalBinding.primary l)
    (ActualSignedPhysicalBinding.nativeViews l)
    (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2 k).pressure
      (ActualSignedPhysicalBinding.reference l) x = _
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  unfold ActualSignedPhysicalBinding.nativeCoefficients
  rw [ActualPeriodizedSignedRealization.coefficients_pressure_at, unit_reference]
  rfl

theorem branch_amplitude_reference (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.rawSignedAmplitude ActualPrimary.slots
        ActualPrimary.outgoing.data.h_pos.le
      (branch P u H hp L) (branchLabel P u H hp L) k x =
    (ActualSignedPhysicalBinding.referenceCopies (ActualSignedExterior.actualLabel L) P u H
        hp).amplitude
      (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) k x := by
  rw [reference_amplitude_formula]
  unfold ActualSignedPhysicalData.rawSignedAmplitude
  rw [branch_request]
  change ActualPeriodizedSignedRealization.referenceScalar _ _ _ L.val.1 x •
    CurlClassBounds.complexify (ActualPeriodizedSignedRealization.referenceNativeUnit _
      (ActualSignedPhysicalData.layout ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
        L.val L.property 0) _ L.val.1 k x) = _
  rw [layout_eq, ← ActualSignedExterior.actualLabel_reference L]
  rfl

theorem branch_pressure_reference (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.rawPressure ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
      (branch P u H hp L) (branchLabel P u H hp L) k x =
    (ActualSignedPhysicalBinding.referenceCopies (ActualSignedExterior.actualLabel L) P u H
        hp).pressure
      (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) k x := by
  rw [reference_pressure_formula]
  unfold ActualSignedPhysicalData.rawPressure
  rw [branch_request]
  change ActualPeriodizedSignedRealization.referenceScalar _ _ _ L.val.1 x •
    ActualPeriodizedSignedRealization.homogeneousPressure _ _ _ _
      (ActualPeriodizedSignedRealization.referenceNativeUnit _
        (ActualSignedPhysicalData.layout ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
          L.val L.property 0) _ L.val.1 k x) = _
  rw [layout_eq, ← ActualSignedExterior.actualLabel_reference L]
  rfl

theorem branch_potential_reference (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.rawPotential ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
      (branch P u H hp L) (branchLabel P u H hp L) k x =
    ActualSignedPhysicalData.potentialMap
      ((ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.frequency
        (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)))
      ((ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.normal
        (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).strip
        (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).directions
        (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) x)
      ((ActualSignedPhysicalBinding.referenceCopies (ActualSignedExterior.actualLabel L) P u H
          hp).amplitude
        (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) k x) := by
  unfold ActualSignedPhysicalData.rawPotential
  rw [branch_amplitude_reference]
  change CurlClassBounds.inverseCarrier
    ((ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.frequency
        L.val.1) •
    CurlClassBounds.normalCoefficient
      ((ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).base.normal
        (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).strip
        (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).directions
            L.val.1 x) _ = _
  rw [← ActualSignedExterior.actualLabel_reference L]
  rfl

theorem waveMask_reference (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.waveMask ActualPrimary.slots L.val
      ((ActualSignedPhysicalData.geometry ActualPrimary.slots L.val 0).coordinates k x.1.2.2) =
    (ActualSignedPhysicalBinding.referenceCopies (ActualSignedExterior.actualLabel L) P u H
        hp).cutoff
      (ActualSignedPhysicalBinding.reference (ActualSignedExterior.actualLabel L)) k x := by
  have he : ActualSignedPhysicalBinding.spatialLabel (ActualSignedExterior.actualLabel L) = L.val :=
    congrArg Subtype.val (ActualSignedExterior.bandLabel_actualLabel L)
  rw [← he]
  simp only [ActualSignedPhysicalBinding.referenceCopies, ActualSignedPhysicalData.dynamicCopyData,
    ActualSignedPhysicalBinding.nativeViews_map]
  rfl

/-- The scalar factor is removed after the one existing native Gaussian
has been applied. No additional cutoff is introduced. -/
theorem cylinder_potential_factor (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.waveMask ActualPrimary.slots L.val
      ((ActualSignedPhysicalData.geometry ActualPrimary.slots L.val 0).coordinates k x.1.2.2) •
      ActualSignedPhysicalData.rawPotential ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
        (branch P u H hp L) (branchLabel P u H hp L) k x =
    ActualSignedUnmaskedBounds.dyadicFactor (ActualSignedExterior.actualLabel L) k
      (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
      (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L) x) •
      ActualSignedUnmaskedBounds.potential (request (B := B) P u) (ActualSignedExterior.actualLabel
          L) k
        (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
        (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L) x) := by
  let l := ActualSignedExterior.actualLabel L
  rw [branch_potential_reference P u H hp L k x, waveMask_reference P u H hp L k x]
  rw [← map_smul]
  change ActualSignedPhysicalData.potentialMap _ _
    (((ActualSignedPhysicalBinding.referenceCopies l P u H hp).localized k).amplitude
      (ActualSignedPhysicalBinding.reference l) x) = _
  rw [ActualSignedPhysicalData.potentialMap_apply,
    ActualSignedPhysicalBinding.primary_normal_reference,
    ← ActualSignedPhysicalBinding.localized_amplitude_reference l P u H hp k x]
  exact ActualSignedUnmaskedBounds.potential_factor (request (B := B) P u) l k
    (ActualSignedUnmaskedBounds.reference l) (ActualSignedPhysicalBinding.toCommonCylinder l x)

theorem cylinder_pressure_factor (L : NativeLabel B N0) (k : Copy) (x : Cylinder) :
    ActualSignedPhysicalData.waveMask ActualPrimary.slots L.val
      ((ActualSignedPhysicalData.geometry ActualPrimary.slots L.val 0).coordinates k x.1.2.2) •
      ActualSignedPhysicalData.rawPressure ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
        (branch P u H hp L) (branchLabel P u H hp L) k x =
    ActualSignedUnmaskedBounds.dyadicFactor (ActualSignedExterior.actualLabel L) k
      (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
      (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L) x) •
      ActualSignedUnmaskedBounds.pressure (request (B := B) P u) (ActualSignedExterior.actualLabel
          L) k
        (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
        (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L) x) := by
  let l := ActualSignedExterior.actualLabel L
  rw [branch_pressure_reference P u H hp L k x, waveMask_reference P u H hp L k x]
  change (((ActualSignedPhysicalBinding.referenceCopies l P u H hp).localized k).pressure
    (ActualSignedPhysicalBinding.reference l) x) = _
  rw [← ActualSignedPhysicalBinding.localized_pressure_reference l P u H hp k x]
  exact ActualSignedUnmaskedBounds.pressure_factor (request (B := B) P u) l k
    (ActualSignedUnmaskedBounds.reference l) (ActualSignedPhysicalBinding.toCommonCylinder l x)

theorem native_potential_factor (L : NativeLabel B N0) (k : Copy) (y : Native) :
    ActualSignedPhysicalData.waveMask ActualPrimary.slots L.val
      ((ActualSignedPhysicalData.geometry ActualPrimary.slots L.val 0).coordinates k y.2.2) •
      ActualSignedPhysicalData.rawPotential ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
        (branch P u H hp L) (branchLabel P u H hp L) k (ActualSignedPhysicalData.nativeCylinder y) =
    SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1) •
      ActualSignedUnmaskedBounds.potential (request (B := B) P u) (ActualSignedExterior.actualLabel
          L) k
        (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
        (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L)
          (ActualSignedPhysicalData.nativeCylinder y)) := by
  have he := cylinder_potential_factor P u H hp L k (ActualSignedPhysicalData.nativeCylinder y)
  rw [ActualSignedUnmaskedBounds.dyadicFactor_reference] at he
  exact he

theorem native_pressure_factor (L : NativeLabel B N0) (k : Copy) (y : Native) :
    ActualSignedPhysicalData.waveMask ActualPrimary.slots L.val
      ((ActualSignedPhysicalData.geometry ActualPrimary.slots L.val 0).coordinates k y.2.2) •
      ActualSignedPhysicalData.rawPressure ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
        (branch P u H hp L) (branchLabel P u H hp L) k (ActualSignedPhysicalData.nativeCylinder y) =
    SquaredPartition.dyadicProfile (SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1) •
      ActualSignedUnmaskedBounds.pressure (request (B := B) P u) (ActualSignedExterior.actualLabel
          L) k
        (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
        (ActualSignedPhysicalBinding.toCommonCylinder (ActualSignedExterior.actualLabel L)
          (ActualSignedPhysicalData.nativeCylinder y)) := by
  have he := cylinder_pressure_factor P u H hp L k (ActualSignedPhysicalData.nativeCylinder y)
  rw [ActualSignedUnmaskedBounds.dyadicFactor_reference] at he
  exact he

end NavierStokes.ActualSignedUnmaskedBinding

end
end

end

section

/-!
# Literal flat dyadic products from locally bounded interior jets

The unmasked factor is smooth only in the open dyadic band.  Its actual
interior jets are locally bounded at each face.  Flatness of the fixed cutoff
then proves smoothness and vanishing of all jets of the literal product,
without assigning new values to the unmasked factor outside the band.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.FlatDyadicExtension

open Set Function Filter
open WaveEdgeExtension (window windowDomain extension extendedJets)
open scoped Topology ContDiff BigOperators

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- The constant and neighborhood may depend on the face point and finite
jet order.  Values and derivatives of `g` outside the open band are unused. -/
def LocalJetBounds (Ω : Set D) (q : D → ℝ) (g : D → E) : Prop :=
  ∀ x ∈ Ω, q x = 1 / 2 ∨ q x = 2 → ∀ m : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      y ∈ windowDomain Ω q (1 / 2) 2 →
        ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j g y‖ ≤ C

theorem tensor_hasFDerivAt {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ (n + 1) f x).curryLeft x := by
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  simp only [fderiv_iteratedFDeriv, Function.comp_apply] at hd
  exact hd

/-- One extra zero tensor makes each flat jet little-o of ambient distance. -/
theorem flat_jet_isLittleO {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hz : ∀ n : ℕ, iteratedFDeriv ℝ n f x = 0) (n : ℕ) :
    (iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x) := by
  have hcurry : (0 : D[×(n + 1)]→L[ℝ] E).curryLeft = 0 := by
    ext u v
    rfl
  have hd : HasFDerivAt (iteratedFDeriv ℝ n f) (0 : D →L[ℝ] (D[×n]→L[ℝ] E)) x := by
    have ht := tensor_hasFDerivAt hf n
    rw [hz (n + 1), hcurry] at ht
    exact ht
  rw [hasFDerivAt_iff_isLittleO] at hd
  simpa only [hz n, _root_.zero_apply, sub_zero] using
    hd

/-- A flat smooth scalar times a factor with locally bounded interior jets
has little-o interior product jets.  Zero extension needs no source values
or source regularity on the other side of the boundary. -/
theorem product_jet_extension_isLittleO {Ω : Set D} (hΩ : IsOpen Ω)
    {q φ : D → ℝ} (hq : ContinuousOn q Ω) (hφ : ContDiffOn ℝ ∞ φ Ω)
    {a b : ℝ} {g : D → E} (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q a b))
    {x : D} (hx : x ∈ Ω) (hflat : ∀ n : ℕ, iteratedFDeriv ℝ n φ x = 0)
    (m : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      y ∈ windowDomain Ω q a b → ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j g y‖ ≤ C) :
    extension q a b (iteratedFDeriv ℝ m (fun y => φ y • g y))
      =o[𝓝 x] (fun y => y - x) := by
  obtain ⟨C, hC, hb⟩ := hB
  let M : ℝ := C + 1
  have hM : 0 < M := by dsimp [M]; linarith
  have hCM : C ≤ M := by dsimp [M]; linarith
  have hU := WaveEdgeExtension.windowDomain_open hΩ hq a b
  have hφx := hφ.contDiffAt (hΩ.mem_nhds hx)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let δ : ℝ := ε / ((2 : ℝ) ^ m * M)
  have hden : 0 < (2 : ℝ) ^ m * M := mul_pos (pow_pos (by norm_num) _) hM
  have hδ : 0 < δ := div_pos hε hden
  have hsmall : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ j φ y‖ ≤ δ * ‖y - x‖ :=
    (eventually_all_finset _).2 (fun j _ => (flat_jet_isLittleO hφx hflat j).bound hδ)
  filter_upwards [hΩ.mem_nhds hx, hb, hsmall] with y hyΩ hby hsy
  by_cases hy : y ∈ window q a b
  · rw [WaveEdgeExtension.extension_inside q a b _ hy]
    have hyU : y ∈ windowDomain Ω q a b := ⟨hyΩ, hy⟩
    change IsOpen (Ω ∩ window q a b) at hU
    change y ∈ Ω ∩ window q a b at hyU
    have hprod := norm_iteratedFDerivWithin_smul_le
      (hφ.mono (inter_subset_left (t := window q a b))) hg hU.uniqueDiffOn hyU
      (n := m) (nat_le_infty m)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hyU] at hprod
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j φ y‖ * ‖iteratedFDeriv ℝ (m - j) g y‖ := hprod
      _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (δ * ‖y - x‖) * M := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hsy j hj) (Nat.cast_nonneg _))
          ((hby hyU (m - j) (Nat.sub_le _ _)).trans hCM)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδ.le (norm_nonneg _)))
      _ = (2 : ℝ) ^ m * (δ * ‖y - x‖) * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
          exact_mod_cast Nat.sum_range_choose m
        rw [hchoose]
      _ = (δ * ((2 : ℝ) ^ m * M)) * ‖y - x‖ := by ring
      _ = ε * ‖y - x‖ := by rw [div_mul_cancel₀ ε hden.ne']
  · rw [WaveEdgeExtension.extension_outside q a b _ hy, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

/-! ## A Taylor family for the literal window extension -/

/-- Small O jets, given by `∀ n : ℕ, ∀ x ∈ Ω, q x = a ∨ q x = b → extension q a b
(iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x)`. -/
def SmallOJets (Ω : Set D) (q : D → ℝ) (a b : ℝ) (f : D → E) : Prop :=
  ∀ n : ℕ, ∀ x ∈ Ω, q x = a ∨ q x = b →
    extension q a b (iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x)

theorem hasFDerivAt_extension_zero {q : D → ℝ} {a b : ℝ} {f : D → E} {x : D}
    (hx : x ∉ window q a b)
    (hf : extension q a b f =o[𝓝 x] (fun y => y - x)) :
    HasFDerivAt (extension q a b f) (0 : D →L[ℝ] E) x := by
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [WaveEdgeExtension.extension_outside q a b f hx,
    _root_.zero_apply, sub_zero] using hf

theorem extendedJets_hasFDerivAt {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b))
    (hB : SmallOJets Ω q a b f) (n : ℕ) {x : D} (hx : x ∈ Ω) :
    HasFDerivAt (fun y => extendedJets q a b f y n)
      (extendedJets q a b f x (n + 1)).curryLeft x := by
  have hqc := (hq x hx).continuousAt (hΩ.mem_nhds hx)
  change HasFDerivAt (extension q a b (iteratedFDeriv ℝ n f))
    (extension q a b (iteratedFDeriv ℝ (n + 1) f) x).curryLeft x
  have hcurry : (0 : D[×(n + 1)]→L[ℝ] E).curryLeft = 0 := by
    ext u v
    rfl
  rcases lt_trichotomy (q x) a with hleft | heq | hleft
  · have hn : x ∉ window q a b := fun h => (not_lt_of_ge hleft.le) h.1
    rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
    exact (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
      (WaveEdgeExtension.extension_germ_left a b _ hqc hleft)
  · have hn : x ∉ window q a b := fun h => (not_lt_of_ge heq.le) h.1
    rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
    exact hasFDerivAt_extension_zero hn (hB n x hx (Or.inl heq))
  · rcases lt_trichotomy (q x) b with hright | heq | hright
    · have hin : x ∈ window q a b := ⟨hleft, hright⟩
      rw [WaveEdgeExtension.extension_inside q a b _ hin]
      have hd := tensor_hasFDerivAt
        (hf.contDiffAt ((WaveEdgeExtension.windowDomain_open hΩ hq a b).mem_nhds ⟨hx, hin⟩)) n
      exact hd.congr_of_eventuallyEq (WaveEdgeExtension.extension_germ_inside a b _ hqc hin)
    · have hn : x ∉ window q a b := fun h => (not_lt_of_ge heq.ge) h.2
      rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
      exact hasFDerivAt_extension_zero hn (hB n x hx (Or.inr heq))
    · have hn : x ∉ window q a b := fun h => (not_lt_of_ge hright.le) h.2
      rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
      exact (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
        (WaveEdgeExtension.extension_germ_right a b _ hqc hright)

theorem hasFTaylorSeriesUpToOn_extension {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b)) (hB : SmallOJets Ω q a b f) :
    HasFTaylorSeriesUpToOn ∞ (extension q a b f) (extendedJets q a b f) Ω := by
  classical
  constructor
  · intro x hx
    by_cases hi : x ∈ window q a b
    · simp only [extendedJets, extension, ite_eq_left hi]
      rfl
    · simp only [extendedJets, extension, ite_eq_right hi]
      rfl
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hq hf hB n hx).hasFDerivWithinAt
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hq hf hB n hx).continuousAt.continuousWithinAt

theorem iteratedFDeriv_extension {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b)) (hB : SmallOJets Ω q a b f)
    (n : ℕ) {x : D} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ n (extension q a b f) x = extension q a b (iteratedFDeriv ℝ n f) x := by
  have h := hasFTaylorSeriesUpToOn_extension hΩ hq hf hB
  have he := (h.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le hΩ.uniqueDiffOn hx).symm
  rwa [iteratedFDerivWithin_of_isOpen n hΩ hx] at he

/-! ## The fixed dyadic cutoff -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem dyadicProduct_eq_extension (q : D → ℝ) (g : D → E) :
    (fun x => SquaredPartition.dyadicProfile (q x) • g x) =
      extension q (1 / 2) 2 (fun x => SquaredPartition.dyadicProfile (q x) • g x) := by
  classical
  funext x
  by_cases hx : x ∈ window q (1 / 2) 2
  · exact (WaveEdgeExtension.extension_inside q (1 / 2) 2
      (fun y => SquaredPartition.dyadicProfile (q y) • g y) hx).symm
  · rw [WaveEdgeExtension.extension_outside q (1 / 2) 2
      (fun y => SquaredPartition.dyadicProfile (q y) • g y) hx]
    have hz : SquaredPartition.dyadicProfile (q x) = 0 := by
      by_contra hn
      have hm : q x ∈ Function.support SquaredPartition.dyadicProfile := hn
      rw [SquaredPartition.dyadicProfile_support] at hm
      exact hx hm
    rw [hz, zero_smul]

/-- Main endpoint: the literal product is smooth on the ambient open domain
and every actual tensor vanishes at either dyadic face. -/
theorem dyadic_product_smooth_and_flat {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) :
    ContDiffOn ℝ ∞ (fun x => SquaredPartition.dyadicProfile (q x) • g x) Ω ∧
      ∀ x ∈ Ω, q x = 1 / 2 ∨ q x = 2 → ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun y => SquaredPartition.dyadicProfile (q y) • g y) x = 0 := by
  let φ : D → ℝ := fun x => SquaredPartition.dyadicProfile (q x)
  let f : D → E := fun x => φ x • g x
  have hφ : ContDiffOn ℝ ∞ φ Ω := SquaredPartition.dyadicProfile_smooth.comp_contDiffOn hq
  have hf : ContDiffOn ℝ ∞ f (windowDomain Ω q (1 / 2) 2) :=
    (hφ.mono (inter_subset_left (t := window q (1 / 2) 2))).smul hg
  have hsmall : SmallOJets Ω q (1 / 2) 2 f := by
    intro n x hx hedge
    have hflat : ∀ j : ℕ, iteratedFDeriv ℝ j φ x = 0 := by
      intro j
      apply NativeBandExtension.flat_comp_jets SquaredPartition.dyadicProfile_smooth
        (hq.contDiffAt (hΩ.mem_nhds hx)) _ j
      intro k
      rcases hedge with he | he
      · rw [he]
        exact (NativeBandExtension.dyadicProfile_endpoint_jets k).1
      · rw [he]
        exact (NativeBandExtension.dyadicProfile_endpoint_jets k).2
    exact product_jet_extension_isLittleO hΩ hq.continuousOn hφ hg hx hflat n (hB x hx hedge n)
  have heq : f = extension q (1 / 2) 2 f := dyadicProduct_eq_extension q g
  constructor
  · change ContDiffOn ℝ ∞ f Ω
    rw [heq]
    exact (hasFTaylorSeriesUpToOn_extension hΩ hq.continuousOn hf hsmall).contDiffOn
  · intro x hx hedge n
    change iteratedFDeriv ℝ n f x = 0
    rw [heq, iteratedFDeriv_extension hΩ hq.continuousOn hf hsmall n hx]
    apply WaveEdgeExtension.extension_outside
    rcases hedge with he | he
    · exact fun hin => (not_lt_of_ge he.le) hin.1
    · exact fun hin => (not_lt_of_ge he.ge) hin.2

theorem dyadic_product_contDiffOn {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) :
    ContDiffOn ℝ ∞ (fun x => SquaredPartition.dyadicProfile (q x) • g x) Ω :=
  (dyadic_product_smooth_and_flat hΩ hq hg hB).1

theorem dyadic_product_face {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) {x : D} (hx : x ∈ Ω) (he : q x = 1 / 2 ∨ q x = 2) :
    ContDiffAt ℝ ∞ (fun y => SquaredPartition.dyadicProfile (q y) • g y) x ∧
      ∀ n : ℕ, iteratedFDeriv ℝ n (fun y => SquaredPartition.dyadicProfile (q y) • g y) x = 0 :=
  ⟨(dyadic_product_contDiffOn hΩ hq hg hB).contDiffAt (hΩ.mem_nhds hx),
    (dyadic_product_smooth_and_flat hΩ hq hg hB).2 x hx he⟩

end NavierStokes.FlatDyadicExtension

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedNativeRegularity

open Set Function Filter WeightedClasses
open CorrectionInitialization
open scoped Topology ContDiff

/-- Full point: an abbreviation for `ActualWaveRegularityData.FullPoint`. -/
abbrev FullPoint := ActualWaveRegularityData.FullPoint

theorem half_weight_bounded {cL cR L : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) L,
      (max 1 (WeightedRadialPrimitive.delta L t)⁻¹) ^ m *
        Real.sqrt (WeightedRadialPrimitive.zeta cL cR L t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((WeightedRadialPrimitive.wholeMajorant_continuous (half_pos hcL) (half_pos hcR) L
        m).continuousOn :
      ContinuousOn _ (Icc (0 : ℝ) L))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  have hi : 1 ≤ (WeightedRadialPrimitive.delta L t)⁻¹ :=
    (one_le_inv₀ (WeightedRadialPrimitive.delta_pos ht)).mpr
      (WeightedRadialPrimitive.delta_le_one L t)
  rw [max_eq_right hi, WaveEdgeExtension.sqrt_zeta ht]
  have hw := WeightedRadialPrimitive.weight_le_wholeMajorant
    (half_pos hcL).le (half_pos hcR).le m ht
  have hm := (le_abs_self (WeightedRadialPrimitive.wholeMajorant (cL/2) (cR/2) L m t)).trans
    ((hC t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left C 0))
  simpa only [WeightedRadialPrimitive.weight, inv_pow, div_eq_mul_inv, mul_comm] using hw.trans hm

theorem radial_weight_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : FullPoint,
      ActualWaveRegularityData.radius x ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
      WaveEdgeExtension.edgeGrowth ActualWaveRegularityData.radius
          (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ m *
        Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) ≤ C := by
  obtain ⟨C, hC, hb⟩ := half_weight_bounded
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num : (0:ℝ)<4))
    (show (0:ℝ)<1 by norm_num) m
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [ActualWaveRegularityData.strip_zeta]
  exact hb _ (WeightedRadialPrimitive.logPosition_mem
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) hx)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_jets_zero_outside {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (n m : ℕ) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (ho : ActualWaveRegularityData.radius x ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    iteratedFDeriv ℝ m (f n) x = 0 := by
  by_cases hc : ActualWaveRegularityData.radius x ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  · have he : ActualWaveRegularityData.radius x = PrimaryTargetBounds.leftRadius
      ActualPrimary.nominal ∨
        ActualWaveRegularityData.radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal
            := by
      rcases not_and_or.mp ho with ha | hb
      · exact Or.inl (le_antisymm (le_of_not_gt ha) hc.1)
      · exact Or.inr (le_antisymm hc.2 (le_of_not_gt hb))
    exact (ActualWaveRegularityData.full_regular_of_class hf hz n).2 m x hx he
  · have hΩ := ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion
    have hρ := (ActualWaveRegularityData.radius_smooth.contDiffAt (hΩ.mem_nhds hx)).continuousAt
    have hg : f n =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hΩ.mem_nhds hx, hρ (isClosed_Icc.isOpen_compl.mem_nhds hc)] with y hy hout
      exact hz n y hy (fun h => hout ⟨h.1.le, h.2.le⟩)
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg m, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply]

theorem radial_class_bounded_jets {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion,
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  obtain ⟨D, hD, hd⟩ := radial_weight_bounded p
  let K := C * ActualSignedStageControls.fullStrip.epsilon n ^ α *
    ActualSignedStageControls.fullStrip.slow n ^ p
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg hC (Real.rpow_pos_of_pos (ActualSignedStageControls.fullStrip.epsilon_pos n) α).le)
    (pow_nonneg (zero_le_one.trans (ActualSignedStageControls.fullStrip.one_le_slow n)) p)
  refine ⟨K*D, mul_nonneg hK hD, ?_⟩
  intro x hx j hj
  by_cases hi : ActualWaveRegularityData.radius x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  · have hm : x ∈ ActualSignedStageControls.fullStrip.domain := by
      rw [ActualWaveRegularityData.strip_domain_eq]
      exact ⟨hx, hi⟩
    have he := hb n x hm j hj
    simp only [majorant, ActualWaveRegularityData.strip_growth, mul_pow] at he
    calc
      _ ≤ K * (WaveEdgeExtension.edgeGrowth ActualWaveRegularityData.radius
          (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p *
          Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) := by
        convert! he using 1
        dsimp [K]
        ring
      _ ≤ K * D := mul_le_mul_of_nonneg_left (hd x hi) hK
  · rw [radial_jets_zero_outside hf hz n j hx hi, norm_zero]
    exact mul_nonneg hK hD

theorem norm_iteratedFDeriv_linear_pull {D F V : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : D →L[ℝ] F) {Ω : Set F} (hΩ : IsOpen Ω) {g : F → V}
    (hg : ContDiffOn ℝ ∞ g Ω) (m : ℕ) {x : D} (hx : e x ∈ Ω) :
    ‖iteratedFDeriv ℝ m (g ∘ e) x‖ ≤ ‖iteratedFDeriv ℝ m g (e x)‖ * ‖e‖ ^ m := by
  have he := e.iteratedFDerivWithin_comp_right hg hΩ.uniqueDiffOn
    (hΩ.preimage e.continuous).uniqueDiffOn hx
      (show (m : WithTop ℕ∞) ≤ ∞ from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)))
  rw [iteratedFDerivWithin_of_isOpen m (hΩ.preimage e.continuous) hx,
    iteratedFDerivWithin_of_isOpen m hΩ hx] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m g (e x)).norm_compContinuousLinearMap_le (fun _ => e)

theorem radial_class_pull_local_bounds {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (e : D →L[ℝ] FullPoint) (Ω : Set D) (q : D → ℝ)
    (hmap : MapsTo e (WaveEdgeExtension.windowDomain Ω q (1 / 2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)) (n : ℕ) :
    FlatDyadicExtension.LocalJetBounds Ω q (f n ∘ e) := by
  intro x _hx _he m
  obtain ⟨C, hC, hb⟩ := radial_class_bounded_jets hf hz n m
  let Q : ℝ := max 1 ‖e‖
  have hQ : 1 ≤ Q := le_max_left _ _
  refine ⟨C * Q ^ m, mul_nonneg hC (pow_nonneg (zero_le_one.trans hQ) m),
      Filter.Eventually.of_forall ?_⟩
  intro y hy j hj
  have hbound := norm_iteratedFDeriv_linear_pull e
    (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion)
    (ActualWaveRegularityData.full_regular_of_class hf hz n).1 j (hmap hy)
  refine hbound.trans (mul_le_mul (hb (e y) (hmap hy) j hj) ?_ (pow_nonneg (norm_nonneg e) j) hC)
  exact (pow_le_pow_left₀ (norm_nonneg e) (le_max_right 1 ‖e‖) j).trans
    (pow_le_pow_right₀ hQ hj)

theorem radial_class_dyadic_pull_smooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (e : D →L[ℝ] FullPoint) {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω)
    (hmap : MapsTo e (WaveEdgeExtension.windowDomain Ω q (1 / 2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (q y) • f n (e y)) Ω ∧
    ∀ x ∈ Ω, q x = 1/2 ∨ q x = 2 → ∀ m,
      iteratedFDeriv ℝ m (fun y => SquaredPartition.dyadicProfile (q y) • f n (e y)) x = 0 := by
  exact FlatDyadicExtension.dyadic_product_smooth_and_flat hΩ hq
    ((ActualWaveRegularityData.full_regular_of_class hf hz n).1.comp e.contDiff.contDiffOn hmap)
    (radial_class_pull_local_bounds hf hz e Ω q hmap n)

/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native
/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualSignedPhysicalBinding.Label B N0

/-- Native cylinder map as an element of `Native →L[ℝ] PhysicalSignedWave.Cylinder`. -/
noncomputable def nativeCylinderMap : Native →L[ℝ] PhysicalSignedWave.Cylinder :=
  let r := ContinuousLinearMap.fst ℝ ℝ (TorusInverse.Plane × TorusInverse.Plane)
  let s := ContinuousLinearMap.snd ℝ ℝ (TorusInverse.Plane × TorusInverse.Plane)
  let tz := (ContinuousLinearMap.fst ℝ TorusInverse.Plane TorusInverse.Plane).comp s
  let y := (ContinuousLinearMap.snd ℝ TorusInverse.Plane TorusInverse.Plane).comp s
  let swap := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  (r.prod ((swap.comp tz).prod y)).prod 0

theorem nativeCylinderMap_apply (y : Native) :
    nativeCylinderMap y = ActualSignedPhysicalData.nativeCylinder y := rfl

/-- Native to common, given by `(ActualSignedPhysicalBinding.toCommonCylinder
l).toContinuousLinearMap.comp nativeCylinderMap`. -/
noncomputable def nativeToCommon {B N0 : ℕ} (l : Label B N0) : Native →L[ℝ] FullPoint :=
  (ActualSignedPhysicalBinding.toCommonCylinder l).toContinuousLinearMap.comp nativeCylinderMap

theorem nativeToCommon_apply {B N0 : ℕ} (l : Label B N0) (y : Native) :
    nativeToCommon l y = ActualSignedPhysicalBinding.toCommonCylinder l
      (ActualSignedPhysicalData.nativeCylinder y) := rfl

/-- Native Q, given by `SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1`. -/
noncomputable def nativeQ (y : Native) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1

theorem nativeQ_smooth : ContDiffOn ℝ ∞ nativeQ ActualSignedPhysicalData.nativePast := by
  intro y hy
  exact ((SimilarityCoordinates.coordinateQ_smooth
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) hy).comp y
      contDiffAt_snd.fst).contDiffWithinAt

theorem nativeToCommon_maps {B N0 : ℕ} (l : Label B N0) :
    MapsTo (nativeToCommon l)
      (WaveEdgeExtension.windowDomain ActualSignedPhysicalData.nativePast nativeQ (1/2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  intro y hy
  exact ⟨⟨hy.1, hy.2⟩, mem_univ _⟩

theorem radial_class_native_smooth {B N0 : ℕ} (l : Label B N0)
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) • f n (nativeToCommon l y))
      ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) • f n
            (nativeToCommon l z)) y = 0 :=
  radial_class_dyadic_pull_smooth hf hz (nativeToCommon l)
    ActualSignedPhysicalData.nativePast_open nativeQ_smooth (nativeToCommon_maps l) n

theorem primary_mask_zero_outside {B N0 : ℕ} (l : Label B N0) (n : ℕ)
    (x : PhysicalSignedWave.Cylinder)
    (ho : SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.2.1.2, x.1.2.1.1) ∉ Ioo (1 /
        2
        : ℝ) 2) :
    (ActualSignedPhysicalBinding.primary l).mask n x = 0 := by
  change ActualPrimary.spatialMask l.1 (x.1.1,x.1.2.1) = 0
  by_contra hn
  exact ho (ActualPrimary.spatialMask_q_range l.1 (x.1.1,x.1.2.1) hn)

theorem referenceScalar_zero_outside {B N0 : ℕ} (l : Label B N0)
    (request : ℕ → PhysicalSignedWave.Cylinder → SignedWaveUpdate.Vec2)
    (j : Fin 2) (n : ℕ) (x : PhysicalSignedWave.Cylinder)
    (ho : SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.2.1.2, x.1.2.1.1) ∉ Ioo (1 /
        2
        : ℝ) 2) :
    ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
        request j n x = 0 := by
  simp only [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar,
    primary_mask_zero_outside l n x ho, mul_zero]

section ActualCoefficients

open ActualSignedUnmaskedBounds

variable {B N0 : ℕ}

theorem own_native_smooth {f : Label B N0 → TorusInverse.Frequency → ℕ → FullPoint → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass ActualSignedStageControls.fullStrip
      (fun (i : Label B N0 × TorusInverse.Frequency) n x =>
        Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) * ActualSignedStageControls.envelope
            i.1 n x)
      α (ownField f))
    (hz : ∀ l k x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f l k (reference l) x = 0)
    (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      f l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          f l k (reference l) (nativeToCommon l z)) y = 0 := by
  have hc : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α (ownField f (l,k)) := by
    apply (hf.each (l,k)).mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    intro n x _
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (ActualPrimaryBounds.fullEnvelope_le_one (l.2,l.1) n x)
  have hzero (n : ℕ) (x : FullPoint)
      (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
      (ho : ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) : ownField f (l,k) n x = 0 := by
    by_cases hn : n = reference l
    · subst n
      rw [ownField_reference]
      exact hz l k x hx ho
    · rw [ownField_other f (l,k) hn]
  have hh := radial_class_native_smooth l hc hzero (reference l)
  simpa only [ownField, ite_eq_left rfl, ite_true] using hh

variable {request : ℕ → FullPoint → SignedWaveUpdate.Vec2} {β : ℝ}
  (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
    (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) β
    ActualSignedStageControls.phaseCell (fun _ n _ x => request n x q))

include hR in
theorem potential_smooth_and_flat (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      potential request l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast
          ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          potential request l k (reference l) (nativeToCommon l z)) y = 0 := by
  exact own_native_smooth (own_potential_pressure_class hR).1
    (fun l k x hx ho => (own_zero_outside request l k hx ho).2.2) l k

include hR in
theorem pressure_smooth_and_flat (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      pressure request l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          pressure request l k (reference l) (nativeToCommon l z)) y = 0 := by
  exact own_native_smooth (own_potential_pressure_class hR).2
    (fun l k x hx ho => (own_zero_outside request l k hx ho).2.1) l k

end ActualCoefficients

section LiteralNativeSources

open ActualSignedUnmaskedBinding

variable {B N0 : ℕ}
  (P : SignedStressPrimitive.Patch) (u : CorrectionState.State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion P.a P.b
    (ActualPrimary.commonContext B) u)
  (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion P.a P.b u.pressure)

/-- The only gates are the original discrete label, harmonic, and band gates. -/
theorem native_potential_source_factor (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n =
    if I.1.1 = (L : PhysicalWaveSum.BandLabel) ∧ I.1.2.val = 1 ∧ n = L.val.1 then
      fun y => SquaredPartition.dyadicProfile (nativeQ y) •
        ActualSignedUnmaskedBounds.potential (request (B := B) P u)
            (ActualSignedExterior.actualLabel L) I.2
          (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
          (nativeToCommon (ActualSignedExterior.actualLabel L) y)
    else fun _ => 0 := by
  classical
  funext y
  by_cases hL : I.1.1 = (L : PhysicalWaveSum.BandLabel)
  · have hm : I.1.1 ∈ (branch P u H hp L).active := by
      change I.1.1 ∈ {(L : PhysicalWaveSum.BandLabel)}
      exact mem_singleton_iff.mpr hL
    have hv : I.1.1.val = L.val := congrArg Subtype.val hL
    erw [ActualSignedPhysicalData.nativePotentialSource, dite_eq_left hm]
    simp only [hL, true_and]
    by_cases hi : I.1.2.val = 1 ∧ n = L.val.1
    · simp only [ite_eq_left hi]
      exact native_potential_factor P u H hp L I.2 y
    · simp only [ite_eq_right hi]
  · have hm : I.1.1 ∉ (branch P u H hp L).active := by
      change I.1.1 ∉ {(L : PhysicalWaveSum.BandLabel)}
      exact fun h => hL (mem_singleton_iff.mp h)
    simp only [ActualSignedPhysicalData.nativePotentialSource, dite_eq_right hm, hL, false_and,
        ite_false]

theorem native_pressure_source_factor (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n =
    if I.1.1 = (L : PhysicalWaveSum.BandLabel) ∧ I.1.2.val = 1 ∧ n = L.val.1 then
      fun y => SquaredPartition.dyadicProfile (nativeQ y) •
        ActualSignedUnmaskedBounds.pressure (request (B := B) P u)
            (ActualSignedExterior.actualLabel L) I.2
          (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
          (nativeToCommon (ActualSignedExterior.actualLabel L) y)
    else fun _ => 0 := by
  classical
  funext y
  by_cases hL : I.1.1 = (L : PhysicalWaveSum.BandLabel)
  · have hm : I.1.1 ∈ (branch P u H hp L).active := by
      change I.1.1 ∈ {(L : PhysicalWaveSum.BandLabel)}
      exact mem_singleton_iff.mpr hL
    have hv : I.1.1.val = L.val := congrArg Subtype.val hL
    erw [ActualSignedPhysicalData.nativePressureSource, dite_eq_left hm]
    simp only [hL, true_and]
    by_cases hi : I.1.2.val = 1 ∧ n = L.val.1
    · simp only [ite_eq_left hi]
      exact native_pressure_factor P u H hp L I.2 y
    · simp only [ite_eq_right hi]
  · have hm : I.1.1 ∉ (branch P u H hp L).active := by
      change I.1.1 ∉ {(L : PhysicalWaveSum.BandLabel)}
      exact fun h => hL (mem_singleton_iff.mp h)
    simp only [ActualSignedPhysicalData.nativePressureSource, dite_eq_right hm, hL, false_and,
        ite_false]

omit P u H hp in
theorem zero_native_smooth_and_flat :
    ContDiffOn ℝ ∞ (fun _ : Native => (0 : E)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun _ : Native => (0 : E)) y = 0 := by
  refine ⟨contDiffOn_const, fun _ _ _ _ => ?_⟩
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]

variable {β : ℝ}
  (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
    (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) β
    ActualSignedStageControls.phaseCell (fun _ n _ x => request (B := B) P u n x q))

include hR in
theorem native_potential_smooth_and_flat (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n)
        ActualSignedPhysicalData.nativePast ∧
    ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
      iteratedFDeriv ℝ m (ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
        ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n) y = 0 := by
  rw [native_potential_source_factor]
  split_ifs
  · exact potential_smooth_and_flat hR (ActualSignedExterior.actualLabel L) I.2
  · exact zero_native_smooth_and_flat

include hR in
theorem native_pressure_smooth_and_flat (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n)
        ActualSignedPhysicalData.nativePast ∧
    ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
      iteratedFDeriv ℝ m (ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
        ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n) y = 0 := by
  rw [native_pressure_source_factor]
  split_ifs
  · exact pressure_smooth_and_flat hR (ActualSignedExterior.actualLabel L) I.2
  · exact zero_native_smooth_and_flat

include hR in
/-- Full positive-time native regularity of the same actual signed family.
Only the actual request jets are used; no native output smoothness is assumed. -/
theorem nativeRegular (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) where
  potential I n := (native_potential_smooth_and_flat P u H hp hR L I n).1
  pressure I n := (native_pressure_smooth_and_flat P u H hp hR L I n).1

end LiteralNativeSources

section ActualResiduals

open ActualSignedUnmaskedBinding

variable {B N0 : ℕ}

/-- The request estimate is derived from the two measured mean residuals
of the same reconstructed state. -/
theorem request_jets_from_residuals
    (u : CorrectionState.State LocalSignedRequest.Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B) u)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (u.axialResidual (ActualPrimary.commonContext B))) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) (α-1)
      ActualSignedStageControls.phaseCell
      (fun _ n _ x => request (B := B) ActualInitialization.patch u n x q) := by
  exact ActualSignedStageControls.fullRequest_jets_from_residuals ActualInitialization.geometry
    (ActualPrimary.commonContext B) u α H hfixed hθ hz
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))

/-- No regularity hypothesis on a native output or unmasked quotient is
needed: the actual mean residual classes provide all required input jets. -/
theorem nativeRegular_from_residuals
    (u : CorrectionState.State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B) u)
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b u.pressure)
    (α : ℝ)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (u.axialResidual (ActualPrimary.commonContext B)))
    (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch ActualInitialization.patch u H hp L) :=
  nativeRegular ActualInitialization.patch u H hp
    (request_jets_from_residuals u α H hfixed hθ hz) L

/-- This is the literal post-particular state used to construct the
canonical signed physical family, with its initialization and gauge intact. -/
theorem cycleNativeRegular
    (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state))
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state).pressure)
    (α : ℝ)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state) =
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state))
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (ActualPrimary.commonContext B) x.state).thetaResidual
            (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (ActualPrimary.commonContext B) x.state).axialResidual
            (ActualPrimary.commonContext B)))
    (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
      ((ActualSignedExterior.cycleFamily x H hp).singleton L) :=
  nativeRegular_from_residuals _ H hp α hfixed hθ hz L

end ActualResiduals

end NavierStokes.ActualSignedNativeRegularity

end
end

end
