/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedUnmaskedBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior

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
