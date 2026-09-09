/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior

@[expose] public section

/-!
# Reference geometry of the actual signed family

Every singleton retains the original primary label, phase, native view,
and current-state request.  Reindexing its dependent payload changes only
the proof of the reference-band equality.  The seven reference-geometry
fields below come from these primitive identities; no equality of output
physical fields or native regularity is assumed.
-/

noncomputable section

namespace NavierStokes.ActualSignedReferenceGeometry

open Set Function CorrectionState CorrectionInitialization
open CorrectionInitialization.ActualPrimary


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

noncomputable def cycleNativeGeometry (l : Label B N0) :
    ActualSignedPhysicalData.ReferenceGeometry (h := h) slots
      ((ActualSignedExterior.cycleFamily x H hp).singleton (ActualSignedExterior.nativeLabel l)) :=
  cycleSingletonGeometry x H hp (ActualSignedExterior.nativeLabel l)

end Cycle

end NavierStokes.ActualSignedReferenceGeometry
