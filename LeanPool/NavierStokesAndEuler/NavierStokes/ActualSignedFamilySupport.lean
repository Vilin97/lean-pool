/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeCopyFamily
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeProfiles
import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeSignedData

/-!
# Support and local smoothness of the actual signed copy family

The aggregate retains the original singleton at each active label and is
zero at omitted labels.  Positive lift-time gating commutes with this
assembly.  The source-domain statements concern the original, ungated
amplitudes on positive lift time.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedFamilySupport

open Set Function Filter ProblemStatement CorrectionInitialization
open CorrectionInitialization.ActualPrimary PhysicalWaveSum PhysicalCopyBounds
open scoped Topology ContDiff

private theorem gate_zeroCopies {H : ℕ} {K : Type*} :
    PositiveTimeCopyFamily.gate
      (DependentSignedPhysicalFamily.zeroCopies : CopyFamily H K) =
        DependentSignedPhysicalFamily.zeroCopies := by
  simp only [PositiveTimeCopyFamily.gate, DependentSignedPhysicalFamily.zeroCopies, ite_self]

private theorem gate_copyAt {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    (L : BandLabel) :
    PositiveTimeCopyFamily.gate (f.copyAt copies L) =
      f.copyAt (fun l => PositiveTimeCopyFamily.gate (copies l)) L := by
  classical
  by_cases hL : L ∈ f.active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hL]
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hL, gate_zeroCopies]

private theorem gate_diagonal {H : ℕ} {K : Type*}
    (f : BandLabel → CopyFamily H K) :
    PositiveTimeCopyFamily.gate (DependentSignedPhysicalFamily.diagonal f) =
      DependentSignedPhysicalFamily.diagonal
        (fun L => PositiveTimeCopyFamily.gate (f L)) := rfl

private theorem gate_assembled {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K) :
    PositiveTimeCopyFamily.gate (f.assembled copies) =
      f.assembled (fun L => PositiveTimeCopyFamily.gate (copies L)) := by
  unfold DependentSignedPhysicalFamily.Family.assembled
  rw [gate_diagonal]
  congr 1
  funext L
  exact gate_copyAt f copies L

private theorem gated_assembled_support {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    {a b h r Z : ℝ} {gap : ℕ}
    (hs : ∀ L, LocalPhysicalCopyBounds.SupportData
      (PositiveTimeCopyFamily.gate (copies L)) a b h r Z gap) :
    LocalPhysicalCopyBounds.SupportData
      (PositiveTimeCopyFamily.gate (f.assembled copies)) a b h r Z gap := by
  rw [gate_assembled]
  exact DependentSignedPhysicalFamily.diagonalSupport _ (f.branchSupport _ hs)

private theorem gated_assembled_smooth {H : ℕ} {K : Type*}
    (f : DependentSignedPhysicalFamily.Family)
    (copies : ActualSignedPhysicalData.NativeLabel f.active → CopyFamily H K)
    {a h r : ℝ}
    (hs : ∀ L, LocalPhysicalCopyBounds.SmoothData
      (PositiveTimeCopyFamily.gate (copies L)) a h r) :
    LocalPhysicalCopyBounds.SmoothData
      (PositiveTimeCopyFamily.gate (f.assembled copies)) a h r := by
  rw [gate_assembled]
  exact DependentSignedPhysicalFamily.diagonalSmooth _ (f.branchSmooth _ hs)

/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label

variable {B N0 : ℕ}
  (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

/-- The actual aggregate potential copies, with the sole positive-time gate. -/
noncomputable def potentialCopies (i : Fin 3) : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i)

/-- The actual aggregate pressure copies, with the same gate. -/
noncomputable def pressureCopies : CopyFamily 1 TorusInverse.Frequency :=
  PositiveTimeCopyFamily.gate
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le)

variable
  (hgeo : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.ReferenceGeometry slots ((ActualSignedExterior.family s).singleton L))

include hgeo

/-- Global support of the aggregate follows from the primitive masks and
targets of its selected singletons. -/
theorem potential_support (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialCopies s i)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius 2 0 := by
  apply gated_assembled_support
  intro L
  exact PositiveTimeSignedData.potential_support slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal) i

theorem pressure_support :
    LocalPhysicalCopyBounds.SupportData (pressureCopies s)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius 2 0 := by
  apply gated_assembled_support
  intro L
  exact PositiveTimeSignedData.pressure_support slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)

variable
  (hn : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.NativeRegular slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L))

include hn

/-- Only the native regularity near actual copy support is used. -/
theorem potential_smooth (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialCopies s i)
      ActualPolarCoverage.inner h slots.radius := by
  apply gated_assembled_smooth
  intro L
  exact PositiveTimeSignedData.potentialSmooth slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)
    (ActualSignedNativeProfiles.nativeProfiles s L) (hn L) i

theorem pressure_smooth :
    LocalPhysicalCopyBounds.SmoothData (pressureCopies s)
      ActualPolarCoverage.inner h slots.radius := by
  apply gated_assembled_smooth
  intro L
  exact PositiveTimeSignedData.pressureSmooth slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)
    (ActualSignedNativeProfiles.nativeProfiles s L) (hn L)

omit hgeo hn

/-- A nonzero original potential amplitude at positive lift time lies in
the actual source strip. No geometry or output estimate is assumed. -/
theorem potential_source_domain (i : Fin 3) (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le
        i).amplitude
      k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip ActualPrimaryBounds.strip
      ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos).domain :=
          by
  classical
  change ((ActualSignedExterior.family s).copyAt
    (fun L => ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L) i) I.1).amplitude k I x ≠ 0 at hne
  by_cases hI : I.1 ∈ (ActualSignedExterior.family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hI] at hne
    exact PositiveTimeSignedData.potential_source_domain slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton ⟨I.1.val, I.1.property, hI⟩)
      (PositiveTimeSignedData.singletonLocalization s ⟨I.1.val, I.1.property, hI⟩)
      outgoing.data.h_pos outgoing.data.h_lt_half
      (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.rightRadius_pos nominal) i k I x hx hne
  · exact (hne (by simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hI,
      DependentSignedPhysicalFamily.zeroCopies])).elim

theorem pressure_source_domain (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).amplitude
      k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip ActualPrimaryBounds.strip
      ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPolarCoverage.inner_pos).domain :=
          by
  classical
  change ((ActualSignedExterior.family s).copyAt
    (fun L => ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton L)) I.1).amplitude k I x ≠ 0 at hne
  by_cases hI : I.1 ∈ (ActualSignedExterior.family s).active
  · simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hI] at hne
    exact PositiveTimeSignedData.pressure_source_domain slots outgoing.data.h_pos.le
      ((ActualSignedExterior.family s).singleton ⟨I.1.val, I.1.property, hI⟩)
      (PositiveTimeSignedData.singletonLocalization s ⟨I.1.val, I.1.property, hI⟩)
      outgoing.data.h_pos outgoing.data.h_lt_half
      (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.rightRadius_pos nominal) k I x hx hne
  · exact (hne (by simp only [DependentSignedPhysicalFamily.Family.copyAt, dite_eq_right hI,
      DependentSignedPhysicalFamily.zeroCopies])).elim

end NavierStokes.ActualSignedFamilySupport
