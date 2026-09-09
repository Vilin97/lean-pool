/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalAngularDiagonal

/-!
# Candidate assembly from the actual finite-stage obligations

The inputs here concern raw increments, their finite uncut prefixes, and
their local endpoint models. The scale sequence, infinite residual limits,
away extensions, divergence and blow-up are then derived for the same sums.

This is a conditional consumer. It does not construct the complete
correction iteration or supply the finite-stage estimates it requires.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedCandidateAssembly

open Set Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

universe u

/-- The quantitative obligations are all on the raw fields or finite
prefixes. In particular no infinite residual limit is a field here. -/
structure StageEstimates (h qbig : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) where
  potential_smooth : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig)
  direct_smooth : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig)
  pressure_smooth : ∀ j, ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig)
  /-- Gain of `StageEstimates`, of type `ℕ → ℝ`. -/
  gain : ℕ → ℝ
  gain_zero : 0 ≤ gain 0
  gain_pos : ∀ j, 1 ≤ j → 0 < gain j
  gain_mono : Monotone gain
  gain_top : Tendsto gain atTop atTop
  /-- Potential loss of `StageEstimates`, of type `ℕ → ℝ`. -/
  potentialLoss : ℕ → ℝ
  /-- Direct loss of `StageEstimates`, of type `ℕ → ℝ`. -/
  directLoss : ℕ → ℝ
  /-- Pressure loss of `StageEstimates`, of type `ℕ → ℝ`. -/
  pressureLoss : ℕ → ℝ
  /-- Potential constant of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  potentialConstant : ℕ → ℕ → ℝ
  /-- Direct constant of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  directConstant : ℕ → ℕ → ℝ
  /-- Pressure constant of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  pressureConstant : ℕ → ℕ → ℝ
  /-- Potential log of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  potentialLog : ℕ → ℕ → ℝ
  /-- Direct log of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  directLog : ℕ → ℕ → ℝ
  /-- Pressure log of `StageEstimates`, of type `ℕ → ℕ → ℝ`. -/
  pressureLog : ℕ → ℕ → ℝ
  potential_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    A gain potentialLoss potentialConstant potentialLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  direct_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    B gain directLoss directConstant directLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  pressure_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    P gain pressureLoss pressureConstant pressureLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  /-- Background loss of `StageEstimates`, of type `ℕ → ℝ`. -/
  backgroundLoss : ℕ → ℝ
  /-- Residual loss of `StageEstimates`, of type `ℕ → ℝ`. -/
  residualLoss : ℕ → ℝ
  finite_background : ∀ J m,
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
      (MixedDiagonalResidual.uncutVelocity A B J) m (-backgroundLoss m)
  finite_residual : ∀ J m,
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
      (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (gain J - residualLoss m)

theorem StageEstimates.exists_schedule {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P)
            := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, _, hs, hz⟩ :=
    MixedDiagonalResidual.exists_physical_schedule_residual_zero hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant
      E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual lower
  exact ⟨a, hal, hap, had, ham, hat, hrecip, hs, hz⟩

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The actual anchored base and finite initialization share stage zero. -/
noncomputable def potentialStages (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig)) : ℕ → VelocityField :=
  MixedAxisPreservation.initializedSeries (TailGaugePotential.finalPotential H v upper bandFloor)
    initial stages

/-- Pressure is recorded as the actual base plus its initialization
change, followed by the pressure differences of full correction stages. -/
noncomputable def pressureStages (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) : ℕ → PressureField :=
  fun j w => if j = 0 then FinalSlowBase.pressure H v upper bandFloor w + initial w
    else stages (j - 1) w

theorem pressureStages_zero (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) (w : SpaceTime) :
    pressureStages H v upper bandFloor initial stages 0 w =
      FinalSlowBase.pressure H v upper bandFloor w + initial w := by
  simp [pressureStages]

theorem pressureStages_succ (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) (j : ℕ) :
    pressureStages H v upper bandFloor initial stages (j + 1) = stages j := by
  funext w
  simp only [pressureStages, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel]

/-- Supply the finite-stage construction once, for these exact raw
families. All infinite-sum and final-force conditions are proved below. -/
theorem candidate_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial.field)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages
        j).field)
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig
      (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (potentialStages H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x)) :
    candidateStatement := by
  let A := potentialStages H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := pressureStages H v upper bandFloor pInitial pStages
  obtain ⟨a, _, hap, _, ham, hat, hgap, hs, hz⟩ :=
    E.exists_schedule F.data.h_pos F.data.h_lt_half hqbig 1
  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  have ha0 : 0 < ar 0 := by
    dsimp [ar]
    exact_mod_cast hap 0
  have hamin (j : ℕ) : ar 0 ≤ ar j := by
    dsimp [ar]
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (A 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hInitial hx hxz (Classical.choice (TailGaugePotential.finalPotential_awayExtensions H v upper
          bandFloor x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hpInitial hx hxz (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions H v upper
          bandFloor).2 x hx))
    simp only [P]
    exact h
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (B 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((hDirect 0).eventually_zero F.data.h_pos F.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (A j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (P j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => simpa only [P, pressureStages_succ] using hpStages j
  have ea := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0 eA
  have eb := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) (fun j _ => hDirect j) hB0 eB
  have ep := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0 eP
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    F.data.h_pos F.data.h_lt_half D hat ha0 hamin (hgap 0)
  have haxis := MixedAxisPreservation.local_initialized_final_origin_blowup
    H v upper bandFloor hqbig initial stages (LocalAngularDiagonal.angularSupport D) hat
  obtain ⟨forcing, hc, _, _⟩ := MixedPeriodicAssembly.exists_candidate_force
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis
  exact ⟨_, _, forcing, hc⟩

end ActualBase

end NavierStokes.MixedCandidateAssembly
