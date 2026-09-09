/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.CandidateConsequences

@[expose] public section

/-!
# Retaining the actual mixed candidate and its consequences

The finite-stage inputs are exactly those of
`MixedCandidateAssembly.candidate_of_finite_stages`. The same selected
schedule supplies the actual velocity and pressure sums, their endpoint
extensions, and the force with all proved consequences.
-/

noncomputable section

namespace NavierStokes.MixedCandidateWitness

open Set Filter ProblemStatement MixedCandidateAssembly
open JointResidualLimits (OneSidedExtension)
open scoped Topology ContDiff

universe u

/-- All properties of the single scale sequence selected from the finite
stage estimates, including smooth sums and vanishing residual jets. -/
noncomputable def SelectedSchedule (h qbig : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ (∀ j, 0 < a j) ∧ (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
    Tendsto (fun j => (a j : ℝ)) atTop atTop ∧ (∀ j, 1 / (a j : ℝ) < qbig) ∧
    MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
    JointResidualLimits.VanishingJointJets
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The original finite-stage inputs produce one schedule and its actual
activated fields, together with the full mixed-force conclusion. -/
theorem exists_candidate_witness_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
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
    let A := potentialStages H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := pressureStages H v upper bandFloor pInitial pStages
    ∃ a : ℕ → ℕ, SelectedSchedule F.data.h qbig A B P a ∧
      let ASum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) A
      let BSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) B
      let PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) P
      ∃ (ea : JointResidualLimits.AwayExtensions ASum)
        (eb : JointResidualLimits.AwayExtensions BSum)
        (ep : JointResidualLimits.AwayExtensions PSum),
      ∃ forcing : VelocityField,
        CandidateProperties
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        ContDiff ℝ ∞ forcing ∧
        CandidateConsequences.Consequences
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
          TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t,
            x)))
          (𝓝[<] (1 : ℝ)) atTop ∧
        (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
          ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
            |(iteratedFDeriv ℝ m forcing (t, x)
              (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
                C * (1 + t) ^ (-K)) ∧
        (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n forcing (1, x) =
          MixedPeriodicAssembly.boundaryLimits ASum BSum PSum ea eb ep x n) := by
  let A := potentialStages H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := pressureStages H v upper bandFloor pInitial pStages
  obtain ⟨a, hal, hap, had, ham, hat, hgap, hs, hz⟩ :=
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
  refine ⟨a, ⟨hal, hap, had, ham, hat, hgap, hs, hz⟩, ea, eb, ep, ?_⟩
  exact CandidateConsequences.mixed_exists_force_with_consequences
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis

end ActualBase

end NavierStokes.MixedCandidateWitness
