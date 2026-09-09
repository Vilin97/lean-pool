/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateWitness
import LeanPool.NavierStokesAndEuler.NavierStokes.AxisPreservation

/-!
# Mixed candidate assembly from primitive axis zero germs

Potential increments may be arbitrary physical fields.  Their local axis zero
germs replace the copy-potential representation used by the original consumer.
All raw estimates, finite residual estimates, shrinking support and finite
endpoint-extension obligations remain unchanged.  The diagonal schedule, axis
blow-up, infinite residual limits and candidate consequences are derived.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GermCandidateAssembly

open Set Function Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open MixedCandidateAssembly (StageEstimates pressureStages pressureStages_zero pressureStages_succ)
open scoped Topology ContDiff

/-- A property of the actual primitive field on a local physical domain.
The zero neighborhood may depend on the point and on the stage. -/
def AxisZeroOn (Ω : Set SpaceTime) (f : VelocityField) : Prop :=
  ∀ w ∈ Ω, PhysicalGraphBounds.radialProjection w = 0 → f =ᶠ[𝓝 w] fun _ => 0

theorem AxisZeroOn.add {Ω : Set SpaceTime} {f g : VelocityField}
    (hf : AxisZeroOn Ω f) (hg : AxisZeroOn Ω g) :
    AxisZeroOn Ω (fun w => f w + g w) := by
  intro w hw ha
  filter_upwards [hf w hw ha, hg w hw ha] with y hy hz
  rw [hy, hz, add_zero]

/-- The original concrete potential-stage data supplies the new hypothesis
directly.  No regularity assertion about its copy representation is added. -/
theorem potentialStage_axisZeroOn {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (p : MixedAxisPreservation.PotentialStage h (MixedAxisPreservation.localDomain h qbig)) :
    AxisZeroOn (MixedAxisPreservation.localDomain h qbig) p.field := by
  intro w hw ha
  exact p.zero_germ hh hh1 (MixedAxisPreservation.localDomain_open hh hh1 qbig)
    hw hw.1 ha

/-- Literal supported mean-stream potentials satisfy the same local property. -/
theorem angularSupport_axisZeroOn {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (p : MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h qbig)) :
    AxisZeroOn (MixedAxisPreservation.localDomain h qbig) p.field := by
  intro w hw ha
  exact p.zero_germ (MixedAxisPreservation.localDomain_open hh hh1 qbig) hw
    (MixedAxisPreservation.radius_zero_of_axis ha)

/-- The base and finite initialization retain the same zeroth cutoff. -/
noncomputable def initializedSeries (base initial : VelocityField)
    (stages : ℕ → VelocityField) : ℕ → VelocityField
  | 0 => fun w => base w + initial w
  | j + 1 => stages j

theorem initializedSeries_zero (base initial : VelocityField) (stages : ℕ → VelocityField)
    (w : SpaceTime) : initializedSeries base initial stages 0 w = base w + initial w := rfl

theorem initializedSeries_succ (base initial : VelocityField) (stages : ℕ → VelocityField)
    (j : ℕ) : initializedSeries base initial stages (j + 1) = stages j := rfl

/-- Substituting the original stage fields gives exactly the original series. -/
theorem initializedSeries_of_potentialStage {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : MixedAxisPreservation.PotentialStage h Ω)
    (stages : ℕ → MixedAxisPreservation.PotentialStage h Ω) :
    initializedSeries base initial.field (fun j => (stages j).field) =
      MixedAxisPreservation.initializedSeries base initial stages := by
  funext j w
  cases j <;> rfl

/-- Local finiteness intersects only finitely many stage-dependent zero
neighborhoods.  On the zeroth cutoff plateau the actual potential sum has
the base germ, including the finite initialization. -/
theorem potentialSum_eq_base_germ {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    {q : SpaceTime → ℝ} {base initial : VelocityField} {stages : ℕ → VelocityField}
    {w : SpaceTime} (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hInitial : initial =ᶠ[𝓝 w] fun _ => 0)
    (hStages : ∀ j, stages j =ᶠ[𝓝 w] fun _ => 0)
    (hsmall : |scales 0 * q w| < 1 / 2) :
    SolenoidalDiagonal.potentialSum scales q (initializedSeries base initial stages)
      =ᶠ[𝓝 w] base := by
  have hz : ∀ j : ℕ, j ≠ 0 →
      initializedSeries base initial stages j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j hj
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hsum := AxisPreservation.potentialSum_eq_first_near hs hq hpos hz
  have hc := (SmoothCutoffs.scaledCutoff_eventually_one hsmall).comp_tendsto hq
  apply hsum.trans
  filter_upwards [hc, hInitial] with y hy hi
  change SmoothCutoffs.scaledCutoff (scales 0) (q y) = 1 at hy
  change SmoothCutoffs.scaledCutoff (scales 0) (q y) • (base y + initial y) = base y
  rw [hy, one_smul, hi, add_zero]

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Potential stages, given by `initializedSeries (TailGaugePotential.finalPotential H v upper
bandFloor) initial stages`. -/
noncomputable def potentialStages (upper : ℝ) (bandFloor : ℕ)
    (initial : VelocityField) (stages : ℕ → VelocityField) : ℕ → VelocityField :=
  initializedSeries (TailGaugePotential.finalPotential H v upper bandFloor) initial stages

/-- The actual mixed diagonal agrees at the origin with the constructed slow
base for all sufficiently late times.  Its blow-up is not an input. -/
theorem origin_eventually_base (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : 0 < qbig) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (hInitial : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStages : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    (fun t : ℝ => MixedPeriodicAssembly.velocity
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (potentialStages H v upper bandFloor initial stages))
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries D)) (t, 0)) =ᶠ[𝓝[<] 1]
      (fun t => FinalSlowBase.velocity H v upper bandFloor (t, 0)) := by
  have hl := ((tendsto_const_nhds.mul
    (AxisPreservation.physicalQ_origin_tendsto F.data.h_pos F.data.h_lt_half)).abs :
    Tendsto (fun t : ℝ => |scales 0 * PhysicalWaveSum.physicalQ F.data.h (t, 0)|)
      (𝓝[<] 1) (𝓝 |scales 0 * 0|))
  simp only [mul_zero, abs_zero] at hl
  have hsmall := hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [MixedAxisPreservation.origin_eventually_localDomain
    F.data.h_pos F.data.h_lt_half hqbig, hsmall] with t ht hst
  have ha := MixedAxisPreservation.radialProjection_origin t
  have hsum := potentialSum_eq_base_germ
    (base := TailGaugePotential.finalPotential H v upper bandFloor) hs
    (PhysicalWaveSum.physicalQ_smoothAt F.data.h_pos F.data.h_lt_half ht.1).continuousAt
    (PhysicalWaveSum.physicalQ_pos F.data.h_pos F.data.h_lt_half ht.1)
    (hInitial (t, 0) ht ha) (fun j => hStages j (t, 0) ht ha) hst
  have hc := (SolenoidalDiagonal.spatialCurl_eventuallyEq hsum).self_of_nhds
  have hd : SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
      (LocalAngularDiagonal.rawSeries D) (t, 0) = 0 :=
    DirectAngularDiagonal.angularSum_axis scales (PhysicalWaveSum.physicalQ F.data.h)
      (fun j => (D j).scalar) t 0 rfl rfl
  change SpatialCurl.spatialCurl (SolenoidalDiagonal.potentialSum scales
    (PhysicalWaveSum.physicalQ F.data.h)
    (initializedSeries (TailGaugePotential.finalPotential H v upper bandFloor) initial stages))
      (t, 0) + _ = _
  rw [hc, hd, add_zero, TailGaugePotential.finalPotential_sameCurl H v upper bandFloor ht.1]

theorem origin_blowup (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : 0 < qbig) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (hInitial : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStages : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (potentialStages H v upper bandFloor initial stages))
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries D)) (t, 0)‖) (𝓝[<] 1) atTop := by
  apply (FinalSlowBase.axis_tendsto H v upper bandFloor).congr'
  exact (origin_eventually_base H v upper bandFloor hqbig initial stages D hInitial hStages
      hs).symm.mono
    (fun _ ht => congrArg norm ht)

/-- This has the original finite-stage obligations, with arbitrary physical
potential increments and their primitive local axis zero germs.  It returns
the same selected schedule, exact mixed fields and full force consequences. -/
theorem exists_candidate_witness_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages j))
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
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    let A := potentialStages H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := pressureStages H v upper bandFloor pInitial pStages
    ∃ a : ℕ → ℕ, MixedCandidateWitness.SelectedSchedule F.data.h qbig A B P a ∧
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
  have haxis := origin_blowup H v upper bandFloor hqbig initial stages D hInitialAxis hStagesAxis
      hat
  refine ⟨a, ⟨hal, hap, had, ham, hat, hgap, hs, hz⟩, ea, eb, ep, ?_⟩
  exact CandidateConsequences.mixed_exists_force_with_consequences
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis

/-- The manuscript's exact candidate target follows from the same primitive
finite-stage data; no separate candidate witness is assumed. -/
theorem candidate_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages j))
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
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    candidateStatement := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ :=
    exists_candidate_witness_of_finite_stages H v upper bandFloor hqbig initial stages D
      pInitial pStages E hInitial hStages hDirect hpInitial hpStages eA eB eP hInitialAxis
          hStagesAxis
  exact ⟨_, _, forcing, hc⟩

end ActualBase

end NavierStokes.GermCandidateAssembly
