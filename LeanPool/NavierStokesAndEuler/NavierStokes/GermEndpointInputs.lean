/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualEndpointInputs
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData

@[expose] public section

/-!
# Endpoint inputs for physical fields assembled by germs

The potential increments may be literal glued physical fields.  Only their
interior smoothness and actual derivative estimates enter the extension
argument; a representation by a fixed-reference copy family is unnecessary.
The zeroth potential and pressure retain the separately extended slow base.
-/

noncomputable section

namespace NavierStokes.GermEndpointInputs

open Set Function Filter ProblemStatement
open scoped Topology ContDiff


/-- Interior data for one actual physical field.  The exponent and logarithmic
loss may depend on the derivative order and on the field.  In particular this
record neither assumes an endpoint limit nor compares different stages. -/
structure PhysicalJets (h qbig : ℝ) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : SpaceTime → V) : Prop where
  smooth : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig)
  bound : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
    ‖iteratedFDeriv ℝ m f w‖ ≤
      C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
        PhysicalWaveSum.physicalQ h w ^ e

namespace PhysicalJets

variable {h qbig : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : SpaceTime → V}

/-- Adapter for the power bounds of the current-band physical construction.
The time restriction is kept, as in the physical wave estimate. -/
theorem of_power
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ e) :
    PhysicalJets h qbig f := by
  refine ⟨hf, fun m => ?_⟩
  obtain ⟨C, e, hm⟩ := hb m
  refine ⟨C, 0, e, fun w hw ht hq => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hm w hw ht hq

/-- The positive-index restriction in `RawStageBounds` is preserved. -/
theorem of_rawStage {A : ℕ → SpaceTime → V} {g L : ℕ → ℝ}
    {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig (A j) := by
  refine ⟨hf, fun m => ⟨C j m, p j m, g j - L m, ?_⟩⟩
  exact fun w hw _ hq => hb j hj m w ⟨hw.1, hw⟩ hq

/-- A smaller scale cap preserves the same constants. -/
theorem mono {qsmall : ℝ} (J : PhysicalJets h qbig f) (hq : qsmall ≤ qbig) :
    PhysicalJets h qsmall f := by
  have hsub : CutStageEstimates.physicalSublevel h qsmall ⊆
      CutStageEstimates.physicalSublevel h qbig :=
    fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩
  exact ⟨J.smooth.mono hsub, fun m => by
    obtain ⟨C, p, e, hb⟩ := J.bound m
    exact ⟨C, p, e, fun w hw => hb w (hsub hw)⟩⟩

/-- Physical identities on the open validity region identify every actual
ordinary jet.  Values at a chart face or beyond the region are irrelevant. -/
theorem congr (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : EqOn g f (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig g := by
  refine ⟨J.smooth.congr he, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  refine ⟨C, p, e, fun w hw ht hq => ?_⟩
  have hloc : g =ᶠ[𝓝 w] f := by
    filter_upwards [(CutStageEstimates.physicalSublevel_open hh hh1 qbig).mem_nhds hw]
      with z hz
    exact he hz
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hloc m]
  exact hb w hw ht hq

/-- Finite sums retain derivative bounds without identifying a summand with
any copy-family construction. -/
theorem add (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (K : PhysicalJets h qbig g) (hh : 0 < h) (hh1 : h < 1 / 2) :
    PhysicalJets h qbig (fun w => f w + g w) := by
  refine ⟨J.smooth.add K.smooth, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  obtain ⟨D, r, s, hk⟩ := K.bound m
  refine ⟨max C 0 + max D 0, max p r, min e s, fun w hw ht hq => ?_⟩
  have hq0 := PhysicalWaveSum.physicalQ_pos hh hh1 hw.1
  have hl : (1 : ℝ) ≤ 1 + |Real.log (PhysicalWaveSum.physicalQ h w)| := by
    linarith [abs_nonneg (Real.log (PhysicalWaveSum.physicalQ h w))]
  have hmono (C' p' e' : ℝ) (hp : p' ≤ max p r) (he : min e s ≤ e') :
      C' * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' ≤
        max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
    calc
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' := by
        gcongr
        exact le_max_left _ _
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hl hp) (le_max_right _ _)
        · exact Real.rpow_le_rpow_of_exponent_ge hq0 hq he
        · exact Real.rpow_nonneg hq0.le _
        · positivity
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f w‖ + ‖iteratedFDeriv ℝ m g w‖ :=
      ResidualStability.norm_jet_add_le
        (CutStageEstimates.physicalSublevel_open hh hh1 qbig) J.smooth K.smooth hw m
    _ ≤ C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e +
        D * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ r *
          PhysicalWaveSum.physicalQ h w ^ s := add_le_add (hb w hw ht hq) (hk w hw ht hq)
    _ ≤ _ := (add_le_add
      (hmono C p e (le_max_left _ _) (min_le_left _ _))
      (hmono D r s (le_max_right _ _) (min_le_right _ _))).trans_eq (by ring)

/-- This is an application of the existing local bounded-jet extension
theorem.  No new boundary regularity hypothesis is introduced. -/
theorem extension [CompleteSpace V] (J : PhysicalJets h qbig f)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) :=
  OffplaneJetExtensions.extension_of_powerLog_jets hh hh1 hqbig J.smooth J.bound hx hqx

end PhysicalJets

section MeanInputs

/-- The actual mean-pressure native bounds supply the single-field input. -/
theorem mean_field_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.field := by
  apply PhysicalJets.of_power (M.field_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.field_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

/-- This applies to both actual mean-stream potentials and the direct angular
increments, with their own physical degree and their original first band. -/
theorem mean_angular_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.angularField := by
  apply PhysicalJets.of_power (M.angular_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.angular_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

end MeanInputs

section ExistingWaveInputs

variable {h qbig : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

/-- Existing initial or signed wave data can be used for those summands.
No such data are requested for the glued particular summand. -/
theorem wave_vector_jets (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.vector := by
  apply PhysicalJets.of_power ((W.vector_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.vector_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

theorem wave_pressure_jets (W : PhysicalStageBounds.WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.pressure := by
  apply PhysicalJets.of_power ((W.pressure_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.pressure_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

end ExistingWaveInputs

section InitialCorrections

open CorrectionInitialization.ActualPrimary

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The finite potential correction at index zero uses the actual initial
wave, temporal mean, and rank mean.  The slow-base gauge is excluded here. -/
theorem initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
        := by
  have ht := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  have hr := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  apply ((wave_vector_jets WA outgoing.data.h_pos outgoing.data.h_lt_half).add
    (ht.add hr outgoing.data.h_pos outgoing.data.h_lt_half)
    outgoing.data.h_pos outgoing.data.h_lt_half).congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w _
  rw [ActualMeanPhysicalData.initialStream_angularField]
  rfl

theorem initial_direct_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField :=
  mean_angular_jets (ActualPhysicalStageBounds.actualInitialAngularInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq

/-- The finite initial pressure correction retains the actual initial
wave pressure and the pressure mean. -/
theorem initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) :=
  (wave_pressure_jets WP outgoing.data.h_pos outgoing.data.h_lt_half).add
    (mean_field_jets (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    outgoing.data.h_pos outgoing.data.h_lt_half

end InitialCorrections

/-- A finite physical sum can be extended directly from estimates of its
actual summands.  Equality is required only on the physical validity region. -/
theorem extension_of_sum3 {h qbig : ℝ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {f f₁ f₂ f₃ : SpaceTime → V}
    (J₁ : PhysicalJets h qbig f₁) (J₂ : PhysicalJets h qbig f₂)
    (J₃ : PhysicalJets h qbig f₃)
    (he : EqOn f (fun w => f₁ w + f₂ w + f₃ w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  apply OffplaneJetExtensions.extension_of_eqOn_sublevel hh hh1 he hx hqx
  exact OffplaneJetExtensions.extension_add
    (OffplaneJetExtensions.extension_add (J₁.extension hh hh1 hqbig hx hqx)
      (J₂.extension hh hh1 hqbig hx hqx)) (J₃.extension hh hh1 hqbig hx hqx)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Bounds for literal raw fields imply all three candidate endpoint inputs.
The base gauge is never subjected to a growth assumption, and the positive
stage estimate is never applied to index zero. -/
theorem endpoints_of_bounds (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    {initial : VelocityField} {pInitial : PressureField}
    (hA0 : EqOn (A 0)
      (fun w => TailGaugePotential.finalPotential H v upper bandFloor w + initial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hP0 : EqOn (P 0)
      (fun w => FinalSlowBase.pressure H v upper bandFloor w + pInitial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JA : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (A j))
    (JV : ∀ j, PhysicalJets F.data.h qbig (V j))
    (JP : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (P j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig A V P := by
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        have hx0 : x ≠ 0 := by intro he; exact hx (by simp [he])
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hA0 hx hqx
        exact OffplaneJetExtensions.extension_add
          (TailGaugePotential.finalPotential_awayExtensions H v upper bandFloor x hx0)
          (Jinitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JA (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    exact (JV j).extension F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hP0 hx hqx
        exact OffplaneJetExtensions.extension_add
          ⟨SlowBaseEndpoint.finalPressureNonzeroAxial H v upper bandFloor hx⟩
          (JpInitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JP (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx

/-- Literal fields accepted by `GermCandidateAssembly`.  In particular
`stages j` may be a glued current-particular field plus signed and mean
corrections; there is no copy-family or potential-stage argument. -/
theorem germ_stage_endpoints (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (Jstages : ∀ j, PhysicalJets F.data.h qbig (stages j))
    (JD : ∀ j, PhysicalJets F.data.h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JpStages : ∀ j, PhysicalJets F.data.h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages) := by
  apply endpoints_of_bounds H v upper bandFloor hqbig
    (fun _ _ => rfl) (fun _ _ => MixedCandidateAssembly.pressureStages_zero ..)
    Jinitial JpInitial ?_ JD ?_
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact Jstages j
  · intro j hj
    cases j with
    | zero => omega
    | succ j => simpa only [MixedCandidateAssembly.pressureStages_succ] using JpStages j

/-- Once the finite-stage estimates have been derived, only the bounded
finite initial pieces remain to be supplied.  This wrapper does not inspect
or impose a representation of any positive physical stage. -/
theorem germ_stage_endpoints_of_estimates (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages))
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (Jdirect : PhysicalJets F.data.h qbig (LocalAngularDiagonal.rawSeries D 0))
    (JpInitial : PhysicalJets F.data.h qbig pInitial) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages) := by
  apply endpoints_of_bounds H v upper bandFloor hqbig
    (fun _ _ => rfl) (fun _ _ => MixedCandidateAssembly.pressureStages_zero ..)
    Jinitial JpInitial
    (fun j hj => PhysicalJets.of_rawStage E.potential_bound hj (E.potential_smooth j)) ?_
    (fun j hj => PhysicalJets.of_rawStage E.pressure_bound hj (E.pressure_smooth j))
  intro j
  cases j with
  | zero => exact Jdirect
  | succ j =>
      exact PhysicalJets.of_rawStage E.direct_bound (Nat.succ_le_succ (Nat.zero_le j))
        (E.direct_smooth (j + 1))

end ActualBase

section ActualInitialChoice

open CorrectionInitialization.ActualPrimary

/-- The chosen initial potential supplies its own native wave data.  The
consumer does not have to provide or postulate such a witness. -/
theorem actual_initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  simpa only [InitialPhysicalData.potentialWaveData_vector] using
    initial_potential_jets B N0 N hN (InitialPhysicalData.potentialWaveData B N0) hq

theorem actual_initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) := by
  simpa only [InitialPhysicalData.pressureWaveData_pressure] using
    initial_pressure_jets B N0 N hN (InitialPhysicalData.pressureWaveData B N0) hq

/-- The same-choice mixed raw sequence has all endpoint inputs.  Positive
fields are arbitrary physical fields, including the genuine glued particular
fields.  Only their derived interior jet estimates are used.  Initialization
is bound to the actual initial wave and actual mean families by local field
identities, with no supplied wave-data or endpoint-extension witness. -/
theorem actual_germ_stage_endpoints (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig))
    (Jstages : ∀ j, PhysicalJets h qbig (stages j))
    (Jdirect : ∀ j, 1 ≤ j → PhysicalJets h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpStages : ∀ j, PhysicalJets h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply germ_stage_endpoints certificate modulation upper B (hq.trans (ChartScales.Q_le_one N))
    initial stages D pInitial pStages
    ((actual_initial_potential_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hInitial)
    Jstages ?_
    ((actual_initial_pressure_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hPressure) JpStages
  intro j
  cases j with
  | zero =>
      exact (initial_direct_jets B N0 N hN hq).congr
        outgoing.data.h_pos outgoing.data.h_lt_half hDirect
  | succ j => exact Jdirect (j + 1) (Nat.succ_le_succ (Nat.zero_le j))

/-- A derived `StageEstimates` record is an alternative source of the
positive-stage estimates.  No quantitative conclusion or representation of
the glued particular field is added as a hypothesis here. -/
theorem actual_germ_stage_endpoints_of_estimates (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages))
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply actual_germ_stage_endpoints B N0 N hN hq initial stages D pInitial pStages
    hInitial hDirect hPressure
  · intro j
    exact PhysicalJets.of_rawStage E.potential_bound (Nat.succ_le_succ (Nat.zero_le j))
      (E.potential_smooth (j + 1))
  · intro j hj
    exact PhysicalJets.of_rawStage E.direct_bound hj (E.direct_smooth j)
  · intro j
    simpa only [MixedCandidateAssembly.pressureStages_succ] using
      PhysicalJets.of_rawStage E.pressure_bound (Nat.succ_le_succ (Nat.zero_le j))
        (E.pressure_smooth (j + 1))

end ActualInitialChoice

end NavierStokes.GermEndpointInputs
