/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointResidualLimits
import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityApproach

/-!
# Joint flatness of the actual excluded slow-base error

One fixed schedule controls its entire compact similarity box. Beyond that
box the actual residual and virtual stress force both vanish, so the error
vanishes in every jet. The resulting estimates impose no upper bound on
the similarity radius of the approach to the origin.

The field estimated here is `FinalSlowBase.error`, which is the actual
Navier--Stokes residual minus its virtual stress force.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GlobalBaseError

open Set Filter ProblemStatement SlowBorelBase
open scoped Topology ContDiff

section Coordinates

theorem cartesian_q_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : SpaceTime} (ht : z.1 < 1) : 0 < (cartesianChart h z).1 :=
  physicalChart_positive hh hh1 ht

theorem cartesian_X_nonneg {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : SpaceTime} (ht : z.1 < 1) : 0 ≤ (cartesianChart h z).2.1 :=
  div_nonneg (AxisymmetricFields.radialEnergy_nonneg z.2) (cartesian_q_pos hh hh1 ht).le

/-- The actual implicit scale tends to zero on a joint approach, without
any bound on `X = radialEnergy / q`. -/
theorem cartesian_q_tendsto_zero {l : Filter SpaceTime} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hl : Tendsto (fun z : SpaceTime => z) l (𝓝 ((1 : ℝ), (0 : Space))))
    (ht : ∀ᶠ z in l, z.1 < 1) :
    Tendsto (fun z => (cartesianChart h z).1) l (𝓝 0) := by
  apply SimilarityApproach.physical_q_tendsto_zero
    (p := fun z : SpaceTime => AxisymmetricFields.profilePoint z.1 z.2) hh hh1
  · exact continuous_fst.continuousAt.tendsto.comp hl
  · have hsp : Tendsto (fun z : SpaceTime => z.2) l (𝓝 (0 : Space)) :=
      continuous_snd.continuousAt.tendsto.comp hl
    have he := ((AxisymmetricFields.projection 2).continuous.tendsto 0).comp hsp
    simp only [AxisymmetricFields.profilePoint, AxisymmetricFields.projection_apply,
      PiLp.zero_apply] at he ⊢
    exact he
  · exact ht

end Coordinates

section FixedSchedule

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The original schedule box contains both the supplied upper radius and
the end of the active stress annulus. -/
theorem exteriorRadius_le_box {upper : ℝ}
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper) :
    BaseExterior.nominalExteriorRadius W ≤ FinalSlowBase.boxRadius W upper :=
  hupper.trans (le_max_left _ _)

theorem error_zero_outside_box (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper)
    {z : SpaceTime} (ht : z.1 < 1)
    (hX : FinalSlowBase.boxRadius W upper < (cartesianChart F.data.h z).2.1) :
    FinalSlowBase.error H v upper B z = 0 := by
  have hr := FinalSlowBase.exterior_residual_zero H v upper B
    (show z ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W) from
      ⟨ht, (exteriorRadius_le_box hupper).trans_lt hX⟩)
  have hs := FinalSlowBase.stressForce_zero_right H v upper B ht
    ((le_max_right upper (NominalConeAssembly.activeRight W)).trans_lt hX)
  change navierStokesResidual (FinalSlowBase.velocity H v upper B)
      (FinalSlowBase.pressure H v upper B) z.1 z.2 -
      FinalSlowBase.stressForce H v upper B z = 0
  rw [hr, hs, sub_self]

/-- The exterior equalities hold on an open neighborhood, so they control
all actual derivatives of the error, not only its value. -/
theorem error_germ_zero_outside_box (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper)
    {z : SpaceTime} (ht : z.1 < 1)
    (hX : FinalSlowBase.boxRadius W upper < (cartesianChart F.data.h z).2.1) :
    FinalSlowBase.error H v upper B =ᶠ[𝓝 z] fun _ => 0 := by
  have hO := BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half
    (FinalSlowBase.boxRadius W upper)
  filter_upwards [hO.mem_nhds (show z ∈ BaseExterior.cartesianExterior F.data.h
    (FinalSlowBase.boxRadius W upper) from ⟨ht, hX⟩)] with y hy
  exact error_zero_outside_box H v upper B hupper hy.1 hy.2

theorem error_jets_zero_outside_box (upper : ℝ) (B m : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper)
    {z : SpaceTime} (ht : z.1 < 1)
    (hX : FinalSlowBase.boxRadius W upper < (cartesianChart F.data.h z).2.1) :
    iteratedFDeriv ℝ m (FinalSlowBase.error H v upper B) z = 0 := by
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (error_germ_zero_outside_box H v upper B hupper ht hX) m).self_of_nhds,
    iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- An arbitrary physical approach with compact carrier and `q → 0` is
allowed. Its similarity radius need not be bounded. The scale sequence in
`FinalSlowBase.error H v upper B` is unchanged between the two regions. -/
theorem error_jetRate (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper)
    {l : Filter SpaceTime} {K : Set SpaceTime} (hK : IsCompact K)
    (hcarrier : ∀ᶠ z in l, z ∈ K) (ht : ∀ᶠ z in l, z.1 < 1)
    (hq : Tendsto (fun z => (cartesianChart F.data.h z).1) l (𝓝 0))
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart F.data.h z).1)
      (FinalSlowBase.error H v upper B) m r := by
  let S : Set SpaceTime :=
    {z | (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper}
  have hS : ∀ᶠ z in l ⊓ 𝓟 S, z ∈ S :=
    (Filter.eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  let P : BaseResidual.PhysicalApproach (l ⊓ 𝓟 S) F.data.h 0
      (FinalSlowBase.boxRadius W upper) := {
    carrier := K
    compact := hK
    in_carrier := hcarrier.filter_mono inf_le_left
    past := ht.filter_mono inf_le_left
    radial := by
      filter_upwards [ht.filter_mono inf_le_left, hS] with z htz hSz
      exact ⟨cartesian_X_nonneg F.data.h_pos F.data.h_lt_half htz, hSz⟩
    scale := hq.mono_left inf_le_left }
  obtain ⟨C, hC, hb⟩ := FinalSlowBase.error_jetRate H v upper B P le_rfl m r hr
  have hb' := Filter.eventually_inf_principal.mp hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [ht, hb'] with z htz hbz
  by_cases hSz : z ∈ S
  · exact hbz hSz
  · have hX : FinalSlowBase.boxRadius W upper < (cartesianChart F.data.h z).2.1 :=
      lt_of_not_ge hSz
    rw [error_jets_zero_outside_box H v upper B m hupper htz hX, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg
      (cartesian_q_pos F.data.h_pos F.data.h_lt_half htz).le r)

theorem error_allJetsFlat (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper)
    {l : Filter SpaceTime} {K : Set SpaceTime} (hK : IsCompact K)
    (hcarrier : ∀ᶠ z in l, z ∈ K) (ht : ∀ᶠ z in l, z.1 < 1)
    (hq : Tendsto (fun z => (cartesianChart F.data.h z).1) l (𝓝 0)) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (FinalSlowBase.error H v upper B) := by
  intro m N
  obtain ⟨C, hC, hb⟩ := error_jetRate H v upper B hupper hK hcarrier ht hq m N (Nat.cast_nonneg N)
  refine ⟨C, hC, ?_⟩
  filter_upwards [ht, hb] with z htz hbz
  simpa only [abs_norm, abs_of_pos (cartesian_q_pos F.data.h_pos F.data.h_lt_half htz),
    Real.rpow_natCast] using hbz

end FixedSchedule

/-! ## The joint past filter at the physical origin -/

/-- Origin past, given by `𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))`. -/
noncomputable def originPast : Filter SpaceTime :=
  𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))

theorem originPast_before : ∀ᶠ z in originPast, z.1 < 1 := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hz.1

theorem originPast_tendsto :
    Tendsto (fun z : SpaceTime => z) originPast (𝓝 ((1 : ℝ), (0 : Space))) :=
  nhdsWithin_le_nhds

theorem originPast_in_compact :
    ∀ᶠ z in originPast, z ∈ Metric.closedBall ((1 : ℝ), (0 : Space)) 1 :=
  nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ zero_lt_one)

theorem originPast_q_tendsto_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    Tendsto (fun z => (cartesianChart h z).1) originPast (𝓝 0) :=
  cartesian_q_tendsto_zero hh hh1 originPast_tendsto originPast_before

section JointOrigin

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

theorem error_joint_jetRate (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper) (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    DiagonalResidual.JetRate originPast (fun z => (cartesianChart F.data.h z).1)
      (FinalSlowBase.error H v upper B) m r :=
  error_jetRate H v upper B hupper (isCompact_closedBall _ _) originPast_in_compact
    originPast_before (originPast_q_tendsto_zero F.data.h_pos F.data.h_lt_half) m r hr

theorem error_joint_allJetsFlat (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper) :
    ResidualStability.AllJetsFlat originPast (fun z => (cartesianChart F.data.h z).1)
      (FinalSlowBase.error H v upper B) :=
  error_allJetsFlat H v upper B hupper (isCompact_closedBall _ _) originPast_in_compact
    originPast_before (originPast_q_tendsto_zero F.data.h_pos F.data.h_lt_half)

/-- Full joint vanishing of all actual error jets at `(1,0)` from the past,
with no bounded-similarity-radius premise. -/
theorem error_vanishingJointJets (upper : ℝ) (B : ℕ)
    (hupper : BaseExterior.nominalExteriorRadius W ≤ upper) :
    JointResidualLimits.VanishingJointJets (FinalSlowBase.error H v upper B) := by
  intro m
  exact SimilarityApproach.jet_tendsto_zero
    (error_joint_jetRate H v upper B hupper m 1 zero_le_one)
    (originPast_q_tendsto_zero F.data.h_pos F.data.h_lt_half)

end JointOrigin

/-! ## One actual profile and one fixed enlarged schedule -/

/-- The enlargement depends only on the originally selected profile and
the supplied constant, never on the physical point, derivative order, or `q`. -/
noncomputable def actualUpper (upper : ℝ) : ℝ :=
  max upper (BaseExterior.nominalExteriorRadius FinalSlowBase.actualProfile.nominal)

/-- Actual error, given by `FinalSlowBase.error FinalSlowBase.actualProfile.certificate
FinalSlowBase.actualProfile.modulation (actualUpper upper) B`. -/
noncomputable def actualError (upper : ℝ) (B : ℕ) : VelocityField :=
  FinalSlowBase.error FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
    (actualUpper upper) B

theorem actual_error_joint_jetRate (upper : ℝ) (B m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    DiagonalResidual.JetRate originPast
      (fun z => (cartesianChart FinalSlowBase.actualProfile.outgoing.data.h z).1)
      (actualError upper B) m r :=
  error_joint_jetRate FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
    (actualUpper upper) B (le_max_right _ _) m r hr

theorem actual_error_joint_allJetsFlat (upper : ℝ) (B : ℕ) :
    ResidualStability.AllJetsFlat originPast
      (fun z => (cartesianChart FinalSlowBase.actualProfile.outgoing.data.h z).1)
      (actualError upper B) :=
  error_joint_allJetsFlat FinalSlowBase.actualProfile.certificate
      FinalSlowBase.actualProfile.modulation
    (actualUpper upper) B (le_max_right _ _)

theorem actual_error_vanishingJointJets (upper : ℝ) (B : ℕ) :
    JointResidualLimits.VanishingJointJets (actualError upper B) :=
  error_vanishingJointJets FinalSlowBase.actualProfile.certificate
      FinalSlowBase.actualProfile.modulation
    (actualUpper upper) B (le_max_right _ _)

end NavierStokes.GlobalBaseError
