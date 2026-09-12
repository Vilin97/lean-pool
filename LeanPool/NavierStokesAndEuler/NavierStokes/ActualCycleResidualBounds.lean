/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseJetBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeExcludedBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeRadialResidualBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointResidualLimits
import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityApproach

/-!
# Residual estimates from the actual correction-cycle invariant

The primary family, common chart, weighted strip and carrier sets below are
the actual selected objects. Finite harmonic bounds are read from `sourceBand`.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleResidualBounds

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open LocalPhysicalCopyBounds PhysicalResidualJetBounds LabelSumBounds
open PhysicalWaveSum PhysicalGraphBounds
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Cylinder: an abbreviation for `Point × ℝ`. -/
abbrev Cylinder := Point × ℝ
/-- Index: an abbreviation for `ActualInitialization.Index`. -/
abbrev Index := ActualInitialization.Index

/-- Label carrier, given by `ActualInitialExcluded.labelCarrier (l.2, l.1) n`. -/
noncomputable def labelCarrier {B N0 : ℕ} (l : Index B N0) (n : ℕ) : Set Point :=
  ActualInitialExcluded.labelCarrier (l.2, l.1) n

theorem labelCarrier_closed {B N0 : ℕ} (l : Index B N0) (n : ℕ) : IsClosed (labelCarrier l n) :=
  ActualInitialExcluded.labelCarrier_closed (l.2, l.1) n

/-- Invariant type used in actual cycle residual bounds. -/
abbrev Invariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) :=
  CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope labelCarrier σ x

/-- Source, constructed using `HarmonicResidual.residualBlock`. -/
noncomputable def source {B N0 : ℕ} (x : CycleState (Index B N0)) (l : Index B N0) : HarmonicBlock
    Point :=
  HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)

/-- Modes, given by `Finset.Icc (-(M : ℤ)) M`. -/
noncomputable def modes (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) M

theorem mem_modes {M : ℕ} {j : ℤ} (hj : j.natAbs ≤ M) : j ∈ modes M := by
  have hh : (j.natAbs : ℤ) ≤ M := by exact_mod_cast hj
  have hpos : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hneg : -j ≤ (j.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -j))
  simp only [modes, Finset.mem_Icc]
  omega

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem source_support (l : Index B N0) (n : ℕ) (i : Fin 3) :
    ((source x l).velocity n i).support ⊆ modes x.coefficients.residualBand := by
  intro j hj
  exact mem_modes ((H.sourceBand l).1 n i j hj)

omit H in
theorem source_zero (l : Index B N0) (n : ℕ) (i : Fin 3) : (source x l).velocity n i 0 = 0 :=
  HarmonicResidual.residualBlock_zero_mode _ _ _ _ _ _ _

theorem source_carrier (l : Index B N0) : CorrectionStep.SameCarrier (source x l)
    (ActualInitialization.primaryBlock l) :=
  ⟨(H.carrier l).frequency, (H.carrier l).phase, (H.carrier l).angular⟩

theorem source_fullPhase (l : Index B N0) (j : ℤ) (n : ℕ) :
    fullPhase (source x l) j n = fullPhase (ActualInitialization.primaryBlock l) j n := by
  funext z
  simp only [fullPhase, (H.source_carrier l).frequency, (H.source_carrier l).phase,
    (H.source_carrier l).angular]

theorem source_zero_germ (l : Index B N0) (j : ℤ) (n : ℕ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain) (hout : z ∉ labelCarrier l n) :
    (fun y => fun i => (source x l).velocity n i j y) =ᶠ[𝓝 z] fun _ => 0 := by
  have he := HarmonicSourceSupport.residualSource_zero_germ_on
    (ActualPrimary.commonContext B) x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    ActualInitialization.geometry.domain_open (labelCarrier_closed l) (H.inputSupport l) j n hz hout
  filter_upwards [he] with y hy
  funext i
  exact congrFun hy i

end Invariant

theorem actual_flatGeometry :
    ∃ cL cR L : ℝ, ∃ ρ : Point → ℝ,
      PhysicalClassBounds.FlatGeometry ActualInitialization.geometry.strip cL cR L ρ := by
  let G := ActualInitialization.geometry
  exact ⟨G.leftWeight, G.rightWeight, _, _, PhysicalClassBounds.movingStrip_flatGeometry
    G.region G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one
        G.slow_ge_one⟩

theorem actual_slow_le : ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ,
    ∀ n, 4 ≤ n → ActualInitialization.geometry.strip.slow n ≤ C * ChartScales.S n ^ p := by
  refine ⟨1, le_rfl, 1, ?_⟩
  intro n hn
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  change max 1 (ChartScales.S n) ≤ 1 * ChartScales.S n ^ 1
  simp [max_eq_right hS]

theorem actual_epsilon (n : ℕ) :
    ActualInitialization.geometry.strip.epsilon n = ChartScales.epsilon ActualPrimary.h n := rfl

theorem actual_wave_weight {B N0 : ℕ} :
    ∃ c : ℝ, 0 < c ∧ ∀ (l : Index B N0) n z, z ∈ ActualInitialization.geometry.strip.domain →
      Real.sqrt (ActualInitialization.geometry.strip.zeta z) * ActualInitialization.envelope l n z ≤
        ActualInitialization.geometry.strip.zeta z ^ c := by
  refine ⟨1/2, by norm_num, ?_⟩
  intro l n z hz
  rw [← Real.sqrt_eq_rpow]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (ActualInitialization.envelope_le_one l n z)

theorem mean_source {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : ℕ → Point → E} (hf : MeanClass ActualInitialization.geometry.strip α f) :
    LocalSourceBounds ActualInitialization.geometry.strip ActualPrimary.h α
      (fun (_ : Unit) _ z => ActualInitialization.geometry.strip.zeta z) (fun (_ : Unit) => f) := by
  refine ⟨UniformPrimaryWeights.class_of_single hf, actual_flatGeometry, ?_, actual_epsilon,
      actual_slow_le⟩
  exact ⟨1, zero_lt_one, fun _ _ _ _ => by rw [Real.rpow_one]⟩

theorem sqrt_source {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : ι → ℕ → Point → E}
    (hf : UniformClass ActualInitialization.geometry.strip
      (fun _ _ z => Real.sqrt (ActualInitialization.geometry.strip.zeta z)) α f) :
    LocalSourceBounds ActualInitialization.geometry.strip ActualPrimary.h α
      (fun _ _ z => Real.sqrt (ActualInitialization.geometry.strip.zeta z)) f := by
  refine ⟨hf, actual_flatGeometry, ?_, actual_epsilon, actual_slow_le⟩
  exact ⟨1/2, by norm_num, fun _ _ _ _ => by rw [Real.sqrt_eq_rpow]⟩

theorem native_on_strip {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {w : ι → ℕ → Point → ℝ} {f : ι → ℕ → Point → E}
    (hf : LocalSourceBounds ActualInitialization.geometry.strip ActualPrimary.h α w f) :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * α) (fun _ => 0) f
        :=
  NativeBounds.of_localSource le_rfl ActualInitialization.geometry.strip.isOpen_domain hf
    (fun l n _ => hf.uniform.smooth l n) (fun _ _ _ _ hz => Or.inl (subset_closure hz))

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem source_localBounds (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    LocalSourceBounds ActualInitialization.geometry.strip ActualPrimary.h (1/2 + σ)
      (fun l n z => Real.sqrt (ActualInitialization.geometry.strip.zeta z) *
          ActualInitialization.envelope l n z)
      (fun l n z => (source x l).velocity n i j z) :=
  coefficient_source_of_uniformVelocity H.residual actual_flatGeometry actual_wave_weight
    actual_epsilon actual_slow_le i j hj

theorem source_native (i : Fin 3) (j : ℤ) :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * (1/2 + σ))
      (fun _ => 0) (fun l n z => (source x l).velocity n i j z) := by
  by_cases hj : j = 0
  · subst j
    simpa only [Invariant.source_zero, Pi.zero_apply] using
      (NativeBounds.zero : NativeBounds 4 ActualInitialization.geometry.strip.domain
        (ActualPrimary.h * (1/2 + σ)) (fun _ => 0) (fun (_ : Index B N0) _ _ => (0 : ℂ)))
  · exact native_on_strip (H.source_localBounds i j hj)

theorem gaussian_native (α : ℝ) (i : Fin 3) (j : ℤ) :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * α) (fun _ => 0)
      (fun l n z => x.coefficients.gaussian l n i j z) :=
  native_on_strip (sqrt_source (H.gaussianFlat α i j))

theorem axis_native (α : ℝ) :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * α) (fun _ => 0)
      (fun (_ : Unit) => x.axisymmetricAlias) :=
  native_on_strip (mean_source (H.axisFlat α))

/-- The current pressure alias has every power, by the actual compact
primitive and gauge estimates, independently of the accumulated alias. -/
theorem current_pressureAlias_class (α : ℝ) :
    MeanClass ActualInitialization.geometry.strip α
      (fun n z => VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge
        (ActualPrimary.commonContext B) x.state n (z, 0)) := by
  have hh := GaugeExcludedBounds.pressureAliasState_mean_bounds ActualPrimary.standardRegion
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (PrimaryTargetBounds.radii_ordered ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    ActualPrimary.outgoing.data.h_pos (by norm_num : (1 : ℝ) ≠ 0)
    (CommonWindow.index ActualPrimary.h) (CommonWindow.gap ActualPrimary.h)
    (CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.slowScale BaseContextAssembly.one_le_slowScale (fun _ => le_max_right _ _)
    (ActualPrimary.commonContext B) x.state H.primitives (ActualInitialization.operators B)
    (ActualInitialization.base_bounds B) H.cumulative H.covariance α
  dsimp only [GaugeExcludedBounds.actualGauge] at hh
  rw [← ActualInitialCoherence.commonGauge_eq_similarity] at hh
  exact hh.1

theorem alias_eq_lift : x.state.errors.aliasError = fun n z => x.axisymmetricAlias n z.1 :=
  H.representation.alias_eq_lift H.aliasCoefficients

theorem meanGood_eq_reduced_sub (n : ℕ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.strip.domain) (i : Fin 3) :
    x.state.meanGoodResidual (ActualPrimary.commonContext B) n z i =
      x.state.reducedMeanResidual (ActualPrimary.commonContext B) n z i -
        x.axisymmetricAlias n z i := by
  have ha : CorrectionStep.AngularContinuous x.state.errors.aliasError := by
    rw [H.alias_eq_lift]
    intro n z i
    change Continuous (fun _ : ℝ => x.axisymmetricAlias n z i)
    exact continuous_const
  have ham : angularMeanVector x.state.errors.aliasError = x.axisymmetricAlias := by
    rw [H.alias_eq_lift]
    funext n z i
    exact congrFun (congrFun (angularAverage_axisymmetric (fun n z => x.axisymmetricAlias n z i))
        n) z
  rw [meanGoodResidual_at _ _ n z i
    (H.baseAngular n z (ActualInitialization.geometry.strip_subset hz) i)
    (H.representation.gaussian_angularContinuous n z i) (ha n z i), H.gaussianMean, ham]
  simp

/-- The missing radial component is derived from the measured pressure
debt, the literal reconstructed pressure and the current compact alias. -/
theorem radial_mean_class :
    MeanClass ActualInitialization.geometry.strip (1 + σ)
      (fun n z => x.state.meanGoodResidual (ActualPrimary.commonContext B) n z 0) := by
  let G := ActualInitialization.geometry
  have hr : GaugeRadialResidualBounds.RadialMatch G.region.carrier G.gauge
      (ActualPrimary.commonContext B).operators := by
    rw [← ActualInitialization.geometry_operators B]
    exact GaugeRadialResidualBounds.RadialMatch.nativeOperators G.region.carrier
      G.gauge G.epsilon G.fast G.axial G.time G.temporal
  have hd : UnweightedClass G.slowStrip (1 + σ)
      (pressureDefect (ActualPrimary.commonContext B) x.state) := H.debt 0
  have hfixed : (VariableGaugeMean.reconstructState G.gauge
      (ActualPrimary.commonContext B) x.state).pressure = x.state.pressure :=
    congrArg State.pressure H.reconstructed
  have hg := GaugeRadialResidualBounds.radialMinusAlias_class G.region G.gauge
    G.inner_pos G.exponent_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one G.length_eq (ActualPrimary.commonContext B) x.state
    H.primitives hr hfixed hd
  have hp := (H.current_pressureAlias_class (1 + σ)).map (ContinuousLinearMap.proj (0 : Fin 3))
  have ha := (H.axisFlat (1 + σ)).map (ContinuousLinearMap.proj (0 : Fin 3))
  apply MeanIncrementBounds.class_congr (MeanIncrementBounds.Class.sub (hg.add hp) ha)
  intro n z hz
  dsimp only
  rw [H.meanGood_eq_reduced_sub n hz 0]
  change x.state.radialResidual (ActualPrimary.commonContext B) n z - x.axisymmetricAlias n z 0 =
    (x.state.radialResidual (ActualPrimary.commonContext B) n z -
      VariableGaugeMean.pressureAliasState G.gauge (ActualPrimary.commonContext B) x.state n (z, 0)
          0 +
      VariableGaugeMean.pressureAliasState G.gauge (ActualPrimary.commonContext B) x.state n (z, 0)
          0) -
        x.axisymmetricAlias n z 0
  ring

theorem mean_component_class (i : Fin 3) :
    MeanClass ActualInitialization.geometry.strip (1 + σ)
      (fun n z => x.state.meanGoodResidual (ActualPrimary.commonContext B) n z i) := by
  fin_cases i
  · exact H.radial_mean_class
  · exact H.mean.angular
  · exact H.mean.axial

theorem mean_native :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * (1 + σ))
      (fun _ => 0) (fun (_ : Unit) => x.state.meanGoodResidual (ActualPrimary.commonContext B)) :=
          by
  apply NativeBounds.pi (by norm_num) ActualInitialization.geometry.strip.isOpen_domain
  intro i
  exact native_on_strip (mean_source (H.mean_component_class i))

theorem extraction_regular (n : ℕ)
    (hdisj : ∀ l ∈ x.coefficients.labels n, ∀ k ∈ x.coefficients.labels n, l ≠ k →
      Disjoint (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain ∩
        tsupport ((x.coefficients.blocks l).oscillation n))
        (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain ∩
          tsupport ((x.coefficients.blocks k).oscillation n))) :
    LocalResidualGrouping.ExtractionRegular ActualInitialization.geometry.strip.domain
      (ActualPrimary.commonContext B) x.state x.coefficients.labels x.coefficients.blocks
      x.coefficients.gaussian x.coefficients.aliasCoefficients n := by
  let G := ActualInitialization.geometry
  constructor
  · exact HarmonicResidual.contextFrame_regular (ActualPrimary.commonContext B) n contDiffOn_fst
      (fun z hz => (ActualInitialization.radius_pos B z hz).ne')
      ((ActualInitialization.operators B).radialProfile.smooth n)
  · intro i
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((ActualInitialization.base_bounds
        B).radial.smooth n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((ActualInitialization.base_bounds
        B).angular.smooth n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((ActualInitialization.base_bounds
        B).axial.smooth n)
  · intro i
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((H.primitives.mean.radial.smooth n).mono G.strip_subset)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((H.primitives.mean.angular.smooth n).mono G.strip_subset)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((H.primitives.mean.axial.smooth n).mono G.strip_subset)
  · exact ((H.primitives.pressure G.inner_pos G.exponent_pos G.length_eq
      (congrArg State.pressure H.reconstructed)).smooth n).mono G.strip_subset
  · intro l hl
    refine ⟨H.phase l n, ?_, ?_⟩
    · intro i
      exact (show HarmonicResidual.SmoothCoefficients G.strip.domain
        ((x.coefficients.blocks l).velocity n i) from fun j => (H.wave i j).smooth l
            n).realCoefficients
    · exact (show HarmonicResidual.SmoothCoefficients G.strip.domain
        ((x.coefficients.blocks l).pressure n) from fun j => (H.pressure j).smooth l
            n).realCoefficients
  · intro l hl i j
    exact (H.gaussianFlat 0 i j).smooth l n
  · intro l hl i
    rw [H.aliasCoefficients l]
    exact HarmonicResidual.smoothCoefficients_zero _
  · exact hdisj
  · intro l hl
    exact H.angular l n

/-- The independent accumulated axisymmetric alias is retained in the
grouping and cancels only through the proved angular mean equation. -/
theorem fullResidual_decomposition {n : ℕ}
    (hreg : LocalResidualGrouping.ExtractionRegular ActualInitialization.geometry.strip.domain
      (ActualPrimary.commonContext B) x.state x.coefficients.labels x.coefficients.blocks
      x.coefficients.gaussian x.coefficients.aliasCoefficients n)
    {z : Cylinder} (hz : z ∈ HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
    (i : Fin 3) :
    LiftedMeanResidual.fullResidual (ActualPrimary.commonContext B) x.state n z i =
      (∑ l ∈ x.coefficients.labels n, (source x l).oscillation n z i) +
        x.state.meanGoodResidual (ActualPrimary.commonContext B) n z.1 i + x.state.errors.total n z
            i := by
  change CorrectionStep.fullResidual (ActualPrimary.commonContext B) x.state n z i = _
  rw [H.representation.fullResidual_reconstructed_local
    ActualInitialization.geometry.strip.isOpen_domain hreg hz i]
  have havg := LocalResidualGrouping.stateGoodResidual_angularAverage
    ActualInitialization.geometry.strip.isOpen_domain H.representation.withAxis hreg hz.1 i
  have hmean := LiftedMeanResidual.angularMean_fullGoodResidual H.meanHypotheses n hz.1 i
  change angularAverage (fun m y => HarmonicResidual.stateGoodResidual
    (ActualPrimary.commonContext B) x.state m y i) n z.1 =
      x.state.meanGoodResidual (ActualPrimary.commonContext B) n z.1 i at hmean
  rw [← havg, hmean]
  rfl

end Invariant

theorem native_restrict {D E ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {N M : ℕ} {U V : Set D}
    {gain : ℝ} {loss : ℕ → ℝ} {f : ι → ℕ → D → E}
    (hf : NativeBounds N U gain loss f) (hNM : N ≤ M) (hVU : V ⊆ U) :
    NativeBounds M V gain loss f := by
  refine ⟨fun l n hn => (hf.smooth l n (hNM.trans hn)).mono hVU, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun l n hn z hz => hb l n (hNM.trans hn) z (hVU hz)⟩

theorem native_lift {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {U : Set Point} {gain : ℝ} {loss : ℕ → ℝ} {f : ι → ℕ → Point → E}
    (hU : IsOpen U) (hf : NativeBounds N U gain loss f) :
    NativeBounds N (HarmonicResidual.liftDomain U) gain loss
      (fun l n (z : Cylinder) => f l n z.1) := by
  rw [LocalResidualGrouping.liftDomain_eq_preimage]
  apply hf.pull_linear hU (ContinuousLinearMap.fst ℝ Point ℝ)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z.1‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using norm_fst_le z

theorem normalizedBase_native (B : ℕ) (α : ℝ) :
    NativeBounds 4 (BaseContextAssembly.slowCarrier ActualPrimary.nominal
        ActualPrimary.standardRegion)
      (ActualPrimary.h * α) (fun _ => 0)
      (fun (_ : Unit) => ActualInitialExcluded.normalizedBase ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper B) := by
  refine ⟨fun _ n _ => ActualInitialExcluded.normalizedBase_smooth _ _ _ _ _ n, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := ActualInitialExcluded.normalizedBase_prefix ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion α m
  refine ⟨C, hC, 0, ?_⟩
  intro _ n _ z hz j hj
  simpa only [sub_zero, pow_zero, mul_one, ChartScales.epsilon,
    ← Real.rpow_mul (ChartScales.Q_pos n).le] using hb n z hz j hj

/-- The fixed base error uses its actual all-power physical estimate.
No flat edge weight is incorrectly assigned to this term. -/
theorem baseError_native (B : ℕ) (α : ℝ) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * α) (fun _ => 0) (fun (_ : Unit) => ActualInitialization.baseError B) := by
  have hS := BaseContextAssembly.slowCarrier_open ActualPrimary.nominal ActualPrimary.standardRegion
  have hV := ActualInitialization.geometry.strip.isOpen_domain
  have hp := (normalizedBase_native B α).pull_linear hS BaseContextAssembly.slowCoordinates
    BaseContextAssembly.slowCoordinates_norm_le
  have hp' := native_restrict hp le_rfl
    (BaseContextAssembly.slowCoordinates_maps ActualPrimary.nominal ActualPrimary.standardRegion)
  have hc : NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * α)
      (fun _ => 0) (fun (_ : Unit) n z => ActualInitialization.baseError B n (z, 0)) := by
    apply NativeBounds.pi (by norm_num) hV
    intro i
    apply (hp'.map hV (AxisymmetricFields.projection i)).congr hV
    intro _ n _ z _
    exact (ActualInitialExcluded.baseError_zero_angle ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B n z i).symm
  apply (native_lift hV hc).congr (HarmonicResidual.liftDomain_open hV)
  intro _ n _ z hz
  ext i
  exact (ActualBaseResidual.baseError_angle_eq ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B n (ActualInitialization.radius_pos B z.1 hz.1)
    (ActualInitialization.strip_time z.1 hz.1) z.2 i).symm

/-- Smoothness of the actual full graph operator follows from its
primitive coefficients and their actual directional derivatives. -/
theorem graphResidual_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (ε : ℝ) {R : E → ℝ} {Vr Vθ Vz Vt : E → E}
    {a : E → Fin 3 → ℝ} {p : E → ℝ} (hR : ContDiffOn ℝ ∞ R U)
    (hRne : ∀ z ∈ U, R z ≠ 0)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (ht : ContDiffOn ℝ ∞ Vt U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun z => a z i) U) (hp : ContDiffOn ℝ ∞ p U) :
    ContDiffOn ℝ ∞ (PhysicalResidualBridge.graphResidual ε R Vr Vθ Vz Vt a p) U := by
  have hi := hR.inv hRne
  have hi2 := (hR.pow 2).inv (fun z hz => pow_ne_zero 2 (hRne z hz))
  have hDr i := HarmonicCalculus.contDiffOn_along hU hr (ha i)
  have hDθ i := HarmonicCalculus.contDiffOn_along hU hθ (ha i)
  have hDz i := HarmonicCalculus.contDiffOn_along hU hz (ha i)
  have hDt i := HarmonicCalculus.contDiffOn_along hU ht (ha i)
  have hPr := HarmonicCalculus.contDiffOn_along hU hr hp
  have hPθ := HarmonicCalculus.contDiffOn_along hU hθ hp
  have hPz := HarmonicCalculus.contDiffOn_along hU hz hp
  have hLap (i : Fin 3) : ContDiffOn ℝ ∞
      (HarmonicCalculus.cylindricalLaplacian R Vr Vθ Vz (fun z => a z i)) U :=
    (((HarmonicCalculus.contDiffOn_along hU hr (hDr i)).add (hi.smul (hDr i))).add
      (hi2.smul (HarmonicCalculus.contDiffOn_along hU hθ (hDθ i)))).add
      (HarmonicCalculus.contDiffOn_along hU hz (hDz i))
  have hJ (b : E → Fin 3 → ℝ) (hb : ∀ i, ContDiffOn ℝ ∞ (fun z => b z i) U)
      (i : Fin 3) : ContDiffOn ℝ ∞ (fun z => LinearWaveResidual.realAngularGenerator (b z) i) U :=
          by
    fin_cases i
    · exact (hb 1).neg
    · exact hb 0
    · exact contDiffOn_const
  have htransport (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => LinearWaveResidual.realTransport R Vr Vθ Vz a a z i) U :=
    (((ha 0).mul (hDr i)).add (((ha 1).div hR hRne).mul ((hDθ i).add (hJ a ha i)))).add
      ((ha 2).mul (hDz i))
  have hframe (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => LinearWaveResidual.realFrameLaplacian R Vr Vθ Vz a z i) U :=
    (hLap i).add (hi2.mul ((contDiffOn_const.mul
      (hJ (fun z j => HarmonicCalculus.along Vθ (fun y => a y j) z) hDθ i)).add
        (hJ (fun z => LinearWaveResidual.realAngularGenerator (a z)) (hJ a ha) i)))
  have hgrad (i : Fin 3) : ContDiffOn ℝ ∞ (fun z =>
      ![HarmonicCalculus.along Vr p z, (R z)⁻¹ * HarmonicCalculus.along Vθ p z,
        HarmonicCalculus.along Vz p z] i) U := by
    fin_cases i
    · exact hPr
    · exact hi.mul hPθ
    · exact hPz
  exact contDiffOn_pi.mpr (fun i =>
    (((hDt i).add (htransport i)).sub (contDiffOn_const.mul (hframe i))).add (hgrad i))

/-- The local primitive realization also supplies smoothness of the full
native residual across the radial edges. It is not an output-jet premise. -/
theorem realization_native_smooth {h : ℝ} {N : ℕ} {gap : ℕ → ℕ} {U : Set Cylinder}
    {c : Context Point} {s : State Point} {p₀ : ℕ → Cylinder → ℝ}
    {u : ProblemStatement.VelocityField} {P : ProblemStatement.PressureField}
    (r : StateRealization h N gap U c s p₀ u P) {n : ℕ} (hn : N ≤ n) :
    ContDiffOn ℝ ∞ (LiftedMeanResidual.fullResidual c s n) U := by
  let G := bandGraph h n (gap n)
  let V : Set Cylinder := PhysicalResidualTZ.swapCylinder ⁻¹' U
  have hV : IsOpen V := r.domain_open.preimage PhysicalResidualTZ.swapCylinder.continuous
  have hR : ∀ z ∈ V, z.1.1 ≠ 0 := fun z hz => r.radius_ne (PhysicalResidualTZ.swapCylinder z) hz
  have hB (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => PhysicalResidualBridge.baseComponents (PhysicalResidualTZ.swapContext c) n z i) V :=
    (r.base_smooth n hn i).comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn (fun _ hz => hz)
  have ha (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => PhysicalResidualBridge.incrementComponents (PhysicalResidualTZ.swapState s) n z i)
          V :=
    (r.increment_smooth n hn i).comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn (fun _ hz
        => hz)
  have hp : ContDiffOn ℝ ∞ ((PhysicalResidualTZ.swapState s).totalPressureIncrement n) V :=
    (r.pressure_smooth n hn).comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn (fun _ hz =>
        hz)
  have hp₀ : ContDiffOn ℝ ∞ (fun z => p₀ n (PhysicalResidualTZ.swapCylinder z)) V :=
    (r.base_pressure_smooth n hn).comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn (fun _
        hz => hz)
  have hbase (z : Cylinder) (hz : z ∈ V) (i : Fin 3) :
      PhysicalResidualBridge.graphResidual G.epsilon PhysicalResidualBridge.ScaledGraph.radius
        G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial G.temporal
        (PhysicalResidualBridge.baseComponents (PhysicalResidualTZ.swapContext c) n)
        (fun y => p₀ n (PhysicalResidualTZ.swapCylinder y)) z i =
      LiftedMeanResidual.virtualDivergence (PhysicalResidualTZ.swapContext c) n z i +
        (PhysicalResidualTZ.swapState s).errors.base n z i := by
    change PhysicalResidualBridge.graphResidual G.epsilon PhysicalResidualBridge.ScaledGraph.radius
      G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial G.temporal
      (fun y => PhysicalResidualBridge.baseComponents c n (PhysicalResidualTZ.swapCylinder y))
      (fun y => p₀ n (PhysicalResidualTZ.swapCylinder y)) z i = _
    rw [PhysicalResidualTZ.graphResidual_swap, PhysicalResidualTZ.virtualDivergence_swap]
    exact r.base_equation n hn (PhysicalResidualTZ.swapCylinder z) hz i
  have hs : ContDiffOn ℝ ∞
      (LiftedMeanResidual.fullResidual (PhysicalResidualTZ.swapContext c)
          (PhysicalResidualTZ.swapState s) n) V := by
    have hgraph := graphResidual_smooth (Vθ := PhysicalResidualBridge.ScaledGraph.angular)
      (Vz := G.axial) (Vt := G.temporal) hV G.epsilon contDiffOn_fst.fst hR
      (G.radial_smooth hR) contDiffOn_const contDiffOn_const contDiffOn_const
      (fun i => (hB i).add (ha i)) (hp₀.add hp)
    apply hgraph.congr
    intro z hz
    ext i
    exact PhysicalResidualBridge.context_fullResidual_eq_graph (r.matching n hn).toMatchesAt
      (PhysicalResidualTZ.swapState s) hV hR hB ha hp₀ hp hz (hbase z hz) i
  have hcomp := hs.comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn
    (show MapsTo PhysicalResidualTZ.swapCylinder U V from fun z hz => by
      change PhysicalResidualTZ.swapCylinder (PhysicalResidualTZ.swapCylinder z) ∈ U
      simpa using hz)
  apply hcomp.congr
  intro z hz
  ext i
  exact (PhysicalResidualTZ.fullResidual_swap c s n (PhysicalResidualTZ.swapCylinder z) i).symm

/-! ## The fixed exterior base and the full physical endpoint -/

/-- Active as an element of `Set ProblemStatement.SpaceTime`. -/
noncomputable def active : Set ProblemStatement.SpaceTime :=
  {w | (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∈
    Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)}

theorem actual_upper_covers_exterior :
    BaseExterior.nominalExteriorRadius ActualPrimary.nominal ≤ ActualPrimary.upper := by
  let R := NominalConeAssembly.activeRight ActualPrimary.nominal
  have hR : 0 < R := FinalSlowBase.terminal_pos ActualPrimary.nominal
  have hswitch : BaseExterior.nominalHeatSwitch ActualPrimary.nominal ≤ R := by
    change ActualPrimary.nominal.controls.radius *
      Real.exp (OutgoingTail.tailStart ActualPrimary.outgoing.data + 1/5) ≤
        ActualPrimary.nominal.controls.radius *
          Real.exp (OutgoingTail.tailStart ActualPrimary.outgoing.data + 3)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      ActualPrimary.nominal.controls.radius_pos.le
  have houter : AssembledSlowBase.nominalOuterX ActualPrimary.nominal ≤ R :=
    (AssembledSlowBase.nominalOuterX_lt_switch ActualPrimary.nominal).le.trans hswitch
  have hexp : Real.exp (1/5 : ℝ) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)
  have hlate : BaseExterior.nominalHeatSwitch ActualPrimary.nominal * Real.exp 3 ≤ 2 * R := by
    have he : BaseExterior.nominalHeatSwitch ActualPrimary.nominal * Real.exp 3 =
        R * Real.exp (1/5 : ℝ) := by
      change ActualPrimary.nominal.controls.radius *
        Real.exp (OutgoingTail.tailStart ActualPrimary.outgoing.data + 1/5) * Real.exp 3 =
          (ActualPrimary.nominal.controls.radius *
            Real.exp (OutgoingTail.tailStart ActualPrimary.outgoing.data + 3)) * Real.exp (1/5)
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hexp hR.le).trans_eq (mul_comm R 2)
  change max (AssembledSlowBase.nominalOuterX ActualPrimary.nominal)
    (max ActualPrimary.nominal.controls.radius
      (BaseExterior.nominalHeatSwitch ActualPrimary.nominal * Real.exp 3)) ≤ 2 * R
  exact max_le (houter.trans (by linarith))
    (max_le (((AssembledSlowBase.nominalOuterX_gt_radius ActualPrimary.nominal).le.trans
        houter).trans
      (by linarith)) hlate)

theorem base_residual_germ (B : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ preterminal) (hout : w ∉ active) :
    residual (FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B)
      (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B)
      =ᶠ[𝓝 w] FinalSlowBase.error ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B := by
  have hs : FinalSlowBase.stressForce ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B =ᶠ[𝓝 w] fun _ => 0 := by
    by_cases hl : (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 <
        NominalConeAssembly.activeLeft ActualPrimary.nominal
    · exact FinalSlowBase.stressForce_core_germ _ _ _ _ hw hl
    · exact FinalSlowBase.stressForce_exterior_germ _ _ _ _ hw
        (lt_of_not_ge (fun hr => hout ⟨le_of_not_gt hl, hr⟩))
  filter_upwards [hs] with y hy
  exact (FinalSlowBase.residual_identity ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B y).trans (by rw [hy, zero_add])

theorem base_exterior_jetRate (B m : ℕ) (r : ℝ) :
    DiagonalResidual.JetRate (GlobalBaseError.originPast ⊓ 𝓟 activeᶜ)
      (physicalQ ActualPrimary.h)
      (residual (FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B)
        (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
            ActualPrimary.upper B)) m r := by
  have he := GlobalBaseError.error_joint_jetRate ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B actual_upper_covers_exterior m (max 0 r) (le_max_left _ _)
  have hsmall : ∀ᶠ w in GlobalBaseError.originPast,
      0 < physicalQ ActualPrimary.h w ∧ physicalQ ActualPrimary.h w ≤ 1 := by
    have hs := (GlobalBaseError.originPast_q_tendsto_zero ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half).eventually (eventually_le_nhds (by
          norm_num : (0 : ℝ) < 1))
    filter_upwards [GlobalBaseError.originPast_before, hs] with w hw hsw
    exact ⟨physicalQ_pos ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half
        hw, hsw⟩
  have he' : DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h)
      (FinalSlowBase.error ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
          B) m r :=
    he.weaken hsmall (le_max_right _ _)
  obtain ⟨C, hC, hb⟩ := he'
  refine ⟨C, hC, ?_⟩
  rw [Filter.eventually_inf_principal]
  filter_upwards [hb, GlobalBaseError.originPast_before] with w hbw hw hout
  rw [iteratedFDeriv_eq_of_eventuallyEq (base_residual_germ B hw hout) m]
  exact hbw

/-! ## Actual carriers, phases, and bounded label sums -/

/-- Gaussian modes, bundling `velocity`, `pressure`, `frequency`, `phase` and the required
compatibility proofs. -/
noncomputable def gaussianModes {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) : HarmonicBlock Point where
  velocity n i := HarmonicResidual.nonconstant (x.coefficients.gaussian l n i)
  pressure := 0
  frequency := (x.coefficients.blocks l).frequency
  phase := (x.coefficients.blocks l).phase
  angularFrequency := (x.coefficients.blocks l).angularFrequency

theorem coefficient_tsupport_carrier {B N0 : ℕ} {E : Type}
    [NormedAddCommGroup E] {l : Index B N0} {n : ℕ} {a : Point → E}
    (ha : ∀ z ∈ ActualInitialization.geometry.domain, z ∉ labelCarrier l n → a z = 0)
    {z : Cylinder} (hz : z ∈ HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
    (hs : z ∈ tsupport (fun y : Cylinder => a y.1)) : z.1 ∈ labelCarrier l n := by
  by_contra hn
  apply (notMem_tsupport_iff_eventuallyEq.mpr (show (fun y : Cylinder => a y.1) =ᶠ[𝓝 z] fun _ => 0
      from ?_)) hs
  have hU := (ActualInitialization.geometry.domain_open.inter (labelCarrier_closed l
      n).isOpen_compl).preimage
    (continuous_fst : Continuous (Prod.fst : Cylinder → Point))
  filter_upwards [hU.mem_nhds (show z.1 ∈ ActualInitialization.geometry.domain ∩ (labelCarrier l
      n)ᶜ from
    ⟨ActualInitialization.geometry.strip_subset hz.1, hn⟩)] with y hy
  exact ha y.1 hy.1 hy.2

theorem oscillation_eq_zero_of_coefficients (b : HarmonicBlock Point) (n : ℕ) (z : Cylinder)
    (hb : ∀ i j, b.velocity n i j z.1 = 0) : b.oscillation n z = 0 := by
  ext i
  simp only [HarmonicBlock.oscillation, HarmonicFields.field, HarmonicFields.evaluate, Finsupp.sum,
    hb, zero_mul, Finset.sum_const_zero, Complex.zero_re, Pi.zero_apply]

theorem oscillation_tsupport_carrier {B N0 : ℕ} {l : Index B N0} {n : ℕ}
    {b : HarmonicBlock Point}
    (hb : ∀ z ∈ ActualInitialization.geometry.domain, z ∉ labelCarrier l n →
      ∀ i j, b.velocity n i j z = 0)
    {z : Cylinder} (hz : z ∈ HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
    (hs : z ∈ tsupport (b.oscillation n)) : z.1 ∈ labelCarrier l n := by
  by_contra hn
  apply (notMem_tsupport_iff_eventuallyEq.mpr (show b.oscillation n =ᶠ[𝓝 z] fun _ => 0 from ?_)) hs
  have hU := (ActualInitialization.geometry.domain_open.inter (labelCarrier_closed l
      n).isOpen_compl).preimage
    (continuous_fst : Continuous (Prod.fst : Cylinder → Point))
  filter_upwards [hU.mem_nhds (show z.1 ∈ ActualInitialization.geometry.domain ∩ (labelCarrier l
      n)ᶜ from
    ⟨ActualInitialization.geometry.strip_subset hz.1, hn⟩)] with y hy
  exact oscillation_eq_zero_of_coefficients b n y (hb y.1 hy.1 hy.2)

theorem fullPhase_eq_weighted {B N0 : ℕ} (b : Index B N0 → HarmonicBlock Point)
    (hc : ∀ l, CorrectionStep.SameCarrier (b l) (ActualInitialization.primaryBlock l))
    (l : Index B N0) (j : ℤ) (n : ℕ) :
    fullPhase (b l) j n = fun z => (j : ℝ) * ActualPhaseJetBounds.weightedPhase (l.2, l.1) n z := by
  funext z
  rw [fullPhase, ← (hc l).frequency, ← (hc l).phase, ← (hc l).angular]
  congr 1
  exact (ActualPhaseJetBounds.weightedPhase_eq_section (l.2, l.1) n z).symm

theorem supportedPhaseBounds {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (b : Index B N0 → HarmonicBlock Point)
    (hc : ∀ l, CorrectionStep.SameCarrier (b l) (ActualInitialization.primaryBlock l))
    (a : Index B N0 → ℕ → Point → ℂ)
    (ha : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∉ labelCarrier l n → a l n z = 0)
    (j : ℤ) :
    SupportedPhaseBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (2 * ActualPrimary.h) (fun l n z => a l n z.1) (fun l => fullPhase (b l) j) := by
  constructor
  · intro l n hn z hz hs
    rw [fullPhase_eq_weighted b hc]
    exact SmoothNear.of_open
      (HarmonicResidual.liftDomain_open ActualInitialization.geometry.strip.isOpen_domain)
      (contDiffOn_const.mul ((ActualPhaseJetBounds.weightedPhase_contDiffOn (l.2, l.1) n).mono
        (fun _ hy => hy.1))) hz
  · intro m
    obtain ⟨C, hC, p, hb⟩ := ActualPhaseJetBounds.harmonicPhase_positive_jets
      (B := B) (N0 := N0) (max 1 |(j : ℝ)|) (le_max_left _ _) m
    refine ⟨C, hC, p, ?_⟩
    intro l n hn z hz hs k hk hkm
    have hcar := coefficient_tsupport_carrier (ha l n) hz hs
    obtain ⟨v, hv⟩ := ActualCarrierGeometry.labelCarrier_phaseCell hN (l.2, l.1) n hz.1 hcar
    rw [fullPhase_eq_weighted b hc]
    exact hb j (le_max_right _ _) n ((l.2, l.1), v) z hv k hk hkm

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem source_coeff_zero_off (l : Index B N0) (n : ℕ) (z : Point)
    (hz : z ∈ ActualInitialization.geometry.domain) (hn : z ∉ labelCarrier l n) (i : Fin 3) (j : ℤ)
        :
    (source x l).velocity n i j z = 0 :=
  congrFun (H.source_zero_germ l j n hz hn).eq_of_nhds i

theorem wave_coeff_zero_off (l : Index B N0) (n : ℕ) (z : Point)
    (hz : z ∈ ActualInitialization.geometry.domain) (hn : z ∉ labelCarrier l n) (i : Fin 3) (j : ℤ)
        :
    (x.coefficients.blocks l).velocity n i j z = 0 := by
  by_cases hj : j = 0
  · subst j
    rw [H.zeroVelocity l n i]
    rfl
  · have he := ((H.inputSupport l).velocity n i) j hj z hz hn
    rwa [HarmonicResidual.realCoefficients_eq_self (H.realCoefficients.velocity l n i)] at he

theorem gaussian_coeff_zero_off (l : Index B N0) (n : ℕ) (z : Point)
    (hz : z ∈ ActualInitialization.geometry.domain) (hn : z ∉ labelCarrier l n) (i : Fin 3) (j : ℤ)
        :
    (gaussianModes x l).velocity n i j z = 0 := by
  by_cases hj : j = 0
  · subst j
    simp [gaussianModes, HarmonicResidual.nonconstant]
  · have he := ((H.inputSupport l).gaussian n i) j hj z hz hn
    rw [HarmonicResidual.realCoefficients_eq_self (H.realCoefficients.gaussian l n i)] at he
    simpa only [gaussianModes, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
        Finsupp.erase_ne hj] using he

theorem actual_disjoint (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {l k : Index B N0} (hlk : l ≠ k) :
    Disjoint (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain ∩
      tsupport ((x.coefficients.blocks l).oscillation n))
      (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain ∩
        tsupport ((x.coefficients.blocks k).oscillation n)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hl := oscillation_tsupport_carrier (H.wave_coeff_zero_off l n) hz.1 hz.2
  have hk := oscillation_tsupport_carrier (H.wave_coeff_zero_off k n) hz'.1 hz'.2
  exact Set.disjoint_left.mp (ActualCarrierGeometry.labelCarrier_disjoint hN n
    (show (l.2, l.1) ≠ (k.2, k.1) from fun he => hlk (Prod.swap_injective he)))
    ⟨hz.1.1, hl⟩ ⟨hz'.1.1, hk⟩

theorem actual_extraction_regular (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ) :
    LocalResidualGrouping.ExtractionRegular ActualInitialization.geometry.strip.domain
      (ActualPrimary.commonContext B) x.state x.coefficients.labels x.coefficients.blocks
      x.coefficients.gaussian x.coefficients.aliasCoefficients n :=
  H.extraction_regular n (fun _ _ _ _ hne => H.actual_disjoint hN n hne)

theorem source_phase (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (i : Fin 3) (j : ℤ) :
    SupportedPhaseBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (2 * ActualPrimary.h) (fun l n z => (source x l).velocity n i j z.1)
      (fun l => fullPhase (source x l) j) :=
  supportedPhaseBounds hN (source x) H.source_carrier
    (fun l n z => (source x l).velocity n i j z) (fun l n z hz hn => H.source_coeff_zero_off l n z
        hz hn i j) j

theorem source_oscillation_native (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun l => (source x l).oscillation) :=
  block_nativeBounds (by
      norm_num) (HarmonicResidual.liftDomain_open ActualInitialization.geometry.strip.isOpen_domain)
    (mul_nonneg (by
        norm_num) ActualPrimary.outgoing.data.h_pos.le) (source x) (modes
            x.coefficients.residualBand)
    (fun l n _ i => H.source_support l n i)
    (fun i j _ => native_lift ActualInitialization.geometry.strip.isOpen_domain (H.source_native i
        j))
    (fun i j _ => H.source_phase hN i j)

end Invariant

theorem block_window_sum {B N0 : ℕ} {gain : ℝ} {loss : ℕ → ℝ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (labels : ℕ → Finset (Index B N0)) (b : Index B N0 → HarmonicBlock Point)
    (hzero : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∉ labelCarrier l n →
      ∀ i j, (b l).velocity n i j z = 0)
    (hb : NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      gain loss (fun l => (b l).oscillation)) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      gain loss (fun (_ : Unit) n z => ∑ l ∈ labels n, (b l).oscillation n z) := by
  apply hb.window_sum (HarmonicResidual.liftDomain_open
      ActualInitialization.geometry.strip.isOpen_domain)
    labels (fun _ => ActualPrimaryCovariance.signedLabelOf)
    (fun _ _ => ActualPrimaryCovariance.signedLabelOf_injective.injOn)
    (fun _ _ l _ => l.1.val.property.1) (CoordinateAlgebra.D ActualPrimary.h)
    (fun n z => ActualPrimaryCovariance.physicalWindow n z.1)
    (fun n _ => (ActualPrimaryCovariance.physicalWindow_continuousOn n).comp
      continuous_fst.continuousOn (fun _ hz => hz.1))
  intro n hn l hl z hz hs
  exact ActualCarrierGeometry.labelCarrier_window hN (l.2, l.1) n hz.1
    (oscillation_tsupport_carrier (hzero l n) hz (subset_closure hs))

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem gaussian_modes_native (α : ℝ) (i : Fin 3) (j : ℤ) :
    NativeBounds 4 ActualInitialization.geometry.strip.domain (ActualPrimary.h * α) (fun _ => 0)
      (fun l n z => (gaussianModes x l).velocity n i j z) := by
  by_cases hj : j = 0
  · subst j
    simpa only [gaussianModes, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
        Finsupp.erase_same, Pi.zero_apply] using
      (NativeBounds.zero : NativeBounds 4 ActualInitialization.geometry.strip.domain
        (ActualPrimary.h * α) (fun _ => 0) (fun (_ : Index B N0) _ _ => (0 : ℂ)))
  · simpa only [gaussianModes, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase,
      Finsupp.erase_ne hj] using H.gaussian_native α i j

theorem gaussian_carrier (l : Index B N0) :
    CorrectionStep.SameCarrier (gaussianModes x l) (ActualInitialization.primaryBlock l) :=
  ⟨(H.carrier l).frequency, (H.carrier l).phase, (H.carrier l).angular⟩

theorem gaussian_phase (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (i : Fin 3) (j : ℤ) :
    SupportedPhaseBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (2 * ActualPrimary.h) (fun l n z => (gaussianModes x l).velocity n i j z.1)
      (fun l => fullPhase (gaussianModes x l) j) :=
  supportedPhaseBounds hN (gaussianModes x) H.gaussian_carrier
    (fun l n z => (gaussianModes x l).velocity n i j z)
    (fun l n z hz hn => H.gaussian_coeff_zero_off l n z hz hn i j) j

theorem gaussian_oscillation_native (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (α : ℝ) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * α) (fun m => (2 * ActualPrimary.h) * m)
      (fun l => (gaussianModes x l).oscillation) := by
  apply block_nativeBounds (by norm_num)
    (HarmonicResidual.liftDomain_open ActualInitialization.geometry.strip.isOpen_domain)
    (mul_nonneg (by norm_num) ActualPrimary.outgoing.data.h_pos.le)
    (gaussianModes x) (modes x.coefficients.residualBand)
  · intro l n hn i j hj
    exact mem_modes (HarmonicResidual.band_nonconstant (H.bands.gaussian l n i) j hj)
  · intro i j hj
    exact native_lift ActualInitialization.geometry.strip.isOpen_domain (H.gaussian_modes_native α
        i j)
  · intro i j hj
    exact H.gaussian_phase hN i j

/-- Removing each zero Fourier mode preserves the total Gaussian field:
the sum of those modes is its actual angular mean, which is zero. -/
theorem gaussian_modes_sum (n : ℕ) (z : Cylinder) :
    (∑ l ∈ x.coefficients.labels n, (gaussianModes x l).oscillation n z) = x.state.errors.gaussian
        n z := by
  classical
  ext i
  have hzero : HarmonicResidual.realAngularMean (fun θ => x.state.errors.gaussian n (z.1, θ) i) = 0
      :=
    congrFun (congrFun (congrFun H.gaussianMean n) z.1) i
  have heq : (fun θ => x.state.errors.gaussian n (z.1, θ) i) =
      fun θ => ∑ l ∈ x.coefficients.labels n,
        coefficientField (x.coefficients.blocks l) (x.coefficients.gaussian l) n (z.1, θ) i :=
    funext (fun θ => H.representation.gaussian n (z.1, θ) i)
  rw [heq, HarmonicResidual.realAngularMean_sum] at hzero
  · have hz : (∑ l ∈ x.coefficients.labels n, (x.coefficients.gaussian l n i 0 z.1).re) = 0 := by
      convert! hzero using 1
      apply Finset.sum_congr rfl
      intro l hl
      exact (HarmonicResidual.realAngularMean_field (x.coefficients.gaussian l n i)
        ((x.coefficients.blocks l).frequency n) ((x.coefficients.blocks l).phase n)
        (H.angular l n) z.1).symm
    simp only [Finset.sum_apply]
    calc
      _ = (∑ l ∈ x.coefficients.labels n,
          coefficientField (x.coefficients.blocks l) (x.coefficients.gaussian l) n z i) -
            ∑ l ∈ x.coefficients.labels n, (x.coefficients.gaussian l n i 0 z.1).re := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        simpa only [HarmonicBlock.oscillation, gaussianModes, coefficientField, Complex.sub_re]
            using congrArg Complex.re
          (HarmonicResidual.field_nonconstant (x.coefficients.gaussian l n i)
            ((x.coefficients.blocks l).frequency n) ((x.coefficients.blocks l).phase n)
            ((x.coefficients.blocks l).angularFrequency n) z)
      _ = x.state.errors.gaussian n z i := by rw [hz, sub_zero, H.representation.gaussian]
  · intro l hl
    exact Complex.reCLM.continuous.comp (HarmonicFields.field_angular_continuous
        (x.coefficients.gaussian l n i)
      ((x.coefficients.blocks l).frequency n) ((x.coefficients.blocks l).phase n)
      ((x.coefficients.blocks l).angularFrequency n) z.1)

theorem source_sum_native (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) n z => ∑ l ∈ x.coefficients.labels n, (source x l).oscillation n z) :=
  block_window_sum hN x.coefficients.labels (source x) H.source_coeff_zero_off
      (H.source_oscillation_native hN)

theorem gaussian_field_native (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (α : ℝ) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * α) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) => x.state.errors.gaussian) := by
  apply (block_window_sum hN x.coefficients.labels (gaussianModes x) H.gaussian_coeff_zero_off
    (H.gaussian_oscillation_native hN α)).congr
      (HarmonicResidual.liftDomain_open ActualInitialization.geometry.strip.isOpen_domain)
  intro _ n _ z _
  exact H.gaussian_modes_sum n z

/-- Every term of the literal state residual has the required native gain.
The phase loss is fixed once, independently of the cycle index. -/
theorem native_residual (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hbase : x.state.errors.base = ActualInitialization.baseError B) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual (ActualPrimary.commonContext B) x.state)
          := by
  let U := HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain
  have hU : IsOpen U := HarmonicResidual.liftDomain_open
      ActualInitialization.geometry.strip.isOpen_domain
  have hβ (m : ℕ) : 0 ≤ (2 * ActualPrimary.h) * m := by
    exact mul_nonneg (mul_nonneg (by
        norm_num) ActualPrimary.outgoing.data.h_pos.le) (Nat.cast_nonneg _)
  have hm : NativeBounds 4 U (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) n z => x.state.meanGoodResidual (ActualPrimary.commonContext B) n z.1) := by
    apply (native_lift ActualInitialization.geometry.strip.isOpen_domain H.mean_native).weaken (by
        norm_num)
    intro m
    simp only [sub_zero]
    exact (sub_le_self _ (hβ m)).trans
      (mul_le_mul_of_nonneg_left (by linarith) ActualPrimary.outgoing.data.h_pos.le)
  have hb : NativeBounds 4 U (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) => x.state.errors.base) := by
    rw [hbase]
    exact (baseError_native B (1/2 + σ)).weaken (by norm_num)
      (fun m => by simpa only [sub_zero] using sub_le_self (ActualPrimary.h * (1/2 + σ)) (hβ m))
  have ha : NativeBounds 4 U (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) => x.state.errors.aliasError) := by
    rw [H.alias_eq_lift]
    exact (native_lift ActualInitialization.geometry.strip.isOpen_domain (H.axis_native (1/2 +
        σ))).weaken
      (by
          norm_num) (fun m => by
              simpa only [sub_zero] using sub_le_self (ActualPrimary.h * (1/2 + σ)) (hβ m))
  have he := excluded_nativeBounds (by norm_num : 1 ≤ 4) hU x.state.errors hb
    (H.gaussian_field_native hN (1/2 + σ)) ha
  apply (((H.source_sum_native hN).add (by norm_num) hU hm).add (by norm_num) hU he).congr hU
  intro _ n hn z hz
  ext i
  simpa only [Pi.add_apply, Finset.sum_apply] using
    (H.fullResidual_decomposition (H.actual_extraction_regular hN n) hz i).symm

end Invariant

/-- The four operations retain the same fixed base error at every stage. -/
theorem iterate_base_error {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (J : ℕ) :
    (CycleState.iterate p c seed J).state.errors.base = seed.state.errors.base := by
  induction J with
  | zero => rfl
  | succ J ih =>
    change ((p J).next (CycleState.iterate p c seed J).coefficients c
      (CycleState.iterate p c seed J).state).errors.base = _
    rw [CycleParameters.next_base_error, ih]

theorem actual_iterate_base_error {B N0 : ℕ} (p : ℕ → CycleParameters (Index B N0)) (J : ℕ) :
    (CycleState.iterate p (ActualPrimary.commonContext B) (ActualInitialization.initialCycleState B
        N0) J).state.errors.base =
      ActualInitialization.baseError B :=
  (iterate_base_error p _ _ J).trans (ActualInitialization.initialState_error_components B N0).1

/-! ## Restriction through the selected dyadic band, including radial edges -/

open ProblemStatement

/-- These are geometric statements about the single band actually selected
by the dyadic argument. The upper comparison is strict. -/
structure SelectedGeometry (a b h : ℝ) (N Δ : ℕ) (gap : ℕ → ℕ)
    (U V : Set Cylinder) (S : Set SpaceTime) : Prop where
  gap_le : ∀ n, N ≤ n → gap n ≤ Δ
  annulus : ∀ n, N ≤ n → ∀ w, w ∈ preterminal → physicalQ h w ≤ ChartScales.Q n →
    ChartScales.Q n < 2 * physicalQ h w → w ∈ S → scaledRadial n w ∈ PhysicalGraphBounds.annulus a b
  in_domain : ∀ n, N ≤ n → ∀ w, w ∈ preterminal → physicalQ h w ≤ ChartScales.Q n →
    ChartScales.Q n < 2 * physicalQ h w → w ∈ S → ∀ j,
    scaledRadial n w ∈ PolarCharts.chartDomain a j → polarGraph a h j n (gap n) w ∈ U
  in_closure : ∀ n, N ≤ n → ∀ w, w ∈ preterminal → physicalQ h w ≤ ChartScales.Q n →
    ChartScales.Q n < 2 * physicalQ h w → w ∈ S → ∀ j,
    scaledRadial n w ∈ PolarCharts.chartDomain a j → polarGraph a h j n (gap n) w ∈ closure V

theorem selected_residual_jet_bound {a b h gain β : ℝ} {N Δ : ℕ} {gap : ℕ → ℕ}
    {U V : Set Cylinder} {S : Set SpaceTime} {c : Context Point} {s : State Point}
    {p₀ : ℕ → Cylinder → ℝ} {u : VelocityField} {P : PressureField}
    (r : StateRealization h N gap U c s p₀ u P)
    (g : SelectedGeometry a b h N Δ gap U V S)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hN : 4 ≤ N)
    (hf : NativeBounds N V gain (fun m => β * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual c s)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, w ∈ preterminal → |w.1| ≤ 1 → physicalQ h w ≤ ChartScales.Q N →
      w ∈ S → ‖iteratedFDeriv ℝ m (residual u P) w‖ ≤
        C * physicalQ h w ^ (gain - physicalLoss h β m) := by
  obtain ⟨A, hA, e, hb⟩ := hf.bounds m
  obtain ⟨C, hC, hCbound⟩ := cartesianPull_jet_bound (b := b) hh.le hh1.le ha Δ m
    (gain - β * m) (residualDegree h) e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall hwS
  have hq := physicalQ_pos hh hh1 hw
  obtain ⟨n, hn, hlo, hhi⟩ := PhysicalMeanJetBounds.exists_comparable_band N hq hsmall
  have hlo' : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
  have hann := g.annulus n hn w hw hlo hhi hwS
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered ha hann
  have hc := PolarCharts.sector_subset_chartDomain ha j hj
  have hdom := g.in_domain n hn w hw hlo hhi hwS j hc
  have hcl := g.in_closure n hn w hw hlo hhi hwS j hc
  have hsmooth := realization_native_smooth r hn
  have hbound : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (LiftedMeanResidual.fullResidual c s n) (polarGraph a h j n (gap n) w)‖ ≤
        A * ChartScales.Q n ^ (gain - β * m) * ChartScales.S n ^ e := by
    intro k hk
    exact jet_bound_at_closure (hsmooth.contDiffAt (r.domain_open.mem_nhds hdom)) hcl k
      (fun z hz => hb () n hn z hz k hk)
  rw [iteratedFDeriv_eq_of_eventuallyEq ((r.chartIdentity ha).germ ha r.domain_open hn j hw hann hc
      hdom) m]
  have he := hCbound n (hN.trans hn) (gap n) (g.gap_le n hn) w hann ht (physicalQ h w) hq
    hlo' hhi.le j (LiftedMeanResidual.fullResidual c s n)
    (SmoothNear.of_open r.domain_open hsmooth hdom)
    (by simpa only [Real.rpow_natCast] using hbound)
  have hexp : gain - β * m - PhysicalMeanJetBounds.loss (residualDegree h) m = gain - physicalLoss
      h β m := by
    unfold physicalLoss
    ring
  simpa only [hexp] using he

theorem selected_residual_jetRate {a b h gain β : ℝ} {N Δ : ℕ} {gap : ℕ → ℕ}
    {U V : Set Cylinder} {S : Set SpaceTime} {c : Context Point} {s : State Point}
    {p₀ : ℕ → Cylinder → ℝ} {u u₀ : VelocityField} {P P₀ : PressureField}
    (r : StateRealization h N gap U c s p₀ u P)
    (g : SelectedGeometry a b h N Δ gap U V S)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hN : 4 ≤ N)
    (hf : NativeBounds N V gain (fun m => β * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual c s))
    (houtside : ∀ w, w ∈ preterminal → physicalQ h w < ChartScales.Q N → w ∉ S →
      u =ᶠ[𝓝 w] u₀ ∧ P =ᶠ[𝓝 w] P₀) (m : ℕ)
    (hbase : DiagonalResidual.JetRate (GlobalBaseError.originPast ⊓ 𝓟 Sᶜ)
      (physicalQ h) (residual u₀ P₀) m (gain - physicalLoss h β m)) :
    DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ h) (residual u P) m
      (gain - physicalLoss h β m) := by
  obtain ⟨C, hC, hb⟩ := selected_residual_jet_bound r g hh hh1 ha hN hf m
  obtain ⟨B, hB, hbase⟩ := hbase
  rw [Filter.eventually_inf_principal] at hbase
  have hsmall : ∀ᶠ w in GlobalBaseError.originPast, physicalQ h w < ChartScales.Q N :=
    (GlobalBaseError.originPast_q_tendsto_zero hh hh1).eventually
      (gt_mem_nhds (ChartScales.Q_pos N))
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  filter_upwards [hbase, hsmall, eventually_time_small (0 : Space),
      GlobalBaseError.originPast_before]
    with w hbw hsw ht hw
  have hq := physicalQ_pos hh hh1 hw
  by_cases hs : w ∈ S
  · exact (hb w hw ht hsw.le hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hB) (Real.rpow_pos_of_pos hq _).le)
  · have hg := houtside w hw hsw hs
    have he : residual u P =ᶠ[𝓝 w] residual u₀ P₀ :=
      ResidualRegularity.residual_eventuallyEq hg.1 hg.2
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    exact (hbw hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC) (Real.rpow_pos_of_pos hq _).le)

/-- Actual gap, given by `ChartScales.nativeIndex ActualPrimary.h n - CommonWindow.index
ActualPrimary.h n`. -/
noncomputable def actualGap (n : ℕ) : ℕ :=
  ChartScales.nativeIndex ActualPrimary.h n - CommonWindow.index ActualPrimary.h n

/-- Actual band graph, given by `PhysicalResidualBridge.commonGraph (ChartScales.Q n)
ActualPrimary.h (CommonWindow.index ActualPrimary.h n)`. -/
noncomputable def actualBandGraph (n : ℕ) : PhysicalResidualBridge.ScaledGraph :=
  PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
      ActualPrimary.h n)

theorem actualGap_le (n : ℕ) : actualGap n ≤ CommonWindow.gap ActualPrimary.h := by
  have hh := CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le n
  unfold actualGap
  omega

theorem actualGap_index (n : ℕ) :
    ChartScales.nativeIndex ActualPrimary.h n - actualGap n = CommonWindow.index ActualPrimary.h n
        := by
  have hh := CommonWindow.index_le_native ActualPrimary.h n
  unfold actualGap
  omega

theorem actual_bandGraph (n : ℕ) : bandGraph ActualPrimary.h n (actualGap n) = actualBandGraph n :=
    by
  simp only [bandGraph, actualGap_index, actualBandGraph]

/-- Actual base pressure, given by `ActualBaseResidual.basePressure ActualPrimary.certificate
ActualPrimary.modulation ActualPrimary.upper B n`. -/
noncomputable def actualBasePressure (B n : ℕ) : Cylinder → ℝ :=
  ActualBaseResidual.basePressure ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n

/-- Only the actual physical realization remains external. Native regularity,
the fixed base equation, and all size estimates are derived in this module. -/
structure PhysicalFields (B N : ℕ) (U : Set Cylinder) (s : State Point)
    (u : VelocityField) (P : PressureField) : Prop where
  velocity_smooth : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (actualBandGraph n) U →
    ContDiffAt ℝ 2 u (z.1, CylindricalResidual.chart z.2)
  pressure_differentiable : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (actualBandGraph n) U →
    DifferentiableAt ℝ P (z.1, CylindricalResidual.chart z.2)
  velocity_germ : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (actualBandGraph n) U →
    (fun y : SpaceTime => u (y.1, CylindricalResidual.chart y.2)) =ᶠ[𝓝 z]
      (fun y => CylindricalResidual.frame (y.2 1)
        (PhysicalResidualTZ.velocityTZ (actualBandGraph n)
          (fun v i => PhysicalResidualBridge.baseComponents (ActualPrimary.commonContext B) n v i +
            PhysicalResidualBridge.incrementComponents s n v i) y))
  pressure_germ : ∀ n, N ≤ n → ∀ z ∈ preterminal,
    z ∈ PhysicalResidualTZ.graphSourceTZ (actualBandGraph n) U →
    CylindricalResidual.pressurePullback P =ᶠ[𝓝 z]
      PhysicalResidualTZ.pressureTZ (actualBandGraph n)
        (fun v => actualBasePressure B n v + s.totalPressureIncrement n v)
  exterior : ∀ w, w ∈ preterminal → physicalQ ActualPrimary.h w < ChartScales.Q N → w ∉ active →
    u w = FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B w ∧
    P w = FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B w

/-- Local exterior equality gives actual field germs inside the valid past
sublevel; no global topological-support condition is used. -/
theorem PhysicalFields.exterior_germs {B N : ℕ} {U : Set Cylinder} {s : State Point}
    {u : VelocityField} {P : PressureField} (d : PhysicalFields B N U s u P)
    {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ ActualPrimary.h w < ChartScales.Q N) (hout : w ∉ active) :
    u =ᶠ[𝓝 w] FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B ∧
    P =ᶠ[𝓝 w] FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B := by
  have ho : IsOpen {w : SpaceTime | w ∈ preterminal ∧ w ∉ active} := by
    exact BaseResidual.chartedDomain_isOpen ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half
      (show IsOpen {p : ℝ × ℝ | p.1 ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)} from
        (isClosed_Icc.preimage continuous_fst).isOpen_compl)
  have hs : ∀ᶠ y in 𝓝 w, physicalQ ActualPrimary.h y < ChartScales.Q N :=
    (physicalQ_smoothAt ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds
          hq)
  have he : ∀ᶠ y in 𝓝 w,
      u y = FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B y ∧
      P y = FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B y := by
    filter_upwards [ho.mem_nhds ⟨hw, hout⟩, hs] with y hy hys
    exact d.exterior y hy.1 hys hy.2
  exact ⟨he.mono (fun _ h => h.1), he.mono (fun _ h => h.2)⟩

namespace Invariant

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

theorem increment_smooth {U : Set Cylinder}
    (hU : ∀ z ∈ U, z.1 ∈ ActualInitialization.geometry.domain) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z => PhysicalResidualBridge.incrementComponents x.state n z i) U := by
  have hw (i : Fin 3) := (H.oscillationSmooth n i).mono (fun z hz => ⟨hU z hz, Set.mem_univ _⟩)
  fin_cases i
  · exact ((H.primitives.mean.radial.smooth n).comp contDiffOn_fst hU).add (hw 0)
  · exact ((H.primitives.mean.angular.smooth n).comp contDiffOn_fst hU).add (hw 1)
  · exact ((H.primitives.mean.axial.smooth n).comp contDiffOn_fst hU).add (hw 2)

theorem totalPressure_smooth {U : Set Cylinder}
    (hU : ∀ z ∈ U, z.1 ∈ ActualInitialization.geometry.domain) (n : ℕ) :
    ContDiffOn ℝ ∞ (x.state.totalPressureIncrement n) U := by
  let G := ActualInitialization.geometry
  have hp := (H.primitives.pressure G.inner_pos G.exponent_pos G.length_eq
    (congrArg State.pressure H.reconstructed)).smooth n
  exact (hp.comp contDiffOn_fst hU).add
    ((H.oscillatoryPressureSmooth n).mono (fun z hz => ⟨hU z hz, Set.mem_univ _⟩))

/-- The native operator and base-pressure obligations of the physical
bridge are consequences of the actual selected base and the invariant. -/
theorem stateRealization {N : ℕ} {U : Set Cylinder} {u : VelocityField} {P : PressureField}
    (hopen : IsOpen U) (hpos : ∀ z ∈ U, 0 < z.1.1)
    (hdom : ∀ z ∈ U, z.1 ∈ ActualInitialization.geometry.domain)
    (hbase : x.state.errors.base = ActualInitialization.baseError B)
    (d : PhysicalFields B N U x.state u P) :
    StateRealization ActualPrimary.h N actualGap U (ActualPrimary.commonContext B) x.state
      (actualBasePressure B) u P := by
  have hd : U ⊆ ActualBaseResidual.domain := by
    intro z hz
    exact ⟨hpos z hz, ActualInitialization.geometry.region.time_pos _ (hdom z hz)⟩
  refine ⟨hopen, fun z hz => (hpos z hz).ne', fun n _ => Nat.sub_le _ _, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [actual_bandGraph]
    exact CommonBaseContext.operators_match_physical ActualPrimary.h (CommonWindow.index
        ActualPrimary.h)
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
          ActualPrimary.nominal)
      (PrimaryTargetBounds.radii_ordered ActualPrimary.nominal) n
  · intro n hn i
    exact (ActualBaseResidual.baseComponents_smooth ActualPrimary.certificate
        ActualPrimary.modulation
      ActualPrimary.upper B (CommonWindow.index ActualPrimary.h) n i).mono hd
  · intro n hn i
    exact H.increment_smooth hdom n i
  · intro n hn
    exact (ActualBaseResidual.basePressure_smooth ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n).mono (fun z hz => (hd hz).2)
  · intro n hn
    exact H.totalPressure_smooth hdom n
  · intro n hn z hz i
    rw [actual_bandGraph, hbase]
    exact ActualBaseResidual.fixed_base_residual ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B (CommonWindow.index ActualPrimary.h) n (hd hz) i
  · simpa only [actual_bandGraph] using d.velocity_smooth
  · simpa only [actual_bandGraph] using d.pressure_differentiable
  · simpa only [actual_bandGraph] using d.velocity_germ
  · simpa only [actual_bandGraph] using d.pressure_germ

end Invariant

/-! ## Actual physical stage and iteration consumers -/

theorem actual_selectedGeometry (N : ℕ) :
    SelectedGeometry ActualPolarCoverage.inner ActualPolarCoverage.outer ActualPrimary.h N
      (CommonWindow.gap ActualPrimary.h) actualGap ActualPolarCoverage.nativeDomain
      (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) active := by
  constructor
  · intro n hn
    exact actualGap_le n
  · intro n hn w hw hlo hhi hs
    exact ActualPolarCoverage.selected_annulus n hw hs hlo hhi
  · intro n hn w hw hlo hhi hs j hj
    exact ActualPolarCoverage.selected_polar_nativeDomain j n (actualGap n) hw hs hlo hhi hj
  · intro n hn w hw hlo hhi hs j hj
    exact ActualPolarCoverage.selected_polar_closure j n (actualGap n) hw hs hlo hhi hj

/-- Physical data: an abbreviation for `PhysicalFields B N ActualPolarCoverage.nativeDomain s u
P`. -/
abbrev PhysicalData (B N : ℕ) (s : State Point) (u : VelocityField) (P : PressureField) :=
  PhysicalFields B N ActualPolarCoverage.nativeDomain s u P

/-- Fixed loss, given by `physicalLoss ActualPrimary.h (2 * ActualPrimary.h) m`. -/
noncomputable def fixedLoss (m : ℕ) : ℝ := physicalLoss ActualPrimary.h (2 * ActualPrimary.h) m

theorem fixedLoss_eq_ledger (m : ℕ) :
    fixedLoss m = ActualIterationLedger.residualLoss ActualPrimary.h (2 * ActualPrimary.h) m := rfl

namespace Invariant

variable {B N0 N : ℕ} {σ : ℝ} {x : CycleState (Index B N0)} (H : Invariant σ x)

include H

/-- The complete physical residual rate follows from the actual invariant.
The local physical fields are only identified, never bounded, by `d`. -/
theorem residual_jetRate {u : VelocityField} {P : PressureField}
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (hN : 4 ≤ N)
    (hbase : x.state.errors.base = ActualInitialization.baseError B)
    (d : PhysicalData B N x.state u P) (m : ℕ) :
    DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h) (residual u P) m
      (ActualPrimary.h * (1/2 + σ) - fixedLoss m) := by
  have hr := H.stateRealization ActualPolarCoverage.nativeDomain_open
    (fun z hz => ActualPolarCoverage.nativeDomain_radius_pos hz)
    (fun z hz => hz.1.1) hbase d
  exact selected_residual_jetRate hr (actual_selectedGeometry N)
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half
    ActualPolarCoverage.inner_pos hN
    (native_restrict (H.native_residual hGeom hbase) hN (Subset.refl _))
    (fun _ hw hq hout => d.exterior_germs hw hq hout) m
    (base_exterior_jetRate B m _)

end Invariant

theorem initial_invariant (B N0 : ℕ) :
    Invariant (1/5) (ActualInitialization.initialCycleState B N0) :=
  ActualInitialization.initial_invariant B N0

theorem origin_positive_small : ∀ᶠ w in GlobalBaseError.originPast,
    0 < physicalQ ActualPrimary.h w ∧ physicalQ ActualPrimary.h w ≤ 1 := by
  have hs := (GlobalBaseError.originPast_q_tendsto_zero ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half).eventually (eventually_le_nhds (by
        norm_num : (0 : ℝ) < 1))
  filter_upwards [GlobalBaseError.originPast_before, hs] with w hw hsw
  exact ⟨physicalQ_pos ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hw,
      hsw⟩

/-- The finite-residual input of the mixed diagonal assembly. `J` is the
number of completed correction cycles, including the actual initialized
state at zero. The derivative loss is fixed before `J` is chosen. -/
theorem finite_residual_rates {B N0 N : ℕ}
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (hN : 4 ≤ N)
    (p : ℕ → CycleParameters (Index B N0)) (u : ℕ → VelocityField) (P : ℕ → PressureField)
    (H : ∀ J, Invariant (ActualIterationLedger.sigma J)
      (CycleState.iterate p (ActualPrimary.commonContext B) (ActualInitialization.initialCycleState
          B N0) J))
    (d : ∀ J, PhysicalData B N
      (CycleState.iterate p (ActualPrimary.commonContext B) (ActualInitialization.initialCycleState
          B N0) J).state
      (u J) (P J)) :
    ∀ J m, DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h)
      (fun w => navierStokesResidual (u J) (P J) w.1 w.2) m
      (ActualIterationLedger.gain ActualPrimary.h J - fixedLoss m) := by
  intro J m
  have he := (H J).residual_jetRate hGeom hN (actual_iterate_base_error p J) (d J) m
  have hgain := ActualIterationLedger.gain_le_residualWave ActualPrimary.outgoing.data.h_pos.le J
  change ActualIterationLedger.gain ActualPrimary.h J ≤
    ActualPrimary.h * (1/2 + ActualIterationLedger.sigma J) at hgain
  exact he.weaken origin_positive_small (sub_le_sub_right hgain _)

end NavierStokes.ActualCycleResidualBounds
