/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.EntranceAlignedBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStressWeights
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileSpectralCone
import LeanPool.NavierStokesAndEuler.NavierStokes.AlignedProfileSpectralCone
import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalCore
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity

/-!
# The slow base on the actual entrance-to-terminal annulus

All fields below use the same solved finite modulation and the same aligned
coefficient family.  The weight exponent is the square of the actual ACT
time, and its two endpoints are the endpoints of the nominal cone interval.
-/

@[expose] public section


noncomputable section

open Set Filter Function
open scoped ContDiff Topology BigOperators EuclideanSpace

namespace NavierStokes.FinalSlowBase

open SlowBorelBase GlobalSlowProfiles AssembledSlowBase

section Geometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Edge exponent, given by `W.controls.activationTime ^ 2`. -/
noncomputable def edgeExponent : ℝ := W.controls.activationTime ^ 2

theorem edgeExponent_pos : 0 < edgeExponent W := sq_pos_of_pos W.controls.activationTime_pos

/-- Log left, given by `Real.log (NominalConeAssembly.activeLeft W)`. -/
noncomputable def logLeft : ℝ := Real.log (NominalConeAssembly.activeLeft W)

/-- Log right, given by `Real.log (NominalConeAssembly.activeRight W)`. -/
noncomputable def logRight : ℝ := Real.log (NominalConeAssembly.activeRight W)

/-- Annulus, given by `Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight
W) ×ˢ Icc (-1 : ℝ) 1`. -/
noncomputable def annulus : Set Inner :=
  Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) ×ˢ Icc (-1 : ℝ) 1

/-- Weight, given by `BaseResidual.activeZeta (edgeExponent W) (logLeft W) (logRight W)`. -/
noncomputable def weight : Inner → ℝ :=
  BaseResidual.activeZeta (edgeExponent W) (logLeft W) (logRight W)

/-- Edge distance, given by `BaseResidual.activeDelta (logLeft W) (logRight W)`. -/
noncomputable def edgeDistance : Inner → ℝ := BaseResidual.activeDelta (logLeft W) (logRight W)

/-- Box radius, given by `max upper (NominalConeAssembly.activeRight W)`. -/
noncomputable def boxRadius (upper : ℝ) : ℝ := max upper (NominalConeAssembly.activeRight W)

theorem terminal_pos : 0 < NominalConeAssembly.activeRight W :=
  mul_pos W.controls.radius_pos (Real.exp_pos _)

theorem logRight_eq : logRight W = ConstructedSlowBase.activeRight W := by
  have he := congrArg Real.log (EntranceAlignedBase.exp_right_eq_cone W)
  simp only [Real.log_exp] at he
  exact he.symm

theorem boxRadius_eq (upper : ℝ) : boxRadius W upper = ConstructedSlowBase.scaleUpper W upper := by
  unfold boxRadius ConstructedSlowBase.scaleUpper ConstructedSlowBase.activeUpper
  rw [EntranceAlignedBase.exp_right_eq_cone]

theorem annulus_eq : annulus W = BaseResidual.activeWindow (logLeft W) (logRight W) := by
  simp only [annulus, BaseResidual.activeWindow, logLeft, logRight,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W), Real.exp_log (terminal_pos W)]

theorem annulus_subset_box (upper : ℝ) : annulus W ⊆ innerBox 0 (boxRadius W upper) := by
  intro p hp
  exact ⟨⟨(NominalConeAssembly.activeLeft_pos W).le.trans hp.1.1.le,
    hp.1.2.le.trans (le_max_right _ _)⟩, hp.2⟩

end Geometry

/-- Equality on a dense open part determines every ambient derivative when
both functions are smooth at the points of the larger set. -/
theorem iteratedFDeriv_eq_on_dense {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : E → V} {s t : Set E} (hs : IsOpen s) (hst : s ⊆ t)
    (hts : t ⊆ closure s)
    (hf : ∀ p ∈ t, ContDiffAt ℝ ∞ f p)
    (hg : ∀ p ∈ t, ContDiffAt ℝ ∞ g p)
    (he : EqOn f g s) (m : ℕ) : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) t := by
  have hj : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) s := by
    intro p hp
    have hfg : f =ᶠ[𝓝 p] g := by
      filter_upwards [hs.mem_nhds hp] with q hq
      exact he hq
    exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hfg m).self_of_nhds
  apply hj.of_subset_closure _ _ hst hts
  · intro p hp
    have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ m f) p :=
      (hf p hp).iteratedFDeriv_right (WithTop.coe_le_coe.mpr le_top)
    exact hd.continuousAt.continuousWithinAt
  · intro p hp
    have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ m g) p :=
      (hg p hp).iteratedFDeriv_right (WithTop.coe_le_coe.mpr le_top)
    exact hd.continuousAt.continuousWithinAt

section Fields

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- Coefficients, given by `EntranceAlignedBase.modulatedCoefficients H v`. -/
noncomputable def coefficients : Coefficients := EntranceAlignedBase.modulatedCoefficients H v

/-- Profile sequence, given by `asSlowProfiles (EntranceAlignedBase.modulatedScheme H v)`. -/
noncomputable def profileSequence : SlowExpansionResidual.SlowProfiles :=
  asSlowProfiles (EntranceAlignedBase.modulatedScheme H v)

theorem coefficients_smooth : SmoothCoefficients (coefficients H v) :=
  EntranceAlignedBase.modulated_smooth H v

theorem finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization (coefficients H v) (profileSequence
        H v) :=
  EntranceAlignedBase.modulated_finiteIdentities H v

theorem stressZeroCore : BaseResidual.StressZeroCore (coefficients H v)
    (NominalConeAssembly.activeLeft W) :=
  EntranceAlignedBase.modulated_stressZeroCore H v

/-- The literal stress of the same finite modulated profile. -/
noncomputable def leadingStress : Inner → Inner := LeadingStressWeights.stress v.profiles F.data.h

theorem leadingStress_smoothAt {p : Inner} (hX : 0 < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (leadingStress v) p :=
  LeadingStressWeights.stress_contDiffAt v.profiles F.data.h
    (ld.domain_nonnegative hX.le (ld.parameters_contains heta)) hX (v.positive_f hX heta).ne'
    (NaturalAxisData.L_pos W.axis.small heta).ne'

theorem leading_stress_eq {p : Inner} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    BaseResidual.stressPair (coefficients H v) 0 p = leadingStress v p :=
  EntranceAlignedBase.modulated_leading_pair_eq H v hX heta

/-- Equality of full derivative tensors holds at both closed parameter
endpoints as well as in the interior. No ambient endpoint germ is assumed. -/
theorem leading_stress_jets (m : ℕ) {p : Inner} (hX : 0 < p.1)
    (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ m (BaseResidual.stressPair (coefficients H v) 0) p =
      iteratedFDeriv ℝ m (leadingStress v) p := by
  apply iteratedFDeriv_eq_on_dense (s := Ioi 0 ×ˢ Ioo (-1 : ℝ) 1)
    (t := Ioi 0 ×ˢ Icc (-1 : ℝ) 1) (isOpen_Ioi.prod isOpen_Ioo)
    (fun _ hp => ⟨hp.1, hp.2.1.le, hp.2.2.le⟩) _
    (fun _ _ => (BaseResidual.stressPair_smooth (coefficients_smooth H v) 0).contDiffAt)
    (fun _ hp => leadingStress_smoothAt v hp.1 hp.2)
    (fun _ hp => leading_stress_eq H v hp.1.le (abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩)) m ⟨hX, heta⟩
  intro q hq
  simpa only [closure_prod_eq, closure_Ioi, closure_Ioo (by
      norm_num : (-1 : ℝ) ≠ 1), mem_prod, mem_Ici]
    using (show q.1 ≥ 0 ∧ q.2 ∈ Icc (-1 : ℝ) 1 from ⟨hq.1.le, hq.2⟩)

theorem leading_weighted (hcone : LeadingStressWeights.FullTrueCone v) :
    ActiveAnnulusWeight.WeightedBounds (Icc (-1 : ℝ) 1)
      (edgeExponent W) (logLeft W) (logRight W)
      (LeadingStressWeights.logStress v.profiles F.data.h) :=
  LeadingStressWeights.weighted_bounds v hcone

theorem leading_lowerBound (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ annulus W, m * weight W p ≤ ‖leadingStress v p‖ := by
  obtain ⟨m, hm, hb⟩ := (leading_weighted v hcone).1
  refine ⟨m, hm, fun p hp => ?_⟩
  have hx : 0 < p.1 := (NominalConeAssembly.activeLeft_pos W).trans hp.1.1
  have hy : Real.log p.1 ∈ Ioo (logLeft W) (logRight W) :=
    ⟨Real.log_lt_log (NominalConeAssembly.activeLeft_pos W) hp.1.1, Real.log_lt_log hx hp.1.2⟩
  have he := hb p.2 hp.2 (Real.log p.1) hy
  simp only [weight, BaseResidual.activeZeta, ActiveAnnulusWeight.radialWeight, ite_eq_left hx,
    LeadingStressWeights.logStress, LeadingStressWeights.logPoint, Function.comp_apply,
    Real.exp_log hx, Prod.mk.eta] at he ⊢
  exact he

theorem leading_ne_zero (hcone : LeadingStressWeights.FullTrueCone v) {p : Inner} (hp : p ∈ annulus
    W) :
    leadingStress v p ≠ 0 :=
  LeadingStressWeights.stress_ne_zero v hcone hp.1.1 hp.1.2 hp.2

theorem leading_radial_jets (hcone : LeadingStressWeights.FullTrueCone v) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ w ∈ annulus W,
      ‖iteratedFDeriv ℝ m (leadingStress v) w‖ ≤
        D * weight W w * (edgeDistance W w)⁻¹ ^ N := by
  obtain ⟨D, hD, N, hb⟩ := (leading_weighted v hcone).2.2 m
  refine ⟨D, hD, N, fun w hw => ?_⟩
  have hX := (NominalConeAssembly.activeLeft_pos W).trans hw.1.1
  have he : leadingStress v =ᶠ[𝓝 w]
      (ActiveAnnulusWeight.radialPullback (LeadingStressWeights.logStress v.profiles F.data.h) ∘
        BaseResidual.swapInner) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with y hy
    simp only [comp_apply]
    change LeadingStressWeights.stress v.profiles F.data.h y =
      LeadingStressWeights.stress v.profiles F.data.h (Real.exp (Real.log y.1), y.2)
    rw [Real.exp_log hy]
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds,
    BaseResidual.swapInner.norm_iteratedFDeriv_comp_right]
  have hbound := hb w.2 hw.2 w.1
    (show w.1 ∈ Ioo (Real.exp (logLeft W)) (Real.exp (logRight W)) from by
      simpa only [logLeft, logRight, Real.exp_log (NominalConeAssembly.activeLeft_pos W),
        Real.exp_log (terminal_pos W)] using hw.1)
  simp only [weight, edgeDistance, BaseResidual.activeZeta, BaseResidual.activeDelta,
    div_eq_mul_inv, inv_pow] at hbound ⊢
  exact hbound

theorem leading_coefficient_jets (hcone : LeadingStressWeights.FullTrueCone v) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ w ∈ annulus W,
      ‖iteratedFDeriv ℝ m (BaseResidual.stressPair (coefficients H v) 0) w‖ ≤
        D * weight W w * (edgeDistance W w)⁻¹ ^ N := by
  obtain ⟨D, hD, N, hb⟩ := leading_radial_jets v hcone m
  refine ⟨D, hD, N, fun w hw => ?_⟩
  rw [leading_stress_jets H v m ((NominalConeAssembly.activeLeft_pos W).trans hw.1.1) hw.2]
  exact hb w hw

/-- Leading frequency, given by `BaseChartJets.leadingFrequency F.data.h W.axis.normalization
(coefficients H v)`. -/
noncomputable def leadingFrequency : PhaseCalculus.Slow → ℝ :=
  BaseChartJets.leadingFrequency F.data.h W.axis.normalization (coefficients H v)

/-- Leading axial, given by `BaseChartJets.leadingAxial F.data.h (coefficients H v)`. -/
noncomputable def leadingAxial : PhaseCalculus.Slow → ℝ :=
  BaseChartJets.leadingAxial F.data.h (coefficients H v)

theorem leadingFrequency_pos {p : PhaseCalculus.Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < leadingFrequency H v p :=
  AlignedProfileSpectralCone.modulated_frequency_pos H v hT hR

theorem spectral_cones (hcone : LeadingStressWeights.FullTrueCone v)
    {p : PhaseCalculus.Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hw : (BaseChartJets.normalizedCoordinates F.data.h p).2 ∈ annulus W) :
    PrimaryRepresentatives.ReferenceCone (leadingFrequency H v p)
      (PhaseEstimates.shearVector (leadingFrequency H v) (leadingAxial H v) p) ∧
    PrimaryRepresentatives.TargetCone (leadingFrequency H v p)
      (PhaseEstimates.shearVector (leadingFrequency H v) (leadingAxial H v) p)
      (ProfileSpectralCone.stressVector v.profiles F.data.h (BaseChartJets.normalizedCoordinates
          F.data.h p).2) :=
  AlignedProfileSpectralCone.modulated_spectral_cones H v hcone hT hR hw.1.1 hw.1.2

/-- The actual covariance target, including its positive chart factor. -/
noncomputable def covarianceTarget (q : ℝ) (N : ℕ) (U : PartitionedCovariance.UnsignedLabel)
    (p : PhaseCalculus.Slow) : MovingFrameODE.Plane :=
  let w := (BaseChartJets.normalizedCoordinates F.data.h p).2
  let T := PartitionedCovariance.chartTarget F.data.h q N
    ![(coefficients H v).stressTheta 0 w, (coefficients H v).stressAxial 0 w] U
  !₂[T 0, T 1]

theorem covarianceTarget_cones (hcone : LeadingStressWeights.FullTrueCone v)
    {p : PhaseCalculus.Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hw : (BaseChartJets.normalizedCoordinates F.data.h p).2 ∈ annulus W)
    {q : ℝ} (hq : 0 < q) (N : ℕ) (U : PartitionedCovariance.UnsignedLabel) :
    PrimaryRepresentatives.ReferenceCone (leadingFrequency H v p)
      (PhaseEstimates.shearVector (leadingFrequency H v) (leadingAxial H v) p) ∧
    PrimaryRepresentatives.TargetCone (leadingFrequency H v p)
      (PhaseEstimates.shearVector (leadingFrequency H v) (leadingAxial H v) p)
      (covarianceTarget H v q N U p) :=
  AlignedProfileSpectralCone.modulated_chartTarget_cones H v hcone hT hR hw.1.1 hw.1.2 hq N U

/-- The sequence is selected once from the aligned enlarged bundle. -/
noncomputable def scales (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  EntranceAlignedBase.scales H v (edgeExponent W) (edgeExponent_pos W) upper B

theorem scales_spec (upper : ℝ) (B : ℕ) : B ≤ scales H v upper B 0 ∧
    AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (coefficients H v) (weight W))
      (innerBox 0 (boxRadius W upper)) (scales H v upper B) := by
  simpa only [scales, coefficients, weight, logLeft, ← logRight_eq W, ← boxRadius_eq W upper] using
    EntranceAlignedBase.scales_spec H v (edgeExponent W) (edgeExponent_pos W) upper B

theorem scales_admissible (upper : ℝ) (B : ℕ) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients H v))
      (innerBox 0 (boxRadius W upper)) (scales H v upper B) := by
  simpa only [scales, coefficients, ← boxRadius_eq W upper] using
    EntranceAlignedBase.scales_admissible H v (edgeExponent W) (edgeExponent_pos W) upper B

theorem scales_strictMono (upper : ℝ) (B : ℕ) : StrictMono (scales H v upper B) :=
  (scales_spec H v upper B).2.strictMono

theorem scales_admissible_on (upper : ℝ) (B : ℕ) {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ boxRadius W upper) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients H v))
      (innerBox lo hi) (scales H v upper B) :=
  ConstructedSlowBase.admissibleScales_mono (scales_admissible H v upper B)
    (fun _ hp => ⟨⟨hlo.trans hp.1.1, hp.1.2.trans hhi⟩, hp.2⟩)

theorem weighted_bound (upper : ℝ) (B : ℕ) :
    ConstructedSlowBase.WeightedStressBound (scales H v upper B) F.data.h (coefficients H v)
      (edgeExponent W) (logLeft W) (logRight W) := by
  simpa only [scales, coefficients, logLeft, ← logRight_eq W] using
    EntranceAlignedBase.scales_weighted H v (edgeExponent W) (edgeExponent_pos W) upper B

/-- Velocity, given by `baseVelocity (scales H v upper B) F.data.h W.axis.normalization
(coefficients H v)`. -/
noncomputable def velocity (upper : ℝ) (B : ℕ) : ProblemStatement.VelocityField :=
  baseVelocity (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)

/-- Pressure, given by `basePressure (scales H v upper B) F.data.h W.axis.normalization
(coefficients H v)`. -/
noncomputable def pressure (upper : ℝ) (B : ℕ) : ProblemStatement.PressureField :=
  basePressure (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)

/-- Vector potential, given by `ConstructedSlowBase.potential (scales H v upper B) F.data.h
W.axis.normalization (coefficients H v)`. -/
noncomputable def vectorPotential (upper : ℝ) (B : ℕ) : ProblemStatement.VelocityField :=
  ConstructedSlowBase.potential (scales H v upper B) F.data.h W.axis.normalization (coefficients H
      v)

/-- Stress force, given by `BaseResidual.baseStressForce (scales H v upper B) F.data.h
W.axis.normalization (coefficients H v)`. -/
noncomputable def stressForce (upper : ℝ) (B : ℕ) : ProblemStatement.SpaceTime →
    ProblemStatement.Space :=
  BaseResidual.baseStressForce (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)

/-- Error, given by `BaseResidual.baseResidual (scales H v upper B) F.data.h
W.axis.normalization (coefficients H v)`. -/
noncomputable def error (upper : ℝ) (B : ℕ) : ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseResidual (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)

/-- Normalized stress, given by `BaseResidual.normalizedTensor (scales H v upper B) F.data.h
(coefficients H v)`. -/
noncomputable def normalizedStress (upper : ℝ) (B : ℕ) : Chart → Inner :=
  BaseResidual.normalizedTensor (scales H v upper B) F.data.h (coefficients H v)

theorem normalizedStress_smoothAt (upper : ℝ) (B : ℕ) {y : Chart} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (normalizedStress H v upper B) y :=
  slowSum_smoothAt (scales_strictMono H v upper B)
    (BaseResidual.stressPair_smooth (coefficients_smooth H v)) F.data.h hy

theorem velocity_eq_curl (upper : ℝ) (B : ℕ) :
    velocity H v upper B = SpatialCurl.spatialCurl (vectorPotential H v upper B) := rfl

theorem vectorPotential_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (vectorPotential H v upper B) BaseResidual.past :=
  ConstructedSlowBase.potential_smooth (scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (coefficients_smooth H v) W.axis.normalization

theorem velocity_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (velocity H v upper B) BaseResidual.past :=
  baseVelocity_smooth (scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (coefficients_smooth H v) W.axis.normalization

theorem pressure_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (pressure H v upper B) BaseResidual.past :=
  BaseResidual.basePressure_smooth (scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (coefficients_smooth H v) W.axis.normalization

theorem stressForce_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (stressForce H v upper B) BaseResidual.past :=
  BaseResidual.baseStressForce_smooth_past (scales_strictMono H v upper B) F.data.h_pos
      F.data.h_lt_half
    (NominalConeAssembly.activeLeft_pos W) (coefficients_smooth H v) (stressZeroCore H v)

theorem error_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (error H v upper B) BaseResidual.past :=
  (ResidualRegularity.contDiffOn_residual BaseResidual.past_isOpen
    (velocity_smooth H v upper B) (pressure_smooth H v upper B)).sub (stressForce_smooth H v upper
        B)

theorem divergence_zero (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space) :
    ProblemStatement.spatialDivergence (velocity H v upper B) t x = 0 :=
  baseVelocity_divergence_zero (scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (coefficients_smooth H v) W.axis.normalization ht x

theorem residual_identity (upper : ℝ) (B : ℕ) (z : ProblemStatement.SpaceTime) :
    ProblemStatement.navierStokesResidual (velocity H v upper B) (pressure H v upper B) z.1 z.2 =
      stressForce H v upper B z + error H v upper B z :=
  BaseResidual.baseResidual_identity _ _ _ _ z

theorem error_jetRate (upper : ℝ) (B : ℕ) {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ boxRadius W upper)
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart F.data.h z).1) (error H v upper B) m n :=
  ConstructedSlowBase.repaired_jetRate
    (EntranceAlignedBase.smallLocalization W H v.profiles v.finiteModification ld.after_initial)
    (EntranceAlignedBase.smallBaseAgreement W H v.profiles v.finiteModification ld.after_initial)
    (EntranceAlignedBase.smallZeroOrder W H v.profiles v.finiteModification ld.after_initial)
    v.finiteModification.contains F.data.h_pos F.data.h_lt_half P
    (scales_admissible_on H v upper B le_rfl hr) (finiteIdentities H v) m n hn

theorem error_allJetsFlat (upper : ℝ) (B : ℕ) {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ boxRadius W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1) (error H v upper B) :=
  ConstructedSlowBase.repaired_allJetsFlat
    (EntranceAlignedBase.smallLocalization W H v.profiles v.finiteModification ld.after_initial)
    (EntranceAlignedBase.smallBaseAgreement W H v.profiles v.finiteModification ld.after_initial)
    (EntranceAlignedBase.smallZeroOrder W H v.profiles v.finiteModification ld.after_initial)
    v.finiteModification.contains F.data.h_pos F.data.h_lt_half P
    (scales_admissible_on H v upper B le_rfl hr) (finiteIdentities H v)

theorem leading_origin : (coefficients H v).axial 0 (0, 0) = W.axis.j := by
  have he := EntranceAlignedBase.modulated_leading_axis H v (eta := 0) (by constructor <;> norm_num)
  simp only [mul_zero, zero_add] at he
  exact he

theorem origin (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    velocity H v upper B (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector 2
          := by
  rw [show velocity H v upper B (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * (coefficients H v).axial 0 (0, 0)) •
        ProblemStatement.coordinateVector 2 from
    BaseResidual.baseVelocity_at_origin (scales_strictMono H v upper B) F.data.h_pos
        F.data.h_lt_half
      (coefficients_smooth H v) W.axis.normalization
      (fun _ hn => (EntranceAlignedBase.modulated_positive_axis H v hn (by
          norm_num : |(0 : ℝ)| ≤ 1)).2.1) ht,
    leading_origin]

theorem axis_tendsto (upper : ℝ) (B : ℕ) :
    Tendsto (fun t : ℝ => ‖velocity H v upper B (t, 0)‖) (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop (scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (coefficients_smooth H v) W.axis.normalization
    (fun _ hn => (EntranceAlignedBase.modulated_positive_axis H v hn (by
        norm_num : |(0 : ℝ)| ≤ 1)).2.1)
  rw [leading_origin]
  exact W.axis.small.j_pos

theorem speedUnbounded (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpeedUnboundedAtOne (velocity H v upper B) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (axis_tendsto H v upper B)

theorem weighted_jets (upper : ℝ) (B m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ annulus W,
      ‖blownJet m (fun y => normalizedStress H v upper B y -
        BaseResidual.stressPair (coefficients H v) 0 y.2) (q, w)‖ ≤
        D * q ^ F.data.h * weight W w * (edgeDistance W w)⁻¹ ^ N := by
  obtain ⟨D, hD, N, hb⟩ := weighted_bound H v upper B m
  exact ⟨D, hD, N, fun q hq hq1 w hw => hb q hq hq1 w (by simpa only [← annulus_eq W] using hw)⟩

/-- The weighted difference can use the literal leading stress even at
the parameter endpoints. Its ambient tensors agree by continuity. -/
theorem stress_difference_jets_eq (upper : ℝ) (B m : ℕ) {q : ℝ} (hq : 0 < q)
    {w : Inner} (hX : 0 < w.1) (heta : w.2 ∈ Icc (-1 : ℝ) 1) :
    blownJet m (fun y => normalizedStress H v upper B y -
      BaseResidual.stressPair (coefficients H v) 0 y.2) (q, w) =
    blownJet m (fun y => normalizedStress H v upper B y - leadingStress v y.2) (q, w) := by
  apply iteratedFDeriv_eq_on_dense
    (s := Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1))
    (t := Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Icc (-1 : ℝ) 1))
    (isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_Ioo))
    (fun _ hy => ⟨hy.1, hy.2.1, hy.2.2.1.le, hy.2.2.2.le⟩) _ _ _ _ m
    (show ((1 : ℝ), w) ∈ Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Icc (-1 : ℝ) 1) from ⟨by
        norm_num, hX, heta⟩)
  · intro y hy
    simpa only [closure_prod_eq, closure_Ioi, closure_Ioo (by
        norm_num : (-1 : ℝ) ≠ 1), mem_prod, mem_Ici]
      using (show 0 ≤ y.1 ∧ 0 ≤ y.2.1 ∧ y.2.2 ∈ Icc (-1 : ℝ) 1 from ⟨hy.1.le, hy.2.1.le, hy.2.2⟩)
  · intro y hy
    apply ContDiffAt.comp y _ (scaleMap q).contDiff.contDiffAt
    exact (normalizedStress_smoothAt H v upper B (by simpa using mul_pos hq hy.1)).sub
      ((BaseResidual.stressPair_smooth (coefficients_smooth H v) 0).contDiffAt.comp _
          contDiffAt_snd)
  · intro y hy
    apply ContDiffAt.comp y _ (scaleMap q).contDiff.contDiffAt
    have hs : ContDiffAt ℝ ∞ (leadingStress v) (scaleMap q y).2 := by
      simpa only [scaleMap_apply] using leadingStress_smoothAt v hy.2.1 hy.2.2
    exact (normalizedStress_smoothAt H v upper B (by simpa using mul_pos hq hy.1)).sub
      (hs.comp (scaleMap q y) contDiffAt_snd)
  · intro y hy
    change normalizedStress H v upper B (scaleMap q y) - BaseResidual.stressPair (coefficients H v)
        0 y.2 =
      normalizedStress H v upper B (scaleMap q y) - leadingStress v y.2
    rw [leading_stress_eq H v hy.2.1.le (abs_le.mpr ⟨hy.2.2.1.le, hy.2.2.2.le⟩)]

theorem weighted_jets_leading (upper : ℝ) (B m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ annulus W,
      ‖blownJet m (fun y => normalizedStress H v upper B y - leadingStress v y.2) (q, w)‖ ≤
        D * q ^ F.data.h * weight W w * (edgeDistance W w)⁻¹ ^ N := by
  obtain ⟨D, hD, N, hb⟩ := weighted_jets H v upper B m
  refine ⟨D, hD, N, fun q hq hq1 w hw => ?_⟩
  rw [← stress_difference_jets_eq H v upper B m hq
    ((NominalConeAssembly.activeLeft_pos W).trans hw.1.1) hw.2]
  exact hb q hq hq1 w hw

theorem physical_stress_eq_normalized (upper : ℝ) (B : ℕ) {p : Chart} (hp : p.1 < 1) :
    (baseStressTheta (scales H v upper B) F.data.h W.axis.normalization (coefficients H v) p,
      baseStressAxial (scales H v upper B) F.data.h W.axis.normalization (coefficients H v) p) =
      (physicalChart F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2) •
        normalizedStress H v upper B (physicalChart F.data.h p) :=
  BaseResidual.physicalTensor_eq_normalized (scales_strictMono H v upper B) F.data.h_pos
      F.data.h_lt_half
    W.axis.normalization (coefficients H v) hp

theorem coefficient_stress_zero_left (n : ℕ) {p : Inner} (hp : p.1 ≤ NominalConeAssembly.activeLeft
    W) :
    (coefficients H v).stressTheta n p = 0 ∧ (coefficients H v).stressAxial n p = 0 :=
  EntranceAlignedBase.aligned_stress_zero_left W H v.profiles v.finiteModification ld.after_initial
      n hp

theorem coefficient_stress_zero_right (n : ℕ) {p : Inner}
    (hp : NominalConeAssembly.activeRight W ≤ p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    (coefficients H v).stressTheta n p = 0 ∧ (coefficients H v).stressAxial n p = 0 :=
  EntranceAlignedBase.modulated_stress_zero_right H v n hp heta

theorem coefficient_stress_support (n : ℕ) :
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
      (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
      ((coefficients H v).stressTheta n) ∧
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
      (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
      ((coefficients H v).stressAxial n) :=
  EntranceAlignedBase.modulated_all_stress_support H v n

theorem positive_stress_support {n : ℕ} (hn : 0 < n) :
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
      (EntranceAlignedBase.zeroEnd W H ld.modulation.left) (NominalConeAssembly.activeRight W)
      ((coefficients H v).stressTheta n) ∧
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
      (EntranceAlignedBase.zeroEnd W H ld.modulation.left) (NominalConeAssembly.activeRight W)
      ((coefficients H v).stressAxial n) :=
  EntranceAlignedBase.modulated_positive_radialSupport H v hn

theorem positive_support_gap :
    NominalConeAssembly.activeLeft W < EntranceAlignedBase.zeroEnd W H ld.modulation.left :=
  (EntranceAlignedBase.window_order W H ld.after_initial).1

theorem normalizedStress_zero_left (upper : ℝ) (B : ℕ) (q : ℝ) {w : Inner}
    (hw : w.1 ≤ NominalConeAssembly.activeLeft W) : normalizedStress H v upper B (q, w) = 0 :=
  BaseResidual.slowSum_zero_of_all (scales H v upper B) F.data.h q
    (fun n => Prod.ext (coefficient_stress_zero_left H v n hw).1 (coefficient_stress_zero_left H v
        n hw).2)

theorem normalizedStress_zero_outside (upper : ℝ) (B : ℕ) (q : ℝ) {w : Inner}
    (hw : w.1 ∉ Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W))
    (heta : w.2 ∈ Icc (-1 : ℝ) 1) : normalizedStress H v upper B (q, w) = 0 :=
  EntranceAlignedBase.modulated_normalizedTensor_zero H v (scales H v upper B) q hw heta

theorem physicalStress_zero_right (upper : ℝ) (B : ℕ) {p : Chart} (hp : p.1 < 1)
    (hX : NominalConeAssembly.activeRight W ≤ (physicalChart F.data.h p).2.1) :
    baseStressTheta (scales H v upper B) F.data.h W.axis.normalization (coefficients H v) p = 0 ∧
    baseStressAxial (scales H v upper B) F.data.h W.axis.normalization (coefficients H v) p = 0 :=
        by
  have heta := (physicalChart_inner_mem F.data.h_pos F.data.h_lt_half hp
    (show (physicalChart F.data.h p).2.1 ∈ Icc (physicalChart F.data.h p).2.1
      (physicalChart F.data.h p).2.1 from ⟨le_rfl, le_rfl⟩)).2
  constructor
  · apply BaseResidual.physicalProfile_zero_of_all
    exact fun n => (coefficient_stress_zero_right H v n hX heta).1
  · apply BaseResidual.physicalProfile_zero_of_all
    exact fun n => (coefficient_stress_zero_right H v n hX heta).2

theorem stressForce_zero_right (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hX : NominalConeAssembly.activeRight W < (cartesianChart F.data.h z).2.1) :
    stressForce H v upper B z = 0 := by
  let p := AxisymmetricFields.profilePoint z.1 z.2
  let theta := baseStressTheta (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)
  let axial := baseStressAxial (scales H v upper B) F.data.h W.axis.normalization (coefficients H v)
  let O : Set Inner := Ioi (NominalConeAssembly.activeRight W) ×ˢ univ
  have hp : p ∈ SimilarityProfile.physicalDomain F.data.h O := ⟨ht, hX, mem_univ _⟩
  have htheta : theta =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [(SimilarityProfile.isOpen_physicalDomain F.data.h_pos F.data.h_lt_half
      (isOpen_Ioi.prod isOpen_univ)).mem_nhds hp] with y hy
    exact (physicalStress_zero_right H v upper B hy.1 hy.2.1.le).1
  have haxial : axial =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [(SimilarityProfile.isOpen_physicalDomain F.data.h_pos F.data.h_lt_half
      (isOpen_Ioi.prod isOpen_univ)).mem_nhds hp] with y hy
    exact (physicalStress_zero_right H v upper B hy.1 hy.2.1.le).2
  have ht0 := htheta.self_of_nhds
  have ha0 := haxial.self_of_nhds
  have htd : SimilarityProfile.partialS theta p = 0 := by
    simp [SimilarityProfile.partialS, htheta.fderiv_eq]
  have had : SimilarityProfile.partialS axial p = 0 := by
    simp [SimilarityProfile.partialS, haxial.fderiv_eq]
  change BaseResidual.stressForce theta axial z = 0
  simp only [BaseResidual.stressForce, SlowResidualMatching.tangentialStressForce,
    LeadingStress.radialDivergence]
  change AxisymmetricResidual.pack
    (_ * (Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS theta p + 2 * theta p / _))
    (_ * (Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS theta p + 2 * theta p / _))
    (-(Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS axial p + 1 * axial p / _)) = _
  simp [ht0, ha0, htd, had, AxisymmetricResidual.pack]

theorem stressForce_exterior_germ (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hX : NominalConeAssembly.activeRight W < (cartesianChart F.data.h z).2.1) :
    stressForce H v upper B =ᶠ[𝓝 z] fun _ => 0 := by
  have hO : IsOpen {w : Inner | NominalConeAssembly.activeRight W < w.1} :=
    isOpen_lt continuous_const continuous_fst
  filter_upwards [(BaseResidual.chartedDomain_isOpen F.data.h_pos F.data.h_lt_half hO).mem_nhds
    (show z ∈ BaseResidual.chartedDomain F.data.h {w : Inner | NominalConeAssembly.activeRight W <
        w.1}
      from ⟨ht, hX⟩)] with y hy
  exact stressForce_zero_right H v upper B hy.1 hy.2

theorem stressForce_jets_zero_in_exterior (upper : ℝ) (B m : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hX : NominalConeAssembly.activeRight W < (cartesianChart F.data.h z).2.1) :
    iteratedFDeriv ℝ m (stressForce H v upper B) z = 0 := by
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (stressForce_exterior_germ H v upper B ht hX)
      m).self_of_nhds,
    iteratedFDeriv_fun_zero, Pi.zero_apply]

theorem stressForce_core_germ (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hX : (cartesianChart F.data.h z).2.1 < NominalConeAssembly.activeLeft W) :
    stressForce H v upper B =ᶠ[𝓝 z] fun _ => 0 :=
  BaseResidual.baseStressForce_core_germ F.data.h_pos F.data.h_lt_half (scales H v upper B)
    (stressZeroCore H v) ht hX

theorem stressForce_jets_zero_in_core (upper : ℝ) (B m : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hX : (cartesianChart F.data.h z).2.1 < NominalConeAssembly.activeLeft W) :
    iteratedFDeriv ℝ m (stressForce H v upper B) z = 0 := by
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (stressForce_core_germ H v upper B ht hX)
      m).self_of_nhds,
    iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- The exterior comparison uses the actual coefficient formulas, not a
separately assumed support or heat-flow conclusion. -/
theorem realizesScheme : ModulatedExterior.RealizesScheme (EntranceAlignedBase.modulatedScheme H v)
    v.finiteModification.contains (coefficients H v) := ⟨rfl, rfl, rfl⟩

theorem exterior_fields_eq_heat (upper : ℝ) (B : ℕ) :
    EqOn (velocity H v upper B) (BaseExterior.heatVelocity (BaseExterior.nominalHeatNormalization
        W) F.data.h)
      (BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) ∧
    EqOn (pressure H v upper B) (BaseExterior.heatPressureField
        (BaseExterior.nominalHeatNormalization W) F.data.h)
      (BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :=
  ModulatedExterior.realized_base_eq_heat W v.profiles v.finiteModification (realizesScheme H v)
    (EntranceAlignedBase.modulated_base_eq H v) (EntranceAlignedBase.modulated_outer H v)
    (coefficients_smooth H v) (ModulatedExterior.actual_squared_swirl_restored v)
    (scales_strictMono H v upper B)

theorem exterior_residual_zero (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    ProblemStatement.navierStokesResidual (velocity H v upper B) (pressure H v upper B) z.1 z.2 = 0
        :=
  ModulatedExterior.realized_base_residual_zero W v.profiles v.finiteModification (realizesScheme H
      v)
    (EntranceAlignedBase.modulated_base_eq H v) (EntranceAlignedBase.modulated_outer H v)
    (coefficients_smooth H v) (ModulatedExterior.actual_squared_swirl_restored v)
    (scales_strictMono H v upper B) hz

theorem exterior_residual_jets_zero (upper : ℝ) (B m : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    iteratedFDeriv ℝ m (fun p => ProblemStatement.navierStokesResidual
      (velocity H v upper B) (pressure H v upper B) p.1 p.2) z = 0 :=
  ModulatedExterior.realized_residual_jets_zero W v.profiles v.finiteModification (realizesScheme H
      v)
    (EntranceAlignedBase.modulated_base_eq H v) (EntranceAlignedBase.modulated_outer H v)
    (coefficients_smooth H v) (ModulatedExterior.actual_squared_swirl_restored v)
    (scales_strictMono H v upper B) hz m

/-- Completed velocity, given by `ModulatedExterior.completedVelocity
(BaseExterior.nominalHeatNormalization W) F.data.h (velocity H v upper B)`. -/
noncomputable def completedVelocity (upper : ℝ) (B : ℕ) : ProblemStatement.VelocityField :=
  ModulatedExterior.completedVelocity (BaseExterior.nominalHeatNormalization W) F.data.h (velocity
      H v upper B)

/-- Completed pressure, given by `ModulatedExterior.completedPressure
(BaseExterior.nominalHeatNormalization W) F.data.h (pressure H v upper B)`. -/
noncomputable def completedPressure (upper : ℝ) (B : ℕ) : ProblemStatement.PressureField :=
  ModulatedExterior.completedPressure (BaseExterior.nominalHeatNormalization W) F.data.h (pressure
      H v upper B)

theorem completedVelocity_before (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime} (ht : z.1 <
    1) :
    completedVelocity H v upper B z = velocity H v upper B z := ite_eq_left ht

theorem completedPressure_before (upper : ℝ) (B : ℕ) {z : ProblemStatement.SpaceTime} (ht : z.1 <
    1) :
    completedPressure H v upper B z = pressure H v upper B z := ite_eq_left ht

/-- The same exterior yields an actual joint one-sided terminal extension
near every non-axis point in the central symmetry plane. -/
theorem terminal_extension (upper : ℝ) (B : ℕ) {x : ProblemStatement.Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set ProblemStatement.SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn (completedVelocity H v upper B)
        (BaseExterior.heatVelocity (BaseExterior.nominalHeatNormalization W) F.data.h) U ∧
      EqOn (completedPressure H v upper B)
        (BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h) U ∧
      ContDiffOn ℝ ∞ (completedVelocity H v upper B) (U ∩ (Iic 1 ×ˢ (univ : Set
          ProblemStatement.Space))) ∧
      ContDiffOn ℝ ∞ (completedPressure H v upper B) (U ∩ (Iic 1 ×ˢ (univ : Set
          ProblemStatement.Space))) :=
  ModulatedExterior.realized_terminal_extension W v.profiles v.finiteModification (realizesScheme H
      v)
    (EntranceAlignedBase.modulated_base_eq H v) (EntranceAlignedBase.modulated_outer H v)
    (coefficients_smooth H v) (ModulatedExterior.actual_squared_swirl_restored v)
    (scales_strictMono H v upper B) hx hs

end Fields

/-- Intermediate data produced by the proved nominal and finite-modulation
constructions. No PDE, support, smoothness, or residual conclusion is stored
as an input to this record. -/
structure ProfileData where
  /-- Outgoing of `ProfileData`, of type `OutgoingProfile.Profile`. -/
  outgoing : OutgoingProfile.Profile
  /-- Nominal of `ProfileData`, of type `NominalProfile.Witness outgoing`. -/
  nominal : NominalProfile.Witness outgoing
  certificate : NominalConeAssembly.Certificate nominal
  /-- Loop of `ProfileData`, of type `ModulatedProfileAssembly.LoopData nominal`. -/
  loop : ModulatedProfileAssembly.LoopData nominal
  /-- Modulation of `ProfileData`, of type `ModulatedProfileAssembly.Witness loop`. -/
  modulation : ModulatedProfileAssembly.Witness loop
  fullTrueCone : LeadingStressWeights.FullTrueCone modulation

theorem profileData_nonempty : Nonempty ProfileData := by
  obtain ⟨F, W, H⟩ := NominalConeAssembly.exists_nominal_cone
  obtain ⟨ld, v, hc⟩ := ModulatedProfileAssembly.exists_of_certificate W H
  exact ⟨⟨F, W, H, ld, v, hc⟩⟩

/-- One actual profile is fixed before choosing the scale lower bound or
the compact profile box. -/
noncomputable def actualProfile : ProfileData := Classical.choice profileData_nonempty

/-- A complete slow base is constructed without a profile, moment repair,
finite PDE identity, support estimate, or residual estimate among the inputs.
The same profile, coefficient sequence, and scale sequence occur throughout. -/
theorem exists_final_base (upper : ℝ) (B : ℕ) :
    ∃ (F : OutgoingProfile.Profile) (W : NominalProfile.Witness F)
      (H : NominalConeAssembly.Certificate W)
      (ld : ModulatedProfileAssembly.LoopData W) (v : ModulatedProfileAssembly.Witness ld),
      LeadingStressWeights.FullTrueCone v ∧
      SmoothCoefficients (coefficients H v) ∧
      BaseResidual.FiniteIdentities F.data.h W.axis.normalization (coefficients H v)
          (profileSequence H v) ∧
      B ≤ scales H v upper B 0 ∧
      AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients H v))
        (innerBox 0 (boxRadius W upper)) (scales H v upper B) ∧
      AdmissibleScales F.data.h
        (BaseResidual.weightedBundle W.axis.normalization (coefficients H v) (weight W))
        (innerBox 0 (boxRadius W upper)) (scales H v upper B) ∧
      ActiveAnnulusWeight.WeightedBounds (Icc (-1 : ℝ) 1)
        (edgeExponent W) (logLeft W) (logRight W)
        (LeadingStressWeights.logStress v.profiles F.data.h) ∧
      ConstructedSlowBase.WeightedStressBound (scales H v upper B) F.data.h (coefficients H v)
        (edgeExponent W) (logLeft W) (logRight W) ∧
      (∀ n : ℕ, SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
          (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
          ((coefficients H v).stressTheta n) ∧
        SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1)
          (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
          ((coefficients H v).stressAxial n)) ∧
      (∀ p : Inner, 0 ≤ p.1 → |p.2| ≤ 1 →
        BaseResidual.stressPair (coefficients H v) 0 p = leadingStress v p) ∧
      velocity H v upper B = SpatialCurl.spatialCurl (vectorPotential H v upper B) ∧
      ContDiffOn ℝ ∞ (vectorPotential H v upper B) BaseResidual.past ∧
      ContDiffOn ℝ ∞ (velocity H v upper B) BaseResidual.past ∧
      ContDiffOn ℝ ∞ (pressure H v upper B) BaseResidual.past ∧
      ContDiffOn ℝ ∞ (stressForce H v upper B) BaseResidual.past ∧
      ContDiffOn ℝ ∞ (error H v upper B) BaseResidual.past ∧
      (∀ t < (1 : ℝ), ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence (velocity H v upper B) t x = 0) ∧
      (∀ z : ProblemStatement.SpaceTime,
        ProblemStatement.navierStokesResidual (velocity H v upper B) (pressure H v upper B) z.1 z.2
            =
          stressForce H v upper B z + error H v upper B z) ∧
      (∀ t < (1 : ℝ), velocity H v upper B (t, 0) =
        ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector
            2) ∧
      ProblemStatement.SpeedUnboundedAtOne (velocity H v upper B) ∧
      (∀ l : Filter ProblemStatement.SpaceTime,
        BaseResidual.PhysicalApproach l F.data.h 0 (boxRadius W upper) →
          ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1) (error H v upper
              B)) ∧
      EqOn (velocity H v upper B)
        (BaseExterior.heatVelocity (BaseExterior.nominalHeatNormalization W) F.data.h)
        (BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) ∧
      EqOn (pressure H v upper B)
        (BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h)
        (BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) := by
  let D := actualProfile
  refine ⟨D.outgoing, D.nominal, D.certificate, D.loop, D.modulation, D.fullTrueCone,
    coefficients_smooth D.certificate D.modulation, finiteIdentities D.certificate D.modulation,
    (scales_spec D.certificate D.modulation upper B).1,
    scales_admissible D.certificate D.modulation upper B,
    (scales_spec D.certificate D.modulation upper B).2,
    leading_weighted D.modulation D.fullTrueCone,
    weighted_bound D.certificate D.modulation upper B,
    coefficient_stress_support D.certificate D.modulation,
    fun _ hx he => leading_stress_eq D.certificate D.modulation hx he,
    velocity_eq_curl D.certificate D.modulation upper B,
    vectorPotential_smooth D.certificate D.modulation upper B,
    velocity_smooth D.certificate D.modulation upper B,
    pressure_smooth D.certificate D.modulation upper B,
    stressForce_smooth D.certificate D.modulation upper B,
    error_smooth D.certificate D.modulation upper B,
    fun _ ht x => divergence_zero D.certificate D.modulation upper B ht x,
    residual_identity D.certificate D.modulation upper B,
    fun _ ht => origin D.certificate D.modulation upper B ht,
    speedUnbounded D.certificate D.modulation upper B,
    fun _ hp => error_allJetsFlat D.certificate D.modulation upper B hp le_rfl,
    (exterior_fields_eq_heat D.certificate D.modulation upper B).1,
    (exterior_fields_eq_heat D.certificate D.modulation upper B).2⟩

end NavierStokes.FinalSlowBase
