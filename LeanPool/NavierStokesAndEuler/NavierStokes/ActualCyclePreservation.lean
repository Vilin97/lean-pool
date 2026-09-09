/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCycleData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIntermediateDebtBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCommonDynamics
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedGaussian
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedMeanBinding
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity

/-!
# Preservation by the actual correction cycle

The fixed parameters, current residual, signed request, and comparison
primary are those of the existing initialization. The concrete wave
constructions supply the inputs to the generic analytic step.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCyclePreservation

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open scoped ContDiff Topology BigOperators


/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index local notation "G" =>
ActualInitialization.geometry local notation "κ" => ChartScales.kappa`. -/
abbrev Index := ActualInitialization.Index

local notation "G" => ActualInitialization.geometry
local notation "κ" => ChartScales.kappa

/-- One fixed similarity geometry and the actual base/rank parameters
work at every correction stage. -/
noncomputable def staticData (B : ℕ) :
    CorrectionAnalyticStep.StaticData G ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      ActualPrimary.rankData (ActualPrimary.commonContext B) κ where
  aliasData := ActualCycleGeometry.similarityData
  coord := rfl
  region := HEq.rfl
  inner := rfl
  outer := rfl
  gauge := ActualCycleGeometry.gauge_eq_geometry.symm
  strip := rfl
  time := rfl
  index_eq := rfl
  operators_eq := rfl
  operators := ActualInitialization.operators B
  base := ActualInitialization.base_bounds B
  axial_eq := rfl
  temporal := rfl
  fast := fun _ => rfl
  angular_slow := by
    intro n R p hp Y
    rfl
  axial_slow := by
    intro n R p hp Y
    rfl
  rankExponent := CoordinateAlgebra.A ActualPrimary.h
  rankCoefficient := ActualPrimary.rankAmplitude
  rankParameters := ActualPrimary.rankData_parameters (G).region.carrier
  rankCoefficient_ne := ActualPrimary.rankAmplitude_pos.ne'
  rank_left := ActualPrimary.active_left_before_rank
  rank_right := ActualPrimary.rank_before_active_right

theorem kappa_small : κ ≤ 1/100000 := by norm_num [ChartScales.kappa]

theorem primary_band {B N0 : ℕ} (l : Index B N0) :
    (ActualInitialization.tangentBlock l).BandLimited 1 :=
  SignedWaveUpdate.coefficientBlock_band _ _ _ _ _

section CurrentState

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    {S : Index B N0 → ℕ → Set Point}
    (H : CycleAnalyticInvariant G (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)

include H

/-- Debt regularity comes from the current primitive invariant; the
reserved pure-power base model is the already proved actual base. -/
theorem rank_geometry :
    LocalRankDefect.RankGeometry (G).gauge ActualPrimary.rankData (G).region.carrier
      (ActualPrimary.commonContext B) x.state :=
  ActualPrimary.rank_geometry (G).region B x.state
    (MeanStageRegularity.debt_smooth H.primitives (G).patch.a_pos
      ((G).patch.a_lt_left.trans ((G).patch.left_lt_right.trans (G).patch.right_lt_b)))

theorem current_normal (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) 0
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) := by
  have he :
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) =
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (ActualInitialization.operators B) (ActualInitialization.radius_pos B)
        (ActualInitialization.primaryBlock l).phase n z i) := by
    funext n l z
    rw [← (H.carrier l).phase]
    rfl
  rw [he]
  exact ActualInitialization.slowNormal_local B N0 i

theorem current_frequency :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) (-(1/2))
      (fun n l _ => (x.coefficients.blocks l).frequency n) := by
  have he : (fun n l (_ : Point) => (x.coefficients.blocks l).frequency n) =
      (fun n l (_ : Point) => (ActualInitialization.primaryBlock l).frequency n) := by
    funext n l z
    rw [← (H.carrier l).frequency]
    rfl
  rw [he]
  exact ActualInitialization.frequency_local B N0

theorem current_angular :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) (-(1/2))
      (fun n l _ => ((x.coefficients.blocks l).angularFrequency n : ℝ)) := by
  have he : (fun n l (_ : Point) => ((x.coefficients.blocks l).angularFrequency n : ℝ)) =
      (fun n l (_ : Point) => ((ActualInitialization.primaryBlock l).angularFrequency n : ℝ)) := by
    funext n l z
    rw [← (H.carrier l).angular]
    rfl
  rw [he]
  exact ActualInitialization.angularFrequency_local B N0

end CurrentState

/-! The actual label set is unchanged by every correction. -/

theorem step_labels {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext
        B)).coefficients.labels =
      x.coefficients.labels := rfl

/-- State, constructed using `CycleState.iterate`. -/
noncomputable def state (B N0 : ℕ) : ℕ → CycleState (Index B N0) :=
  CycleState.iterate (fun _ => ActualCycleParameters.fixedParameters B N0)
    (ActualPrimary.commonContext B) (ActualInitialization.initialCycleState B N0)

theorem state_zero (B N0 : ℕ) : state B N0 0 = ActualInitialization.initialCycleState B N0 := rfl

theorem state_succ (B N0 n : ℕ) :
    state B N0 (n+1) = (state B N0 n).step (ActualCycleParameters.fixedParameters B N0)
      (ActualPrimary.commonContext B) := rfl

theorem state_labels (B N0 n : ℕ) :
    (state B N0 n).coefficients.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B
        N0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih


/-- The fixed comparison primary is the original finite tangent field. -/
noncomputable def primaryField (B N0 : ℕ) : Oscillation Point :=
  LabelSumBounds.fieldSum (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (fun l => (ActualInitialization.tangentBlock l).oscillation)

theorem primaryField_eq (B N0 : ℕ) :
    primaryField B N0 = ActualPrimaryCovariance.tangentSum B N0 := by
  funext n z i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (fun f : Oscillation Point => f n z i)
    (ActualInitialization.tangentBlock_represents l)

theorem primaryField_smooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth (G).domain (primaryField B N0) := by
  rw [primaryField_eq]
  exact ActualInitialMean.tangent_angularSmooth B N0

theorem primaryField_periodic (B N0 : ℕ) :
    OscillationPeriodic (G).region.carrier (primaryField B N0) := by
  intro n R s hs theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  simp only [ActualInitialization.tangentBlock_represents]
  have he := congrFun (ActualPrimaryCoherence.piece_tangentVelocity_periodic
      ActualPrimary.standardRegion l.2 l.1 n (ActualCycleParameters.activeLabel_index n l hl)
      k ((R, (s, Y)), theta)) i
  simp only [ActualPrimaryCoherence.chartDeck, TorusAverages.latticePoint,
    Prod.add_def, add_zero] at he
  exact he


/-- A true source core with its native dyadic restriction lies in the
existing quantitative control cell on the evaluation strip. -/
theorem meanControl_of_source_and_nativeQ {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {z : Point} (hz : z ∈ (G).strip.domain)
    (hS : z ∈ ActualInitialization.labelCarrier l n)
    (hQ : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n z)) ∈ Icc (1 / 2 : ℝ) 2) :
    z ∈ ActualInitialization.meanControlCell n l := by
  obtain ⟨k, hn, hcell, hclock⟩ := ActualCarrierGeometry.labelCarrier_phaseCell hN
    (l.2,l.1) n (x := (z,0)) hz hS
  refine ⟨k, hn, hcell, hclock, ?_⟩
  rw [← congrFun (ActualSignedStageControls.nativePoint_eq_fullCopy l n k hn) (z,0)]
  exact hQ

/-- Restrict a local estimate only on the actual evaluation domain. -/
theorem localUnweighted_restrict {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData Point} {C K : ℕ → I → Set Point} {α : ℝ}
    {f : ℕ → I → Point → E}
    (h : LocalizedWaveBounds.LocalUnweighted s C α f)
    (hKC : ∀ n l z, z ∈ s.domain → z ∈ K n l → z ∈ C n l) :
    LocalizedWaveBounds.LocalUnweighted s K α f where
  weight_nonneg := h.weight_nonneg
  smooth := fun n l z hz hk => h.smooth n l z hz (hKC n l z hz hk)
  bounds := by
    intro m
    obtain ⟨A, hA, p, hb⟩ := h.bounds m
    exact ⟨A, hA, p, fun n l z hz hk j hj => hb n l z hz (hKC n l z hz hk) j hj⟩

theorem family_primary_eq {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    SignedMeanGain.primaryField f a = primaryField B N0 := by
  simp only [SignedMeanGain.primaryField, primaryField, hp, hl]

theorem family_primary_smooth {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    WaveStateRegularity.AngularSmooth (G).domain (SignedMeanGain.primaryField f a) := by
  rw [family_primary_eq f a hp hl]
  exact primaryField_smooth B N0

theorem family_primary_periodic {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    OscillationPeriodic (G).region.carrier (SignedMeanGain.primaryField f a) := by
  rw [family_primary_eq f a hp hl]
  exact primaryField_periodic B N0


/-- The cycle keeps the actual closed radial and native dyadic cores. -/
abbrev Invariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop :=
  CycleAnalyticInvariant G (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope
    ActualCoreSupport.refinedCarrier σ x

theorem core_control {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {z : Point} (hz : z ∈ (G).strip.domain)
    (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    z ∈ ActualInitialization.meanControlCell n l := by
  have h := (ActualCoreSupport.mem_refinedCarrier_iff l n
    (ActualInitialization.strip_time z hz)).mp hc
  exact meanControl_of_source_and_nativeQ hN l n hz h.1 h.2.2

theorem core_normal {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) 0
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) :=
  localUnweighted_restrict (current_normal H i)
    (fun n l _z hz hc => core_control hN l n hz hc)

theorem core_frequency {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) (-(1/2))
      (fun n l _ => (x.coefficients.blocks l).frequency n) :=
  localUnweighted_restrict (current_frequency H)
    (fun n l _z hz hc => core_control hN l n hz hc)

theorem core_angular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) (-(1/2))
      (fun n l _ => ((x.coefficients.blocks l).angularFrequency n : ℝ)) :=
  localUnweighted_restrict (current_angular H)
    (fun n l _z hz hc => core_control hN l n hz hc)

/-- Existing estimates stated on the broad carrier apply by inclusion;
the stronger support is still retained by the cycle invariant. -/
theorem broad_invariant {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) :
    CycleAnalyticInvariant G (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualInitialization.labelCarrier σ x := by
  refine { H with inputSupport := ?_ }
  intro l
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i j hj z hz hn
    exact (H.inputSupport l).velocity n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n j hj z hz hn
    exact (H.inputSupport l).pressure n j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n i j hj z hz hn
    exact (H.inputSupport l).gaussian n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n i j hj z hz hn
    exact (H.inputSupport l).aliasError n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))

/-- The strengthened support is already proved for the literal initial state. -/
theorem initial_invariant (B N0 : ℕ) : Invariant (1/5) (state B N0 0) :=
  ActualCoreSupport.initial_invariant B N0

theorem closed_radius_mem_closure {z : Point} (hz : z ∈ (G).domain)
    (hr : ActualCoreSupport.radialRatio z ∈ Icc (G).patch.a (G).patch.b) :
    z ∈ closure (G).strip.domain := by
  let ell := VariableGaugeMean.qLength (2 * ActualPrimary.h) z.2.1
  have hT := (G).region.time_pos z.2.1 hz
  have hp : 0 < ell := VariableGaugeMean.qLength_pos
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) hT
  let f : ℝ → Point := fun r => (r * ell, z.2)
  have hf : Continuous f := (continuous_id.mul continuous_const).prodMk continuous_const
  have hi : ActualCoreSupport.radialRatio z ∈ closure (Ioo (G).patch.a (G).patch.b) := by
    rwa [closure_Ioo ((G).patch.a_lt_left.trans
      ((G).patch.left_lt_right.trans (G).patch.right_lt_b)).ne]
  have hm : MapsTo f (Ioo (G).patch.a (G).patch.b) (G).strip.domain := by
    intro r hrr
    apply (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
        _).mpr
    refine ⟨hz, ?_⟩
    rw [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq]
    change r * ell / ell ∈ Ioo (G).patch.a (G).patch.b
    simpa only [mul_div_cancel_right₀ _ hp.ne'] using hrr
  have hc := hf.continuousAt.continuousWithinAt.mem_closure hi hm
  have he : f (ActualCoreSupport.radialRatio z) = z := by
    change (z.1 / ell * ell, z.2) = z
    rw [div_mul_cancel₀ _ hp.ne']
  rwa [he] at hc

theorem physicalPosition_continuous (n : ℕ) (i : Fin 3) :
    Continuous (fun z : Point => ActualPrimary.physicalPosition n z i) := by
  fin_cases i
  · exact continuous_const.mul continuous_fst
  · exact continuous_const.mul continuous_snd.fst.snd
  · exact continuous_const.mul continuous_snd.fst.fst

theorem physicalPosition_bound_closed (n : ℕ) {z : Point}
    (hz : z ∈ closure (G).strip.domain) (i : Fin 3) :
    |ActualPrimary.physicalPosition n z i| ≤ BaseContextAssembly.geometryBound
      ActualPrimary.nominal ActualPrimary.standardRegion := by
  have hc : IsClosed {x : Point | |ActualPrimary.physicalPosition n x i| ≤
      BaseContextAssembly.geometryBound ActualPrimary.nominal ActualPrimary.standardRegion} :=
    isClosed_le (physicalPosition_continuous n i).abs continuous_const
  exact closure_minimal
    (fun x hx => ActualPrimary.physicalPosition_bound ActualPrimary.standardRegion n hx i) hc hz

theorem core_near {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ (G).domain) (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    ActualPrimaryBounds.near (l.2,l.1) n := by
  have hT := (G).region.time_pos z.2.1 hz
  have hcore := (ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc
  apply ActualWaveRegularityData.near_of_native_band l n
    (p := BaseContextAssembly.slowCoordinates z) hT
  · exact hz.2
  · have hq := hcore.2.2
    change SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n z)) ∈ Icc (1/2 : ℝ) 2 at hq
    rwa [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange] at hq

/-- Every supported label belongs to the literal finite sum in that band,
including at the two closed radial edges. -/
theorem core_active {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ (G).domain) (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n := by
  have hT := (G).region.time_pos z.2.1 hz
  have hcore := (ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc
  have hclose := closed_radius_mem_closure hz hcore.2.1
  have hslow := ActualCarrierGeometry.labelCarrier_slow_core (l.2,l.1) n hcore.1
  have hbox := ActualCarrierGeometry.nativeSlowCore_physicalBox (l.2,l.1) hslow
  rw [ActualPrimaryCovariance.nativePoint_position] at hbox
  apply (ActualPrimary.mem_activeLabels ActualPrimary.standardRegion n l.1 l.2).mpr
  apply Finset.mem_biUnion.mpr
  refine ⟨BaseChartJets.cellBand l.1, (core_near l n hz hc).2, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(PrimaryGeometryAssembly.label ActualPrimary.nominal l.1).2, ?_, rfl⟩
  apply CommonWindow.grid_mem_of_box l.1.val.property.1 (physicalPosition_bound_closed n hclose)
  exact hbox

section SignedOutputs
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state
local notation "post" => CycleParameters.afterParticular p v c u
local notation "request" => CycleParameters.signedRequest p v c u

theorem signed_request_jets (first : ActualParticularMeanGain.Result x σ) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun _ _ z => ActualSignedStageControls.fullStrip.zeta z) (σ-κ)
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
      (fun _ n _ z => request n z q) := by
  have h := ActualSignedStageControls.fullRequest_jets_from_residuals G c post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial
    (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
  simp only [show (1+σ-κ)-1 = σ-κ by ring] at h
  exact h

theorem signed_common_bounds (first : ActualParticularMeanGain.Result x σ) :
    ActualSignedOutputBounds.OutputBounds (B := B) (N0 := N0) request (1/2+σ-κ) := by
  have h := ActualSignedOutputBounds.actual_common_bounds (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial
  simp only [show (1+σ-κ)-1/2 = 1/2+σ-κ by ring] at h
  exact h

theorem signed_block_bounds (first : ActualParticularMeanGain.Result x σ) :
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1/2+σ-κ)
      (fun l n z => ((p).signedTangent v c u l).velocity n i j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1/2+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-2*κ)
      (fun l n z => ((p).signedCurl v c u l).velocity n i j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-4*κ)
      (fun (l : Index B N0) n z => ((ActualSignedStageControls.parameters l).goodBlock (G).strip
          request).velocity n i j z)) := by
  have h := ActualSignedOutputBounds.actual_block_bounds (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial
  simp only [show (1+σ-κ)-1/2 = 1/2+σ-κ by ring,
    show (1+σ-κ)-κ = 1+σ-2*κ by ring,
    show (1+σ-κ)-3*κ = 1+σ-4*κ by ring] at h
  exact h

theorem signed_gaussian_bounds (first : ActualParticularMeanGain.Result x σ)
    (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass (G).strip (fun _ _ z => Real.sqrt ((G).strip.zeta z)) β
      (fun l n z => ((p).signedGaussianBlock v c u l).velocity n i j z) :=
  ActualSignedGaussian.actual_gaussianBlock_jets (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial β i j

theorem signed_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedBlock v c u l).velocity n i) :=
  ActualWaveRegularityData.signed_exact_coefficients_smooth l request
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_pressure_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedBlock v c u l).pressure n) :=
  ActualWaveRegularityData.signed_pressure_coefficients_smooth l request
    ((signed_common_bounds first).pressure.each l) n

theorem signed_gaussian_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedGaussianBlock v c u l).velocity n i)
        :=
  ActualWaveRegularityData.signed_gaussian_coefficients_smooth l request
    ((ActualSignedGaussian.globalGaussian_all_gains (signed_request_jets first) 0).each l) n i

theorem signed_field_smooth (first : ActualParticularMeanGain.Result x σ) :
    WaveStateRegularity.AngularSmooth (G).domain ((p).signedVelocity v c u) := by
  intro n i
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_exact_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_field_periodic :
    OscillationPeriodic (G).region.carrier ((p).signedVelocity v c u) := by
  intro n R z hz theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (ActualWaveRegularityData.signed_block_periodic l (G).strip (G).patch (G).coord
    c post n R z hz theta Y k) i

theorem signed_field_support :
    WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b ((p).signedVelocity v c u)
        := by
  apply WaveStateRegularity.fieldSum_support
  intro n l hl theta i z hz hn
  exact ActualWaveRegularityData.signed_exact_support l (G).patch (G).coord c post
    n theta i z hz hn

theorem signed_pressure_field_smooth (first : ActualParticularMeanGain.Result x σ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((p).signedPressure v c u n) ((G).domain ×ˢ (univ : Set ℝ)) := by
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_pressure_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).pressure.each l) n

theorem signed_tangent_field_smooth (first : ActualParticularMeanGain.Result x σ) :
    WaveStateRegularity.AngularSmooth (G).domain
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  intro n i
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_tangent_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_tangent_field_periodic :
    OscillationPeriodic (G).region.carrier
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  intro n R z hz theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (ActualWaveRegularityData.signed_tangent_periodic l (G).patch (G).coord c post
    n R z hz theta Y k) i

theorem signed_tangent_field_support :
    WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  apply WaveStateRegularity.fieldSum_support
  intro n l hl theta i z hz hn
  exact ActualWaveRegularityData.signed_tangent_support l (G).patch (G).coord c post
    n theta i z hz hn

end SignedOutputs

section Assembly
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state

theorem particular_inputs (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (ha : ∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope
      (1 / 2 + σ) (fun l n z => ((p).particularBlock v c u l).velocity n i j z))
    (hs : WaveStateRegularity.AngularSmooth (G).domain ((p).particularVelocity v c u))
    (hp : OscillationPeriodic (G).region.carrier ((p).particularVelocity v c u))
    (hr : WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b
      ((p).particularVelocity v c u)) :
    ActualParticularMeanGain.Inputs x σ where
  amplitude := ha
  smooth := hs
  periodic := hp
  supported := hr
  old_support := ActualCycleAssembly.old_supported x H hN
    ActualCoreSupport.refinedCarrier_subset_broad
  particular_support := ActualCycleAssembly.particular_supported_of_inputSupport x hN
    (ActualCycleAssembly.cycle_particular_inputSupport hN x c (broad_invariant H).inputSupport)

/-- Step data of waves used in actual cycle preservation. -/
noncomputable def stepDataOfWaves (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (W : CorrectionAnalyticStep.WaveData G p v c u ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier σ κ) :
    CorrectionAnalyticStep.StepData G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) H hσ := by
  let hP0 := fun (l : Index B N0) n z (_hz : z ∈ (G).strip.domain) =>
    ActualInitialization.envelope_nonneg l n z
  let hP1 := fun (l : Index B N0) n z (_hz : z ∈ (G).strip.domain) =>
    ActualInitialization.envelope_le_one l n z
  let a := ActualCycleAssembly.assembly x H hσ W.particular W.tangent W.curl hP0 hP1 hN
    ActualCoreSupport.refinedCarrier_subset_broad
  have hs := ActualCycleAssembly.assembly_supports x H hσ W.particular W.tangent W.curl
    hP0 hP1 hN ActualCoreSupport.refinedCarrier_subset_broad
  have ha : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 :=
    hs.1.trans hl
  refine {
    waves := W
    primaryBand := 1
    primary_band := primary_band
    envelope_nonneg := hP0
    envelope_le_one := hP1
    cells := fun n l => ActualCoreSupport.refinedCarrier l n
    carrier_closed := ActualCoreSupport.refinedCarrier_closed
    carrier_cells := fun _ _ => Subset.rfl
    normal := core_normal H hN
    frequency := core_frequency H hN
    angular := core_angular H hN
    assembly := a
    labels := hs.1
    old_support := hs.2.1
    particular_support := hs.2.2
    primary_smooth := family_primary_smooth _ a rfl ha
    primary_periodic := family_primary_periodic _ a rfl ha
    rank_geometry := rank_geometry H
    tailStart := (ActualPrimary.choice B N0).prepared.N + 1
    cross_tail := ?_ }
  intro n hn z hz i
  exact ActualSignedMeanBinding.family_requested_cross_tail c
    ((p).afterParticular v c u) _ a rfl rfl ha hn hz i

end Assembly

/-- In a band with no compatible common cover, the actual incoming
source has a zero germ throughout the complete slow cylinder. -/
theorem residualSource_zero_germ_of_not_ordered {B N0 : ℕ} {σ : ℝ}
    {x : CycleState (Index B N0)} (H : Invariant σ x)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n)
    (j : ℤ) {z : Point} (hz : z ∈ (G).domain) :
    ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l)
      (x.coefficients.aliasCoefficients l) j n =ᶠ[𝓝 z] fun _ => 0 := by
  apply HarmonicSourceSupport.residualSource_zero_germ_on _ _ _ _ _
    (G).domain_open (ActualCoreSupport.refinedCarrier_closed l) (H.inputSupport l) j n hz
  intro hc
  exact hn (ActualCycleParameters.activeLabel_index n l (core_active l n hz hc))

section SignedEquations
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state
local notation "post" => CycleParameters.afterParticular p v c u
local notation "request" => CycleParameters.signedRequest p v c u

theorem signed_solenoidal (first : ActualParticularMeanGain.Result x σ) (l : Index B N0) :
    HarmonicWaveInteraction.ModeSolenoidal (G).strip c ((p).signedBlock v c u l) :=
  ActualSignedCommonDynamics.actual_modeSolenoidal G rfl post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial l

theorem signed_linear_bounds (H : Invariant σ x)
    (first : ActualParticularMeanGain.Result x σ) :
    UniformHarmonicInteraction.UniformVelocity (G).strip ActualInitialization.envelope
      (1+σ-4*κ) (fun l => HarmonicWaveInteraction.linearGoodBlock c
        ((p).beforeSignedBlock v c u l) ((p).signedBlock v c u l)
        ((p).signedGaussianBlock v c u l).velocity) := by
  have hc (l : Index B N0) : SameCarrier ((p).beforeSignedBlock v c u l)
      ((p).signedBlock v c u l) := by
    have h := ActualCycleParameters.invariant_fixedParameters_signed_carrier H l
    exact ⟨h.frequency,h.phase,h.angular⟩
  have h := ActualSignedCommonDynamics.actual_linearGood_bounds G rfl post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial
    ((p).beforeSignedBlock v c u) hc
  simp only [show (1+σ-κ)-3*κ = 1+σ-4*κ by ring] at h
  exact h

theorem signed_inputSupport (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn (G).domain (ActualCoreSupport.refinedCarrier l)
      ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity 0 :=
  ActualCycleAssembly.refined_signed_inputSupport l (G).strip request

end SignedEquations

/-- Native particular data used in actual cycle preservation. -/
noncomputable def nativeParticularData {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j

theorem nativeParticular_inactive {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    (nativeParticularData x l j).common.amplitude n =ᶠ[𝓝 z] fun _ => 0 := by
  have hp : z.1.1 ∈ ActualCarrierTransport.parameterDomain := hz.1
  apply ActualCycleAssembly.common_raw_zero_germ_of_factorization l
    (ActualCoreSupport.refinedCarrier l) (ActualCycleAssembly.refinedSlowCore l)
    (ActualCoreSupport.refinedCarrier_closed l) (ActualCycleAssembly.refined_carrier_factorization
        hN l)
    (ActualPrimary.commonContext B) x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) (H.inputSupport l) j n hp
  intro hs
  have hc := (ActualCycleAssembly.refined_carrier_factorization hN l n z.1.1 hp z.2).mpr hs
  exact hn (ActualCycleParameters.activeLabel_index n l (core_active l n hp hc))


section Factory
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state

theorem waveData_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.WaveData G p v c u ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier σ κ := by
  let d := particular_inputs H hN P.amplitude P.field P.periodic P.support
  have first := ActualParticularMeanGain.postParticular_gain H d hσ
  have hb := signed_block_bounds first
  exact {
    carrier := ActualCycleParameters.invariant_fixedParameters_signed_carrier H
    particular := P.amplitude
    tangent := hb.1
    curl := hb.2.2.2.1
    particularPressure := P.pressure
    signedPressure := hb.2.2.1
    particularSmooth := P.coefficients
    signedSmooth := signed_coefficients_smooth first
    particularPressureSmooth := P.pressureCoefficients
    signedPressureSmooth := signed_pressure_coefficients_smooth first
    particularGaussianSmooth := P.gaussianCoefficients
    signedGaussianSmooth := signed_gaussian_coefficients_smooth first
    particularSolenoidal := P.solenoidal
    signedSolenoidal := signed_solenoidal first
    particularSupport := ActualCycleAssembly.cycle_refined_particular_inputSupport hN x c
        H.inputSupport
    signedSupport := signed_inputSupport
    particularGaussian := P.gaussian
    signedGaussian := signed_gaussian_bounds first
    particularField := P.field
    signedField := signed_field_smooth first
    particularPressureField := P.pressureField
    signedPressureField := signed_pressure_field_smooth first
    particularPeriodic := P.periodic
    signedPeriodic := signed_field_periodic
    particularRadialSupport := P.support
    signedRadialSupport := signed_field_support
    tangentField := signed_tangent_field_smooth first
    tangentPeriodic := signed_tangent_field_periodic
    tangentRadialSupport := signed_tangent_field_support
    particularLinear := P.linear
    signedLinear := signed_linear_bounds H first }

/-- Step data of particular, given by `stepDataOfWaves H hN hσ hl (waveData_of_particular H hN
hσ P)`. -/
noncomputable def stepDataOfParticular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.StepData G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) H hσ :=
  stepDataOfWaves H hN hσ hl (waveData_of_particular H hN hσ P)

theorem stepResult_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.StepResult G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (σ := σ) («κ» := κ) :=
  CorrectionAnalyticStep.step _ _ _ _ _ _ _ _ _ _ _ _
    (staticData B) H hσ kappa_small (stepDataOfParticular H hN hσ hl P)

theorem afterTemporal_debt_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    UnweightedClass ActualInitialization.slowStrip (1+σ-2*κ)
      (debt c (ActualIntermediateDebtBounds.postTemporal x)) :=
  ActualIntermediateDebtBounds.afterTemporal_debt_from_stepData
    (staticData B) H hσ (P.inputs H hN) (stepDataOfParticular H hN hσ hl P)

end Factory

/-- The actual run retains analytic bounds, full chart coherence, and
individual torus periods as distinct, proved invariants. -/
structure RunInvariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop where
  analytic : Invariant σ x
  coherent : ActualCycleCoherence.Coherent x
  periodic : ActualCyclePeriodicity.Periodic x

theorem initial_runInvariant (B N0 : ℕ) :
    RunInvariant (ActualIterationLedger.sigma 0) (state B N0 0) where
  analytic := by simpa only [ActualIterationLedger.sigma_zero] using initial_invariant B N0
  coherent := ActualCycleCoherence.initial B N0
  periodic := ActualCyclePeriodicity.initial B N0


theorem coherent_core_cover {B N0 : ℕ} {x : CycleState (Index B N0)}
    (C : ActualCycleCoherence.Coherent x) :
    ∀ l n z, z ∈ ActualInitialization.geometry.domain →
      z ∈ ActualCoreSupport.refinedCarrier l n → l ∈ x.coefficients.labels n := by
  intro l n z hz hc
  rw [C.labels]
  exact core_active l n hz hc

theorem wave_transport_of_particular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) (P : ActualParticularCycleData.Data x σ)
    (n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) :
    CycleStateCoherence.CycleWavesOn ActualCycleCoherence.geometry
      (ActualCycleParameters.fixedParameters B N0) x.coefficients
      (ActualPrimary.commonContext B) x.state (ActualInitialCoherence.overlap n m) n m k :=
  ActualCycleCoherence.waves R.analytic (waveData_of_particular R.analytic hN hσ P)
    R.coherent (coherent_core_cover R.coherent) ActualCoreSupport.refinedCarrier_closed
    (fun _ _ => Subset.rfl) n m k hi

theorem next_runInvariant_of_particular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) (P : ActualParticularCycleData.Data x σ) :
    RunInvariant (σ+1/10)
      (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext B)) where
  analytic := (stepResult_of_particular R.analytic hN hσ R.coherent.labels P).invariant
  coherent := ActualCycleCoherence.step R.analytic (waveData_of_particular R.analytic hN hσ P)
    R.coherent (coherent_core_cover R.coherent) ActualCoreSupport.refinedCarrier_closed
    (fun _ _ => Subset.rfl)
  periodic := ActualCyclePeriodicity.step R.analytic R.periodic


theorem particularData {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) : ActualParticularCycleData.Data x σ :=
  ActualParticularCycleData.actual_data R.analytic R.periodic hN hσ

theorem next_runInvariant {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) :
    RunInvariant (σ+1/10)
      (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext B)) :=
  next_runInvariant_of_particular R hN hσ (particularData R hN hσ)

/-- Every stage belongs to the same fixed construction, with no wave,
regularity, covariance, or periodicity output supplied as an assumption. -/
theorem state_runInvariant (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    RunInvariant (ActualIterationLedger.sigma j) (state B N0 j) := by
  induction j with
  | zero => exact initial_runInvariant B N0
  | succ j ih =>
      rw [ActualIterationLedger.sigma_succ, state_succ]
      exact next_runInvariant ih hN (ActualIterationLedger.sigma_admissible j)

theorem state_invariant (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    Invariant (ActualIterationLedger.sigma j) (state B N0 j) :=
  (state_runInvariant B N0 hN j).analytic

theorem state_coherent (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualCycleCoherence.Coherent (state B N0 j) :=
  (state_runInvariant B N0 hN j).coherent

theorem state_periodic (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualCyclePeriodicity.Periodic (state B N0 j) :=
  (state_runInvariant B N0 hN j).periodic

theorem state_particularData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularCycleData.Data (state B N0 j) (ActualIterationLedger.sigma j) :=
  particularData (state_runInvariant B N0 hN j) hN (ActualIterationLedger.sigma_admissible j)

theorem state_particularInputs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularMeanGain.Inputs (state B N0 j) (ActualIterationLedger.sigma j) :=
  (state_particularData B N0 hN j).inputs (state_invariant B N0 hN j) hN

theorem state_waveData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.WaveData ActualInitialization.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (ActualPrimary.commonContext B) (state B N0 j).state ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (ActualIterationLedger.sigma j) ChartScales.kappa :=
  waveData_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_particularData B N0 hN j)

/-- State step data, constructed using `stepDataOfParticular`. -/
noncomputable def stateStepData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.StepData ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
      (state B N0 j) ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) (state_invariant B N0 hN j)
      (ActualIterationLedger.sigma_admissible j) :=
  stepDataOfParticular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_result (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.StepResult ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
      (state B N0 j) ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (σ := ActualIterationLedger.sigma j) («κ» :=
          ChartScales.kappa) :=
  stepResult_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_afterTemporal_debt (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    UnweightedClass ActualInitialization.slowStrip
      (1+ActualIterationLedger.sigma j-2*ChartScales.kappa)
      (debt (ActualPrimary.commonContext B)
        (ActualIntermediateDebtBounds.postTemporal (state B N0 j))) :=
  afterTemporal_debt_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_wave_transport (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) :
    CycleStateCoherence.CycleWavesOn ActualCycleCoherence.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (ActualPrimary.commonContext B) (state B N0 j).state
      (ActualInitialCoherence.overlap n m) n m k :=
  wave_transport_of_particular (state_runInvariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_particularData B N0 hN j) n m k hi

theorem state_covariance_moving (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    (∀ i k, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement (state B N0 j).state.oscillation
        ((ActualCycleParameters.fixedParameters B N0).particularVelocity (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state) i k)) ∧
    (∀ i k, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement
        ((ActualCycleParameters.fixedParameters B N0).afterParticular (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state).oscillation
        ((ActualCycleParameters.fixedParameters B N0).signedVelocity (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state) i k)) :=
  (state_waveData B N0 hN j).covariance_moving (state_invariant B N0 hN j).oscillationSmooth
    (state_invariant B N0 hN j).oscillationPeriodic


end NavierStokes.ActualCyclePreservation
