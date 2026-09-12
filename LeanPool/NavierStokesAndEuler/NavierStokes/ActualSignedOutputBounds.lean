/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData

/-!
# Actual signed outputs from native support estimates

The background is the same chosen primary background.  Its local controls
are restricted to the signed phase cells before applying the native-copy
localization and periodization estimates.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedOutputBounds

open Set Function Filter WeightedClasses CorrectionStep ActualSignedStageControls
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

/-- Copies, given by `(parameters l).copyData ActualPrimaryBounds.strip request`. -/
noncomputable def copies (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) : PeriodizedWaveBounds.CopyData FullPoint Frequency :=
  (parameters l).copyData ActualPrimaryBounds.strip request

/-- Joint cell, given by `phaseCell i.1 n i.2`. -/
noncomputable def jointCell (n : ℕ) (i : SignedLabel B N0 × Frequency) : Set FullPoint :=
  phaseCell i.1 n i.2

/-- Primary index, given by `((i.1.2, i.1.1), i.2)`. -/
noncomputable def primaryIndex (i : SignedLabel B N0 × Frequency) :
    ActualPrimaryBounds.CopyIndex B N0 := ((i.1.2, i.1.1), i.2)

/-- Uniform primary estimates restrict to the actual signed phase cells.
The constants are chosen before both the label and the lattice copy. -/
theorem primary_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℕ → ActualPrimaryBounds.CopyIndex B N0 → FullPoint → ℝ} {α : ℝ}
    {f : ℕ → ActualPrimaryBounds.CopyIndex B N0 → FullPoint → E}
    (hf : LocalizedWaveBounds.LocalClass fullStrip ActualPrimaryBounds.controlCell w α f) :
    LocalizedWaveBounds.LocalClass fullStrip jointCell
      (fun n i => w n (primaryIndex i)) α (fun n i => f n (primaryIndex i)) := by
  refine ⟨fun n i x hx => hf.weight_nonneg n (primaryIndex i) x hx,
    fun n i x hx hi => hf.smooth n (primaryIndex i) x hx hi.1, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n i x hx hi j hj => hb n (primaryIndex i) x hx hi.1 j hj⟩

theorem envelope_nonneg (l : SignedLabel B N0) (n : ℕ) (x : FullPoint) :
    0 ≤ envelope l n x := ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n x

theorem background_normal_eq (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) :
    (jointRawBackground (copies (B := B) (N0 := N0) request)).normal fullStrip (directions B) =
      fun n i => ActualPrimaryBounds.actualFamily.normal fullStrip (directions B) n (primaryIndex
          i) := rfl

theorem background_defect_eq (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) :
    (jointRawBackground (copies (B := B) (N0 := N0) request)).defect fullStrip (directions B) =
      fun n i => ActualPrimaryBounds.actualFamily.defect fullStrip (directions B) n (primaryIndex
          i) := rfl

/-- This background certificate has zero amplitude and pressure.  Every
nonzero field in it is an actual primary background or phase expression. -/
theorem background_inputs (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) :
    LocalizedWaveBounds.InputBounds fullStrip jointCell
      (fun n i x => envelope i.1 n x) 0 ChartScales.kappa (directions B)
      (jointRawBackground (copies (B := B) (N0 := N0) request)) := by
  have h := ActualPrimaryBounds.actual_local_inputs (B := B) (N0 := N0)
  refine {
    loss_nonneg := h.loss_nonneg
    radial_profile := primary_local h.radial_profile
    radial_scale := h.radial_scale
    fast_scale := h.fast_scale
    frequency_scale := primary_local h.frequency_scale
    radius := primary_local h.radius
    inverse_radius := primary_local h.inverse_radius
    radial_base := primary_local h.radial_base
    frequency_base := primary_local h.frequency_base
    axial_base := primary_local h.axial_base
    radial_base_aux := fun n i x hx hi => h.radial_base_aux n (primaryIndex i) x hx hi.1
    frequency_base_aux := fun n i x hx hi => h.frequency_base_aux n (primaryIndex i) x hx hi.1
    axial_base_aux := fun n i x hx hi => h.axial_base_aux n (primaryIndex i) x hx hi.1
    normal := primary_local h.normal
    defect := primary_local h.defect
    amplitude := ?_
    pressure := ?_ }
  · intro j
    exact LocalizedWaveBounds.LocalClass.zero
      (fun n i x _ => mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg i.1 n x))
  · exact LocalizedWaveBounds.LocalClass.zero
      (fun n i x _ => mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg i.1 n x))

theorem normal_range (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    ActualPrimaryBounds.normalFloor B N0 ≤
        ‖(copies request l).background.normal fullStrip (directions B) n x‖ ∧
      ‖(copies request l).background.normal fullStrip (directions B) n x‖ ≤
        ActualPrimaryBounds.normalCeiling B N0 := by
  exact ActualPrimaryBounds.chart_normal_range (B := B) (N0 := N0)
    (i := ((l.2, l.1), k)) (n := n) (x := x) hx hc.1

theorem inverse_frequency (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) :
    LocalizedWaveBounds.LocalUnweighted fullStrip jointCell (1 / 2)
      (fun n i (_ : FullPoint) => 1 / (copies (B := B) (N0 := N0) request i.1).background.frequency
          n) :=
  primary_local (ActualPrimaryBounds.inverse_carrier_local (B := B) (N0 := N0))

/-- A genuine cutoff zero germ kills both localized input fields. -/
theorem localized_zero_of_cutoff (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hzero : cutoff l k n =ᶠ[𝓝 x] fun _ => 0) :
    (((copies request l).localized k).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((copies request l).localized k).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  constructor
  · filter_upwards [hzero] with y hy
    change cutoff l k n y • (copies request l).amplitude n k y = 0
    rw [hy, zero_smul]
  · filter_upwards [hzero] with y hy
    change (cutoff l k n y : ℂ) * (copies request l).pressure n k y = 0
    rw [hy, Complex.ofReal_zero, zero_mul]

theorem localized_zero_of_mask (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hzero : mask l k n =ᶠ[𝓝 x] fun _ => 0) :
    (((copies request l).localized k).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((copies request l).localized k).pressure n =ᶠ[𝓝 x] fun _ => 0) :=
  PeriodizedSignedParameters.localized_zero_of_mask
    (p := parameters l) (s := ActualPrimaryBounds.strip) request hzero

/-- Every point in a copy cell either has the actual phase estimates or
has a neighborhood on which both localized input fields vanish. -/
theorem phaseCell_or_localized_zero (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ fullStrip.domain) :
    x ∈ phaseCell l n k ∨
      (((copies request l).localized k).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((copies request l).localized k).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  rcases ActualWaveRegularityData.signed_phaseCell_or_zero l n k hx with hc | hcut | hmask
  · exact Or.inl hc
  · exact Or.inr (localized_zero_of_cutoff request l hcut)
  · exact Or.inr (localized_zero_of_mask request l hmask)

/-- These are the literal five outputs of one actual signed copy family. -/
structure OutputBounds (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (α : ℝ) : Prop where
  amplitude : LabelSumBounds.UniformWaveClass fullStrip (envelope (B := B) (N0 := N0)) α
    (fun l => (copies request l).common.amplitude)
  corrected : LabelSumBounds.UniformWaveClass fullStrip (envelope (B := B) (N0 := N0)) α
    (fun l => ((copies request l).commonCorrected fullStrip (directions B)).amplitude)
  pressure : LabelSumBounds.UniformWaveClass fullStrip (envelope (B := B) (N0 := N0)) (α + 1 / 2)
    (fun l => (copies request l).common.pressure)
  curl : LabelSumBounds.UniformWaveClass fullStrip (envelope (B := B) (N0 := N0))
    (α + 1 / 2 - ChartScales.kappa)
    (fun l => (copies request l).common.curlCorrection fullStrip (directions B))
  good : LabelSumBounds.UniformWaveClass fullStrip (envelope (B := B) (N0 := N0))
    (α + 1 / 2 - 3 * ChartScales.kappa)
    (fun l => (copies request l).globalGood fullStrip (directions B))

/-- Native input bounds are proved from the actual signed quotient and
projected pressure, followed by the actual single cutoff. -/
theorem native_inputs {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    LocalizedWaveBounds.InputBounds fullStrip jointCell
      (fun n i x => envelope i.1 n x) (β + 1 / 2) ChartScales.kappa (directions B)
      (LocalizedWaveBounds.jointNativeFamily (copies (B := B) (N0 := N0) request)) := by
  obtain ⟨ha, hp⟩ := raw_coefficients_jets hR
  have hp' : PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * envelope l n x)
      ((β + 1 / 2) + 1 / 2) (phaseCell (B := B) (N0 := N0))
      (fun l => (copies request l).pressure) := by
    simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring]
    exact hp
  have hin := uniform_localInput_of_coefficients (copies (B := B) (N0 := N0) request)
    (background_inputs request)
    (fun l n x _ => envelope_nonneg l n x) ha hp'
  exact hin.with_cutoff (LocalizedWaveBounds.LocalClass.of_uniformLocalJets
    (fun _ _ _ _ => zero_le_one) (cutoff_local_jets (B := B) (N0 := N0)))

/-- All common outputs follow from native input estimates and actual
support.  No common, corrected, or good output bound is a premise. -/
theorem common_bounds {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) : OutputBounds (B := B) (N0 := N0) request (β + 1 / 2) := by
  have hout := LocalizedWaveBounds.uniform_common_bounds_from_supported_native
    (copies (B := B) (N0 := N0) request) cells (fun l n k => cutoff_support l n k) phaseCell
    (fun l n x _ => envelope_nonneg l n x) (native_inputs hR)
    (show ChartScales.kappa ≤ 1 / 2 by norm_num [ChartScales.kappa])
    (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun l n k x hx hc => (normal_range request l n k hx hc).1)
    (fun l n k x hx hc => (normal_range request l n k hx hc).2)
    (inverse_frequency request)
    (fun l n k x hx _ => phaseCell_or_localized_zero request l n k hx)
  exact ⟨hout.1, hout.2.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2⟩

/-- The actual request is estimated from the current measured residuals.
Only primitive incoming state data and its ordinary mean classes are used. -/
theorem actual_common_bounds (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    OutputBounds (B := B) (N0 := N0)
      (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u) (α - 1 / 2) := by
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  simpa only [show α - 1 + 1 / 2 = α - 1 / 2 by ring] using common_bounds hr'

/-- Mean envelope, given by `envelope l n (x, 0)`. -/
noncomputable def meanEnvelope (l : SignedLabel B N0) (n : ℕ) (x : Point) : ℝ :=
  envelope l n (x, 0)

/-- The same bounds apply to the actual stored tangent, exact, pressure,
curl-difference, and good harmonic blocks. -/
theorem block_bounds {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (β + 1 / 2)
      (fun l n x => ((parameters l).tangentBlock ActualPrimaryBounds.strip request).velocity n i j
          x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (β + 1 / 2)
      (fun l n x => ((parameters l).exactBlock ActualPrimaryBounds.strip request).velocity n i j
          x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (β + 1)
      (fun l n x => ((parameters l).exactBlock ActualPrimaryBounds.strip request).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0))
      (β + 1 - ChartScales.kappa)
      (fun l n x => ((parameters l).curlBlock ActualPrimaryBounds.strip request).velocity n i j x))
          ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0))
      (β + 1 - 3 * ChartScales.kappa)
      (fun l n x => ((parameters l).goodBlock ActualPrimaryBounds.strip request).velocity n i j x))
          := by
  have h := common_bounds hR
  simpa only [show β + 1 / 2 + 1 / 2 = β + 1 by ring] using
    PeriodizedSignedParameters.uniform_block_bounds (parameters (B := B) (N0 := N0))
      ActualPrimaryBounds.strip request
      (P := meanEnvelope (B := B) (N0 := N0)) (α := β + 1 / 2) (κ := ChartScales.kappa)
      h.amplitude h.corrected h.pressure h.curl h.good

/-- The stored signed blocks are bounded directly from the measured
incoming residuals.  There is no signed-output estimate among the inputs. -/
theorem actual_block_bounds (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    let request := LocalSignedRequest.fullRequest G.strip G.patch G.coord c u
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (α - 1 / 2)
      (fun l n x => ((parameters l).tangentBlock ActualPrimaryBounds.strip request).velocity n i j
          x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (α - 1 / 2)
      (fun l n x => ((parameters l).exactBlock ActualPrimaryBounds.strip request).velocity n i j
          x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) α
      (fun l n x => ((parameters l).exactBlock ActualPrimaryBounds.strip request).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (α - ChartScales.kappa)
      (fun l n x => ((parameters l).curlBlock ActualPrimaryBounds.strip request).velocity n i j x))
          ∧
    (∀ i j, LabelSumBounds.UniformWaveClass ActualPrimaryBounds.strip
      (meanEnvelope (B := B) (N0 := N0)) (α - 3 * ChartScales.kappa)
      (fun l n x => ((parameters l).goodBlock ActualPrimaryBounds.strip request).velocity n i j x))
          := by
  dsimp only
  have h := actual_common_bounds (B := B) (N0 := N0) G hs c u α H hfixed hθ hz
  simpa only [sub_add_cancel] using
    PeriodizedSignedParameters.uniform_block_bounds (parameters (B := B) (N0 := N0))
      ActualPrimaryBounds.strip (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)
      (P := meanEnvelope (B := B) (N0 := N0)) (α := α - 1 / 2) (κ := ChartScales.kappa)
      h.amplitude h.corrected h.pressure h.curl h.good

/-- The cut native vector-potential coefficient before restoring the
carrier or applying the physical coordinate prefactor. -/
noncomputable def localPotential (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    HarmonicCalculus.ComplexVector :=
  CurlClassBounds.inverseCarrier ((copies request l).background.frequency n) •
    CurlClassBounds.normalCoefficient
      ((copies request l).background.normal fullStrip (directions B) n x)
      (((copies request l).localized k).amplitude n x)

/-- The inverse carrier supplies the extra half-power in the actual
localized vector potential.  Physical scaling factors stay outside it. -/
theorem localPotential_jets {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1)
      (phaseCell (B := B) (N0 := N0)) (localPotential request) := by
  have hc := (native_inputs hR).normalCoefficient_class
    (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun n i x hx hi => (normal_range request i.1 n i.2 hx hi).1)
    (fun n i x hx hi => (normal_range request i.1 n i.2 hx hi).2)
  have hi := (LocalizedWaveBounds.unweighted_smul (inverse_frequency request) hc).map
    (Complex.I • ContinuousLinearMap.id ℝ HarmonicCalculus.ComplexVector)
  rw [show (1 / 2 : ℝ) + (β + 1 / 2) = β + 1 by ring] at hi
  have hp : LocalizedWaveBounds.LocalWave fullStrip (jointCell (B := B) (N0 := N0))
      (fun n i x => envelope i.1 n x) (β + 1)
      (fun n i => localPotential request i.1 n i.2) := by
    apply hi.congr
    intro n i x
    ext j
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
      Pi.smul_apply, Complex.real_smul, smul_eq_mul, localPotential,
      CurlClassBounds.inverseCarrier]
    push_cast
    ring_nf
    rfl
  exact hp.to_uniformLocalJets

theorem localized_pressure_jets {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) (β + 1)
      (phaseCell (B := B) (N0 := N0))
      (fun l n k => ((copies request l).localized k).pressure n) := by
  have hp := (native_inputs hR).pressure
  rw [show β + 1 / 2 + 1 / 2 = β + 1 by ring] at hp
  exact hp.to_uniformLocalJets

/-- Native potential and pressure bounds directly from the actual
incoming residual classes, before their distinct physical prefactors. -/
theorem actual_native_potential_pressure_jets (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    let request := LocalSignedRequest.fullRequest G.strip G.patch G.coord c u
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) α
      (phaseCell (B := B) (N0 := N0)) (localPotential request) ∧
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * envelope l n x) α
      (phaseCell (B := B) (N0 := N0))
      (fun l n k => ((copies request l).localized k).pressure n) := by
  dsimp only
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  exact ⟨by simpa only [sub_add_cancel] using localPotential_jets hr',
    by simpa only [sub_add_cancel] using localized_pressure_jets hr'⟩

end NavierStokes.ActualSignedOutputBounds
