/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSupportPreservation
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanBoundsReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledActualParticularControl
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds

/-!
# Actual particular-wave data on the active label-band pairs

The reference phase and native slot are those of the existing initializer
choice.  The forced fields use the literal current harmonic residual.  Active
pair estimates do not impose polynomial clock bounds on inactive bands.
The actual source support and transported cutoff then globalize the native
estimates. The final theorems give uniform bounds for the literal common
and finite-harmonic fields from the current analytic invariant.
-/

section

/-!
# Actual particular background on the full retained carrier

The retained source mask gives the padded native scale interval `(1/4,4)`.
The cells below use its phase carrier and closed clock core without adding
the narrower dyadic mask of the original primary coefficient support.
-/

section

/-!
# Local background bounds for the actual particular harmonics

The fixed harmonic changes the frequency.  Its phase is the same primary
phase, including the free angular variable.  All primitive bounds are pulled
from the actual primary inputs on the same closed support cells.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularBackground

open Set Function Filter WeightedClasses LinearWaveBounds LocalizedWaveBounds
open CorrectionState CorrectionStep CorrectionInitialization
open scoped Topology ContDiff

section Isometry

variable {D E V I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The same jet constants work after the native coordinate isometry. -/
theorem localClass_reindex (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {K : ℕ → I → Set E} {w : ℕ → I → E → ℝ} {α : ℝ}
    {f : ℕ → I → E → V} (hf : LocalClass s K w α f) :
    LocalClass (ParticularWaveBounds.reindexStrip e s) (fun n i => e ⁻¹' K n i)
      (fun n i x => w n i (e x)) α (fun n i x => f n i (e x)) := by
  refine ⟨fun n i x hx => hf.weight_nonneg n i (e x) hx,
    fun n i x hx hi => (hf.smooth n i (e x) hx hi).comp x e.contDiff.contDiffAt, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n i x hx hi j hj
  rw [StateReindex.norm_iteratedFDeriv_pull]
  exact hb n i (e x) hx hi j hj

/-- Reindex family, given by `WaveFamily.ofCoefficients (fun i =>
ParticularWaveBounds.reindexCoefficients e (a.coefficients i))`. -/
noncomputable def reindexFamily (e : D ≃ₗᵢ[ℝ] E) (a : WaveFamily E I) : WaveFamily D I :=
  WaveFamily.ofCoefficients (fun i => ParticularWaveBounds.reindexCoefficients e (a.coefficients i))

theorem normal_reindex (e : D ≃ₗᵢ[ℝ] E) (a : WaveCoefficients E)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : D) :
    (ParticularWaveBounds.reindexCoefficients e a).normal
      (ParticularWaveBounds.reindexStrip e s) (ParticularWaveBounds.reindexDirections e d) n x =
      a.normal s d n (e x) := by
  simp only [WaveCoefficients.normal, HarmonicCalculus.phaseNormal, HarmonicCalculus.along,
    ParticularWaveBounds.reindexCoefficients, ParticularWaveBounds.reindexDirections,
    ParticularWaveBounds.reindexStrip, GraphDirections.radialField, GraphDirections.axialField,
    StateReindex.fderiv_pull, map_add, map_smul, e.apply_symm_apply]

theorem defect_reindex (e : D ≃ₗᵢ[ℝ] E) (a : WaveCoefficients E)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : D) :
    (ParticularWaveBounds.reindexCoefficients e a).defect
      (ParticularWaveBounds.reindexStrip e s) (ParticularWaveBounds.reindexDirections e d) n x =
      a.defect s d n (e x) := by
  simp only [WaveCoefficients.defect, LinearWaveResidual.materialPhaseDefect,
    LinearWaveResidual.timeDirection, HarmonicCalculus.along,
    ParticularWaveBounds.reindexCoefficients, ParticularWaveBounds.reindexDirections,
    ParticularWaveBounds.reindexStrip, GraphDirections.radialField, GraphDirections.axialField,
    GraphDirections.fastField, StateReindex.fderiv_pull, map_add, map_sub, map_smul,
    e.apply_symm_apply]

theorem auxiliary_reindex (e : D ≃ₗᵢ[ℝ] E) {f : E → ℝ} (d : E) {x : D}
    (h : (fun y => fderiv ℝ f y d) =ᶠ[𝓝 (e x)] fun _ => 0) :
    (fun y => fderiv ℝ (fun z => f (e z)) y (e.symm d)) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.comp_tendsto e.continuous.continuousAt] with y hy
  simpa only [StateReindex.fderiv_pull, e.apply_symm_apply, Function.comp_def] using hy

theorem inputBounds_reindex (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {K : ℕ → I → Set E} {P : ℕ → I → E → ℝ} {α κ : ℝ}
    {d : GraphDirections E} {a : WaveFamily E I} (h : InputBounds s K P α κ d a) :
    InputBounds (ParticularWaveBounds.reindexStrip e s) (fun n i => e ⁻¹' K n i)
      (fun n i x => P n i (e x)) α κ (ParticularWaveBounds.reindexDirections e d)
      (reindexFamily e a) := by
  refine {
    loss_nonneg := h.loss_nonneg
    radial_profile := localClass_reindex e h.radial_profile
    radial_scale := h.radial_scale
    fast_scale := h.fast_scale
    frequency_scale := localClass_reindex e h.frequency_scale
    radius := localClass_reindex e h.radius
    inverse_radius := localClass_reindex e h.inverse_radius
    radial_base := localClass_reindex e h.radial_base
    frequency_base := localClass_reindex e h.frequency_base
    axial_base := localClass_reindex e h.axial_base
    radial_base_aux := fun n i x hx hi => auxiliary_reindex e d.auxiliary (h.radial_base_aux n i (e
        x) hx hi)
    frequency_base_aux := fun n i x hx hi => auxiliary_reindex e d.auxiliary (h.frequency_base_aux
        n i (e x) hx hi)
    axial_base_aux := fun n i x hx hi => auxiliary_reindex e d.auxiliary (h.axial_base_aux n i (e
        x) hx hi)
    normal := ?_
    defect := ?_
    amplitude := fun j => localClass_reindex e (h.amplitude j)
    pressure := localClass_reindex e h.pressure }
  · exact (localClass_reindex e h.normal).congr (fun n i x =>
      (normal_reindex e (a.coefficients i) s d n x).symm)
  · exact (localClass_reindex e h.defect).congr (fun n i x =>
      (defect_reindex e (a.coefficients i) s d n x).symm)

/-- This operation changes only the harmonic frequency and sets the two
unknown coefficients to zero. In particular its actual normal and defect
are unchanged. -/
noncomputable def zeroRescale (q : ℝ) (a : WaveFamily D I) : WaveFamily D I :=
  { a with
    amplitude := fun _ _ _ => 0
    pressure := fun _ _ _ => 0
    frequency := fun n i => q * a.frequency n i }

theorem zeroRescale_normal (q : ℝ) (a : WaveFamily D I)
    (s : StripData D) (d : GraphDirections D) :
    (zeroRescale q a).normal s d = a.normal s d := rfl

theorem zeroRescale_defect (q : ℝ) (a : WaveFamily D I)
    (s : StripData D) (d : GraphDirections D) :
    (zeroRescale q a).defect s d = a.defect s d := rfl

theorem inputBounds_zeroRescale {s : StripData D} {K : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α κ : ℝ} {d : GraphDirections D} {a : WaveFamily D I}
    (h : InputBounds s K P α κ d a) (q : ℝ) (W : ℕ → I → D → ℝ)
    (hW : ∀ n i x, x ∈ s.domain → 0 ≤ W n i x) (β : ℝ) :
    InputBounds s K W β κ d (zeroRescale q a) where
  loss_nonneg := h.loss_nonneg
  radial_profile := h.radial_profile
  radial_scale := h.radial_scale
  fast_scale := h.fast_scale
  frequency_scale := LocalizedWaveBounds.constant_real_mul h.frequency_scale q
  radius := h.radius
  inverse_radius := h.inverse_radius
  radial_base := h.radial_base
  frequency_base := h.frequency_base
  axial_base := h.axial_base
  radial_base_aux := h.radial_base_aux
  frequency_base_aux := h.frequency_base_aux
  axial_base_aux := h.axial_base_aux
  normal := h.normal
  defect := h.defect
  amplitude := fun _ => LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i x
      hx))
  pressure := LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i x hx))

end Isometry

theorem coefficients_ext {D : Type} {a b : WaveCoefficients D}
    (hR : a.radius = b.radius) (hr : a.radialBase = b.radialBase)
    (hF : a.frequencyBase = b.frequencyBase) (hG : a.axialBase = b.axialBase)
    (hΦ : a.phase = b.phase) (hA : a.amplitude = b.amplitude)
    (hp : a.pressure = b.pressure) (hk : a.frequency = b.frequency) : a = b := by
  cases a
  cases b
  congr

/-! ## The same primary choice in native/free-angle coordinates -/

/-- Label: an abbreviation for `ActualPrimaryBounds.SignedLabel B N0`. -/
abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
/-- Copy index: an abbreviation for `ActualPrimaryBounds.CopyIndex B N0`. -/
abbrev CopyIndex (B N0 : ℕ) := ActualPrimaryBounds.CopyIndex B N0
/-- Parameter: an abbreviation for `CorrectionStep.CycleSlow`. -/
abbrev Parameter := CorrectionStep.CycleSlow
/-- Native: an abbreviation for `(Parameter × ℝ) × TorusInverse.Plane`. -/
abbrev Native := (Parameter × ℝ) × TorusInverse.Plane

/-- Native to full, given by `ParticularWaveAssembly.angleShuffle.symm.trans
(StateReindex.cylinder cycleAssoc.symm)`. -/
noncomputable def nativeToFull : Native ≃ₗᵢ[ℝ] ActualPrimary.FullPoint :=
  ParticularWaveAssembly.angleShuffle.symm.trans (StateReindex.cylinder cycleAssoc.symm)

/-- Native strip, given by `ParticularWaveBounds.reindexStrip nativeToFull
ActualPrimaryBounds.fullStrip`. -/
noncomputable def nativeStrip : StripData Native :=
  ParticularWaveBounds.reindexStrip nativeToFull ActualPrimaryBounds.fullStrip

/-- Cells, given by `nativeToFull ⁻¹' ActualPrimaryBounds.controlCell n i`. -/
noncomputable def cells {B N0 : ℕ} (n : ℕ) (i : CopyIndex B N0) : Set Native :=
  nativeToFull ⁻¹' ActualPrimaryBounds.controlCell n i

/-- Directions, given by `ParticularWaveBounds.reindexDirections nativeToFull
(ActualPrimaryBounds.directions B)`. -/
noncomputable def directions (B : ℕ) : GraphDirections Native :=
  ParticularWaveBounds.reindexDirections nativeToFull (ActualPrimaryBounds.directions B)

/-- Primary block as an element of `HarmonicBlock CyclePoint`. -/
noncomputable def primaryBlock {B N0 : ℕ} (l : Label B N0) : HarmonicBlock CyclePoint :=
  (ActualPrimary.piece ActualPrimary.standardRegion l.1 l.2).tangentBlock
    (fun n z => (ActualPrimary.chartCoefficients l.1 l.2).phase n (z, 0))
    (fun _ => PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 l.2)

/-- Carrier, constructed using `ParticularWaveAssembly.actualCarrier`. -/
noncomputable def carrier {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (j : ℤ) (l : Label B N0) : WaveCoefficients Native :=
  ParticularWaveAssembly.actualCarrier
    (ParticularWaveBounds.reindexCoefficients nativeToFull (ActualPrimary.chartCoefficients l.1
        l.2))
    (StateReindex.block cycleAssoc.symm (b l)) j

/-- Background family, given by `WaveFamily.ofCoefficients (fun i =>
ParticularWaveBounds.zeroAmplitudes (carrier b j i.1))`. -/
noncomputable def backgroundFamily {B N0 : ℕ}
    (b : Label B N0 → HarmonicBlock CyclePoint) (j : ℤ) : WaveFamily Native (CopyIndex B N0) :=
  WaveFamily.ofCoefficients (fun i => ParticularWaveBounds.zeroAmplitudes (carrier b j i.1))

theorem primary_phase_affine {B N0 : ℕ} (l : Label B N0) (n : ℕ)
    (x : CyclePoint) (θ : ℝ) :
    (ActualPrimary.chartCoefficients l.1 l.2).phase n (x, θ) =
      (primaryBlock l).phase n x +
        ((primaryBlock l).angularFrequency n : ℝ) / (primaryBlock l).frequency n * θ := by
  change (ActualPrimary.absolutePhase l.1 l.2 (ActualPrimary.toAbsolute n x, θ)) /
      (ChartScales.carrier ActualPrimary.h n : ℝ) =
    (ActualPrimary.absolutePhase l.1 l.2 (ActualPrimary.toAbsolute n x, 0)) /
      (ChartScales.carrier ActualPrimary.h n : ℝ) +
    (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 l.2 : ℝ) /
      (ChartScales.carrier ActualPrimary.h n : ℝ) * θ
  simp only [ActualPrimary.absolutePhase, mul_zero, zero_add]
  ring

theorem carrier_phase {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) (l : Label B N0) :
    (carrier b j l).phase =
      fun n z => (ActualPrimary.chartCoefficients l.1 l.2).phase n (nativeToFull z) := by
  funext n z
  change (b l).phase n (cycleAssoc.symm (z.1.1, z.2)) +
      ((b l).angularFrequency n : ℝ) / (b l).frequency n * z.1.2 = _
  rw [← (hb l).phase, ← (hb l).angular, ← (hb l).frequency]
  exact (primary_phase_affine l n (cycleAssoc.symm (z.1.1, z.2)) z.1.2).symm

theorem carrier_frequency {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) (l : Label B N0) :
    (carrier b j l).frequency = fun n => (j : ℝ) * (ChartScales.carrier ActualPrimary.h n : ℝ) := by
  funext n
  change (j : ℝ) * (b l).frequency n = _
  rw [← (hb l).frequency]
  rfl

theorem backgroundFamily_eq {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) :
    backgroundFamily b j = reindexFamily nativeToFull
      (zeroRescale (j : ℝ) (ActualPrimaryBounds.actualFamily (B := B) (N0 := N0))) := by
  unfold backgroundFamily reindexFamily
  apply congrArg WaveFamily.ofCoefficients
  funext i
  apply coefficients_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact carrier_phase b hb j i.1
  · rfl
  · rfl
  · exact carrier_frequency b hb j i.1

/-- All order-zero background classes, at every derivative order, are
derived from the primary inputs. The envelope can be any nonnegative one
because the velocity and pressure slots are zero. Constants remain uniform
in the spatial label and lattice copy. -/
theorem actual_background_inputs {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ)
    (W : ℕ → CopyIndex B N0 → Native → ℝ)
    (hW : ∀ n i x, x ∈ nativeStrip.domain → 0 ≤ W n i x) :
    InputBounds nativeStrip cells W 0 ChartScales.kappa (directions B) (backgroundFamily b j) := by
  rw [backgroundFamily_eq b hb j]
  let Wfull : ℕ → CopyIndex B N0 → ActualPrimary.FullPoint → ℝ :=
    fun n i x => W n i (nativeToFull.symm x)
  have hWfull : ∀ n i x, x ∈ ActualPrimaryBounds.fullStrip.domain → 0 ≤ Wfull n i x := by
    intro n i x hx
    apply hW
    change nativeToFull (nativeToFull.symm x) ∈ ActualPrimaryBounds.fullStrip.domain
    simpa only [nativeToFull.apply_symm_apply] using hx
  have hh := inputBounds_reindex nativeToFull
    (inputBounds_zeroRescale (ActualPrimaryBounds.actual_local_inputs (B := B) (N0 := N0))
      (j : ℝ) Wfull hWfull 0)
  simp only [Wfull, nativeToFull.symm_apply_apply] at hh
  exact hh

theorem background_normal {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) (n : ℕ)
    (i : CopyIndex B N0) (x : Native) :
    (backgroundFamily b j).normal nativeStrip (directions B) n i x =
      ActualPrimaryBounds.chartNormal i.1 n (nativeToFull x) := by
  rw [backgroundFamily_eq b hb j]
  change (ParticularWaveBounds.reindexCoefficients nativeToFull
    ((zeroRescale (j : ℝ) ActualPrimaryBounds.actualFamily).coefficients i)).normal
    _ _ n x = _
  unfold nativeStrip directions
  rw [normal_reindex]
  change (zeroRescale (j : ℝ) ActualPrimaryBounds.actualFamily).normal
    _ _ n i (nativeToFull x) = _
  rw [zeroRescale_normal, ActualPrimaryBounds.actualFamily_normal_eq]

theorem background_normal_range {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ)
    {n : ℕ} {i : CopyIndex B N0} {x : Native}
    (hx : x ∈ nativeStrip.domain) (hi : x ∈ cells n i) :
    ActualPrimaryBounds.normalFloor B N0 ≤ ‖(backgroundFamily b j).normal nativeStrip (directions
        B) n i x‖ ∧
      ‖(backgroundFamily b j).normal nativeStrip (directions B) n i x‖ ≤
        ActualPrimaryBounds.normalCeiling B N0 := by
  rw [background_normal b hb j]
  exact ActualPrimaryBounds.chart_normal_range hx hi

theorem background_defect {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) (n : ℕ)
    (i : CopyIndex B N0) (x : Native) :
    (backgroundFamily b j).defect nativeStrip (directions B) n i x =
      ActualPhaseDefect.defect i.1.1 i.1.2 n (nativeToFull x) := by
  rw [backgroundFamily_eq b hb j]
  change (ParticularWaveBounds.reindexCoefficients nativeToFull
    ((zeroRescale (j : ℝ) ActualPrimaryBounds.actualFamily).coefficients i)).defect
    _ _ n x = _
  unfold nativeStrip directions
  rw [defect_reindex]
  change (zeroRescale (j : ℝ) ActualPrimaryBounds.actualFamily).defect
    _ _ n i (nativeToFull x) = _
  rw [zeroRescale_defect, ActualPrimaryBounds.actualFamily_defect_eq]

theorem background_inverse_frequency {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) (j : ℤ) :
    LocalUnweighted nativeStrip cells (1 / 2 : ℝ)
      (fun n i (_ : Native) => 1 / (backgroundFamily b j).frequency n i) := by
  have hh := localClass_reindex nativeToFull
    (LocalizedWaveBounds.constant_real_mul
      (ActualPrimaryBounds.inverse_carrier_local (B := B) (N0 := N0)) ((j : ℝ)⁻¹))
  apply hh.congr
  intro n i x
  change (j : ℝ)⁻¹ * (1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) =
    1 / (carrier b j i.1).frequency n
  rw [carrier_frequency b hb j]
  simp only [one_div, mul_inv_rev]
  ring

theorem background_frequency_ne {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (primaryBlock l)) {j : ℤ} (hj : j ≠ 0)
    (n : ℕ) (i : CopyIndex B N0) : (backgroundFamily b j).frequency n i ≠ 0 := by
  change (carrier b j i.1).frequency n ≠ 0
  rw [carrier_frequency b hb j]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hj)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos ActualPrimary.h n)).ne'

end NavierStokes.ActualParticularBackground

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ParticularPaddedBackground

open Set Function Filter WeightedClasses PhaseJetBounds
open LinearWaveBounds LocalizedWaveBounds CorrectionState CorrectionStep
open CorrectionInitialization ActualPrimaryBounds
open scoped Topology ContDiff

variable {B N0 : ℕ}

/-- Padded cell as an element of `Set ActualPrimary.FullPoint`. -/
noncomputable def paddedCell (n : ℕ) (i : CopyIndex B N0) : Set ActualPrimary.FullPoint :=
  {x | near i.1 n ∧
    (fullCopy i.1 n i.2 x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier i.1.2 ∧
    (fullCopy i.1 n i.2 x).2 ∈ (ActualPrimary.clockWindow i.1.2).core}

/-- Cells, given by `ActualParticularBackground.nativeToFull ⁻¹' paddedCell n i`. -/
noncomputable def cells (n : ℕ) (i : CopyIndex B N0) : Set ActualParticularBackground.Native :=
  ActualParticularBackground.nativeToFull ⁻¹' paddedCell n i

theorem primary_control_subset_padded (n : ℕ) (i : CopyIndex B N0) :
    controlCell n i ⊆ paddedCell n i :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩

theorem padded_q (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hc : x ∈ paddedCell n i) :
    SimilarityHomogeneity.chartQ ActualPrimary.h (fullCopy i.1 n i.2 x).1 ∈
      Ioo (1 / 4 : ℝ) 4 :=
  (ActualCarrierGeometry.cell_geometry hN i.1.2 hc.2.1).2.2.2.2.1

theorem padded_maps (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion).carrier i.1 := by
  have hr := copyPoint_radial i.1 n i.2 (x := ActualSignedGeometry.meanEquiv.symm x.1) hx
  apply ActualPhaseDefect.native_reduced_domain_mem ActualPhaseDefect.paddedRegion i.1.1 i.1.2
      hc.2.1
  · apply (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPhaseDefect.paddedRegion
      (BaseContextAssembly.insertSlow (fullCopy i.1 n i.2 x).1)).mpr
    exact ⟨⟨hr.1, padded_q hN hc⟩, hr.2⟩
  · simp only [ActualPrimary.length_sign i.1.1 i.1.2]
    exact hc.2.2.2

theorem polynomial_on_padded (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SignedLabel B N0 → PhaseCalculus.Slow × ℝ → E}
    (hf : PolynomialJets (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion) f) :
    LocalUnweighted fullStrip paddedCell 0
      (fun n i x => f i.1 ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
  let D := ActualPhaseDefect.reducedJetDomain (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion
  refine ⟨fun _ _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n i x hx hc
    have hm := padded_maps hN hx hc
    rw [slotCopy_affine] at hm
    have hh := ((hf.smooth i.1).contDiffAt ((D.isOpen i.1).mem_nhds hm)).comp x
      (((slotLinear i.1 n).contDiff.add
        (contDiff_const (c := slotOfNative (copyPoint i.1 n i.2 0)))).contDiffAt)
    simpa only [← slotCopy_affine, Function.comp_def] using hh
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    have hcost := copyCost_one
    refine ⟨C * 25 ^ p * copyCost ^ m, by positivity, p + m, ?_⟩
    intro n i x hx hc j hj
    have hG := fullStrip.one_le_growth n x
    have hS := fullStrip.one_le_slow n
    have hm := padded_maps hN hx hc
    have hscale : D.scale i.1 ≤ 25 * fullStrip.growth n x := by
      exact (ActualSignedGeometry.S_window_le hc.1.1 (near_distance hc.1).2).trans
        (mul_le_mul_of_nonneg_left
          ((le_max_right 1 (ChartScales.S n)).trans (fullStrip.slow_le_growth n x)) (by norm_num))
    have hlin : ‖slotLinear i.1 n‖ ^ j ≤ copyCost ^ m * fullStrip.growth n x ^ m := by
      calc
        _ ≤ (copyCost * fullStrip.slow n) ^ m :=
          (pow_le_pow_left₀ (norm_nonneg _) (slotLinear_bound hc.1) j).trans
            (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hcost hS) hj)
        _ ≤ (copyCost * fullStrip.growth n x) ^ m := by gcongr; exact fullStrip.slow_le_growth n x
        _ = _ := mul_pow _ _ _
    have hu := PhaseJetBounds.norm_jet_comp_affine (D.isOpen i.1) (hf.smooth i.1)
      (slotLinear i.1 n) (slotOfNative (copyPoint i.1 n i.2 0))
      (by simpa only [← slotCopy_affine] using hm) j
    simp only [← slotCopy_affine] at hu
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (f i.1) ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)‖ *
          ‖slotLinear i.1 n‖ ^ j := hu
      _ ≤ (C * (25 * fullStrip.growth n x) ^ p) * (copyCost ^ m * fullStrip.growth n x ^ m) := by
        have hfb := (hb i.1 j hj _ hm).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (D.one_le_scale i.1)) hscale p) (zero_le_one.trans
              hC))
        exact mul_le_mul hfb hlin (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hfb)
      _ = majorant fullStrip (fun _ _ => 1) 0 (C * 25 ^ p * copyCost ^ m) (p + m) n x := by
        rw [majorant, mul_pow, pow_add, Real.rpow_zero]
        ring

/-! ## The actual normal and material defect on the larger cells -/

theorem padded_normal_germ {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    chartNormal i.1 n =ᶠ[𝓝 x] fun y => normalScale i.1 n •
      (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 y).1, (fullCopy i.1 n i.2 y).2.2) := by
  let P := ActualPrimary.phases B N0 i.1.1
  let l := spatialLabel i.1
  let gap := ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand i.1.2) -
      CommonWindow.index ActualPrimary.h n
  have hp : ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand i.1.2))
      ((PhysicalResidualTZ.swapCylinder x).1.1, (PhysicalResidualTZ.swapCylinder x).1.2.1) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier i.1.2 := hc.2.1
  have hcore : (ActualSignedGeometry.slotGeometry ActualPrimary.slots
      ActualSignedGeometry.vectors_det l 0).coordinates i.2
      (CommonCoverSolve.coverPower gap (PhysicalResidualTZ.swapCylinder x).1.2.2) ∈
      (ActualSignedGeometry.clockWindow ActualPrimary.slots l.1).core := by
    erw [ActualSignedGeometry.slot_coordinates_from_zero]
    have hl : l.1 = BaseChartJets.cellBand i.1.2 := rfl
    have hg : gap = ChartScales.nativeIndex ActualPrimary.h (spatialLabel i.1).1 -
        CommonWindow.index ActualPrimary.h n := rfl
    have hY : (PhysicalResidualTZ.swapCylinder x).1.2.2 = (ActualSignedGeometry.meanEquiv.symm
        x.1).2 := rfl
    rw [hg, hY, ← fullCopy_slot]
    rw [hl, ← clock_eq i.1]
    exact hc.2.2
  have hxR : 0 < x.1.1 := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hx
  have hphys := ActualSignedGeometry.phase_normal_view_germ ActualPrimary.slots
    ActualPrimary.outgoing.data.h_pos.le (label_large i.1) (CommonWindow.index ActualPrimary.h n)
        gap
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand i.1.2))
    (ChartScales.carrier ActualPrimary.h n) (ChartScales.carrier ActualPrimary.h
        (BaseChartJets.cellBand i.1.2))
    (P.phase.p i.1.2) (P.phase.pz i.1.2) (P.phase.x0 i.1.2) (P.phase.F i.1.2) (P.phase.G i.1.2)
    ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).isOpen i.1.2)
    (P.baseF.smooth i.1.2) (P.baseG.smooth i.1.2) i.2 (P.phase.theta i.1.2)
    (x := PhysicalResidualTZ.swapCylinder x)
    hxR hp hcore
  have hfull := hphys.comp_tendsto PhysicalResidualTZ.swapCylinder.continuous.continuousAt
  filter_upwards [hfull] with y hy
  rw [chartNormal, fullStrip, context_normal_swap (ActualPrimary.commonContext B) strip
    (ActualPrimary.chartCoefficients i.1.1 i.1.2) n
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
        ActualPrimary.h n))
    (CommonBaseContext.context_matches_physical ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B _ n)
    rfl rfl
    (ActualSignedGeometry.preparedViewPhase ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.slots
      (ActualPrimary.choice B N0).prepared i.1.1 i.1.2 n (CommonWindow.index ActualPrimary.h n))
    (funext (ActualPrimary.chartCoefficients_phase_view i.1.1 i.1.2 n (CommonWindow.index_le
        hc.1.2)))]
  apply hy.trans
  change normalScale i.1 n • _ = normalScale i.1 n • _
  apply congrArg (fun z => normalScale i.1 n • z)
  change PhaseCalculus.phaseNormal _ _ _ _ _ _ _ = PhaseCalculus.phaseNormal _ _ _ _ _ _ _
  erw [ActualSignedGeometry.slot_coordinates_from_zero]
  rfl

theorem padded_normalScale_local : LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
    (fun n i (_ : ActualPrimary.FullPoint) => normalScale i.1 n) := by
  apply local_constant normalUpper_pos.le
  intro n i x _ hx
  have h := normalScale_bounds hx.1
  rw [abs_of_pos (normalLower_pos.trans_le h.1)]
  exact h.2

theorem padded_normal_local (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i => chartNormal i.1 n) := by
  have hn := LocalizedWaveBounds.unweighted_smul
    (padded_normalScale_local (B := B) (N0 := N0))
    (polynomial_on_padded hN native_normal_polynomial)
  have hn' : LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i x => normalScale i.1 n • (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
    simpa only [zero_add] using hn
  exact hn'.congr_germ (fun _ _ _ hx hc => (padded_normal_germ hx hc).symm)

theorem padded_normal_range {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ paddedCell n i) :
    normalFloor B N0 ≤ ‖chartNormal i.1 n x‖ ∧
      ‖chartNormal i.1 n x‖ ≤ normalCeiling B N0 := by
  let P := ActualPrimary.phases B N0 i.1.1
  have ht : (fullCopy i.1 n i.2 x).2.2 ∈ P.V i.1.2 :=
    P.interval i.1.2 (by erw [ActualPrimary.length_sign i.1.1 i.1.2]; exact hc.2.2.2)
  have hdom : ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).slot P.V P.openV).carrier i.1.2 :=
    ⟨hc.2.1, ht⟩
  have hlow := P.normal_range.1 i.1.2 _ hdom
  have hupp := P.normal_range.2 i.1.2 _ hdom
  have hscale := normalScale_bounds hc.1
  rw [(padded_normal_germ hx hc).eq_of_nhds, norm_smul, Real.norm_eq_abs,
    abs_of_pos (normalLower_pos.trans_le hscale.1)]
  have hj : i.1.1 = 0 ∨ i.1.1 = 1 := by omega
  have hb : min (ActualPrimary.phases B N0 0).b (ActualPrimary.phases B N0 1).b ≤ P.b := by
    rcases hj with h | h <;> simp only [P, h]
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hM : P.M ^ 2 + 3 * P.M ≤
      max ((ActualPrimary.phases B N0 0).M ^ 2 + 3 * (ActualPrimary.phases B N0 0).M)
        ((ActualPrimary.phases B N0 1).M ^ 2 + 3 * (ActualPrimary.phases B N0 1).M) := by
    rcases hj with h | h <;> simp only [P, h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact ⟨mul_le_mul hscale.1 (hb.trans hlow)
      (le_min (ActualPrimary.phases B N0 0).b_pos.le (ActualPrimary.phases B N0 1).b_pos.le)
      (normalLower_pos.trans_le hscale.1).le,
    mul_le_mul hscale.2 (hupp.trans hM) (norm_nonneg _) normalUpper_pos.le⟩

theorem padded_defect_local (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 1
    (fun n i => ActualPhaseDefect.defect i.1.1 i.1.2 n) := by
  have hweight : LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 0
      (fun n i (_ : ActualPrimary.FullPoint) => ActualPhaseDefect.materialWeight i.1.2 n) := by
    apply local_constant (show 0 ≤ ActualPhaseDefect.materialWeightBound by
      have h0 := ActualSignedGeometry.powerBound_one (ActualPrimary.h / 2 + 1 / 2)
      have h1 := ActualSignedGeometry.powerBound_one (CoordinateAlgebra.A ActualPrimary.h -
          ActualPrimary.h)
      unfold ActualPhaseDefect.materialWeightBound
      positivity)
    intro n i x _ hc
    obtain ⟨hp, hu⟩ := ActualPhaseDefect.active_materialWeight_bound i.1.2 n hc.1.2
    simpa only [abs_of_pos hp] using hu
  have hr := polynomial_on_padded hN (ActualPhaseDefect.native_reduced_polynomial
    (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion)
  have hm := (LocalizedWaveBounds.unweighted_mul hweight hr).band_smul
      (LinearWaveBounds.band_epsilon fullStrip)
  have hm' : LocalizedWaveBounds.LocalUnweighted fullStrip (paddedCell (B := B) (N0 := N0)) 1
      (fun n i x => ChartScales.epsilon ActualPrimary.h n * ActualPhaseDefect.materialWeight i.1.2
          n *
        ActualPhaseDefect.reducedExpression i.1.1 i.1.2 n i.2 x) := by
    simp only [zero_add, smul_eq_mul, mul_assoc, ActualPhaseDefect.reducedExpression_eq_native]
        at hm ⊢
    exact hm
  apply hm'.congr_germ
  intro n i x hx hc
  apply Filter.EventuallyEq.symm
  apply ActualPhaseDefect.active_copy_defect_germ i.1.1 i.1.2 n hc.1.2 i.2 hx hc.2.1
  rw [← clock_eq i.1]
  exact hc.2.2

/-! ## Zero input slots and the unchanged native carrier -/

theorem full_background_inputs (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) (W : ℕ → CopyIndex B N0 → ActualPrimary.FullPoint → ℝ)
    (hW : ∀ n i x, x ∈ fullStrip.domain → 0 ≤ W n i x) :
    InputBounds fullStrip paddedCell W 0 ChartScales.kappa (directions B)
      (ActualParticularBackground.zeroRescale (j : ℝ) (actualFamily (B := B) (N0 := N0))) := by
  have ho := CommonBaseContext.context_operator_bounds ActualPrimary.certificate
      ActualPrimary.modulation
    ActualPrimary.upper B region (CommonWindow.index_le_native ActualPrimary.h)
  refine {
    loss_nonneg := by norm_num [ChartScales.kappa]
    radial_profile := LocalClass.of_global (HarmonicWaveInteraction.class_lift ho.radialProfile)
    radial_scale := ho.radialFrequency
    fast_scale := ho.fastCoefficient
    frequency_scale := LocalizedWaveBounds.constant_real_mul (LocalClass.band_const carrier_band)
        (j : ℝ)
    radius := LocalClass.of_global radius_unweighted
    inverse_radius := LocalClass.of_global (HarmonicWaveInteraction.class_lift ho.invRadius)
    radial_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.radialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B region))
    frequency_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.frequencyBase_unweighted ActualPrimary.certificate
          ActualPrimary.modulation ActualPrimary.upper B region))
    axial_base := LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.axialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B region))
    radial_base_aux := ?_
    frequency_base_aux := ?_
    axial_base_aux := ?_
    normal := ?_
    defect := ?_
    amplitude := fun _ => LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i
        x hx))
    pressure := LocalClass.zero (fun n i x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n i x hx)) }
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.radialSlow ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.frequencySlow ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.axialSlow ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B n))
  · rw [ActualParticularBackground.zeroRescale_normal, actualFamily_normal_eq]
    exact padded_normal_local hN
  · rw [ActualParticularBackground.zeroRescale_defect, actualFamily_defect_eq]
    exact padded_defect_local hN

/-- The literal `actualCarrier`, now controlled on every retained padded
cell. No dyadic mask or additional support hypothesis is imposed. -/
theorem actual_background_inputs (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (W : ℕ → CopyIndex B N0 → ActualParticularBackground.Native → ℝ)
    (hW : ∀ n i x, x ∈ ActualParticularBackground.nativeStrip.domain → 0 ≤ W n i x) :
    InputBounds ActualParticularBackground.nativeStrip cells W 0 ChartScales.kappa
      (ActualParticularBackground.directions B) (ActualParticularBackground.backgroundFamily b j)
          := by
  rw [ActualParticularBackground.backgroundFamily_eq b hb j]
  let Wfull : ℕ → CopyIndex B N0 → ActualPrimary.FullPoint → ℝ :=
    fun n i x => W n i (ActualParticularBackground.nativeToFull.symm x)
  have hWfull : ∀ n i x, x ∈ fullStrip.domain → 0 ≤ Wfull n i x := by
    intro n i x hx
    apply hW
    change ActualParticularBackground.nativeToFull (ActualParticularBackground.nativeToFull.symm x)
        ∈
      fullStrip.domain
    simpa only [ActualParticularBackground.nativeToFull.apply_symm_apply] using hx
  have hh := ActualParticularBackground.inputBounds_reindex ActualParticularBackground.nativeToFull
    (full_background_inputs hN j Wfull hWfull)
  simp only [Wfull, ActualParticularBackground.nativeToFull.symm_apply_apply] at hh
  exact hh

theorem background_normal_range
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l)) (j : ℤ)
    {n : ℕ} {i : CopyIndex B N0} {x : ActualParticularBackground.Native}
    (hx : x ∈ ActualParticularBackground.nativeStrip.domain) (hi : x ∈ cells n i) :
    normalFloor B N0 ≤ ‖(ActualParticularBackground.backgroundFamily b j).normal
      ActualParticularBackground.nativeStrip (ActualParticularBackground.directions B) n i x‖ ∧
    ‖(ActualParticularBackground.backgroundFamily b j).normal ActualParticularBackground.nativeStrip
      (ActualParticularBackground.directions B) n i x‖ ≤ normalCeiling B N0 := by
  rw [ActualParticularBackground.background_normal b hb j]
  exact padded_normal_range hx hi

theorem background_inverse_frequency
    (b : SignedLabel B N0 → HarmonicBlock CyclePoint)
    (hb : ∀ l, SameCarrier (b l) (ActualParticularBackground.primaryBlock l)) (j : ℤ) :
    LocalUnweighted ActualParticularBackground.nativeStrip (cells (B := B) (N0 := N0)) (1 / 2 : ℝ)
      (fun n i (_ : ActualParticularBackground.Native) =>
        1 / (ActualParticularBackground.backgroundFamily b j).frequency n i) := by
  have hh : LocalUnweighted ActualParticularBackground.nativeStrip (cells (B := B) (N0 := N0)) (1 /
      2 : ℝ)
      (fun n _ (_ : ActualParticularBackground.Native) =>
        1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) :=
    LocalClass.band_const inverse_carrier_band
  apply (LocalizedWaveBounds.constant_real_mul hh ((j : ℝ)⁻¹)).congr
  intro n i x
  change (j : ℝ)⁻¹ * (1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) =
    1 / (ActualParticularBackground.carrier b j i.1).frequency n
  rw [ActualParticularBackground.carrier_frequency b hb j]
  simp only [one_div, mul_inv_rev]
  ring

end NavierStokes.ParticularPaddedBackground

end
end

end

section

/-!
# Geometric jets for the actual scaled particular inverse

The normal, its native time derivative, and the action operator are
computed from the selected transported frame. Their native-copy jets
follow from the selected phase construction and the polynomial coordinate
cost, without estimates on a solved velocity or pressure as hypotheses.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ScaledParticularFrameJets

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds PeriodizedWaveBounds
open ActualParticularControl
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane

section FrameAlgebra

variable {ι Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {U : Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}

theorem frame_normal_jets (h : FrameJets U d) :
    PolynomialJets U (fun i => (d i).normal) := by
  exact ((h.beta.mul h.rho).pair (h.beta.smul h.K)).clm MovingFrameODE.packCLM

theorem frame_motion_jets (h : FrameJets U d) :
    PolynomialJets U (fun i => (d i).normalMotion) := by
  exact (((h.betaDot.mul h.rho).add (h.beta.mul h.rhoDot)).pair
    ((h.betaDot.smul h.K).add ((h.beta.mul h.rotation).smul h.N))).clm MovingFrameODE.packCLM

theorem frame_action_jets (h : FrameJets U d) :
    PolynomialJets U (fun i z => PrimaryCopyBridge.baseOperator ((d i).F z) ((d i).shear z)) :=
  (h.F.pair h.shear).clm PrimaryCopyBridge.baseOperatorFamily

end FrameAlgebra

section UniformAffine

variable {Label I X Q E : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translation may depend on the lattice copy; its size never
enters a derivative bound. -/
theorem polynomial_native_jets (s : StripData X)
    {U : Domain (Label × ℕ) Q} {f : (Label × ℕ) → Q → E}
    (hf : PolynomialJets U f) (C : Label → ℕ → I → Set X)
    (L : Label → ℕ → X →L[ℝ] Q) (b : Label → ℕ → I → Q)
    (hscale : ∀ l n, U.scale (l, n) = s.slow n)
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hL : ∀ l n, ‖L l n‖ ≤ A * s.slow n ^ a)
    (hmap : ∀ l n k x, x ∈ s.domain → x ∈ C l n k → L l n x + b l n k ∈ U.carrier (l, n)) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n k x => f (l,n) (L l n x + b l n k)) := by
  let V : PrimaryCopyBounds.JetDomain (Label × ℕ) Q :=
    { toDomain := U
      growth := fun i _ => U.scale i
      scale_le_growth := fun _ _ _ => le_rfl }
  have hn : PrimaryCopyBounds.NativeJets V (fun _ _ => 1) f :=
    PrimaryCopyBounds.NativeJets.of_polynomial hf
  apply hn.copy_localJets s (fun _ _ _ => 1) 0 (fun l n => (l,n))
    (fun l n _ => L l n) b C (fun _ _ _ _ => zero_le_one) hmap
    (A := 1) (B := A) le_rfl hA 1 a
  · intro l n k x hx hk
    change U.scale (l,n) ≤ 1 * s.growth n x ^ 1
    simpa only [hscale, pow_one, one_mul] using s.slow_le_growth n x
  · intro l n k
    exact hL l n
  · intro l n k x hx hk
    simp only [Real.rpow_zero, mul_one, le_refl]

end UniformAffine

section NativeCoordinates

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Argument, given by `(χ x.1, (g.coordinates k x.2).2)`. -/
noncomputable def argument (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency)
    (x : P × Plane) : Slow × ℝ := (χ x.1, (g.coordinates k x.2).2)

/-- Argument linear as an element of `(P × Plane) →L[ℝ] (Slow × ℝ)`. -/
noncomputable def argumentLinear (χ : P →L[ℝ] Slow) (g : Geometry) :
    (P × Plane) →L[ℝ] (Slow × ℝ) :=
  (χ.comp (ContinuousLinearMap.fst ℝ P Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P
        Plane)))

theorem argument_affine (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency) (x : P × Plane) :
    argument χ g k x = argumentLinear χ g x + (0,(g.coordinates k 0).2) := by
  change (χ x.1, (g.coordinates k x.2).2) = (χ x.1+0, (g.coordinateLinear x.2).2+(g.coordinates k
      0).2)
  rw [g.coordinates_eq_affine]
  simp only [Prod.snd_add, zero_add, add_comm]

theorem argumentLinear_norm (χ : P →L[ℝ] Slow) (g : Geometry) :
    ‖argumentLinear χ g‖ ≤ ‖χ‖ + CommonCoverClass.argumentCost g := by
  have hg : 0 ≤ CommonCoverClass.argumentCost g := zero_le_one.trans
      (CommonCoverClass.one_le_argumentCost g)
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    have hh : 0 ≤ ‖g.pointLinear‖ * (1+‖g.coordinateLinear‖) := by positivity
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) hg)
  intro x
  change ‖(χ x.1, (g.coordinateLinear x.2).2)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact (χ.le_opNorm x.1).trans ((mul_le_mul_of_nonneg_left (norm_fst_le x) (norm_nonneg χ)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hg) (norm_nonneg x)))
  · exact (norm_snd_le (g.coordinateLinear x.2)).trans ((g.coordinateLinear.le_opNorm x.2).trans
      ((mul_le_mul hc (norm_snd_le x) (norm_nonneg x.2) hg).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg χ)) (norm_nonneg x))))

theorem argument_smooth (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency) :
    ContDiff ℝ ∞ (argument χ g k) := by
  have he : argument χ g k = fun x => argumentLinear χ g x+(0,(g.coordinates k 0).2) :=
    funext (argument_affine χ g k)
  rw [he]
  exact (argumentLinear χ g).contDiff.add contDiff_const

end NativeCoordinates

section ActualJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : Domain (Label × ℕ) Slow}
  (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
  (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
  (clock normal : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)

/-- Tangent, given by `PrimaryCopyBridge.frameTangentData (nativeFrame
(ScaledActualParticularControl.frame F φ clock normal (l,n)) χ) j (source l n)`. -/
noncomputable def tangent (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) : TangentData P Space :=
  PrimaryCopyBridge.frameTangentData
    (nativeFrame (ScaledActualParticularControl.frame F φ clock normal (l,n)) χ) j (source l n)

theorem argument_mem {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    argument χ (g l n) k x ∈
      ((ScaledActualParticularControl.targetDomain (D := D) s φ).slot
        (ScaledActualParticularControl.interval F clock)
        (ScaledActualParticularControl.interval_open F clock)).carrier (l,n) :=
  ⟨hx.1.2.1, ScaledActualParticularControl.interval_contains F clock (l,n)
    ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩⟩

theorem frame_field_native_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Label × ℕ) → Slow × ℝ → E}
    (hf : PolynomialJets
      ((ScaledActualParticularControl.targetDomain (D := D) s φ).slot
        (ScaledActualParticularControl.interval F clock)
        (ScaledActualParticularControl.interval_open F clock)) f)
    {C : ℝ} {a : ℕ} (hC : 1 ≤ C)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ C * s.slow n ^ a) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => f (l,n) (argument χ (g l n) k x)) := by
  have hL l n : ‖argumentLinear χ (g l n)‖ ≤ (‖χ‖+C)*s.slow n^a := by
    apply (argumentLinear_norm χ (g l n)).trans
    have hs := one_le_pow₀ (s.one_le_slow n) (n := a)
    have hp := mul_le_mul_of_nonneg_left hs (norm_nonneg χ)
    nlinarith [hgeometry l n]
  have hj := polynomial_native_jets (CommonCoverClass.sourceStrip s) hf
    (ScaledActualParticularControl.patch s F χ φ clock g r)
    (fun l n => argumentLinear χ (g l n)) (fun l n k => (0,(g l n).coordinates k 0 |>.2))
    (fun _ _ => rfl) (A := ‖χ‖+C) (a := a) (by linarith [norm_nonneg χ]) hL
    (fun l n k x hx hk => by
      rw [← argument_affine]
      exact argument_mem s F χ φ clock g r hk)
  simpa only [← argument_affine] using hj

theorem native_normal_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      (ScaledActualParticularControl.frame F φ clock normal (l,n)).normal (argument χ (g l n) k x)
          := rfl

theorem native_motion_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).normalDot (ParticularWaveBounds.nativePoint (g l n) k
        x) =
      (ScaledActualParticularControl.frame F φ clock normal (l,n)).normalMotion (argument χ (g l n)
          k x) := rfl

theorem native_action_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).action (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      PrimaryCopyBridge.baseOperator
        ((ScaledActualParticularControl.frame F φ clock normal (l,n)).F (argument χ (g l n) k x))
        ((ScaledActualParticularControl.frame F φ clock normal (l,n)).shear (argument χ (g l n) k
            x)) := rfl

/-- These are the three actual geometric inputs needed by the pressure
estimate in `ParticularCopyBounds.uniform_coefficients_jets`. -/
theorem native_geometry_jets
    (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {A B C : ℝ} {a : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ A) (hscale : ∀ i, D.scale i ≤ B * s.slow i.2)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ C * s.slow n ^ a) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).normal
        (ParticularWaveBounds.nativePoint (g l n) k x)) ∧
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).normalDot
        (ParticularWaveBounds.nativePoint (g l n) k x)) ∧
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).action
        (ParticularWaveBounds.nativePoint (g l n) k x)) := by
  have hd := ScaledActualParticularControl.frame_jets s F φ clock normal hA hB hφ hscale
  exact ⟨frame_field_native_jets s F χ φ clock g r (frame_normal_jets hd) hC hgeometry,
    frame_field_native_jets s F χ φ clock g r (frame_motion_jets hd) hC hgeometry,
    frame_field_native_jets s F χ φ clock g r (frame_action_jets hd) hC hgeometry⟩

end ActualJets

section NormalRange

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : Domain (Label × ℕ) Slow}
  (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
  (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
  (clock normal : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)

/-- The frame reconstructed from the selected actual phase has exactly
that phase's normal; the nonzero transverse normal follows from its
proved reference comparison. -/
theorem selected_frame_normal_eq {i : Label × ℕ} {z : Slow × ℝ}
    (hz : z ∈ (D.slot F.V F.openV).carrier i) :
    (F.frame i).normal z = F.phase.normal i z := by
  have ht := (normal_range_of_reference_close F.B F.K F.slope F.error
    F.b_pos F.one_le_M F.B_bound F.K_unit F.slope_bound F.error_small F.normal_close).1 i z hz
  have hn : MovingFrameODE.tail (F.phase.normal i z) ≠ 0 :=
    norm_pos_iff.mp (F.b_pos.trans_le ht)
  exact PrimaryODE.FrameData.ofNormalLocal_normal _ _ _ _ _ _ _ _ hn

theorem native_normal_eq_scaled (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    (tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      normal.value l n • F.phase.normal (l,n)
        (φ (l,n) (χ x.1), clock.value l n * ((g l n).coordinates k x.2).2) := by
  rw [native_normal_eq]
  change (transportedFrame (F.frame (l,n)) (φ (l,n)) 0 (clock.value l n) (normal.value l n)).normal
    (argument χ (g l n) k x) = _
  rw [transported_normal]
  simp only [argument, zero_add]
  congr 1
  exact selected_frame_normal_eq F ⟨hx.1.2.1,
    F.interval (l,n) (ScaledActualParticularControl.clock_mem F clock
        ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩)⟩

theorem normal_lower_pos : 0 < normal.lower * F.b := mul_pos normal.lower_pos F.b_pos

/-- Both range constants precede every label, band, native copy and
evaluation point. There is no inverse dependence on the clock rate. -/
theorem native_normal_bounds (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    normal.lower * F.b ≤
      ‖(tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k
          x)‖ ∧
    ‖(tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k
        x)‖ ≤
      normal.upper * (F.M^2 + 3*F.M) := by
  rw [native_normal_eq_scaled s F χ φ clock normal g r source j hx,
    norm_smul, Real.norm_eq_abs, abs_of_pos (normal.value_pos l n)]
  have hz : (φ (l,n) (χ x.1), clock.value l n * ((g l n).coordinates k x.2).2) ∈
      (D.slot F.V F.openV).carrier (l,n) :=
    ⟨hx.1.2.1, F.interval (l,n)
      (ScaledActualParticularControl.clock_mem F clock ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩)⟩
  constructor
  · exact (mul_le_mul_of_nonneg_right (normal.bounds l n).1 F.b_pos.le).trans
      (mul_le_mul_of_nonneg_left (F.normal_range.1 (l,n) _ hz) (normal.value_pos l n).le)
  · exact (mul_le_mul_of_nonneg_right (normal.bounds l n).2 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (F.normal_range.2 (l,n) _ hz) (zero_le_one.trans normal.upper_one))

end NormalRange

end NavierStokes.ScaledParticularFrameJets

end
end

end

section

/-!
# The actual broad carrier in the canonical particular coordinates

Only the selected geometry and its closed source support occur here.  No
property of a solved particular or signed field is assumed.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCarrierTransportBase

open Set Function Filter
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open CommonCoverSolve
open scoped Topology ContDiff

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Parameter: an abbreviation for `CorrectionStep.CycleSlow`. -/
abbrev Parameter := CorrectionStep.CycleSlow
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Index: an abbreviation for `ActualPrimary.Label B N0 × Fin 2`. -/
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

variable {B N0 : ℕ}

/-- Domain, given by `PhysicalMeanDomain.slowDomain standardRegion.carrier`. -/
noncomputable def domain : Set Point :=
  PhysicalMeanDomain.slowDomain standardRegion.carrier

/-- Label carrier, given by `ActualInitialExcluded.labelCarrier (l.2,l.1) n`. -/
noncomputable def labelCarrier (l : Index B N0) (n : ℕ) : Set Point :=
  ActualInitialExcluded.labelCarrier (l.2,l.1) n

/-- Associated point, given by `CorrectionStep.cycleAssoc.symm (p, Y)`. -/
noncomputable def associatedPoint (p : Parameter) (Y : Plane) : Point :=
  CorrectionStep.cycleAssoc.symm (p, Y)

/-- Parameter domain, given by `{p | p.2 ∈ standardRegion.carrier}`. -/
noncomputable def parameterDomain : Set Parameter :=
  {p | p.2 ∈ standardRegion.carrier}

theorem associatedPoint_mem_domain (p : Parameter) (Y : Plane) :
    associatedPoint p Y ∈ domain ↔ p ∈ parameterDomain := Iff.rfl

/-- Ordered, given by `CommonWindow.index h n ≤ ChartScales.nativeIndex h
(BaseChartJets.cellBand l.1)`. -/
noncomputable def Ordered (l : Index B N0) (n : ℕ) : Prop :=
  CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.1)

/-- Slow map, given by `nativeSlow l.1 (toAbsolute n (associatedPoint p 0))`. -/
noncomputable def slowMap (l : Index B N0) (n : ℕ) (p : Parameter) : PhaseCalculus.Slow :=
  nativeSlow l.1 (toAbsolute n (associatedPoint p 0))

theorem slowMap_eq (l : Index B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    slowMap l n p = nativeSlow l.1 (toAbsolute n (associatedPoint p Y)) := rfl

theorem slowMap_continuous (l : Index B N0) (n : ℕ) : Continuous (slowMap l n) :=
  (nativeSlow_smooth l.1).continuous.comp ((toAbsolute_smooth n).continuous.comp
    (CorrectionStep.cycleAssoc.symm.continuous.comp (continuous_id.prodMk continuous_const)))

/-- Slow core, given by `slowMap l n ⁻¹' ActualGaussianCoverage.actualSlowCore certificate
modulation (choice B N0).prepared l.1`. -/
noncomputable def slowCore (l : Index B N0) (n : ℕ) : Set Parameter :=
  slowMap l n ⁻¹' ActualGaussianCoverage.actualSlowCore certificate modulation
    (choice B N0).prepared l.1

theorem slowCore_closed (l : Index B N0) (n : ℕ) : IsClosed (slowCore l n) :=
  (ActualGaussianCoverage.actualSlowCore_closed certificate modulation
    (choice B N0).prepared l.1).preimage (slowMap_continuous l n)

/-- Reference length, given by `(phases B N0 l.2).L l.1`. -/
noncomputable def referenceLength (l : Index B N0) : ℝ :=
  (phases B N0 l.2).L l.1

theorem referenceLength_pos (l : Index B N0) : 0 < referenceLength l :=
  (phases B N0 l.2).L_pos l.1

/-- Clock, given by `PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
(BaseChartJets.cellBand l.1))`. -/
noncomputable def clock (l : Index B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight h (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.1))

theorem clock_pos (l : Index B N0) (n : ℕ) : 0 < clock l n :=
  PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _

/-- Spatial label, given by `PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label
nominal l.1) l.2`. -/
noncomputable def spatialLabel (l : Index B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.1) l.2

/-- Reference geometry, given by `ActualSignedGeometry.slotGeometry slots vectors_det
(spatialLabel l) 0`. -/
noncomputable def referenceGeometry (l : Index B N0) : Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

/-- Gap, given by `ChartScales.nativeIndex h (BaseChartJets.cellBand l.1) - CommonWindow.index h
n`. -/
noncomputable def gap (l : Index B N0) (n : ℕ) : ℕ :=
  ChartScales.nativeIndex h (BaseChartJets.cellBand l.1) - CommonWindow.index h n

/-- Geometry, given by `CopySolveCompatibility.transportGeometry (referenceGeometry l) (gap l n)
0 (clock l n) (clock_pos l n).ne'`. -/
noncomputable def geometry (l : Index B N0) (n : ℕ) : Geometry :=
  CopySolveCompatibility.transportGeometry (referenceGeometry l) (gap l n) 0
    (clock l n) (clock_pos l n).ne'

theorem reference_refine (l : Index B N0) (n : ℕ) :
    CopySolveCompatibility.refineGeometry (referenceGeometry l) (gap l n) =
      chartGeometry n l.2 l.1 := by
  simp only [CopySolveCompatibility.refineGeometry, referenceGeometry,
    ActualSignedGeometry.slotGeometry, CommonCoverClass.bandGeometry, Nat.zero_add,
    chartGeometry, ActualPrimary.geometry, spatialLabel, gap]
  rfl

/-- Source region, given by `ActualGaussianCoverage.sourceRegion (slowCore l n) (geometry l n)
slots.radius (referenceLength l) (clock l n)`. -/
noncomputable def sourceRegion (l : Index B N0) (n : ℕ) : Set (Parameter × Plane) :=
  ActualGaussianCoverage.sourceRegion (slowCore l n) (geometry l n)
    slots.radius (referenceLength l) (clock l n)

theorem sourceRegion_closed (l : Index B N0) (n : ℕ) : IsClosed (sourceRegion l n) :=
  ActualGaussianCoverage.sourceRegion_closed (slowCore_closed l n) _ _ _ _

/-- The common-band logarithmic range holds on the full slow domain,
without any restriction on the radial variable. -/
theorem domain_log_band (n : ℕ) {x : Point}
    (hx : x ∈ domain) :
    SquaredPartition.logCoordinate (physicalScale n x) ∈
      Icc ((n : ℝ) - 1) ((n : ℝ) + 1) := by
  have hq : SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Ioo (1/2 : ℝ) 2 := hx.2
  apply PhysicalWaveSum.logCoordinate_in_band
  · change 0 < ChartScales.Q n * _
    exact mul_pos (ChartScales.Q_pos n) (lt_trans (by norm_num) hq.1)
  · change ChartScales.Q n / 2 ≤ ChartScales.Q n * _
    nlinarith [ChartScales.Q_pos n, hq.1]
  · change ChartScales.Q n * _ ≤ 2 * ChartScales.Q n
    nlinarith [ChartScales.Q_pos n, hq.2]

/-- Broad carrier support forces the same finite band distance on the
entire slow domain, including radii outside the analytic strip. -/
theorem carrier_band_distance (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ domain)
    (hc : x ∈ labelCarrier l n) :
    n ≤ BaseChartJets.cellBand l.1 + 2 ∧ BaseChartJets.cellBand l.1 ≤ n + 2 := by
  have hn := domain_log_band n hx
  have hm := ActualCarrierGeometry.labelCarrier_log_band hN (l.2,l.1) n hx.1 hc
  have hnm : n < BaseChartJets.cellBand l.1 + 3 := by
    have he : (n : ℝ) < (BaseChartJets.cellBand l.1 : ℝ) + 3 := by linarith [hn.1, hm.2]
    exact_mod_cast he
  have hmn : BaseChartJets.cellBand l.1 < n + 3 := by
    have he : (BaseChartJets.cellBand l.1 : ℝ) < (n : ℝ) + 3 := by linarith [hm.1, hn.2]
    exact_mod_cast he
  omega

theorem ordered_of_carrier (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ domain)
    (hc : x ∈ labelCarrier l n) : Ordered l n := by
  obtain ⟨hnm, hmn⟩ := carrier_band_distance hN l n hx hc
  have hm4 : 4 ≤ BaseChartJets.cellBand l.1 := ActualPrimaryBounds.label_large (l.2,l.1)
  apply CommonWindow.index_le
  unfold CommonWindow.levels
  apply Finset.mem_insert_of_mem
  exact Finset.mem_Icc.mpr ⟨max_le (by omega) (by omega), hmn⟩

theorem carrier_empty_of_not_ordered
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    (hn : ¬ Ordered l n) :
    Disjoint domain (labelCarrier l n) := by
  rw [Set.disjoint_left]
  intro x hx hc
  exact hn (ordered_of_carrier hN l n hx hc)

/-! The canonical geometry rescales time after the same native refinement. -/

theorem coordinates_clock (l : Index B N0) (n : ℕ) (k : TorusInverse.Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 (clock l n) ((geometry l n).coordinates k Y) =
      (chartGeometry n l.2 l.1).coordinates k Y := by
  change CopySolveCompatibility.nativeTimeMap 0 (clock l n)
      ((CopySolveCompatibility.transportGeometry
        (referenceGeometry l)
        (gap l n) 0 (clock l n) _).coordinates k Y) = _
  rw [ScaledTangentTransport.coordinates_transport,
    ← CopySolveCompatibility.coordinates_refine]
  exact congrArg (fun g : Geometry => g.coordinates k Y)
    (reference_refine l n)

theorem native_coordinates (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (p : Parameter) (Y : Plane) (k : TorusInverse.Frequency) :
    (ActualPrimary.geometry l.2 l.1).coordinates k (toAbsolute n (associatedPoint p Y)).2 =
      CopySolveCompatibility.nativeTimeMap 0 (clock l n) ((geometry l n).coordinates k Y) := by
  rw [coordinates_clock]
  exact chartGeometry_coordinates n l.2 l.1 hn k Y

theorem mem_sourceRegion (l : Index B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    (p,Y) ∈ sourceRegion l n ↔ p ∈ slowCore l n ∧
      ∃ k : TorusInverse.Frequency,
        (geometry l n).coordinates k Y ∈
          ActualGaussianCoverage.sourceCell slots.radius (referenceLength l) (clock l n) := by
  simp only [sourceRegion, ActualGaussianCoverage.sourceRegion, mem_inter_iff, mem_preimage,
    HarmonicSourceSupport.nativeUnion, mem_iUnion, PeriodizedWaveBounds.nativeCell,
        Set.mem_ofPred_eq]

/-- Under the actual index ordering, the broad primary carrier is exactly
the source region of the canonical particular geometry. -/
theorem labelCarrier_iff_sourceRegion (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (p : Parameter) (Y : Plane) :
    associatedPoint p Y ∈ labelCarrier l n ↔
      (p,Y) ∈ sourceRegion l n := by
  rw [mem_sourceRegion]
  change (∃ k : TorusInverse.Frequency,
    (nativeSlow l.1 (toAbsolute n (associatedPoint p Y)),
      (ActualPrimary.geometry l.2 l.1).coordinates k (toAbsolute n (associatedPoint p Y)).2) ∈
        ActualGaussianCoverage.actualSlowCore certificate modulation (choice B N0).prepared l.1 ×ˢ
          ActualGaussianCoverage.sourceCell slots.radius (referenceLength l) 1) ↔ _
  constructor
  · rintro ⟨k, hs, hk⟩
    refine ⟨hs, k, ?_⟩
    apply (ActualGaussianCoverage.mem_sourceCell_clock (clock_pos l n) _).mpr
    rwa [← native_coordinates l n hn p Y k]
  · rintro ⟨hs, k, hk⟩
    refine ⟨k, hs, ?_⟩
    rw [native_coordinates l n hn p Y k]
    exact (ActualGaussianCoverage.mem_sourceCell_clock (clock_pos l n) _).mp hk

/-- The unordered branch is empty. This makes the same source-region
description valid on the full slow domain for every band. -/
noncomputable def activeSlowCore (l : Index B N0) (n : ℕ) : Set Parameter := by
  classical
  exact if Ordered l n then slowCore l n else ∅

theorem activeSlowCore_closed (l : Index B N0) (n : ℕ) : IsClosed (activeSlowCore l n) := by
  classical
  unfold activeSlowCore
  split
  · exact slowCore_closed l n
  · exact isClosed_empty

/-- Canonical source region, given by `ActualGaussianCoverage.sourceRegion (activeSlowCore l n)
(geometry l n) slots.radius (referenceLength l) (clock l n)`. -/
noncomputable def canonicalSourceRegion (l : Index B N0) (n : ℕ) : Set (Parameter × Plane) :=
  ActualGaussianCoverage.sourceRegion (activeSlowCore l n) (geometry l n)
    slots.radius (referenceLength l) (clock l n)

theorem canonicalSourceRegion_closed (l : Index B N0) (n : ℕ) :
    IsClosed (canonicalSourceRegion l n) :=
  ActualGaussianCoverage.sourceRegion_closed (activeSlowCore_closed l n) _ _ _ _

theorem labelCarrier_iff_canonicalSourceRegion
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {p : Parameter} (hp : p ∈ parameterDomain) (Y : Plane) :
    associatedPoint p Y ∈ labelCarrier l n ↔
      (p,Y) ∈ canonicalSourceRegion l n := by
  classical
  by_cases hn : Ordered l n
  · simpa only [canonicalSourceRegion, activeSlowCore, ite_eq_left hn, sourceRegion] using
      labelCarrier_iff_sourceRegion l n hn p Y
  · have hnot : associatedPoint p Y ∉ labelCarrier l n :=
      fun hc => hn (ordered_of_carrier hN l n hp hc)
    simp only [hnot, canonicalSourceRegion, ActualGaussianCoverage.sourceRegion,
      activeSlowCore, ite_eq_right hn, mem_inter_iff, mem_preimage, mem_empty_iff_false, false_and]

/-- Cutoff as an element of `Plane → ℝ`. -/
noncomputable def cutoff (l : Index B N0) (n : ℕ) : Plane → ℝ :=
  (fun z => (clockWindow l.1).cutoff z *
    GaussianTailFlat.slotCutoff (referenceLength l) z.2) ∘
      CopySolveCompatibility.nativeTimeMap 0 (clock l n)

theorem cutoff_eq_native (l : Index B N0) (n : ℕ) :
    cutoff l n = ActualGaussianCoverage.nativeCutoff slots.radius (referenceLength l)
      slots.radius_pos (referenceLength_pos l) (clock l n) := by
  funext z
  simp only [cutoff, Function.comp_apply, ActualGaussianCoverage.nativeCutoff,
    CopySolveCompatibility.nativeTimeMap, zero_add]
  rfl

theorem reference_outer_injective (l : Index B N0) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (referenceGeometry l).center +
        (referenceGeometry l).basis z) ''
        (ActualGaussianCoverage.referenceWindow slots.radius (referenceLength l)
          slots.radius_pos (referenceLength_pos l)).outer) := by
  exact ActualGaussianCoverage.actual_outer_injective slots vectors_det outgoing.data.h_pos.le
    (l := spatialLabel l)
    (ActualPrimaryBounds.label_large (l.2,l.1)) 0

theorem geometry_outer_injective (l : Index B N0) (n : ℕ) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (geometry l n).center + (geometry l n).basis z) ''
        ActualGaussianCoverage.outerCell slots.radius (referenceLength l) (clock l n)) :=
  ActualGaussianCoverage.transported_outer_injective
    (referenceGeometry l)
    (gap l n)
    slots.radius_pos (referenceLength_pos l) (clock_pos l n) (reference_outer_injective l)

end NavierStokes.ActualCarrierTransportBase

end
end

end

section

/-!
# Scalar-clock support of the actual particular solve

This support argument uses the literal complex Volterra solve and the
Gaussian-times-padding cutoff. Clock factors only need to be positive
at each band; no uniform range for the complete clock family is assumed.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ScalarParticularSupport

open Set Function Filter WeightedClasses
open scoped ContDiff Topology BigOperators

section ScalarParticularSupport

open CommonCoverSolve TorusInverse LinearWaveBounds PeriodizedWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (base : WaveCoefficients ((P × ℝ) × Plane))
    (t : ℕ → TangentData (P × ℝ) ProblemStatement.Space)
    (f : ℕ → (P × ℝ) × Plane → HarmonicCalculus.ComplexVector)
    (g : ℕ → Geometry) (r L rate : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hL : ∀ n, 0 < L n) (hc : ∀ n, 0 < rate n)

/-- The literal complex Volterra solve and its separately transported
Gaussian/outer cutoff, without uniform bounds on the clock scalars. -/
noncomputable def scalarData : CopyData ((P × ℝ) × Plane) Frequency :=
  complexCopyData base t f g (fun _ => 0) (fun n => L n / rate n)
    (fun n => (div_pos (hL n) (hc n)).le)
    (fun n => ActualGaussianCoverage.nativeCutoff (r n) (L n) (hr n) (hL n) (rate n))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem scalarData_amplitude (n : ℕ) (k : Frequency) :
    (scalarData base t f g r L rate hr hL hc).amplitude n k =
      ParticularWaveBounds.complexCopyVelocity (t n) (f n) (g n)
        (div_pos (hL n) (hc n)).le k := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem scalarData_pressure (n : ℕ) (k : Frequency) :
    (scalarData base t f g r L rate hr hL hc).pressure n k =
      ParticularWaveBounds.complexCopyPressure (t n) (f n) (g n)
        (div_pos (hL n) (hc n)).le k (base.frequency n) := rfl

variable
    (hinj : ∀ n, InjOn TorusAverages.quotientPoint
      ((fun z => (g n).center + (g n).basis z) ''
        ActualGaussianCoverage.outerCell (r n) (L n) (rate n)))

/-- Scalar cells, constructed using `nativeCells`. -/
noncomputable def scalarCells : Cells ((P × ℝ) × Plane) Frequency :=
  nativeCells g (fun n => ActualGaussianCoverage.outerCell (r n) (L n) (rate n))
    (fun _ => ActualGaussianCoverage.outerCell_compact _ _ _) hinj

omit [NormedSpace ℝ P] in
theorem scalarData_cutoff_support (n : ℕ) (k : Frequency) :
    support ((scalarData base t f g r L rate hr hL hc).cutoff n k) ⊆
      (scalarCells g r L rate hinj).carrier n k :=
  native_cutoff_support (g n)
    (ActualGaussianCoverage.nativeCutoff_support (hr n) (hL n) (hc n)) k

variable (U : Set P) (S : ℕ → Set P)
    (hf : ∀ n (x : (P × ℝ) × Plane), x.1.1 ∈ U →
      (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n) →
      f n =ᶠ[𝓝 x] fun _ => 0)

include hf hinj

/-- Outside the source carrier, each padded native cell has a zero
cutoff or a zero whole-path Volterra solve. -/
theorem scalarData_native_zero_alternative (n : ℕ) (k : Frequency)
    {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ U)
    (hk : x ∈ (scalarCells g r L rate hinj).carrier n k)
    (hn : (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
    ((scalarData base t f g r L rate hr hL hc).cutoff n k =ᶠ[𝓝 x] fun _ => 0) ∨
    (((scalarData base t f g r L rate hr hL hc).amplitude n k =ᶠ[𝓝 x] fun _ => 0) ∧
     ((scalarData base t f g r L rate hr hL hc).pressure n k =ᶠ[𝓝 x] fun _ => 0)) := by
  have hk' : (g n).coordinates k x.2 ∈ ActualGaussianCoverage.outerCell (r n) (L n) (rate n) := hk
  by_cases ht : ((g n).coordinates k x.2).2 ∈ Ioo 0 (L n / rate n)
  · have hzero (hpath : ∀ v ∈ Icc 0 (L n / rate n),
        (x.1.1, (g n).path k x.2 v) ∉
          ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
        ((scalarData base t f g r L rate hr hL hc).amplitude n k =ᶠ[𝓝 x] fun _ => 0) ∧
        ((scalarData base t f g r L rate hr hL hc).pressure n k =ᶠ[𝓝 x] fun _ => 0) := by
      rw [scalarData_amplitude, scalarData_pressure]
      exact ⟨ActualGaussianCoverage.complexCopyVelocity_zero_germ _ _ _ _
        (fun v hv => hf n (x.1, (g n).path k x.2 v) hx (hpath v hv)),
        LabelSupportPreservation.complexCopyPressure_zero_germ _ _ _ _ _ ht
        (fun v hv => hf n (x.1, (g n).path k x.2 v) hx (hpath v hv))⟩
    by_cases hp : x.1.1 ∈ S n
    · by_cases hxi : ((g n).coordinates k x.2).1 ∈ Icc (-(r n)) (r n)
      · left
        have htime : ((g n).coordinates k x.2).2 ∉
            Icc ((L n / rate n) / 6) (5 * (L n / rate n) / 6) := by
          intro hv
          apply hn
          exact ⟨hp, mem_iUnion.mpr ⟨k, hxi, hv⟩⟩
        exact (LabelSupportPreservation.nativeCutoff_source_time_zero_germ
          (hr n) (hL n) (hc n) htime).comp_tendsto
            (((g n).coordinates_contDiff k).continuous.comp continuous_snd).continuousAt
      · right
        apply hzero
        intro v hv hh
        obtain ⟨i, hi⟩ := mem_iUnion.mp hh.2
        exact ActualGaussianCoverage.path_sourceCell_excluded (g n) (hr n) (hL n) (hc n)
          (hinj n) hk' hxi v hv i hi
    · right
      exact hzero (fun _ _ hh => hp hh.1)
  · left
    exact (ActualGaussianCoverage.nativeCutoff_time_zero_germ
      (hr n) (hL n) (hc n) ht).comp_tendsto
        (((g n).coordinates_contDiff k).continuous.comp continuous_snd).continuousAt

theorem scalarData_zero_germs (s : StripData ((P × ℝ) × Plane))
    (d : GraphDirections ((P × ℝ) × Plane)) (n : ℕ)
    {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ U)
    (hn : (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
    let a := scalarData base t f g r L rate hr hL hc
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGaussian d n =ᶠ[𝓝 x] fun _ => 0) := by
  apply LabelSupportPreservation.common_zero_germs_of_native
    (scalarData base t f g r L rate hr hL hc) (scalarCells g r L rate hinj)
    (scalarData_cutoff_support base t f g r L rate hr hL hc hinj) s d (hf n x hx hn)
  intro k hk
  exact scalarData_native_zero_alternative base t f g r L rate hr hL hc hinj U S hf n k hx hk hn

end ScalarParticularSupport

end NavierStokes.ScalarParticularSupport

end
end

end

section

/-!
# Jets of the literal transported native cutoff

The product consists of the padded reference window and the separate Gaussian
slot cutoff. On the analytic patch the window equals one on an ambient
neighborhood, including at the closed transverse endpoints. Its exact germ
therefore transfers the Gaussian clock estimates without assumptions about a
source, correction state, or modal-control output.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.NativeCutoffJets

open Set Function Filter WeightedClasses
open CommonCoverSolve TorusInverse PrimaryPulseBounds PeriodizedWaveBounds
open scoped Topology ContDiff

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

/-- The literal cutoff, before placing it in any particular-solve record. -/
noncomputable def literalCutoff (l : Label) (n : ℕ) (k : Frequency)
    (x : P × Plane) : ℝ :=
  (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2)) *
    GaussianTailFlat.slotCutoff (F.L (l,n))
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2)).2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem literalCutoff_eq_referenceTransport (l : Label) (n : ℕ) (k : Frequency) :
    literalCutoff (P := P) F clock g r hr l n k =
      fun x => ActualGaussianCoverage.referenceCutoff (r l n) (F.L (l,n))
        (hr l n) (F.L_pos (l,n))
          (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
            ((g l n).coordinates k x.2)) := rfl

variable (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)

/-- Patch membership supplies the actual closed-core hypothesis of the
reference window's neighborhood theorem. -/
theorem nativeTime_mem_core (l : Label) (n : ℕ) (k : Frequency) {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2) ∈
      (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
        (hr l n) (F.L_pos (l,n))).core := by
  change ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) ∧
    0 + clock.value l n * ((g l n).coordinates k x.2).2 ∈ Icc 0 (F.L (l,n))
  simp only [zero_add]
  exact And.intro hx.2 (ScaledActualParticularControl.clock_mem F clock
      ⟨hx.1.2.2.1.le, hx.1.2.2.2.le⟩)

/-- This is an ambient germ, obtained from the padded window's exact
cutoff_germ theorem rather than from its value at the boundary point. -/
theorem literalCutoff_gaussian_germ (l : Label) (n : ℕ) (k : Frequency)
    {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    literalCutoff F clock g r hr l n k =ᶠ[𝓝 x]
      fun y => GaussianTailFlat.profile
        (ActualGaussianCoverage.theta F clock l n ((g l n).coordinates k y.2).2) := by
  have hm := nativeTime_mem_core F clock g r hr s χ φ l n k hx
  have hc : Continuous (fun y : P × Plane =>
      CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k y.2)) :=
    (CopySolveCompatibility.nativeTimeMap_continuous _ _).comp
      (((g l n).coordinates_contDiff k).continuous.comp continuous_snd)
  have he := ((ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff_germ hm).comp_tendsto hc.continuousAt
  filter_upwards [he] with y hy
  dsimp only [Function.comp_def] at hy
  change (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k y.2)) * _ = _
  rw [hy, one_mul]
  simp only [GaussianTailFlat.slotCutoff, CopySolveCompatibility.nativeTimeMap,
    ActualGaussianCoverage.theta, zero_add]

/-- All finite jets are uniform in the label, band, and lifted copy. The
only quantitative input beyond the primitive phase and clock is the
polynomial bound for the actual affine geometry. -/
theorem literalCutoff_uniformLocalJets {u0 : ℝ}
    (hu0 : 0 < u0) (hu : ∀ l n, F.u (l, n) = u0)
    (hcost : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ l n,
      CommonCoverClass.argumentCost (g l n) ≤ K * s.slow n ^ p) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (literalCutoff F clock g r hr) := by
  have hj := ActualGaussianCoverage.gaussian_clock_uniform_jets F clock
    (CommonCoverClass.sourceStrip s)
    (ScaledActualParticularControl.patch s F χ φ clock g r) g hu0 hu hcost
  apply ActualSignedControl.uniform_local_congr hj
  intro l n k x _ hx
  exact (literalCutoff_gaussian_germ F clock g r hr s χ φ l n k hx).symm

end NavierStokes.NativeCutoffJets

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularStageControls

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CorrectionState CorrectionStep CommonCoverSolve TorusInverse
open scoped ContDiff Topology BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Parameter: an abbreviation for `PhysicalParticularWave.Parameter`. -/
abbrev Parameter := PhysicalParticularWave.Parameter
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Native: an abbreviation for `(Parameter × ℝ) × Plane`. -/
abbrev Native := (Parameter × ℝ) × Plane
/-- AP: an abbreviation for `CorrectionInitialization.ActualPrimary.FullPoint`. -/
abbrev AP := CorrectionInitialization.ActualPrimary.FullPoint
/-- Label: an abbreviation for `Fin 2 × CorrectionInitialization.ActualPrimary.Label B N0 /-!
Reindexing retains the selected phase, its frame, and all uniform constants. -/`. -/
abbrev Label (B N0 : ℕ) := Fin 2 × CorrectionInitialization.ActualPrimary.Label B N0

/-! Reindexing retains the selected phase, its frame, and all uniform constants. -/

/-- Reindex domain, bundling `scale`, `carrier`, `isOpen`, `one_le_scale`. -/
noncomputable def reindexDomain {ι κ : Type} (D : Domain ι Slow) (e : κ → ι) : Domain κ Slow where
  scale i := D.scale (e i)
  carrier i := D.carrier (e i)
  isOpen i := D.isOpen (e i)
  one_le_scale i := D.one_le_scale (e i)

/-- Reindex phase, bundling `epsilon`, `p`, `pz`, `x0` and the required compatibility proofs. -/
noncomputable def reindexPhase {ι κ : Type} (F : PhaseFamily ι) (e : κ → ι) : PhaseFamily κ where
  epsilon i := F.epsilon (e i)
  p i := F.p (e i)
  pz i := F.pz (e i)
  x0 i := F.x0 (e i)
  theta i := F.theta (e i)
  F i := F.F (e i)
  G i := F.G (e i)

/-- Reindex construction, bundling `phase`, `V`, `openV`, `lam` and the required compatibility
proofs. -/
noncomputable def reindexConstruction {ι κ : Type} {D : Domain ι Slow}
    (F : PhaseConstruction D) (e : κ → ι) : PhaseConstruction (reindexDomain D e) where
  phase := reindexPhase F.phase e
  V i := F.V (e i)
  openV i := F.openV (e i)
  lam i := F.lam (e i)
  c0 i := F.c0 (e i)
  u i := F.u (e i)
  L i := F.L (e i)
  viscosity i := F.viscosity (e i)
  B i := F.B (e i)
  K i := F.K (e i)
  slope i := F.slope (e i)
  error i := F.error (e i)
  r := F.r
  b := F.b
  M := F.M
  C := F.C
  E := F.E
  r_pos := F.r_pos
  b_pos := F.b_pos
  one_le_M := F.one_le_M
  C_nonneg := F.C_nonneg
  E_nonneg := F.E_nonneg
  baseF := PrimaryGeometryAssembly.polynomial_restrict_reindex F.baseF e (fun _ => rfl) (fun _ _ h
      => h)
  baseG := PrimaryGeometryAssembly.polynomial_restrict_reindex F.baseG e (fun _ => rfl) (fun _ _ h
      => h)
  constants i := F.constants (e i)
  epsilon_ne i := F.epsilon_ne (e i)
  radius i := F.radius (e i)
  slot i := F.slot (e i)
  lam_bound i := F.lam_bound (e i)
  c0_bound i := F.c0_bound (e i)
  u_bound i := F.u_bound (e i)
  rate_bound i := F.rate_bound (e i)
  viscosity_bound i := F.viscosity_bound (e i)
  B_bound i := F.B_bound (e i)
  K_unit i := F.K_unit (e i)
  slope_bound i := F.slope_bound (e i)
  error_small i := F.error_small (e i)
  normal_close i := F.normal_close (e i)
  lam_pos i := F.lam_pos (e i)
  u_pos i := F.u_pos (e i)
  L_pos i := F.L_pos (e i)
  interval i := F.interval (e i)
  viscosity_nonneg i := F.viscosity_nonneg (e i)
  damping_error i := F.damping_error (e i)
  modal_errors i := F.modal_errors (e i)

@[simp] theorem reindex_frame {ι κ : Type} {D : Domain ι Slow}
    (F : PhaseConstruction D) (e : κ → ι) (i : κ) :
    (reindexConstruction F e).frame i = F.frame (e i) := rfl

/-! The original physical slot, Gaussian cutoff, and actual current-state data. -/

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

/-- Spatial label, given by `PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label
nominal l.2) l.1`. -/
noncomputable def spatialLabel (l : Label B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.2) l.1

/-- Reference geometry, given by `ActualSignedGeometry.slotGeometry slots vectors_det
(spatialLabel l) 0`. -/
noncomputable def referenceGeometry (l : Label B N0) : Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0

/-- Gap, given by `ChartScales.nativeIndex h (BaseChartJets.cellBand l.2) - CommonWindow.index h
n`. -/
noncomputable def gap (l : Label B N0) (n : ℕ) : ℕ :=
  ChartScales.nativeIndex h (BaseChartJets.cellBand l.2) - CommonWindow.index h n

theorem reference_refine (l : Label B N0) (n : ℕ) :
    CopySolveCompatibility.refineGeometry (referenceGeometry l) (gap l n) =
      chartGeometry n l.1 l.2 := by
  simp only [CopySolveCompatibility.refineGeometry, referenceGeometry,
    ActualSignedGeometry.slotGeometry, CommonCoverClass.bandGeometry, Nat.zero_add,
    chartGeometry, geometry, spatialLabel, gap]
  rfl

/-- Reference cutoff, given by `(clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff
((phases B N0 l.1).L l.2) z.2`. -/
noncomputable def referenceCutoff (l : Label B N0) (z : Plane) : ℝ :=
  (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff ((phases B N0 l.1).L l.2) z.2

theorem referenceCutoff_compact (l : Label B N0) : HasCompactSupport (referenceCutoff l) :=
  (clockWindow l.2).cutoff_compact.mul_right

/-- Reference, bundling `band`, `geometry`, `length`, `length_pos` and the required
compatibility proofs. -/
noncomputable def reference (l : Label B N0) : ParticularWaveAssembly.Reference Parameter where
  band := BaseChartJets.cellBand l.2
  geometry := referenceGeometry l
  length := (phases B N0 l.1).L l.2
  length_pos := (phases B N0 l.1).L_pos l.2
  tangent j := PrimaryCopyBridge.frameTangentData
    (ActualParticularControl.nativeFrame ((phases B N0 l.1).frame l.2)
      ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap)
    j (fun _ => 0)
  cutoff := referenceCutoff l
  cutoff_compact := referenceCutoff_compact l

/-- Native to full, given by `ParticularWaveAssembly.angleShuffle.symm.trans
(StateReindex.cylinder cycleAssoc.symm)`. -/
noncomputable def nativeToFull : Native ≃ₗᵢ[ℝ] AP :=
  ParticularWaveAssembly.angleShuffle.symm.trans (StateReindex.cylinder cycleAssoc.symm)

/-- Background, given by `ParticularWaveBounds.reindexCoefficients nativeToFull
(chartCoefficients l.1 l.2)`. -/
noncomputable def background (l : Label B N0) : LinearWaveBounds.WaveCoefficients Native :=
  ParticularWaveBounds.reindexCoefficients nativeToFull (chartCoefficients l.1 l.2)

/-- Directions, given by `ParticularWaveBounds.reindexDirections nativeToFull
(PrimaryResidualClass.directions (commonContext B))`. -/
noncomputable def directions : LinearWaveBounds.GraphDirections Native :=
  ParticularWaveBounds.reindexDirections nativeToFull (PrimaryResidualClass.directions
      (commonContext B))

/-- Associated context, given by `StateReindex.context cycleAssoc.symm (commonContext B)`. -/
noncomputable def associatedContext : Context (Parameter × Plane) :=
  StateReindex.context cycleAssoc.symm (commonContext B)

/-- Associated strip, given by `ParticularWaveBounds.reindexStrip cycleAssoc.symm
(BaseContextAssembly.nativeStrip nominal standardRegion)`. -/
noncomputable def associatedStrip : StripData (Parameter × Plane) :=
  ParticularWaveBounds.reindexStrip cycleAssoc.symm (BaseContextAssembly.nativeStrip nominal
      standardRegion)

/-- Assembly, bundling `reference`, `charts`, `parameter`, `gap` and the required compatibility
proofs. -/
noncomputable def assembly (x : CycleState (Label B N0)) (l : Label B N0) :
    ParticularWaveAssembly.AssemblyData Parameter where
  reference := reference l
  charts := {
    parameter n := PhysicalParticularWave.parameterChange h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
    gap := gap l
    amplitude n := PhysicalParticularWave.velocityWeight h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) }
  context := associatedContext (B := B)
  state := StateReindex.state cycleAssoc.symm x.state
  carrierBlock := StateReindex.block cycleAssoc.symm (x.coefficients.blocks l)
  gaussianInput := StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l)
  aliasInput := StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)
  background := background l
  copy := fun _ => 0
  strip := ParticularParameters.nativeStrip associatedStrip
  directions := directions (B := B)

/-- Parameters, given by `ParticularParameters.fromReference (assembly x l) h (gap l)`. -/
noncomputable def parameters (x : CycleState (Label B N0)) (l : Label B N0) :
    ParticularParameters Parameter :=
  ParticularParameters.fromReference (assembly x l) h (gap l)

theorem parameters_source (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    ((parameters x l).copyData (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j).source =
      ParticularWaveAssembly.sourceFamily (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j := rfl

theorem parameters_length (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    (parameters x l).length n = (phases B N0 l.1).L l.2 /
      PhysicalParticularWave.clockWeight h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) := rfl

/-- Fixed primitive data for all iterations of the same labeled construction. -/
noncomputable def canonicalParameters (l : Label B N0) : ParticularParameters Parameter where
  tangent j n := ScaledTangentTransport.transportTangent ((reference l).tangent j)
    (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (gap l n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (reference l).band)
      ((j:ℝ)*ChartScales.carrier h n) ((j:ℝ)*ChartScales.carrier h (reference l).band))
  geometry n := CopySolveCompatibility.transportGeometry (reference l).geometry (gap l n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n)
      (ChartScales.Q_pos (reference l).band) _).ne'
  length n := (reference l).length /
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band)
  length_pos n := div_pos (reference l).length_pos
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n)
      (ChartScales.Q_pos (reference l).band) _)
  cutoff n := (reference l).cutoff ∘ CopySolveCompatibility.nativeTimeMap 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (reference l).band))
  background := background l
  directions := directions (B := B)

theorem parameters_eq_canonical (x : CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n) :
    parameters x l = canonicalParameters l := by
  have he : (assembly x l).carrierBlock.frequency = fun n => (ChartScales.carrier h n : ℝ) :=
    funext hfrequency
  dsimp only [parameters, canonicalParameters, ParticularParameters.fromReference,
    PhysicalParticularWave.referenceFrequency]
  rw [he]
  rfl

/-! The sign combination is proved before specializing the constructed profile. -/

/-- Signed phase, bundling `epsilon`, `p`, `pz`, `x0` and the required compatibility proofs. -/
noncomputable def signedPhase {ι : Type} {D : Domain ι Slow}
    (F : Fin 2 → PhaseConstruction D) : PhaseFamily (Fin 2 × ι) where
  epsilon l := (F l.1).phase.epsilon l.2
  p l := (F l.1).phase.p l.2
  pz l := (F l.1).phase.pz l.2
  x0 l := (F l.1).phase.x0 l.2
  theta l := (F l.1).phase.theta l.2
  F l := (F l.1).phase.F l.2
  G l := (F l.1).phase.G l.2

/-- Signed construction, bundling `phase`, `V`, `openV`, `lam` and the required compatibility
proofs. -/
noncomputable def signedConstruction {ι : Type} {D : Domain ι Slow}
    (F : Fin 2 → PhaseConstruction D)
    (hr : ∀ j, (F j).r = (F 0).r) (hb : ∀ j, (F j).b = (F 0).b)
    (hM : ∀ j, (F j).M = (F 0).M) (hC : ∀ j, (F j).C = (F 0).C)
    (hE : ∀ j, (F j).E = (F 0).E)
    (hF : ∀ j, (F j).phase.F = (F 0).phase.F)
    (hG : ∀ j, (F j).phase.G = (F 0).phase.G) :
    PhaseConstruction (reindexDomain D (Prod.snd : Fin 2 × ι → ι)) where
  phase := signedPhase F
  V l := (F l.1).V l.2
  openV l := (F l.1).openV l.2
  lam l := (F l.1).lam l.2
  c0 l := (F l.1).c0 l.2
  u l := (F l.1).u l.2
  L l := (F l.1).L l.2
  viscosity l := (F l.1).viscosity l.2
  B l := (F l.1).B l.2
  K l := (F l.1).K l.2
  slope l := (F l.1).slope l.2
  error l := (F l.1).error l.2
  r := (F 0).r
  b := (F 0).b
  M := (F 0).M
  C := (F 0).C
  E := (F 0).E
  r_pos := (F 0).r_pos
  b_pos := (F 0).b_pos
  one_le_M := (F 0).one_le_M
  C_nonneg := (F 0).C_nonneg
  E_nonneg := (F 0).E_nonneg
  baseF := by
    have he : (signedPhase F).F = fun l => (F 0).phase.F l.2 := by
      funext l
      exact congrFun (hF l.1) l.2
    rw [he]
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (F 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ h => h)
  baseG := by
    have he : (signedPhase F).G = fun l => (F 0).phase.G l.2 := by
      funext l
      exact congrFun (hG l.1) l.2
    rw [he]
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (F 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ h => h)
  constants l := by
    have h := (F l.1).constants l.2
    simp only [hM] at h
    exact h
  epsilon_ne l := (F l.1).epsilon_ne l.2
  radius l := by
    have h := (F l.1).radius l.2
    simp only [hr, hM] at h
    exact h
  slot l := by
    have h := (F l.1).slot l.2
    simp only [hM] at h
    exact h
  lam_bound l := by simpa only [hM] using (F l.1).lam_bound l.2
  c0_bound l := by simpa only [hb, hM] using (F l.1).c0_bound l.2
  u_bound l := by simpa only [hM] using (F l.1).u_bound l.2
  rate_bound l := by
    have h := (F l.1).rate_bound l.2
    simp only [hM] at h
    exact h
  viscosity_bound l := by simpa only [hM] using (F l.1).viscosity_bound l.2
  B_bound l := by simpa only [hb, hM] using (F l.1).B_bound l.2
  K_unit l := (F l.1).K_unit l.2
  slope_bound l := by
    have h := (F l.1).slope_bound l.2
    simp only [hM] at h
    exact h
  error_small l := (F l.1).error_small l.2
  normal_close l := (F l.1).normal_close l.2
  lam_pos l := (F l.1).lam_pos l.2
  u_pos l := (F l.1).u_pos l.2
  L_pos l := (F l.1).L_pos l.2
  interval l := (F l.1).interval l.2
  viscosity_nonneg l := (F l.1).viscosity_nonneg l.2
  damping_error l := by
    have h := (F l.1).damping_error l.2
    simp only [hE] at h
    exact h
  modal_errors l := by
    have h := (F l.1).modal_errors l.2
    simp only [hC] at h
    exact h

/-- Joint domain, given by `reindexDomain (PrimaryGeometryAssembly.domain nominal (choice B
N0).prepared.N) Prod.snd`. -/
noncomputable def jointDomain : Domain (Label B N0) Slow :=
  reindexDomain (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N) Prod.snd

/-- Joint phase, given by `signedPhase (phases B N0)`. -/
noncomputable def jointPhase : PhaseFamily (Label B N0) := signedPhase (phases B N0)

theorem phase_common_bounds (j : Fin 2) :
    (phases B N0 j).r = (phases B N0 0).r ∧
    (phases B N0 j).b = (phases B N0 0).b ∧
    (phases B N0 j).M = (phases B N0 0).M ∧
    (phases B N0 j).C = (phases B N0 0).C ∧
    (phases B N0 j).E = (phases B N0 0).E :=
  PrimaryGeometryAssembly.common_bounds certificate modulation (choice B N0).prepared
      slots.radius_pos j 0

theorem phase_frequency_eq (j : Fin 2) : (phases B N0 j).phase.F = (phases B N0 0).phase.F := by
  funext L
  exact (PrimaryGeometryAssembly.construction_frequency certificate modulation
    (choice B N0).prepared slots.radius_pos j L).trans
    (PrimaryGeometryAssembly.construction_frequency certificate modulation
      (choice B N0).prepared slots.radius_pos 0 L).symm

theorem phase_axial_eq (j : Fin 2) : (phases B N0 j).phase.G = (phases B N0 0).phase.G := by
  funext L
  exact (PrimaryGeometryAssembly.construction_axial certificate modulation
    (choice B N0).prepared slots.radius_pos j L).trans
    (PrimaryGeometryAssembly.construction_axial certificate modulation
      (choice B N0).prepared slots.radius_pos 0 L).symm

/-- Joint construction, constructed using `signedConstruction`. -/
noncomputable def jointConstruction : PhaseConstruction (jointDomain (B := B) (N0 := N0)) :=
  signedConstruction (phases B N0)
    (fun j => (phase_common_bounds j).1)
    (fun j => (phase_common_bounds j).2.1)
    (fun j => (phase_common_bounds j).2.2.1)
    (fun j => (phase_common_bounds j).2.2.2.1)
    (fun j => (phase_common_bounds j).2.2.2.2)
    phase_frequency_eq phase_axial_eq

@[simp] theorem joint_frame (l : Label B N0) :
    (jointConstruction (B := B) (N0 := N0)).frame l = (phases B N0 l.1).frame l.2 := rfl

/-! Changing the native clock preserves the same grouped Gaussian exactly. -/

theorem copyEnvelope_time (g : Geometry) (r L rate : ℝ) (hrate : 0 < rate)
    (W : ℝ → ℝ) (Y : Plane) :
    WaveEnvelopeTransport.copyEnvelope (CopySolveCompatibility.timeGeometry g 0 rate hrate.ne')
      r (L / rate) (fun t => W (rate*t)) Y =
      WaveEnvelopeTransport.copyEnvelope g r L W Y := by
  classical
  apply tsum_congr
  intro k
  have he := CopySolveCompatibility.coordinates_timeGeometry g 0 rate hrate.ne' k Y
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [CopySolveCompatibility.nativeTimeMap, zero_add] at h1 h2
  have hm : (CopySolveCompatibility.timeGeometry g 0 rate hrate.ne').coordinates k Y ∈
      WaveEnvelopeTransport.rectangle r (L/rate) ↔
      g.coordinates k Y ∈ WaveEnvelopeTransport.rectangle r L := by
    change (_ ∈ Icc (-r) r ∧ 0 ≤ _ ∧ _ ≤ L/rate) ↔
      (_ ∈ Icc (-r) r ∧ 0 ≤ _ ∧ _ ≤ L)
    rw [h1, ← h2]
    constructor
    · rintro ⟨hu, h0, hL⟩
      exact ⟨hu, mul_nonneg hrate.le h0, by
        simpa only [mul_comm] using (le_div_iff₀ hrate).mp hL⟩
    · rintro ⟨hu, h0, hL⟩
      exact ⟨hu, (mul_nonneg_iff_of_pos_left hrate).mp h0,
        (le_div_iff₀ hrate).mpr (by simpa only [mul_comm] using hL)⟩
  change (if _ then W _ else 0) = (if _ then W _ else 0)
  simp only [hm, h2]

theorem copyEnvelope_transport (g : Geometry) (gap : ℕ) (r L rate : ℝ)
    (hrate : 0 < rate) (W : ℝ → ℝ) (Y : Plane) :
    WaveEnvelopeTransport.copyEnvelope
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne')
      r (L/rate) (fun t => W (rate*t)) Y =
    WaveEnvelopeTransport.copyEnvelope (CopySolveCompatibility.refineGeometry g gap) r L W Y :=
  copyEnvelope_time (CopySolveCompatibility.refineGeometry g gap) r L rate hrate W Y

/-! The slow/fast association keeps the full moving weight unchanged. -/

/-- Slow insert, bundling `toFun`, `map_add`, `map_smul`, `cont`. -/
noncomputable def slowInsert : Parameter →L[ℝ] CyclePoint where
  toFun p := (p.1,(p.2,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)

/-- Slow strip, given by `HarmonicWaveInteraction.pullbackStrip (BaseContextAssembly.nativeStrip
nominal standardRegion) slowInsert`. -/
noncomputable def slowStrip : StripData Parameter :=
  HarmonicWaveInteraction.pullbackStrip (BaseContextAssembly.nativeStrip nominal standardRegion)
      slowInsert

theorem sourceStrip_eq : CommonCoverClass.sourceStrip slowStrip = associatedStrip := by
  rfl

theorem nativeStrip_eq :
    CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip) =
      ParticularParameters.nativeStrip associatedStrip := by
  rfl

/-- Pulse envelope, given by `PrimaryPulseBounds.referenceP ((phases B N0 l.1).lam l.2) ((phases
B N0 l.1).u l.2) ((phases B N0 l.1).L l.2)`. -/
noncomputable def pulseEnvelope (l : Label B N0) : ℝ → ℝ :=
  PrimaryPulseBounds.referenceP ((phases B N0 l.1).lam l.2) ((phases B N0 l.1).u l.2)
    ((phases B N0 l.1).L l.2)

/-- Envelope, given by `WaveEnvelopeTransport.copyEnvelope (chartGeometry n l.1 l.2)
slots.radius ((phases B N0 l.1).L l.2) (pulseEnvelope l) z.2`. -/
noncomputable def envelope (l : Label B N0) (n : ℕ) (z : Parameter × Plane) : ℝ :=
  WaveEnvelopeTransport.copyEnvelope (chartGeometry n l.1 l.2) slots.radius
    ((phases B N0 l.1).L l.2) (pulseEnvelope l) z.2

/-- Mean envelope, given by `envelope l n (cycleAssoc z)`. -/
noncomputable def meanEnvelope (l : Label B N0) (n : ℕ) (z : CyclePoint) : ℝ :=
  envelope l n (cycleAssoc z)

/-- Native envelope, given by `envelope l n (z.1.1,z.2)`. -/
noncomputable def nativeEnvelope (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  envelope l n (z.1.1,z.2)

theorem envelope_nonneg (l : Label B N0) (n : ℕ) (z : Parameter × Plane) : 0 ≤ envelope l n z :=
  WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _
    (fun t => (PrimaryPulseBounds.referenceP_pos _ _ _ t).le) _

/-- Active, given by `1 ≤ n ∧ BaseChartJets.cellBand l.2 ∈ CommonWindow.levels n`. -/
noncomputable def Active (l : Label B N0) (n : ℕ) : Prop :=
  1 ≤ n ∧ BaseChartJets.cellBand l.2 ∈ CommonWindow.levels n

/-- Active pair: an abbreviation for `{i : Label B N0 × ℕ // Active i.1 i.2}`. -/
abbrev ActivePair (B N0 : ℕ) := {i : Label B N0 × ℕ // Active i.1 i.2}

section Selected

variable (e : ℕ → ActivePair B N0)

/-- Selected label, given by `(e n).val.1`. -/
noncomputable def selectedLabel (n : ℕ) : Label B N0 := (e n).val.1

/-- Selected band, given by `(e n).val.2`. -/
noncomputable def selectedBand (n : ℕ) : ℕ := (e n).val.2

/-- Selected construction, given by `reindexConstruction (jointConstruction (B := B) (N0 := N0))
(fun i : Unit × ℕ => selectedLabel e i.2)`. -/
noncomputable def selectedConstruction :=
  reindexConstruction (jointConstruction (B := B) (N0 := N0))
    (fun i : Unit × ℕ => selectedLabel e i.2)

/-- Selected strip, given by `UniformPrimaryWeights.reindexedStrip slowStrip (fun n =>
(selectedBand e n, ()))`. -/
noncomputable def selectedStrip : StripData Parameter :=
  UniformPrimaryWeights.reindexedStrip slowStrip (fun n => (selectedBand e n, ()))

/-- Selected slot, given by `spatialLabel (selectedLabel e n)`. -/
noncomputable def selectedSlot (_ : Unit) (n : ℕ) : SlotColoring.Label :=
  spatialLabel (selectedLabel e n)

theorem selected_near (u : Unit) (n : ℕ) :
    selectedBand e n ≤ (selectedSlot e u n).1 + 4 ∧
      (selectedSlot e u n).1 ≤ selectedBand e n + 4 :=
  CommonWindow.distance (e n).property.2

/-- Selected clock, given by `ActualSignedGeometry.clockScale (selectedBand e) (fun u n =>
(selectedSlot e u n).1) (selected_near e) h`. -/
noncomputable def selectedClock :=
  ActualSignedGeometry.clockScale (selectedBand e) (fun u n => (selectedSlot e u n).1)
    (selected_near e) h

/-- Selected normal, given by `ActualSignedGeometry.normalScale (selectedBand e) (fun u n =>
(selectedSlot e u n).1) (selected_near e) outgoing.data.h_pos.le`. -/
noncomputable def selectedNormal :=
  ActualSignedGeometry.normalScale (selectedBand e) (fun u n => (selectedSlot e u n).1)
    (selected_near e) outgoing.data.h_pos.le

/-- Selected gap, given by `gap (selectedLabel e n) (selectedBand e n)`. -/
noncomputable def selectedGap (_ : Unit) (n : ℕ) : ℕ := gap (selectedLabel e n) (selectedBand e n)

/-- Selected geometry, constructed using `ScaledActualParticularControl.geometry`. -/
noncomputable def selectedGeometry :=
  ScaledActualParticularControl.geometry
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (selectedClock e)

/-- Selected length, given by `ScaledActualParticularControl.length (selectedConstruction e)
(selectedClock e)`. -/
noncomputable def selectedLength :=
  ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e)

/-- Selected pulse envelope, given by `ScaledActualParticularControl.envelope
(selectedConstruction e) (selectedClock e)`. -/
noncomputable def selectedPulseEnvelope :=
  ScaledActualParticularControl.envelope (selectedConstruction e) (selectedClock e)

theorem selected_geometry_eq (x : CycleState (Label B N0)) (n : ℕ) :
    selectedGeometry e () n = (parameters x (selectedLabel e n)).geometry (selectedBand e n) := rfl

theorem selected_length_eq (x : CycleState (Label B N0)) (n : ℕ) :
    selectedLength e () n = (parameters x (selectedLabel e n)).length (selectedBand e n) := rfl

theorem selected_gap_bound (u : Unit) (n : ℕ) :
    selectedGap e u n ≤ CommonWindow.gap h + SlotColoring.nativeGap h :=
  ActualSignedGeometry.common_native_gap outgoing.data.h_pos.le
    (CommonWindow.indexBounds h outgoing.data.h_pos.le)
    (e n).property.1 (by
      have := ((choice B N0).prepared.large _ (selectedLabel e n).2.property).four_le
      exact le_trans (by norm_num) this)
    (selected_near e u n).1 (selected_near e u n).2

theorem selected_slot_large (u : Unit) (n : ℕ) : 4 ≤ (selectedSlot e u n).1 :=
  ((choice B N0).prepared.large _ (selectedLabel e n).2.property).four_le

theorem selected_scale (i : Unit × ℕ) :
    (reindexDomain (jointDomain (B := B) (N0 := N0))
      (fun z : Unit × ℕ => selectedLabel e z.2)).scale i =
      ChartScales.S (selectedSlot e i.1 i.2).1 := rfl

theorem selected_length (i : Unit × ℕ) :
    (selectedConstruction e).L i = ChartScales.slotLength slots.radius h (selectedSlot e i.1 i.2).1
        := rfl

theorem selected_envelope_eq (n : ℕ) (z : Parameter × Plane) :
    ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
      (selectedLength e) (selectedPulseEnvelope e) () n z =
      envelope (selectedLabel e n) (selectedBand e n) z := by
  have he := copyEnvelope_transport (referenceGeometry (selectedLabel e n)) (selectedGap e () n)
    slots.radius ((selectedConstruction e).L ((),n)) ((selectedClock e).value () n)
    ((selectedClock e).value_pos () n) (pulseEnvelope (selectedLabel e n)) z.2
  rw [show selectedGap e () n = gap (selectedLabel e n) (selectedBand e n) from rfl,
    reference_refine] at he
  exact he

end Selected

/-! The input class is exactly the residual component of the cycle invariant. -/

theorem select_uniform {ι X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData X} {w : ι → ℕ → X → ℝ} {f : ι → ℕ → X → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass s w α f) (e : ℕ → ι × ℕ) :
    LabelSumBounds.UniformClass (UniformPrimaryWeights.reindexedStrip s (fun n => ((e n).2, ())))
      (fun (_ : Unit) n => w (e n).1 (e n).2) α (fun (_ : Unit) n => f (e n).1 (e n).2) := by
  refine ⟨fun _ n => hf.weight_nonneg (e n).1 (e n).2,
    fun _ n => hf.smooth (e n).1 (e n).2, ?_⟩
  intro m
  obtain ⟨C,hC,p,hp⟩ := hf.bounds m
  exact ⟨C,hC,p,fun _ n => hp (e n).1 (e n).2⟩

theorem associated_residual_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
      (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
            l))) :
    UniformHarmonicInteraction.UniformVelocity associatedStrip envelope α
      (fun l => HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput) := by
  exact MeanBoundsReindex.residualBlock_uniform_pull cycleAssoc.symm (commonContext B) x.state
    x.coefficients.blocks x.coefficients.gaussian x.coefficients.aliasCoefficients H

/-- Current source, constructed using `ParticularWaveAssembly.sourceFamily`. -/
noncomputable def currentSource (x : CycleState (Label B N0)) (j : ℤ)
    (l : Label B N0) : ℕ → Native → HarmonicCalculus.ComplexVector :=
  ParticularWaveAssembly.sourceFamily (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

theorem current_source_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
      (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)))
    (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass (CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j) := by
  have hs := ActualParticularControl.residualSource_uniform associatedStrip envelope α
    (associatedContext (B := B)) (StateReindex.state cycleAssoc.symm x.state)
    (fun l => (assembly x l).carrierBlock) (fun l => (assembly x l).gaussianInput)
    (fun l => (assembly x l).aliasInput) (fun _ => j)
    (fun i => associated_residual_class x H i j hj)
  have ht := ActualParticularControl.uniform_parameter_pull hs
    (ActualParticularControl.forgetAngle (P := Parameter))
  have he : CommonCoverClass.parameterStrip associatedStrip
      (ActualParticularControl.forgetAngle (P := Parameter)) =
      CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip) := rfl
  rw [he] at ht
  exact ht

theorem invariant_current_source_class (x : CycleState (Label B N0))
    {G : SignedMeanGain.Geometry} {primary : Label B N0 → HarmonicBlock CyclePoint} {σ : ℝ}
    {labelCarrier : Label B N0 → ℕ → Set CyclePoint}
    (H : CycleAnalyticInvariant G (commonContext B) primary meanEnvelope labelCarrier σ x)
    (hstrip : G.strip = BaseContextAssembly.nativeStrip nominal standardRegion)
    (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass (CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope (1/2+σ) (currentSource x j) := by
  apply current_source_class x _ j hj
  simpa only [hstrip] using H.residual

theorem source_angle_reindex (s : StripData Parameter) (index : ℕ → ℕ) :
    CommonCoverClass.sourceStrip
      (ActualParticularControl.angleStrip
        (UniformPrimaryWeights.reindexedStrip s (fun n => (index n, ())))) =
    UniformPrimaryWeights.reindexedStrip
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun n => (index n, ())) := rfl

theorem selected_source_class (x : CycleState (Label B N0)) {α : ℝ}
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) (e : ℕ → ActivePair B N0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
        (selectedLength e) (selectedPulseEnvelope e)) α
      (fun (_ : Unit) n => currentSource x j (selectedLabel e n) (selectedBand e n)) := by
  rw [show CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)) =
    UniformPrimaryWeights.reindexedStrip
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n => (selectedBand e n, ())) from source_angle_reindex slowStrip (selectedBand e)]
  have hw : ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
      (selectedLength e) (selectedPulseEnvelope e) =
      (fun (_ : Unit) n (z : Native) => nativeEnvelope (selectedLabel e n) (selectedBand e n) z) :=
          by
    funext u n z
    exact selected_envelope_eq e n (z.1.1,z.2)
  rw [hw]
  exact select_uniform H (fun n => (e n).val)

section ModalConstruction

variable (e : ℕ → ActivePair B N0)

/-- Selected phi, given by `ScaledActualParticularControl.physicalPhi h (selectedBand e) (fun u
n => (selectedSlot e u n).1)`. -/
noncomputable def selectedPhi := ScaledActualParticularControl.physicalPhi h
  (selectedBand e) (fun u n => (selectedSlot e u n).1)

/-- Selected chi, given by
`ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap.comp
(ContinuousLinearMap.fst ℝ Parameter ℝ)`. -/
noncomputable def selectedChi : (Parameter × ℝ) →L[ℝ] Slow :=
  ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ Parameter ℝ)

/-- Selected frame, constructed using `ActualParticularControl.nativeFrame`. -/
noncomputable def selectedFrame (n : ℕ) : PrimaryODE.FrameData ((Parameter × ℝ) × ℝ) :=
  ActualParticularControl.nativeFrame
    (ScaledActualParticularControl.frame (selectedConstruction e) (selectedPhi e)
      (selectedClock e) (selectedNormal e) ((),n)) selectedChi

/-- Selected patch, constructed using `ScaledActualParticularControl.patch`. -/
noncomputable def selectedPatch : Unit → ℕ → Frequency → Set Native :=
  ScaledActualParticularControl.patch (ActualParticularControl.angleStrip (selectedStrip e))
    (selectedConstruction e) selectedChi (selectedPhi e) (selectedClock e) (selectedGeometry e)
    (fun _ _ => slots.radius)

theorem selected_scale_le (i : Unit × ℕ) :
    (reindexDomain (jointDomain (B := B) (N0 := N0))
      (fun z : Unit × ℕ => selectedLabel e z.2)).scale i ≤ 25*(selectedStrip e).slow i.2 := by
  rw [selected_scale]
  exact ScaledActualParticularControl.active_scale_bound (selectedStrip e)
    (selectedBand e) (fun u n => (selectedSlot e u n).1) (fun n => (e n).property.1)
    (selected_near e) (fun n => le_max_right _ _) i.1 i.2

theorem selected_geometry_bound (u : Unit) (n : ℕ) :
    CommonCoverClass.argumentCost (selectedGeometry e u n) ≤
      ScaledActualParticularControl.slotCost vectors_det (selectedClock e)
        (CommonWindow.gap h + SlotColoring.nativeGap h) * (selectedStrip e).slow n^2 :=
  ScaledActualParticularControl.slot_geometry_cost slots vectors_det (selectedSlot e)
    (selectedStrip e) outgoing.data.h_pos.le (selectedClock e) (selectedGap e)
    (CommonWindow.gap h + SlotColoring.nativeGap h) (selected_gap_bound e)
    (selected_slot_large e) (fun u n => selected_scale_le e (u,n)) u n

/-- The real or imaginary control is constructed from the selected phase,
the exact clock and slot geometry, and the current residual class. -/
noncomputable def selectedControl (x : CycleState (Label B N0)) {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :=
  ScaledActualParticularControl.scaledControl
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e)
    selectedChi (selectedPhi e) (selectedClock e) (selectedNormal e)
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (fun _ _ => slots.radius)
    (ActualSignedGeometry.slowChangeCost_one h) (by norm_num : (1:ℝ) ≤ 25)
    (ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h))
    (ScaledActualParticularControl.physicalPhi_bound h (selectedBand e)
      (fun u n => (selectedSlot e u n).1) (selected_near e))
    (selected_scale_le e)
    (fun u n => by
      rw [selected_length]
      exact ActualSignedGeometry.slotGeometry_separated slots vectors_det
        outgoing.data.h_pos.le (selected_slot_large e u n) 0)
    (selected_geometry_bound e) j hj
    (fun (_ : Unit) n z => part (currentSource x j (selectedLabel e n) (selectedBand e n) z))
    ((selected_source_class x H e).map part)

theorem selected_tangent_eq (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (f : Native → ProblemStatement.Space) :
    ScaledActualParticularControl.withSource
      ((parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n)) f =
      PrimaryCopyBridge.frameTangentData (selectedFrame e n) j f := by
  have he := ScaledActualParticularControl.angle_transport_withSource
    ((selectedConstruction e).frame ((),n))
    ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
    (selectedPhi e ((),n))
    (ScaledActualParticularControl.physicalPsi h (selectedBand e)
      (fun u q => (selectedSlot e u q).1) ((),n))
    (ScaledActualParticularControl.physical_commute h (selectedBand e)
      (fun u q => (selectedSlot e u q).1) ((),n))
    (fun _ => 0) f j (selectedGap e () n) ((selectedClock e).value () n)
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q (selectedBand e n))
      (ChartScales.Q (selectedSlot e () n).1)) ((selectedNormal e).value () n)
  have ht := ScaledActualParticularControl.actualSlot_tangent_eq (selectedSlot e)
    (selectedConstruction e) outgoing.data.h_pos.le (selectedBand e) (selected_near e)
    (fun _ _ _ => 0) (selectedGap e) j hj () n
  have ha : (parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n) =
      ScaledActualParticularControl.transportedTangent (selectedConstruction e)
        ActualSignedGeometry.swapParameter.toContinuousLinearEquiv.toContinuousLinearMap
        (ScaledActualParticularControl.physicalPsi h (selectedBand e)
          (fun u q => (selectedSlot e u q).1)) (selectedClock e) (selectedNormal e)
        (fun _ _ _ => 0) (selectedGap e)
        (fun u q => PhysicalParticularWave.velocityWeight h (ChartScales.Q (selectedBand e q))
          (ChartScales.Q (selectedSlot e u q).1)) j () n := by
    dsimp only [selectedClock, selectedNormal]
    rw [ht]
    dsimp only [parameters, ParticularParameters.nativeTangent, ParticularParameters.fromReference,
      assembly, reference, PhysicalParticularWave.referenceFrequency, StateReindex.block]
    rw [hfrequency, hfrequency]
    rfl
  rw [ha]
  exact he

/-- Selected source, given by `currentSource x j (selectedLabel e n) (selectedBand e n)`. -/
noncomputable def selectedSource (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) (n : ℕ) :=
  currentSource x j (selectedLabel e n) (selectedBand e n)

/-- Selected tangent, given by `(parameters x (selectedLabel e n)).nativeTangent j (selectedBand
e n)`. -/
noncomputable def selectedTangent (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) (n : ℕ) :=
  (parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n)

/-- Selected background, constructed using `ParticularCopyBounds.reindexedBase`. -/
noncomputable def selectedBackground (x : CycleState (Label B N0)) (j : ℤ) (_ : Unit) :=
  ParticularCopyBounds.reindexedBase
    (fun l => ((parameters x l).copyData (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput
          j).background)
    (fun n => (selectedBand e n, selectedLabel e n))

/-- This is the control of the literal selected `fromReference` tangent,
after its source is overwritten by the corresponding part of the current HR source. -/
noncomputable def selectedActualControl (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (part : HarmonicCalculus.ComplexVector →L[ℝ] ProblemStatement.Space) :
    ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) α
      (fun (_ : Unit) n => selectedFrame e n)
      (fun u n => ScaledActualParticularControl.withSource (selectedTangent e x j u n)
        (fun z => part (selectedSource e x j u n z)))
      j (selectedGeometry e) (selectedLength e) (selectedPulseEnvelope e) (selectedPatch e) := by
  have he : (fun u n => ScaledActualParticularControl.withSource (selectedTangent e x j u n)
      (fun z => part (selectedSource e x j u n z))) =
      (fun (_ : Unit) n => PrimaryCopyBridge.frameTangentData (selectedFrame e n) j
        (fun z => part (selectedSource e x j () n z))) := by
    funext u n
    exact selected_tangent_eq e x hfrequency j hj n _
  rw [he]
  exact selectedControl e x j hj H part

theorem selected_inverse_frequency (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) :
    UniformPrimaryWeights.UniformBandBound
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) (1/2)
      (fun u n => 1 / (selectedBackground e x j u).frequency n) := by
  have hb := UniformPrimaryWeights.harmonic_inverse_bandBound
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
    (fun (_ : Unit) _ => j) (fun _ _ => hj)
  have he (u : Unit) (n : ℕ) : (selectedBackground e x j u).frequency n =
      (j:ℝ) * CurlClassBounds.carrierFrequency
        (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e))) n :=
            by
    change (j:ℝ) * (x.coefficients.blocks (selectedLabel e n)).frequency (selectedBand e n) = _
    rw [hfrequency]
    rfl
  simpa only [he, mul_comm] using hb

end ModalConstruction

theorem uniform_to_local {ι I X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData X} {w : ι → ℕ → X → ℝ} {f : ι → ℕ → X → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass s w α f) (C : ι → ℕ → I → Set X) :
    PeriodizedWaveBounds.UniformLocalJets s w α C (fun l n _ => f l n) := by
  refine ⟨fun l n _ z hz _ => (hf.smooth l n).contDiffAt (s.isOpen_domain.mem_nhds hz), ?_⟩
  intro m
  obtain ⟨K,hK,p,hp⟩ := hf.bounds m
  exact ⟨K,hK,p,fun l n _ z hz _ => hp l n z hz⟩

/-- The actual computed copy data, with the current residual as source. -/
noncomputable def data (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :=
  (parameters x l).copyData (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j

/-- The active phase patch includes the transverse boundary. Its time
coordinate is the actual transported clock. -/
noncomputable def controlPatch (l : Label B N0) (n : ℕ) (k : Frequency) : Set Native :=
  {z | Active l n ∧
    (z.1.1 ∈ slowStrip.domain ∧
      ActualSignedGeometry.slowChange h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2))
        (ActualSignedGeometry.swapParameter z.1.1) ∈ jointDomain.carrier l ∧
      (((canonicalParameters l).geometry n).coordinates k z.2).2 ∈
        Ioo 0 ((canonicalParameters l).length n)) ∧
    (((canonicalParameters l).geometry n).coordinates k z.2).1 ∈
      Icc (-slots.radius) slots.radius}

theorem selected_controlPatch (e : ℕ → ActivePair B N0) (u : Unit) (q : ℕ) (k : Frequency) :
    controlPatch (selectedLabel e q) (selectedBand e q) k = selectedPatch e u q k := by
  ext z
  change (Active (selectedLabel e q) (selectedBand e q) ∧ _) ↔ _
  have ha : Active (selectedLabel e q) (selectedBand e q) := (e q).property
  rw [and_iff_right ha]
  rfl

theorem selected_data_amplitude (e : ℕ → ActivePair B N0)
    (x : CycleState (Label B N0)) (j : ℤ) (u : Unit) (q : ℕ) (k : Frequency) :
    (data x (selectedLabel e q) j).amplitude (selectedBand e q) k =
      (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).amplitude q := rfl

theorem selected_data_pressure (e : ℕ → ActivePair B N0)
    (x : CycleState (Label B N0)) (j : ℤ) (u : Unit) (q : ℕ) (k : Frequency) :
    (data x (selectedLabel e q) j).pressure (selectedBand e q) k =
      (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).pressure q := rfl

section RawSelected

variable (e : ℕ → ActivePair B N0)

/-- Selected weight, constructed using `ActualParticularControl.groupedEnvelope`. -/
noncomputable def selectedWeight : Unit → ℕ → Native → ℝ :=
  ActualParticularControl.groupedEnvelope (selectedGeometry e) (fun _ _ => slots.radius)
    (selectedLength e) (selectedPulseEnvelope e)

theorem selectedWeight_nonneg (u : Unit) (n : ℕ) (z : Native) : 0 ≤ selectedWeight e u n z := by
  change 0 ≤ WaveEnvelopeTransport.copyEnvelope (selectedGeometry e u n) slots.radius
    (selectedLength e u n) (selectedPulseEnvelope e u n) z.2
  exact WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _
    (fun t => (PrimaryPulseBounds.referenceP_pos ((selectedConstruction e).lam (u,n))
      ((selectedConstruction e).u (u,n)) ((selectedConstruction e).L (u,n))
      ((selectedClock e).value u n*t)).le) _

theorem selectedWeight_eq (u : Unit) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ selectedPatch e u n k) :
    selectedWeight e u n z = selectedPulseEnvelope e u n ((selectedGeometry e u n).coordinates k
        z.2).2 :=
  ScaledActualParticularControl.patch_envelope
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e)
    selectedChi (selectedPhi e) (selectedClock e)
    (ScaledActualParticularControl.slotReference slots vectors_det (selectedSlot e))
    (selectedGap e) (fun _ _ => slots.radius)
    (fun u n => by
      rw [selected_length]
      exact ActualSignedGeometry.slotGeometry_separated slots vectors_det
        outgoing.data.h_pos.le (selected_slot_large e u n) 0) hz

theorem selected_raw_jets (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun u n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip (selectedStrip e))).zeta z) * selectedWeight e u n z)
      α (selectedPatch e)
      (fun u n k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).amplitude n) ∧
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun u n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip (selectedStrip e))).zeta z) * selectedWeight e u n z)
      (α+1/2) (selectedPatch e)
      (fun u n k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).pressure n) := by
  let f := fun u n z => ParticularWaveBounds.realPart (selectedSource e x j u n z)
  have he : ScaledParticularFrameJets.tangent (selectedConstruction e) selectedChi
      (selectedPhi e) (selectedClock e) (selectedNormal e) f j =
      fun u n => ParticularWaveBounds.realData (selectedTangent e x j u n) (selectedSource e x j u
          n) := by
    funext u n
    exact (selected_tangent_eq e x hfrequency j hj n _).symm
  have hgeo := ScaledParticularFrameJets.native_geometry_jets
    (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e) selectedChi
    (selectedPhi e) (selectedClock e) (selectedNormal e) (selectedGeometry e) (fun _ _ =>
        slots.radius)
    f j (ActualSignedGeometry.slowChangeCost_one h) (by norm_num : (1:ℝ) ≤ 25)
    (ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h))
    (ScaledActualParticularControl.physicalPhi_bound h (selectedBand e)
      (fun u n => (selectedSlot e u n).1) (selected_near e))
    (selected_scale_le e) (selected_geometry_bound e)
  rw [he] at hgeo
  have hrange (u n k z) (hz : z ∈ selectedPatch e u n k) :=
    ScaledParticularFrameJets.native_normal_bounds
      (ActualParticularControl.angleStrip (selectedStrip e)) (selectedConstruction e) selectedChi
      (selectedPhi e) (selectedClock e) (selectedNormal e) (selectedGeometry e) (fun _ _ =>
          slots.radius)
      f j hz
  simp only [he] at hrange
  exact ParticularCopyBounds.uniform_coefficients_jets
    (selectedBackground e x j) (selectedTangent e x j) (selectedSource e x j)
    (selectedGeometry e) (selectedLength e)
    (fun u n => ScaledActualParticularControl.length_pos (selectedConstruction e) (selectedClock e)
        u n)
    (selectedPulseEnvelope e) (selectedWeight e) (fun (_ : Unit) n => selectedFrame e n) j
        (selectedPatch e)
    (selectedActualControl e x hfrequency j hj H ParticularWaveBounds.realPart)
    (selectedActualControl e x hfrequency j hj H ParticularWaveBounds.imagPart)
    (fun u n z _ => selectedWeight_nonneg e u n z)
    (fun u n k z _ hz => (selectedWeight_eq e u n k hz).ge)
    hgeo.1 hgeo.2.1 hgeo.2.2
    (uniform_to_local (selected_source_class x H e) (selectedPatch e))
    (ScaledParticularFrameJets.normal_lower_pos (selectedConstruction e) (selectedNormal e))
    (fun u n k z _ hz => (hrange u n k z hz).1)
    (fun u n k z _ hz => (hrange u n k z hz).2)
    (selected_inverse_frequency e x hfrequency j hj)

end RawSelected

/-- The selector is only an indexing device. Both actual raw fields have
one bound before the original spatial label, active band, and lattice copy. -/
theorem raw_jets (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun l n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z) * nativeEnvelope l n z)
      α controlPatch (fun l => (data x l j).amplitude) ∧
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun l n z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z) * nativeEnvelope l n z)
      (α+1/2) controlPatch (fun l => (data x l j).pressure) := by
  classical
  by_cases hne : Nonempty (ActivePair B N0)
  · let : Nonempty (ActivePair B N0) := hne
    let e : ℕ → ActivePair B N0 := Classical.choose (exists_surjective_nat (ActivePair B N0))
    have he : Surjective e := Classical.choose_spec (exists_surjective_nat (ActivePair B N0))
    have hs := selected_raw_jets e x hfrequency j hj H
    have hp : (fun (_ : Unit) q k => controlPatch (selectedLabel e q) (selectedBand e q) k) =
        selectedPatch e := by
      funext u q k
      exact selected_controlPatch e u q k
    have hw : selectedWeight e =
        (fun (_ : Unit) q (z : Native) => nativeEnvelope (selectedLabel e q) (selectedBand e q) z)
            := by
      funext u q z
      exact selected_envelope_eq e q (z.1.1,z.2)
    have hstrip : CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip
        e)) =
        UniformPrimaryWeights.reindexedStrip
          (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
          (fun q => (selectedBand e q, ())) := source_angle_reindex slowStrip (selectedBand e)
    have ha : (fun (_ : Unit) q k => (data x (selectedLabel e q) j).amplitude (selectedBand e q) k)
        =
        (fun u q k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
          (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
          (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
            (selectedConstruction e) (selectedClock e) u n)).amplitude q) := by
      funext u q k
      exact selected_data_amplitude e x j u q k
    have hb : (fun (_ : Unit) q k => (data x (selectedLabel e q) j).pressure (selectedBand e q) k) =
        (fun u q k => (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
          (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
          (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
            (selectedConstruction e) (selectedClock e) u n)).pressure q) := by
      funext u q k
      exact selected_data_pressure e x j u q k
    rw [hstrip, hw, ← hp, ← ha, ← hb] at hs
    exact ⟨ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
      (fun _ _ _ _ _ hcell => hcell.1) hs.1,
      ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
        (fun _ _ _ _ _ hcell => hcell.1) hs.2⟩
  · have hempty (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native)
        (hz : z ∈ controlPatch l n k) : False := hne ⟨⟨(l,n),hz.1⟩⟩
    constructor <;> constructor
    · intro l n k z _ hz
      exact (hempty l n k z hz).elim
    · intro N
      exact ⟨0, le_rfl, 0, fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩
    · intro l n k z _ hz
      exact (hempty l n k z hz).elim
    · intro N
      exact ⟨0, le_rfl, 0, fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩

/-! The support geometry is the same canonical scalar-clock geometry. -/

/-- Support label, given by `(l.2,l.1)`. -/
noncomputable def supportLabel (l : Label B N0) : ActualCarrierTransportBase.Index B N0 :=
  (l.2,l.1)

theorem support_geometry_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.geometry (supportLabel l) n = (parameters x l).geometry n := rfl

theorem support_length_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.referenceLength (supportLabel l) /
      ActualCarrierTransportBase.clock (supportLabel l) n = (parameters x l).length n := rfl

theorem support_cutoff_eq (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ) :
    ActualCarrierTransportBase.cutoff (supportLabel l) n = (parameters x l).cutoff n := rfl

theorem copyData_ext {D I : Type} {a b : PeriodizedWaveBounds.CopyData D I}
    (hb : a.background = b.background) (ha : a.amplitude = b.amplitude)
    (hp : a.pressure = b.pressure) (hc : a.cutoff = b.cutoff) (hs : a.source = b.source) : a = b :=
        by
  cases a
  cases b
  cases hb
  cases ha
  cases hp
  cases hc
  cases hs
  rfl

theorem data_scalar_eq (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    data x l j = ScalarParticularSupport.scalarData (data x l j).background
      ((parameters x l).nativeTangent j) (currentSource x j l)
      (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
      (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
      (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
      (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l)) := by
  apply copyData_ext
  · rfl
  · rfl
  · rfl
  · funext n k z
    exact congrFun (ActualCarrierTransportBase.cutoff_eq_native (supportLabel l) n)
      ((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2)
  · rfl

/-- Carrier cells, constructed using `ScalarParticularSupport.scalarCells`. -/
noncomputable def carrierCells (l : Label B N0) : PeriodizedWaveBounds.Cells Native Frequency :=
  ScalarParticularSupport.scalarCells (P := Parameter)
    (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
    (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
    (ActualCarrierTransportBase.clock (supportLabel l))
    (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l))

theorem data_cutoff_support (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) (k : Frequency) :
    Function.support ((data x l j).cutoff n k) ⊆ (carrierCells l).carrier n k := by
  rw [data_scalar_eq x l j]
  exact ScalarParticularSupport.scalarData_cutoff_support (data x l j).background
    ((parameters x l).nativeTangent j) (currentSource x j l)
    (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
    (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
    (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
    (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l))
    (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l)) n k

/-- Input support type used in actual particular stage controls. -/
abbrev InputSupport (x : CycleState (Label B N0)) : Prop :=
  ∀ l, HarmonicSourceSupport.InputSupportOn ActualCarrierTransportBase.domain
    (ActualCarrierTransportBase.labelCarrier (supportLabel l))
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)

theorem currentSource_pull (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n : ℕ) :
    currentSource x j l n = fun z =>
      ParticularWaveAssembly.residualSource (commonContext B) x.state (x.coefficients.blocks l)
        (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j n (nativeToFull z).1 :=
            by
  funext z
  change ParticularWaveAssembly.residualSource
      (StateReindex.context cycleAssoc.symm (commonContext B)) (StateReindex.state cycleAssoc.symm
          x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
      j n (z.1.1,z.2) = _
  unfold ParticularWaveAssembly.residualSource
  rw [StateReindex.residualBlock_pull]
  rfl

/-- Actual incoming coefficient support supplies the source's zero germ
on the full slow domain; no zero-germ conclusion about the solved field is assumed. -/
theorem currentSource_zero_germ (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : Native}
    (hz : z.1.1 ∈ ActualCarrierTransportBase.parameterDomain)
    (hout : (z.1.1, z.2) ∉ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n) :
    currentSource x j l n =ᶠ[𝓝 z] fun _ => 0 := by
  have hnot : (nativeToFull z).1 ∉ ActualCarrierTransportBase.labelCarrier (supportLabel l) n := by
    intro hc
    exact hout ((ActualCarrierTransportBase.labelCarrier_iff_canonicalSourceRegion hN
      (supportLabel l) n hz z.2).mp hc)
  have he := HarmonicSourceSupport.residualSource_zero_germ_on (commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    (PhysicalMeanDomain.slowDomain_open standardRegion.isOpen)
    (fun n => ActualInitialExcluded.labelCarrier_closed l n) (hs l) j n
    (x := (nativeToFull z).1) hz hnot
  rw [currentSource_pull]
  exact he.comp_tendsto (continuous_fst.comp nativeToFull.continuous).continuousAt

/-! Actual source-carrier coverage of the analytic patch. -/

theorem native_parameter_domain {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
        :
    z.1.1 ∈ ActualCarrierTransportBase.parameterDomain :=
  ((BaseContextAssembly.nativeStrip_mem nominal standardRegion (nativeToFull z).1).mp hz).1

theorem sourceRegion_mem_controlPatch (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k)
    (hs : (z.1.1, z.2) ∈ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n) :
    z ∈ controlPatch l n k := by
  have hc : (nativeToFull z).1 ∈ ActualInitialExcluded.labelCarrier l n :=
    (ActualCarrierTransportBase.labelCarrier_iff_canonicalSourceRegion hN
      (supportLabel l) n (native_parameter_domain hz) z.2).mpr hs
  obtain ⟨q, hnear, hphase, _⟩ := ActualCarrierGeometry.labelCarrier_phaseCell hN l n
    (x := nativeToFull z) hz hc
  have hphase' : ActualSignedGeometry.slowChange h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2))
      (ActualSignedGeometry.swapParameter z.1.1) ∈ jointDomain.carrier l := hphase
  rcases hs with ⟨_, hfast⟩
  obtain ⟨k', hcoord⟩ := Set.mem_iUnion.mp hfast
  have houter : z ∈ (carrierCells l).carrier n k' :=
    ActualGaussianCoverage.sourceCell_subset_outer slots.radius_pos
      (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hcoord
  have heq : k = k' := (carrierCells l).unique n k k' z hk houter
  subst k'
  exact ⟨hnear, ⟨hz, hphase', ActualGaussianCoverage.sourceCell_time
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hcoord⟩, hcoord.1⟩

/-- Every native cell is either controlled, killed by the actual cutoff,
or has both a zero raw solve and a zero current forcing germ. -/
theorem data_control_alternative (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k) :
    z ∈ controlPatch l n k ∨
      ((data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∨
      ((data x l j).amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).pressure n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0) := by
  by_cases hsource : (z.1.1,z.2) ∈
      ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n
  · exact Or.inl (sourceRegion_mem_controlPatch hN l n k hz hk hsource)
  · right
    have he := ScalarParticularSupport.scalarData_native_zero_alternative (data x l j).background
      ((parameters x l).nativeTangent j) (currentSource x j l)
      (ActualCarrierTransportBase.geometry (supportLabel l)) (fun _ => slots.radius)
      (fun _ => ActualCarrierTransportBase.referenceLength (supportLabel l))
      (ActualCarrierTransportBase.clock (supportLabel l)) (fun _ => slots.radius_pos)
      (fun _ => ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
      (ActualCarrierTransportBase.clock_pos (supportLabel l))
      (ActualCarrierTransportBase.geometry_outer_injective (supportLabel l))
      ActualCarrierTransportBase.parameterDomain
      (ActualCarrierTransportBase.activeSlowCore (supportLabel l))
      (fun n z hz hn => currentSource_zero_germ x hs hN l j n hz hn)
      n k (native_parameter_domain hz) hk hsource
    rw [← data_scalar_eq x l j] at he
    rcases he with hcut | ⟨ha,hp⟩
    · exact Or.inl hcut
    · exact Or.inr ⟨ha,hp,currentSource_zero_germ x hs hN l j n
        (native_parameter_domain hz) hsource⟩

theorem data_control_cover (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ (carrierCells l).carrier n k) :
    z ∈ controlPatch l n k ∨
      (((data x l j).localized k).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
      (((data x l j).localized k).pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  rcases data_control_alternative x hs hN l j n k hz hk with h | hcut | ⟨ha,hp,_⟩
  · exact Or.inl h
  · exact Or.inr ((data x l j).localized_zero_germs hcut)
  · right
    refine ⟨?_, LabelSupportPreservation.localized_pressure_zero_of_raw (data x l j) hp⟩
    filter_upwards [ha] with y hy
    change (data x l j).cutoff n k y • (data x l j).amplitude n k y = 0
    rw [hy, smul_zero]

/-! The literal transported window/Gaussian product has uniform jets. -/

theorem selected_u (e : ℕ → ActivePair B N0) (u : Unit) (n : ℕ) :
    (selectedConstruction e).u (u,n) = (choice B N0).prepared.u :=
  PrimaryGeometryAssembly.construction_u certificate modulation
    (choice B N0).prepared slots.radius_pos (selectedLabel e n).1 (selectedLabel e n).2

theorem selected_cutoff_eq (e : ℕ → ActivePair B N0) (x : CycleState (Label B N0)) (j : ℤ)
    (u : Unit) (n : ℕ) (k : Frequency) :
    (data x (selectedLabel e n) j).cutoff (selectedBand e n) k =
      NativeCutoffJets.literalCutoff (selectedConstruction e) (selectedClock e) (selectedGeometry e)
        (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos) u n k := rfl

theorem selected_cutoff_jets (e : ℕ → ActivePair B N0) (x : CycleState (Label B N0)) (j : ℤ) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip e)))
      (fun _ _ _ => 1) 0 (selectedPatch e)
      (fun (_ : Unit) n k => (data x (selectedLabel e n) j).cutoff (selectedBand e n) k) := by
  have he : (fun (_ : Unit) n k => (data x (selectedLabel e n) j).cutoff (selectedBand e n) k) =
      NativeCutoffJets.literalCutoff (selectedConstruction e) (selectedClock e) (selectedGeometry e)
        (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos) := by
    funext u n k
    exact selected_cutoff_eq e x j u n k
  rw [he]
  exact NativeCutoffJets.literalCutoff_uniformLocalJets (selectedConstruction e) (selectedClock e)
    (selectedGeometry e) (fun _ _ => slots.radius) (fun _ _ => slots.radius_pos)
    (ActualParticularControl.angleStrip (selectedStrip e)) selectedChi (selectedPhi e)
    (choice B N0).prepared.u_pos (selected_u e)
    ⟨_, ScaledActualParticularControl.slotCost_one vectors_det (selectedClock e)
      (CommonWindow.gap h + SlotColoring.nativeGap h), 2, selected_geometry_bound e⟩

theorem cutoff_jets (x : CycleState (Label B N0)) (j : ℤ) :
    PeriodizedWaveBounds.UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun _ _ _ => 1) 0 controlPatch (fun l => (data x l j).cutoff) := by
  classical
  by_cases hne : Nonempty (ActivePair B N0)
  · let : Nonempty (ActivePair B N0) := hne
    let e : ℕ → ActivePair B N0 := Classical.choose (exists_surjective_nat (ActivePair B N0))
    have he : Surjective e := Classical.choose_spec (exists_surjective_nat (ActivePair B N0))
    have hj := selected_cutoff_jets e x j
    have hp : (fun (_ : Unit) q k => controlPatch (selectedLabel e q) (selectedBand e q) k) =
        selectedPatch e := by
      funext u q k
      exact selected_controlPatch e u q k
    have hstrip : CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip (selectedStrip
        e)) =
        UniformPrimaryWeights.reindexedStrip
          (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
          (fun q => (selectedBand e q, ())) := source_angle_reindex slowStrip (selectedBand e)
    rw [hstrip, ← hp] at hj
    exact ActualSignedGeometry.uniformLocalJets_of_selected_pairs _ Active e he
      (fun _ _ _ _ _ hcell => hcell.1) hj
  · have hempty (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native)
        (hz : z ∈ controlPatch l n k) : False := hne ⟨⟨(l,n),hz.1⟩⟩
    refine ⟨fun l n k z _ hz => (hempty l n k z hz).elim, fun _ => ?_⟩
    exact ⟨0,le_rfl,0,fun l n k z _ hz _ _ => (hempty l n k z hz).elim⟩

/-! Derived local background bounds and actual common-field estimates. -/

theorem canonical_geometry_eq (l : Label B N0) (n : ℕ) :
    (canonicalParameters l).geometry n =
      ActualCarrierTransportBase.geometry (supportLabel l) n := rfl

theorem control_clock (l : Label B N0) (n : ℕ) (k : Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 (ActualCarrierTransportBase.clock (supportLabel l) n)
      (((canonicalParameters l).geometry n).coordinates k Y) =
        (chartGeometry n l.1 l.2).coordinates k Y := by
  rw [canonical_geometry_eq]
  simpa only [supportLabel] using
    ActualCarrierTransportBase.coordinates_clock (supportLabel l) n k Y

theorem controlPatch_subset_padded (l : Label B N0) (n : ℕ) (k : Frequency) :
    controlPatch l n k ⊆ ParticularPaddedBackground.cells n (l,k) := by
  intro z hz
  refine ⟨hz.1, hz.2.1.2.1, ?_⟩
  simp only [ActualPrimaryBounds.fullCopy, ActualPrimaryBounds.copyPoint,
    ActualSignedGeometry.copyPoint]
  change (chartGeometry n l.1 l.2).coordinates k z.2 ∈ (clockWindow l.2).core
  rw [← control_clock]
  change _ ∈ Icc (-slots.radius) slots.radius ∧
    0 + ActualCarrierTransportBase.clock (supportLabel l) n *
      (((canonicalParameters l).geometry n).coordinates k z.2).2 ∈
        Icc 0 ((phases B N0 0).L l.2)
  refine ⟨hz.2.2, ?_⟩
  have hc := ActualCarrierTransportBase.clock_pos (supportLabel l) n
  have ht := hz.2.1.2.2
  change 0 < _ ∧ _ < ((phases B N0 l.1).L l.2) /
    ActualCarrierTransportBase.clock (supportLabel l) n at ht
  rw [length_sign l.1 l.2] at ht
  exact ⟨by simpa only [zero_add] using (mul_pos hc ht.1).le,
    by simpa only [zero_add, mul_comm] using ((lt_div_iff₀ hc).mp ht.2).le⟩

theorem local_restrict {D I E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {C K : ℕ → I → Set D} {w : ℕ → I → D → ℝ}
    {α : ℝ} {f : ℕ → I → D → E}
    (hf : LocalizedWaveBounds.LocalClass s C w α f)
    (hsub : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∈ C n i) :
    LocalizedWaveBounds.LocalClass s K w α f :=
  hf.enlarge (fun n i x hx hi => Or.inl (hsub n i x hx hi))

theorem inputs_restrict {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {C K : ℕ → I → Set D} {W : ℕ → I → D → ℝ}
    {α κ : ℝ} {d : LinearWaveBounds.GraphDirections D}
    {a : LocalizedWaveBounds.WaveFamily D I}
    (hf : LocalizedWaveBounds.InputBounds s C W α κ d a)
    (hsub : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∈ C n i) :
    LocalizedWaveBounds.InputBounds s K W α κ d a where
  loss_nonneg := hf.loss_nonneg
  radial_profile := local_restrict hf.radial_profile hsub
  radial_scale := hf.radial_scale
  fast_scale := hf.fast_scale
  frequency_scale := local_restrict hf.frequency_scale hsub
  radius := local_restrict hf.radius hsub
  inverse_radius := local_restrict hf.inverse_radius hsub
  radial_base := local_restrict hf.radial_base hsub
  frequency_base := local_restrict hf.frequency_base hsub
  axial_base := local_restrict hf.axial_base hsub
  radial_base_aux n i x hx hi := hf.radial_base_aux n i x hx (hsub n i x hx hi)
  frequency_base_aux n i x hx hi := hf.frequency_base_aux n i x hx (hsub n i x hx hi)
  axial_base_aux n i x hx hi := hf.axial_base_aux n i x hx (hsub n i x hx hi)
  normal := local_restrict hf.normal hsub
  defect := local_restrict hf.defect hsub
  amplitude j := local_restrict (hf.amplitude j) hsub
  pressure := local_restrict hf.pressure hsub

/-- Preserves carriers: an abbreviation for `∀ l, SameCarrier (x.coefficients.blocks l)
(ActualParticularBackground.primaryBlock l)`. -/
abbrev PreservesCarriers (x : CycleState (Label B N0)) : Prop :=
  ∀ l, SameCarrier (x.coefficients.blocks l) (ActualParticularBackground.primaryBlock l)

theorem preserves_frequency {x : CycleState (Label B N0)} (hx : PreservesCarriers x)
    (l : Label B N0) (n : ℕ) :
    (x.coefficients.blocks l).frequency n = ChartScales.carrier h n :=
  (congrFun (hx l).frequency n).symm

theorem data_background_eq (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :
    (data x l j).background =
      ActualParticularBackground.carrier (fun l => x.coefficients.blocks l) j l := rfl

theorem native_background_eq (x : CycleState (Label B N0)) (j : ℤ) :
    jointRawBackground (fun l => data x l j) =
      ActualParticularBackground.backgroundFamily (fun l => x.coefficients.blocks l) j := rfl

theorem actual_background_inputs (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) :
    LocalizedWaveBounds.InputBounds
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n (i : Label B N0 × Frequency) => controlPatch i.1 n i.2)
      (fun n i z => nativeEnvelope i.1 n z) 0 ChartScales.kappa (directions (B := B))
      (jointRawBackground (fun l => data x l j)) := by
  rw [native_background_eq]
  exact inputs_restrict
    (ParticularPaddedBackground.actual_background_inputs hN
      (fun l => x.coefficients.blocks l) hx j (fun n i z => nativeEnvelope i.1 n z)
      (fun n i z _ => envelope_nonneg i.1 n (z.1.1,z.2)))
    (fun n i z _ hz => controlPatch_subset_padded i.1 n i.2 hz)

theorem actual_normal_range (x : CycleState (Label B N0)) (hx : PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)).domain)
    (hk : z ∈ controlPatch l n k) :
    ActualPrimaryBounds.normalFloor B N0 ≤ ‖(data x l j).background.normal
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) (directions (B
          := B)) n z‖ ∧
    ‖(data x l j).background.normal
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) (directions (B
          := B)) n z‖ ≤
        ActualPrimaryBounds.normalCeiling B N0 := by
  exact ParticularPaddedBackground.background_normal_range
    (fun l => x.coefficients.blocks l) hx j (n := n) (i := (l,k)) (x := z)
    hz (controlPatch_subset_padded l n k hk)

theorem actual_inverse_frequency (x : CycleState (Label B N0)) (hx : PreservesCarriers x) (j : ℤ) :
    LocalizedWaveBounds.LocalUnweighted
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun n (i : Label B N0 × Frequency) => controlPatch i.1 n i.2) (1/2)
      (fun n i (_ : Native) => 1/(data x i.1 j).background.frequency n) := by
  exact local_restrict
    (ParticularPaddedBackground.background_inverse_frequency (fun l => x.coefficients.blocks l) hx
        j)
    (fun n i z _ hz => controlPatch_subset_padded i.1 n i.2 hz)

theorem common_bounds (x : CycleState (Label B N0)) (hx : PreservesCarriers x)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j)) :
    let s := CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)
    LabelSumBounds.UniformWaveClass s nativeEnvelope α (fun l => (data x l j).common.amplitude) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope α
      (fun l => ((data x l j).commonCorrected s (directions (B := B))).amplitude) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2) (fun l => (data x l
        j).common.pressure) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2-ChartScales.kappa)
      (fun l => (data x l j).common.curlCorrection s (directions (B := B))) ∧
    LabelSumBounds.UniformWaveClass s nativeEnvelope (α+1/2-3*ChartScales.kappa)
      (fun l => (data x l j).globalGood s (directions (B := B))) := by
  have hr := raw_jets x (preserves_frequency hx) j hj H
  exact uniform_common_bounds_from_raw (fun l => data x l j) carrierCells
    (fun l n k => data_cutoff_support x l j n k)
    (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (actual_background_inputs x hx hN j) hr.1 hr.2 (cutoff_jets x j)
    (by norm_num [ChartScales.kappa]) (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun l n k z hz hk => (actual_normal_range x hx l j n k hz hk).1)
    (fun l n k z hz hk => (actual_normal_range x hx l j n k hz hk).2)
    (actual_inverse_frequency x hx j)
    (fun l n k z hz hk => data_control_cover x hs hN l j n k hz hk)

/-! The exact moving weight, finite harmonic assembly, and invariant interface. -/

theorem meanEnvelope_eq_primary (l : Label B N0) (n : ℕ) (z : CyclePoint) :
    meanEnvelope l n z = ActualPrimaryBounds.meanEnvelope l n z := rfl

theorem nativeEnvelope_le_one (l : Label B N0) (n : ℕ) (z : Native) :
    nativeEnvelope l n z ≤ 1 :=
  ActualPrimaryBounds.fullEnvelope_le_one l n (nativeToFull z)

theorem native_wave_to_weighted {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : Label B N0 → ℕ → Native → E}
    (hf : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)) nativeEnvelope
          α f) :
    LabelSumBounds.UniformClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      (fun _ _ z => Real.sqrt ((CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip slowStrip)).zeta z)) α f :=
  hf.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun l n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (nativeEnvelope_le_one l n z))

/-- Residual bounds type used in actual particular stage controls. -/
abbrev ResidualBounds (x : CycleState (Label B N0)) (α : ℝ) : Prop :=
  UniformHarmonicInteraction.UniformVelocity
    (BaseContextAssembly.nativeStrip nominal standardRegion) meanEnvelope α
    (fun l => HarmonicResidual.residualBlock (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))

/-- Associated update as an element of `HarmonicBlock (Parameter × Plane)`. -/
noncomputable def associatedUpdate (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock (Parameter × Plane) :=
  (parameters x l).updateBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

/-- Associated good as an element of `HarmonicBlock (Parameter × Plane)`. -/
noncomputable def associatedGood (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock (Parameter × Plane) :=
  (parameters x l).goodBlock associatedStrip (assembly x l).context (assembly x l).state
    (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput N

theorem associated_assembled_bounds (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (H : ResidualBounds x α) (N : ℕ) :
    (∀ i j, LabelSumBounds.UniformWaveClass associatedStrip envelope α
      (fun l n z => (associatedUpdate x N l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass associatedStrip envelope (α+1/2)
      (fun l n z => (associatedUpdate x N l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass associatedStrip envelope (α+1/2-3*ChartScales.kappa)
      (fun l n z => (associatedGood x N l).velocity n i j z)) := by
  have hm (j : ℤ) (hj : j ∈ ParticularWaveAssembly.modes N) :=
    common_bounds x hx hs hN j ((ParticularWaveAssembly.mem_modes N j).mp hj).1
      (current_source_class x H j ((ParticularWaveAssembly.mem_modes N j).mp hj).1)
  exact ParticularParameters.uniform_assembled_bounds (fun l => parameters x l)
    associatedStrip (associatedContext (B := B)) (StateReindex.state cycleAssoc.symm x.state)
    (fun l => StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (fun l => StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (fun l => StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
    N (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (fun j hj => (hm j hj).2.1) (fun j hj => (hm j hj).2.2.1)
    (fun j hj => (hm j hj).2.2.2.2)

/-- Output block, given by `StateReindex.block cycleAssoc (associatedUpdate x N l)`. -/
noncomputable def outputBlock (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock CyclePoint := StateReindex.block cycleAssoc (associatedUpdate x N l)

/-- Output good, given by `StateReindex.block cycleAssoc (associatedGood x N l)`. -/
noncomputable def outputGood (x : CycleState (Label B N0)) (N : ℕ) (l : Label B N0) :
    HarmonicBlock CyclePoint := StateReindex.block cycleAssoc (associatedGood x N l)

theorem associated_wave_return {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : Label B N0 → ℕ → Parameter × Plane → E}
    (hf : LabelSumBounds.UniformWaveClass associatedStrip envelope α f) :
    LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope α (fun l n z => f l n (cycleAssoc z)) := by
  exact MeanBoundsReindex.uniformClass_return cycleAssoc hf

/-- The finite harmonic assembly and coordinate association retain
constants chosen before the spatial label and band. -/
theorem assembled_bounds (x : CycleState (Label B N0))
    (hx : PreservesCarriers x) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (H : ResidualBounds x α) (N : ℕ) :
    (∀ i j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope α (fun l n z => (outputBlock x N l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope (α+1/2) (fun l n z => (outputBlock x N l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (BaseContextAssembly.nativeStrip nominal standardRegion)
      meanEnvelope (α+1/2-3*ChartScales.kappa)
      (fun l n z => (outputGood x N l).velocity n i j z)) := by
  obtain ⟨ha,hp,hg⟩ := associated_assembled_bounds x hx hs hN H N
  exact ⟨fun i j => associated_wave_return (ha i j),
    fun j => associated_wave_return (hp j), fun i j => associated_wave_return (hg i j)⟩

/-- The quantitative inputs are precisely fields of the current analytic
invariant. The geometric equalities identify its actual strip and carrier. -/
theorem invariant_assembled_bounds (x : CycleState (Label B N0))
    {G : SignedMeanGain.Geometry} {σ : ℝ}
    (H : CycleAnalyticInvariant G (commonContext B) ActualParticularBackground.primaryBlock
      meanEnvelope (fun l => ActualCarrierTransportBase.labelCarrier (supportLabel l)) σ x)
    (hstrip : G.strip = BaseContextAssembly.nativeStrip nominal standardRegion)
    (hdomain : G.domain = ActualCarrierTransportBase.domain)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    (∀ i j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1/2+σ)
      (fun l n z => (outputBlock x x.coefficients.residualBand l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1+σ)
      (fun l n z => (outputBlock x x.coefficients.residualBand l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass G.strip meanEnvelope (1+σ-3*ChartScales.kappa)
      (fun l n z => (outputGood x x.coefficients.residualBand l).velocity n i j z)) := by
  have hs : InputSupport x := by
    intro l
    simpa only [hdomain] using H.inputSupport l
  have hr : ResidualBounds x (1/2+σ) := by
    simpa only [hstrip] using H.residual
  have hout := assembled_bounds x H.carrier hs hN hr x.coefficients.residualBand
  have hα : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  simpa only [hstrip, hα] using hout

end NavierStokes.ActualParticularStageControls
