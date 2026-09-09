/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveAssembly

@[expose] public section

/-!
# Local background bounds for the actual particular harmonics

The fixed harmonic changes the frequency.  Its phase is the same primary
phase, including the free angular variable.  All primitive bounds are pulled
from the actual primary inputs on the same closed support cells.
-/

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

abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
abbrev CopyIndex (B N0 : ℕ) := ActualPrimaryBounds.CopyIndex B N0
abbrev Parameter := CorrectionStep.CycleSlow
abbrev Native := (Parameter × ℝ) × TorusInverse.Plane

noncomputable def nativeToFull : Native ≃ₗᵢ[ℝ] ActualPrimary.FullPoint :=
  ParticularWaveAssembly.angleShuffle.symm.trans (StateReindex.cylinder cycleAssoc.symm)

noncomputable def nativeStrip : StripData Native :=
  ParticularWaveBounds.reindexStrip nativeToFull ActualPrimaryBounds.fullStrip

noncomputable def cells {B N0 : ℕ} (n : ℕ) (i : CopyIndex B N0) : Set Native :=
  nativeToFull ⁻¹' ActualPrimaryBounds.controlCell n i

noncomputable def directions (B : ℕ) : GraphDirections Native :=
  ParticularWaveBounds.reindexDirections nativeToFull (ActualPrimaryBounds.directions B)

noncomputable def primaryBlock {B N0 : ℕ} (l : Label B N0) : HarmonicBlock CyclePoint :=
  (ActualPrimary.piece ActualPrimary.standardRegion l.1 l.2).tangentBlock
    (fun n z => (ActualPrimary.chartCoefficients l.1 l.2).phase n (z, 0))
    (fun _ => PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 l.2)

noncomputable def carrier {B N0 : ℕ} (b : Label B N0 → HarmonicBlock CyclePoint)
    (j : ℤ) (l : Label B N0) : WaveCoefficients Native :=
  ParticularWaveAssembly.actualCarrier
    (ParticularWaveBounds.reindexCoefficients nativeToFull (ActualPrimary.chartCoefficients l.1
      l.2))
    (StateReindex.block cycleAssoc.symm (b l)) j

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
