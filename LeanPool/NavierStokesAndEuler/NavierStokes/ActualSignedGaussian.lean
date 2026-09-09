/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialExcluded
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds

/-!
# Gaussian cutoff errors of the actual signed correction

The transverse cutoff and the Gaussian cutoff remain in the literal
native cutoff.  The transverse factor has zero fast derivative.  Thus
the actual error vanishes on the central Gaussian plateau and retains
the exact square-root edge weight at every decay exponent.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedGaussian

open Set Function Filter WeightedClasses CorrectionInitialization
open ActualSignedStageControls
open scoped ContDiff Topology BigOperators


variable {B N0 : ℕ}

/-- Copies, given by `(parameters l).copyData ActualPrimaryBounds.strip request`. -/
noncomputable def copies (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) : PeriodizedWaveBounds.CopyData FullPoint Frequency :=
  (parameters l).copyData ActualPrimaryBounds.strip request

/-- Local gaussian, given by `(copies request l).localGaussian (directions B) n k`. -/
noncomputable def localGaussian (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) : FullPoint → HarmonicCalculus.ComplexVector :=
  (copies request l).localGaussian (directions B) n k

theorem source_zero (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (l : SignedLabel B N0) :
    (copies request l).source = fun _ _ => 0 := rfl

theorem localGaussian_formula (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    localGaussian request l n k x =
      (directions B).Dfast (cutoff l k) n x • (copies request l).amplitude n k x := by
  unfold localGaussian
  rw [PeriodizedWaveBounds.CopyData.localGaussian_eq]
  change _ + (1 - cutoff l k n x) • (0 : HarmonicCalculus.ComplexVector) = _
  simp only [smul_zero, add_zero]
  rfl

/-- Transverse, given by `PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l
n k x).2.1`. -/
noncomputable def transverse (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : ℝ :=
  PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1

theorem transverse_smooth (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ (transverse l k n) :=
  (SquaredPartition.gridMask_smooth ActualPrimary.slots.radius 0).comp
    (nativePoint_smooth l n k).snd.fst

/-- Only the native clock changes along the fast direction. -/
theorem transverse_fast_zero (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    (directions B).Dfast (transverse l k) n x = 0 := by
  have hd : HasDerivAt (fun _ : ℝ =>
      PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1)
      0 (nativePoint l n k x).2.2 := hasDerivAt_const _ _
  have h := ActualPrimaryDynamics.along_copy l.2 l.1 n k
    (fun y => PartitionedCovariance.cutoff ActualPrimary.slots.radius y.2.1) hd
    ((transverse_smooth l n k).differentiable (by simp)).differentiableAt
  simp only [smul_zero] at h
  exact h

/-- The product cutoff is differentiated literally. The transverse
derivative term vanishes; no cutoff factor is silently moved into the mask. -/
theorem cutoff_fast (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    (directions B).Dfast (cutoff l k) n x =
      transverse l k n x * (directions B).Dfast
        (fun m y => GaussianTailFlat.profile (nativeTime l m k y)) n x := by
  have ht := ((transverse_smooth l n k).differentiable (by simp)).differentiableAt (x := x)
  have hg := ((GaussianTailFlat.profile_contDiff.comp (nativeTime_smooth l n k)).differentiable
    (by simp)).differentiableAt (x := x)
  simp only [Function.comp_def] at hg
  have hz := transverse_fast_zero l n k x
  change fderiv ℝ (transverse l k n) x ((directions B).fastField n x) = 0 at hz
  change fderiv ℝ (fun y => transverse l k n y * GaussianTailFlat.profile (nativeTime l n k y))
    x ((directions B).fastField n x) =
      transverse l k n x * fderiv ℝ (fun y => GaussianTailFlat.profile (nativeTime l n k y))
        x ((directions B).fastField n x)
  rw [fderiv_fun_mul ht hg]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hz]
  ring

/-- The central Gaussian plateau kills the actual error even when the
transverse cutoff is strictly between zero and one. -/
theorem localGaussian_zero_plateau (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hm : |nativeTime l n k x - 1 / 2| < 1 / 5) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  have hg := (GaussianTailFlat.profile_eventually_one hm).comp_tendsto
    (nativeTime_smooth l n k).continuous.continuousAt.tendsto
  have hc : cutoff l k n =ᶠ[𝓝 x] transverse l k n := by
    filter_upwards [hg] with y hy
    change GaussianTailFlat.profile (nativeTime l n k y) = 1 at hy
    change transverse l k n y * GaussianTailFlat.profile (nativeTime l n k y) = transverse l k n y
    rw [hy, mul_one]
  have hd := ParticularWaveAssembly.along_germ hc ((directions B).fastField n)
  filter_upwards [hd] with y hy
  rw [localGaussian_formula]
  change HarmonicCalculus.along ((directions B).fastField n) (cutoff l k n) y • _ = 0
  rw [hy]
  change (directions B).Dfast (transverse l k) n y • _ = 0
  rw [transverse_fast_zero, zero_smul]

theorem localGaussian_zero_of_cutoff (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hz : cutoff l k n =ᶠ[𝓝 x] fun _ => 0) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 :=
  LocalizedGaussianBounds.localGaussian_zero_of_cutoff_source (copies request l) (directions B)
    hz (Filter.Eventually.of_forall (fun _ => rfl))

theorem localGaussian_zero_of_mask (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hz : mask l k n =ᶠ[𝓝 x] fun _ => 0) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  have ha : (copies request l).amplitude n k =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hz] with y hy
    exact ((parameters l).raw_zero_of_mask request n k y hy).1
  exact (copies request l).localGaussian_zero_of_fields (directions B) ha
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem localGaussian_zero_outside_phaseCell (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∉ phaseCell l n k) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  rcases ActualWaveRegularityData.signed_phaseCell_or_zero l n k hx with h | h | h
  · exact (hc h).elim
  · exact localGaussian_zero_of_cutoff request l h
  · exact localGaussian_zero_of_mask request l h

/-- Band scales, bundling `power`, `epsilon_eq`, `boundConstant`, `constant_one_le` and the
required compatibility proofs. -/
noncomputable def bandScales : GaussianTailFlat.BandScaleControl fullStrip where
  power := ActualPrimary.h
  epsilon_eq := fun _ => rfl
  boundConstant := 1
  constant_one_le := le_rfl
  degree := 1
  slow_le := fun n => by
    change max 1 (ChartScales.S n) ≤ 1 * (1 + ChartScales.S n) ^ 1
    simp only [pow_one, one_mul]
    have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
    exact max_le (by linarith) (by linarith)

theorem envelope_gaussian (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hc : x ∈ phaseCell l n k) :
    envelope l n x ≤ Real.exp (-ActualInitialExcluded.gaussianRate B N0 *
      (nativeTime l n k x - 1 / 2)^2 * ActualInitialExcluded.gaussianLength (l.2,l.1) n) := by
  have he : envelope l n x = ActualPrimaryBounds.pulseEnvelope (l.2,l.1)
      (ActualPrimaryBounds.fullCopy (l.2,l.1) n k x).2.2 :=
    ActualPrimaryBounds.envelope_copy (l.2,l.1) n k hc.1.2.2.1
  rw [he, ActualInitialExcluded.gaussianLength_eq (l.2,l.1) n hc.1.1]
  have hh := ActualInitialExcluded.nativeEnvelope_gaussian (l.2,l.1) hc.1.2.2.1.2
  simp only [nativeTime, nativePoint_eq_fullCopy l n k hc.1.1] at hh ⊢
  exact hh

/-! ## Uniform Gaussian absorption with the edge weight retained -/

theorem localGaussian_wave_jets {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    LocalizedWaveBounds.LocalWave fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => phaseCell i.1 n i.2)
      (fun n i x => envelope i.1 n x) (σ + 1 / 2)
      (fun n i => localGaussian request i.1 n i.2) := by
  have hw : ∀ l n x, x ∈ fullStrip.domain →
      0 ≤ Real.sqrt (fullStrip.zeta x) * envelope (B := B) (N0 := N0) l n x :=
    fun l n x _ => mul_nonneg (Real.sqrt_nonneg _)
      (ActualPrimaryBounds.fullEnvelope_nonneg (l.2,l.1) n x)
  have hu := LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw
    (raw_coefficients_jets hR).1
  have hψ := LocalizedWaveBounds.LocalClass.of_uniformLocalJets
    (fun _ _ _ _ => zero_le_one) (cutoff_local_jets (B := B) (N0 := N0))
  have hf : LocalizedWaveBounds.LocalWave fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => phaseCell i.1 n i.2)
      (fun n i x => envelope i.1 n x) (σ + 1 / 2)
      (fun _ _ (_ : FullPoint) => (0 : HarmonicCalculus.ComplexVector)) :=
    LocalizedWaveBounds.LocalClass.zero (fun n i x hx => hw i.1 n x hx)
  have hfast : BandBound fullStrip 0 (directions B).fastScale :=
    (ActualPrimaryBounds.actual_local_inputs (B := B) (N0 := N0)).fast_scale
  exact LocalizedGaussianBounds.indexedCutoffError_wave_class (directions B) hψ hfast hu hf

/-- All joint jets of the literal local Gaussian error have every
epsilon exponent, with exactly the square-root edge weight. -/
theorem localGaussian_all_gains {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun l : SignedLabel B N0 => (cells l).carrier)
      (fun l n k => localGaussian request l n k) := by
  have hflat := ActualGaussianCoverage.indexed_gaussian_weighted_all_gains
    (localGaussian_wave_jets hR) bandScales
    (fun n i x => nativeTime i.1 n i.2 x)
    (fun n i => ActualInitialExcluded.gaussianLength (i.1.2,i.1.1) n)
    (fun n i => ActualInitialExcluded.gaussianLength_pos (i.1.2,i.1.1) n)
    ActualInitialExcluded.gaussianLengthLower ActualInitialExcluded.gaussianLengthLower_pos
    (fun _ _ => le_max_right _ _) (ActualInitialExcluded.gaussianRate_pos B N0)
    (fun n i _ _ hi => envelope_gaussian i.1 n i.2 hi)
    (fun n i _ _ _ hm => localGaussian_zero_plateau request i.1 n i.2 hm) β
  have hlarge : LocalizedWaveBounds.LocalClass fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => (cells i.1).carrier n i.2)
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun n i => localGaussian request i.1 n i.2) := by
    apply hflat.enlarge
    intro n i x hx _
    by_cases hc : x ∈ phaseCell i.1 n i.2
    · exact Or.inl hc
    · exact Or.inr (localGaussian_zero_outside_phaseCell request i.1 n i.2 hx hc)
  exact hlarge.to_uniformLocalJets

/-- Global gaussian, given by `(copies request l).globalGaussian (directions B)`. -/
noncomputable def globalGaussian (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) : ℕ → FullPoint → HarmonicCalculus.ComplexVector :=
  (copies request l).globalGaussian (directions B)

/-- The actual periodized Gaussian coefficient, including its source
complement, has the exact weighted class. The signed source is identically zero. -/
theorem globalGaussian_all_gains {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) :
    LabelSumBounds.UniformClass fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (globalGaussian (B := B) (N0 := N0) request) := by
  have hf : LocalizedGaussianBounds.UniformComplementJets fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun l : SignedLabel B N0 => (cells l).carrier)
      (fun l => (copies request l).source) :=
    LocalizedGaussianBounds.UniformComplementJets.of_zero_germs fullStrip _ β _ _
      (fun _ _ _ _ _ => Filter.Eventually.of_forall (fun _ => rfl))
  exact LocalizedGaussianBounds.uniform_globalGaussian_class_with_complement
    (copies request) cells (fun l n k => cutoff_support l n k) (directions B)
    (fun _ _ _ _ => Real.sqrt_nonneg _) (localGaussian_all_gains hR β) hf

/-- This is the precise Fourier-coefficient class required by the signed
Gaussian field of `CorrectionAnalyticStep.WaveData`. -/
theorem gaussianBlock_jets {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass ActualPrimaryBounds.strip
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) β
      (fun l : SignedLabel B N0 => fun n x =>
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).velocity n i j x) := by
  have hg : LabelSumBounds.UniformClass
      (HarmonicWaveInteraction.productStrip ActualPrimaryBounds.strip)
      (fun (_ : SignedLabel B N0) (_ : ℕ) (x : FullPoint) =>
        Real.sqrt (ActualPrimaryBounds.strip.zeta x.1)) β
      (globalGaussian request) := globalGaussian_all_gains hR β
  have hs := UniformBlockBounds.uniform_slice
    (s := ActualPrimaryBounds.strip)
    (w := fun (_ : SignedLabel B N0) (_ : ℕ) (x : Point) =>
      Real.sqrt (ActualPrimaryBounds.strip.zeta x)) hg
  have hi := hs.map (ContinuousLinearMap.proj i)
  exact UniformBlockBounds.pair_uniform hi 1 j

/-- Actual current residuals and primitive identities supply the request
jet premise; no signed Gaussian output estimate is an input. -/
theorem actual_gaussianBlock_jets (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass ActualPrimaryBounds.strip
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) β
      (fun l : SignedLabel B N0 => fun n x =>
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip
          (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)).velocity n i j x) := by
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  exact gaussianBlock_jets hr' β i j

end NavierStokes.ActualSignedGaussian
