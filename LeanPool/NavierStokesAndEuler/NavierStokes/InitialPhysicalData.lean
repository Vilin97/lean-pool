/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryDynamics
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseJetBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCarrierGeometry
import LeanPool.NavierStokesAndEuler.NavierStokes.InitialNativeRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds

/-!
# The actual initial primary potential and its physical copies

Every field below uses the fixed `ActualPrimary.choice B N0`.  The
normal-potential operator is applied to the actual cutoff amplitude; its
estimates are obtained from the existing support-local primitive controls.
The lattice index is retained through Cartesian realization.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.InitialPhysicalData

open Set Function Filter WeightedClasses HarmonicCalculus
open CorrectionInitialization ActualPrimaryBounds
open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable

/-- Point: an abbreviation for `ActualPrimary.FullPoint`. -/
abbrev Point := ActualPrimary.FullPoint
/-- Signed label: an abbreviation for `ActualPrimaryBounds.SignedLabel B N0`. -/
abbrev SignedLabel (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency

section NativePotential

variable {B N0 : ℕ}

/-- The coefficient of the genuine vector potential, before restoring
its carrier.  The Gaussian cutoff occurs in `cutCoefficients` once. -/
noncomputable def potentialCoefficient (l : SignedLabel B N0) (n : ℕ) (x : Point) :
    ComplexVector :=
  CurlClassBounds.inverseCarrier ((cutCoefficients l).frequency n) •
    CurlClassBounds.normalCoefficient
      ((cutCoefficients l).normal fullStrip (directions B) n x)
      ((cutCoefficients l).amplitude n x)

theorem potentialCoefficient_zero (l : SignedLabel B N0) (n : ℕ) (x : Point)
    (ha : (cutCoefficients l).amplitude n x = 0) :
    potentialCoefficient l n x = 0 := by
  simp [potentialCoefficient, CurlClassBounds.normalCoefficient,
    CurlClassBounds.normalCross, ha]

theorem potentialCoefficient_zero_germ (l : SignedLabel B N0) (n : ℕ) {x : Point}
    (ha : (cutCoefficients l).amplitude n =ᶠ[𝓝 x] fun _ => 0) :
    potentialCoefficient l n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ha] with y hy
  exact potentialCoefficient_zero l n y hy

theorem potentialCoefficient_local :
    LocalizedWaveBounds.LocalWave fullStrip (controlCell (B := B) (N0 := N0))
      (fun n i => fullEnvelope i.1 n) 1
      (fun n i => potentialCoefficient i.1 n) := by
  have hc := (actual_local_inputs (B := B) (N0 := N0)).normalCoefficient_class
    (normalFloor_pos B N0)
    (fun _ _ _ hx hi => (actualFamily_normal_range hx hi).1)
    (fun _ _ _ hx hi => (actualFamily_normal_range hx hi).2)
  have hs := (LocalizedWaveBounds.unweighted_smul
    (inverse_carrier_local (B := B) (N0 := N0)) hc).map
      (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)
  have he : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [he] at hs
  apply hs.congr
  intro n i x
  ext j
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, potentialCoefficient,
    CurlClassBounds.inverseCarrier]
  change Complex.I * (((1 / (((cutCoefficients i.1).frequency n : ℝ)) : ℝ) : ℂ) * _) =
    (Complex.I / (((cutCoefficients i.1).frequency n : ℝ) : ℂ)) * _
  simp only [actualFamily, LocalizedWaveBounds.WaveFamily.normal,
    LocalizedWaveBounds.WaveFamily.coefficients,
    LocalizedWaveBounds.WaveFamily.ofCoefficients, LinearWaveBounds.WaveCoefficients.normal]
  push_cast
  ring

/-- Uniformity is over the entire signed label family.  On the complement
of the genuine phase patches the actual amplitude has a zero germ. -/
theorem potentialCoefficient_uniform :
    LabelSumBounds.UniformWaveClass fullStrip (fullEnvelope (B := B) (N0 := N0)) 1
      potentialCoefficient := by
  have hj : PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * fullEnvelope l n x) 1
      (fun (l : SignedLabel B N0) n k => controlCell n (l, k))
      (fun l n _k => potentialCoefficient l n) :=
    potentialCoefficient_local.to_uniformLocalJets
  apply PeriodizedWaveBounds.uniformClass_of_local_germs
    (fun l n x _ => mul_nonneg (Real.sqrt_nonneg _) (fullEnvelope_nonneg l n x)) hj
  intro l n x hx
  rcases actual_input_cover l n hx with ⟨k, hk⟩ | ⟨ha, _⟩
  · exact Or.inl ⟨k, hk, Filter.EventuallyEq.rfl⟩
  · exact Or.inr (potentialCoefficient_zero_germ l n ha)

end NativePotential

section GermBounds

variable {D E I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : StripData D} {w : I → ℕ → D → ℝ} {α : ℝ}
  {f0 g0 : I → ℕ → D → E}

/-- A supported copy inherits the same constants when it is locally
equal to the full coefficient or to zero. -/
theorem uniform_of_germ_or_zero (hf : LabelSumBounds.UniformClass s w α f0)
    (hg : ∀ i n x, x ∈ s.domain →
      (g0 i n =ᶠ[𝓝 x] f0 i n) ∨ (g0 i n =ᶠ[𝓝 x] fun _ => 0)) :
    LabelSumBounds.UniformClass s w α g0 := by
  refine ⟨hf.weight_nonneg, ?_, ?_⟩
  · intro i n x hx
    rcases hg i n x hx with he | he
    · exact (((hf.smooth i n).contDiffAt (s.isOpen_domain.mem_nhds hx)).congr_of_eventuallyEq
        he).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro i n x hx j hj
    rcases hg i n x hx with he | he
    · rw [PeriodizedWaveBounds.jets_eq_of_germ he j]
      exact hb i n x hx j hj
    · simp only [PeriodizedWaveBounds.jets_eq_of_germ he j,
        iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact majorant_nonneg s (w i) α hC p n x (hf.weight_nonneg i n x hx)

end GermBounds

section NativeCopies

variable {B N0 : ℕ}

/-- Copy amplitude, given by `copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n
k (nativeOfFull x)`. -/
noncomputable def copyAmplitude (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : ComplexVector :=
  copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n k (nativeOfFull x)

/-- Copy pressure coefficient, given by `copied (2 * CoordinateAlgebra.A ActualPrimary.h)
cutNativePressure l n k (nativeOfFull x)`. -/
noncomputable def copyPressureCoefficient (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : ℂ :=
  copied (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n k (nativeOfFull x)

/-- Copy potential coefficient, constructed using `CurlClassBounds.inverseCarrier`. -/
noncomputable def copyPotentialCoefficient (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : ComplexVector :=
  CurlClassBounds.inverseCarrier ((cutCoefficients l).frequency n) •
    CurlClassBounds.normalCoefficient
      ((cutCoefficients l).normal fullStrip (directions B) n x)
      (copyAmplitude l k n x)

theorem copyAmplitude_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hx : x ∈ fullStrip.domain) (hk : nativeOfFull x ∈ (copyCells l).carrier n k) :
    copyAmplitude l k n =ᶠ[𝓝 x] (cutCoefficients l).amplitude n := by
  have he := (PeriodizedWaveBounds.copySum_germ (copyCells l) n
    (copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n)
    (copied_support _ _ cut_native_velocity_support l n) hk).comp_tendsto
      nativeOfFull.continuous.continuousAt
  exact ((cut_amplitude_germ l n hx).trans he).symm

theorem copyAmplitude_zero_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hk : nativeOfFull x ∉ (copyCells l).carrier n k) :
    copyAmplitude l k n =ᶠ[𝓝 x] fun _ => 0 :=
  (PeriodizedWaveBounds.zero_germ_of_support ((copyCells l).closed n k)
    (copied_support _ _ cut_native_velocity_support l n k) hk).comp_tendsto
      nativeOfFull.continuous.continuousAt

theorem copyPotential_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hx : x ∈ fullStrip.domain) (hk : nativeOfFull x ∈ (copyCells l).carrier n k) :
    copyPotentialCoefficient l k n =ᶠ[𝓝 x] potentialCoefficient l n := by
  filter_upwards [copyAmplitude_germ l k n hx hk] with y hy
  simp only [copyPotentialCoefficient, potentialCoefficient, hy]

theorem copyPotential_zero_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hk : nativeOfFull x ∉ (copyCells l).carrier n k) :
    copyPotentialCoefficient l k n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [copyAmplitude_zero_germ l k n hk] with y hy
  simp [copyPotentialCoefficient, CurlClassBounds.normalCoefficient,
    CurlClassBounds.normalCross, hy]

theorem copyPressure_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hx : x ∈ fullStrip.domain) (hk : nativeOfFull x ∈ (copyCells l).carrier n k) :
    copyPressureCoefficient l k n =ᶠ[𝓝 x] (cutCoefficients l).pressure n := by
  have he := (PeriodizedWaveBounds.copySum_germ (copyCells l) n
    (copied (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n)
    (copied_support _ _ cut_native_pressure_support l n) hk).comp_tendsto
      nativeOfFull.continuous.continuousAt
  exact ((cut_pressure_germ l n hx).trans he).symm

theorem copyPressure_zero_germ (l : SignedLabel B N0) (k : Frequency) (n : ℕ) {x : Point}
    (hk : nativeOfFull x ∉ (copyCells l).carrier n k) :
    copyPressureCoefficient l k n =ᶠ[𝓝 x] fun _ => 0 :=
  (PeriodizedWaveBounds.zero_germ_of_support ((copyCells l).closed n k)
    (copied_support _ _ cut_native_pressure_support l n k) hk).comp_tendsto
      nativeOfFull.continuous.continuousAt

theorem copyPotential_uniform :
    LabelSumBounds.UniformWaveClass fullStrip
      (fun i : SignedLabel B N0 × Frequency => fullEnvelope i.1) 1
      (fun i => copyPotentialCoefficient i.1 i.2) := by
  apply uniform_of_germ_or_zero (potentialCoefficient_uniform.reindex Prod.fst)
  intro i n x hx
  by_cases hk : nativeOfFull x ∈ (copyCells i.1).carrier n i.2
  · exact Or.inl (copyPotential_germ i.1 i.2 n hx hk)
  · exact Or.inr (copyPotential_zero_germ i.1 i.2 n hk)

theorem copyPressure_uniform :
    LabelSumBounds.UniformWaveClass fullStrip
      (fun i : SignedLabel B N0 × Frequency => fullEnvelope i.1) 1
      (fun i => copyPressureCoefficient i.1 i.2) := by
  apply uniform_of_germ_or_zero (chart_cut_pressure_uniform.reindex Prod.fst)
  intro i n x hx
  by_cases hk : nativeOfFull x ∈ (copyCells i.1).carrier n i.2
  · exact Or.inl (copyPressure_germ i.1 i.2 n hx hk)
  · exact Or.inr (copyPressure_zero_germ i.1 i.2 n hk)

end NativeCopies

section Labels

variable {B N0 : ℕ}

/-- Band label, given by `⟨spatialLabel l, label_large l⟩`. -/
noncomputable def bandLabel (l : SignedLabel B N0) : PhysicalWaveSum.BandLabel :=
  ⟨spatialLabel l, label_large l⟩

theorem bandLabel_injective : Function.Injective (bandLabel (B := B) (N0 := N0)) := by
  intro l m he
  exact ActualCarrierGeometry.signedLabel_injective (congrArg Subtype.val he)

/-- Active, given by `Set.range (bandLabel (B := B) (N0 := N0))`. -/
noncomputable def active : Set PhysicalWaveSum.BandLabel := Set.range (bandLabel (B := B) (N0 :=
    N0))

/-- Selected, given by `hL.choose`. -/
noncomputable def selected (L : PhysicalWaveSum.BandLabel) (hL : L ∈ active (B := B) (N0 := N0)) :
    SignedLabel B N0 := hL.choose

theorem selected_label (L : PhysicalWaveSum.BandLabel) (hL : L ∈ active (B := B) (N0 := N0)) :
    bandLabel (selected L hL) = L := hL.choose_spec

theorem selected_band (L : PhysicalWaveSum.BandLabel) (hL : L ∈ active (B := B) (N0 := N0)) :
    BaseChartJets.cellBand (selected L hL).2 = L.val.1 :=
  congrArg (fun x : PhysicalWaveSum.BandLabel => x.val.1) (selected_label L hL)

theorem selected_eq (l : SignedLabel B N0) (hL : bandLabel l ∈ active) :
    selected (bandLabel l) hL = l := bandLabel_injective (selected_label _ hL)

/-- Gap, given by `ChartScales.nativeIndex ActualPrimary.h L.val.1 - CommonWindow.index
ActualPrimary.h L.val.1`. -/
noncomputable def gap (L : PhysicalWaveSum.BandLabel) : ℕ :=
  ChartScales.nativeIndex ActualPrimary.h L.val.1 - CommonWindow.index ActualPrimary.h L.val.1

/-- Geometry, given by `ActualSignedPhysicalData.geometry ActualPrimary.slots L.val (gap L)`. -/
noncomputable def geometry (L : PhysicalWaveSum.BandLabel) : CommonCoverSolve.Geometry :=
  ActualSignedPhysicalData.geometry ActualPrimary.slots L.val (gap L)

theorem geometry_bandLabel (l : SignedLabel B N0) :
    geometry (bandLabel l) = ActualPrimary.chartGeometry (BaseChartJets.cellBand l.2) l.1 l.2 := rfl

/-- Selected carrier, constructed using `ActualSignedPhysicalData.carrier`. -/
noncomputable def selectedCarrier (l : SignedLabel B N0) (k : Frequency) :
    PhysicalWaveSum.CarrierData :=
  ActualSignedPhysicalData.carrier (h := ActualPrimary.h) (spatialLabel l) k
    ((ActualPrimary.phases B N0 l.1).phase.p l.2)
    ((ActualPrimary.phases B N0 l.1).phase.pz l.2)
    ((ActualPrimary.phases B N0 l.1).phase.x0 l.2)
    ((ActualPrimary.phases B N0 l.1).phase.F l.2)
    ((ActualPrimary.phases B N0 l.1).phase.G l.2)

/-- Carrier, with branches according to `hL : L ∈ active (B := B) (N0 := N0)`. -/
noncomputable def carrier (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    PhysicalWaveSum.CarrierData :=
  if hL : L ∈ active (B := B) (N0 := N0) then selectedCarrier (selected L hL) k
  else ActualSignedPhysicalData.carrier (h := ActualPrimary.h) L.val k 0 0 0 (fun _ => 0) (fun _ =>
      0)

theorem carrier_bandLabel (l : SignedLabel B N0) (k : Frequency) :
    carrier (B := B) (N0 := N0) (bandLabel l) k = selectedCarrier l k := by
  have hl : bandLabel l ∈ active (B := B) (N0 := N0) := ⟨l, rfl⟩
  simp only [carrier, dite_eq_left hl, selected_eq]

theorem selectedCarrier_center (l : SignedLabel B N0) (k : Frequency) :
    (selectedCarrier l k).center =
      ActualSignedPhysicalData.center (h := ActualPrimary.h) (spatialLabel l) k := rfl

/-- Source index: an abbreviation for `PhysicalWaveSum.WaveIndex 1 × Frequency`. -/
abbrev SourceIndex := PhysicalWaveSum.WaveIndex 1 × Frequency

/-- Source choice, with branches according to `hL : I.1.1 ∈ active (B := B) (N0 := N0)`. -/
noncomputable def sourceChoice (I : SourceIndex) : Option (SignedLabel B N0 × Frequency) :=
  if hL : I.1.1 ∈ active (B := B) (N0 := N0) then
    if I.1.2.val = 1 then some (selected I.1.1 hL, I.2) else none
  else none

/-- Source family, with branches according to `n = I.1.1.val.1`. -/
noncomputable def sourceFamily {E : Type} [Zero E]
    (f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E)
    (I : SourceIndex) (n : ℕ) (x : LocalSignedRequest.Point) : E :=
  if n = I.1.1.val.1 then
    match sourceChoice (B := B) (N0 := N0) I with
    | some l => f l n x
    | none => 0
  else 0

theorem sourceFamily_eq_some {E : Type} [Zero E]
    (f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E)
    (I : SourceIndex) (n : ℕ) (hn : n = I.1.1.val.1) (l : SignedLabel B N0 × Frequency)
    (hl : sourceChoice I = some l) : sourceFamily f I n = f l n := by
  funext x
  simp only [sourceFamily, ite_eq_left hn, hl]

theorem sourceFamily_eq_zero {E : Type} [Zero E]
    (f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E)
    (I : SourceIndex) (n : ℕ)
    (hz : n ≠ I.1.1.val.1 ∨ sourceChoice (B := B) (N0 := N0) I = none) :
    sourceFamily f I n = fun _ => 0 := by
  funext x
  rcases hz with hn | hc
  · simp only [sourceFamily, ite_eq_right hn]
  · simp only [sourceFamily, hc, ite_self]

theorem sourceFamily_uniform {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E}
    (hf : LabelSumBounds.UniformClass strip (fun _ _ x => Real.sqrt (strip.zeta x)) 1 f) :
    LabelSumBounds.UniformClass strip (fun (_ : SourceIndex) _ x => Real.sqrt (strip.zeta x)) 1
      (sourceFamily f) := by
  refine ⟨fun _ _ _ _ => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro I n
    by_cases hn : n = I.1.1.val.1
    · cases hc : sourceChoice (B := B) (N0 := N0) I with
      | none => rw [sourceFamily_eq_zero _ _ _ (Or.inr hc)]; exact contDiffOn_const
      | some l => rw [sourceFamily_eq_some _ _ _ hn l hc]; exact hf.smooth l n
    · rw [sourceFamily_eq_zero _ _ _ (Or.inl hn)]; exact contDiffOn_const
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro I n x hx j hj
    have hz : (0 : ℝ) ≤ majorant strip (fun _ x => Real.sqrt (strip.zeta x)) 1 C p n x :=
      majorant_nonneg strip _ 1 hC p n x (Real.sqrt_nonneg _)
    by_cases hn : n = I.1.1.val.1
    · cases hc : sourceChoice (B := B) (N0 := N0) I with
      | none =>
          rw [sourceFamily_eq_zero _ _ _ (Or.inr hc)]
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hz
      | some l => rw [sourceFamily_eq_some _ _ _ hn l hc]; exact hb l n x hx j hj
    · rw [sourceFamily_eq_zero _ _ _ (Or.inl hn)]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hz

/-- Native potential source, given by `sourceFamily (fun (l : SignedLabel B N0 × Frequency) n x
=> copyPotentialCoefficient l.1 l.2 n (x, 0))`. -/
noncomputable def nativePotentialSource (B N0 : ℕ) : SourceIndex → ℕ → LocalSignedRequest.Point →
    ComplexVector :=
  sourceFamily (fun (l : SignedLabel B N0 × Frequency) n x => copyPotentialCoefficient l.1 l.2 n
      (x, 0))

/-- Native pressure source, given by `sourceFamily (fun (l : SignedLabel B N0 × Frequency) n x
=> copyPressureCoefficient l.1 l.2 n (x, 0))`. -/
noncomputable def nativePressureSource (B N0 : ℕ) : SourceIndex → ℕ → LocalSignedRequest.Point → ℂ
    :=
  sourceFamily (fun (l : SignedLabel B N0 × Frequency) n x => copyPressureCoefficient l.1 l.2 n (x,
      0))

theorem nativePotentialSource_uniform :
    LabelSumBounds.UniformClass strip (fun (_ : SourceIndex) _ x => Real.sqrt (strip.zeta x)) 1
      (nativePotentialSource (B := B) (N0 := N0)) := by
  apply sourceFamily_uniform
  apply UniformBlockBounds.uniform_slice
  apply copyPotential_uniform.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _)
  intro l n x hx
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (fullEnvelope_le_one l.1 n x)

theorem nativePressureSource_uniform :
    LabelSumBounds.UniformClass strip (fun (_ : SourceIndex) _ x => Real.sqrt (strip.zeta x)) 1
      (nativePressureSource (B := B) (N0 := N0)) := by
  apply sourceFamily_uniform
  apply UniformBlockBounds.uniform_slice
  apply copyPressure_uniform.mono_weight (fun _ _ _ _ => Real.sqrt_nonneg _)
  intro l n x hx
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (fullEnvelope_le_one l.1 n x)

/-- Potential family, bundling `gap`, `carrier`, `amplitude`, `CartesianCopySource`. -/
noncomputable def potentialFamily (B N0 : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap := gap
  carrier k L := carrier (B := B) (N0 := N0) L k
  amplitude k I x := if 0 < x.1.1 then
    (ChartScales.Q I.1.val.1 ^ (-ActualPrimary.h)) •
      CartesianCopySource.rotatedSource (nativePotentialSource (B := B) (N0 := N0)) (I, k)
          I.1.val.1 x i
    else 0

/-- Pressure family, bundling `gap`, `carrier`, `amplitude`, `nativePressureSource`. -/
noncomputable def pressureFamily (B N0 : ℕ) : PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap := gap
  carrier k L := carrier (B := B) (N0 := N0) L k
  amplitude k I x := if 0 < x.1.1 then
    (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h))) •
      nativePressureSource (B := B) (N0 := N0) (I, k) I.1.val.1
        (PhysicalClassBounds.cylindricalMap x)
    else 0

end Labels

section SourceBounds

variable {B N0 : ℕ}

theorem strip_flat_geometry :
    ∃ cL cR L : ℝ, ∃ ρ : LocalSignedRequest.Point → ℝ,
      PhysicalClassBounds.FlatGeometry strip cL cR L ρ := by
  refine ⟨FinalSlowBase.edgeExponent ActualPrimary.nominal / 4, 1,
    WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal),
    (fun x => WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius
        ActualPrimary.nominal)
      (LocalSignedRequest.profileMap (2 * ActualPrimary.h) x).1), ?_⟩
  exact PhysicalClassBounds.movingStrip_flatGeometry region
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale

theorem native_source_bounds {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : I → ℕ → LocalSignedRequest.Point → E}
    (hf : LabelSumBounds.UniformClass strip (fun _ _ x => Real.sqrt (strip.zeta x)) 1 f) :
    LocalPhysicalCopyBounds.LocalSourceBounds strip ActualPrimary.h 1
      (fun _ _ x => Real.sqrt (strip.zeta x)) f := by
  refine ⟨hf, strip_flat_geometry, ⟨1 / 2, by norm_num, ?_⟩, fun _ => rfl,
    ⟨1, le_rfl, 1, ?_⟩⟩
  · intro l n x hx
    exact (Real.sqrt_eq_rpow _).le
  · intro n hn
    have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
    change max 1 (ChartScales.S n) ≤ 1 * ChartScales.S n ^ 1
    simp only [max_eq_right hS, pow_one, one_mul, le_refl]

theorem nativePotentialSource_bounds :
    LocalPhysicalCopyBounds.LocalSourceBounds strip ActualPrimary.h 1
      (fun (_ : SourceIndex) _ x => Real.sqrt (strip.zeta x)) (nativePotentialSource B N0) :=
  native_source_bounds nativePotentialSource_uniform

theorem nativePressureSource_bounds :
    LocalPhysicalCopyBounds.LocalSourceBounds strip ActualPrimary.h 1
      (fun (_ : SourceIndex) _ x => Real.sqrt (strip.zeta x)) (nativePressureSource B N0) :=
  native_source_bounds nativePressureSource_uniform

end SourceBounds

section ActualSupport

variable {B N0 : ℕ}

theorem near_self (l : SignedLabel B N0) : near l (BaseChartJets.cellBand l.2) :=
  ⟨(by have hh : 4 ≤ BaseChartJets.cellBand l.2 := label_large l; omega), CommonWindow.self_mem _⟩

theorem copyPoint_self (l : SignedLabel B N0) (k : Frequency) (x : ActualSignedGeometry.Native) :
    copyPoint l (BaseChartJets.cellBand l.2) k x =
      (x.1, (geometry (bandLabel l)).coordinates k x.2) := by
  have hQ := ChartScales.Q_pos (BaseChartJets.cellBand l.2)
  change (ActualSignedGeometry.slowChange ActualPrimary.h
    (ChartScales.Q (BaseChartJets.cellBand l.2)) (ChartScales.Q (BaseChartJets.cellBand l.2)) x.1,
        _) = _
  apply Prod.ext
  · simp only [ActualSignedGeometry.slowChange_apply, PhysicalParticularWave.ratioPower,
      div_self (Real.rpow_pos_of_pos hQ _).ne', one_mul]
  · rfl

theorem copied_self {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → ActualSignedGeometry.Native → E)
    (l : SignedLabel B N0) (k : Frequency) (x : ActualSignedGeometry.Native) :
    copied a f l (BaseChartJets.cellBand l.2) k x =
      f l (x.1, (geometry (bandLabel l)).coordinates k x.2) := by
  have hQ := Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) a
  simp only [copied, ite_eq_left (near_self l), coefficientScale, PhysicalParticularWave.ratioPower,
    div_self hQ.ne', one_smul, copyPoint_self]

theorem attached_pair_support (l : SignedLabel B N0) (x : ActualSignedGeometry.Native)
    (hne : ActualPrimary.attachedRawVelocity l.1 l.2 x ≠ 0 ∨
      ActualPrimary.attachedRawPressure l.1 l.2 x ≠ 0) :
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
          ActualPrimary.nominal) ∧
    SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 ∧
    x.1 ∈ ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.2 ∧
    x.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  have hr : WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
          ActualPrimary.nominal) := by
    by_contra ho
    rcases hne with hv | hp
    · exact hv (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ ho)
    · exact hp (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ ho)
  have hraw : ActualPrimary.rawVelocity l.1 l.2 x ≠ 0 := by
    intro hv
    rcases hne with hne | hne
    · exact hne (by simp [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
        WaveEdgeExtension.extension, ActualPrimary.outerRawVelocity, hv])
    · have hp := ActualPrimary.rawPressure_zero_of_velocity_zero l.1 l.2 x hv
      exact hne (by simp [ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
        WaveEdgeExtension.extension, ActualPrimary.outerRawPressure, hp])
  have hm : ActualPrimary.spatialMask l.2 x.1 ≠ 0 := by
    intro hz
    exact hraw (by simp [ActualPrimary.rawVelocity, PartitionedCovariance.amplitude, hz])
  refine ⟨hr, ActualPrimary.spatialMask_q_range l.2 x.1 hm,
    ActualPrimary.spatialMask_native_support l.2 x.1 hm, ?_⟩
  exact hne.elim (ActualPrimary.attachedRawVelocity_core l.1 l.2 x)
    (ActualPrimary.attachedRawPressure_core l.1 l.2 x)

theorem cut_pair_support (l : SignedLabel B N0) (x : ActualSignedGeometry.Native)
    (hne : cutNativeVelocity l x ≠ 0 ∨ cutNativePressure l x ≠ 0) :
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
          ActualPrimary.nominal) ∧
    SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 ∧
    x.1 ∈ ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.2 ∧
    x.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  apply attached_pair_support l x
  rcases hne with hv | hp
  · left
    intro hz
    exact hv (by simp [cutNativeVelocity, hz])
  · right
    intro hz
    exact hp (by simp [cutNativePressure, hz])

end ActualSupport

section SupportedCells

variable {B N0 : ℕ}

/-- Lift point: an abbreviation for `PhysicalGraphBounds.LiftPoint`. -/
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint

/-- Slow input, given by `(ActualSignedGeometry.meanEquiv.symm
(PhysicalClassBounds.cylindricalMap x)).1`. -/
noncomputable def slowInput (x : LiftPoint) : PhaseCalculus.Slow :=
  (ActualSignedGeometry.meanEquiv.symm (PhysicalClassBounds.cylindricalMap x)).1

theorem slowInput_continuous : Continuous slowInput :=
  (ActualSignedGeometry.meanEquiv.symm.continuous.comp
    CartesianCopySource.cylindricalMap_continuous).fst

/-- Native at, given by `(slowInput x, (geometry L).coordinates k x.2)`. -/
noncomputable def nativeAt (L : PhysicalWaveSum.BandLabel) (k : Frequency) (x : LiftPoint) :
    ActualSignedGeometry.Native := (slowInput x, (geometry L).coordinates k x.2)

theorem copyAmplitude_nativeAt (l : SignedLabel B N0) (k : Frequency) (x : LiftPoint) :
    copyAmplitude l k (BaseChartJets.cellBand l.2) (PhysicalClassBounds.cylindricalMap x, 0) =
      cutNativeVelocity l (nativeAt (bandLabel l) k x) := by
  rw [copyAmplitude, copied_self]
  rfl

theorem copyPressure_nativeAt (l : SignedLabel B N0) (k : Frequency) (x : LiftPoint) :
    copyPressureCoefficient l k (BaseChartJets.cellBand l.2) (PhysicalClassBounds.cylindricalMap x,
        0) =
      cutNativePressure l (nativeAt (bandLabel l) k x) := by
  rw [copyPressureCoefficient, copied_self]
  rfl

theorem sourceFamily_nonzero {E : Type} [Zero E]
    (f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E)
    (I : SourceIndex) (n : ℕ) (x : LocalSignedRequest.Point)
    (hne : sourceFamily f I n x ≠ 0) :
    ∃ l : SignedLabel B N0, bandLabel l = I.1.1 ∧ I.1.2.val = 1 ∧ n = I.1.1.val.1 ∧
      f (l, I.2) n x ≠ 0 := by
  by_cases hn : n = I.1.1.val.1
  · by_cases hL : I.1.1 ∈ active (B := B) (N0 := N0)
    · by_cases hI : I.1.2.val = 1
      · refine ⟨selected I.1.1 hL, selected_label _ _, hI, hn, ?_⟩
        simpa only [sourceFamily, ite_eq_left hn, sourceChoice, dite_eq_left hL, ite_eq_left hI]
            using hne
      · exact (hne (by
          simp only [sourceFamily, ite_eq_left hn, sourceChoice, dite_eq_left hL, ite_eq_right
              hI])).elim
    · exact (hne (by simp only [sourceFamily, ite_eq_left hn, sourceChoice, dite_eq_right hL])).elim
  · exact (hne (by simp only [sourceFamily, ite_eq_right hn])).elim

theorem potential_amplitude_data (i : Fin 3) (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : (potentialFamily B N0 i).amplitude k I x ≠ 0) :
    ∃ l : SignedLabel B N0, bandLabel l = I.1 ∧ I.2.val = 1 ∧ 0 < x.1.1 ∧
      cutNativeVelocity l (nativeAt I.1 k x) ≠ 0 := by
  have ht : 0 < x.1.1 := by
    by_contra ht
    exact hx (by simp only [potentialFamily, ite_eq_right ht])
  have hs : nativePotentialSource B N0 (I, k) I.1.val.1 (PhysicalClassBounds.cylindricalMap x) ≠ 0
      := by
    intro hz
    exact hx (by simp only [potentialFamily, ite_eq_left ht, CartesianCopySource.rotatedSource,
      hz, map_zero, Pi.zero_apply, smul_zero])
  obtain ⟨l, hl, hI, _, hn⟩ := sourceFamily_nonzero _ (I, k) I.1.val.1
    (PhysicalClassBounds.cylindricalMap x) hs
  have hm : I.1.val.1 = BaseChartJets.cellBand l.2 :=
    (congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl).symm
  have ha : copyAmplitude l k I.1.val.1 (PhysicalClassBounds.cylindricalMap x, 0) ≠ 0 := by
    intro hz
    exact hn (by simp [copyPotentialCoefficient, CurlClassBounds.normalCoefficient,
      CurlClassBounds.normalCross, hz])
  rw [hm, copyAmplitude_nativeAt, hl] at ha
  exact ⟨l, hl, hI, ht, ha⟩

theorem pressure_amplitude_data (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : (pressureFamily B N0).amplitude k I x ≠ 0) :
    ∃ l : SignedLabel B N0, bandLabel l = I.1 ∧ I.2.val = 1 ∧ 0 < x.1.1 ∧
      cutNativePressure l (nativeAt I.1 k x) ≠ 0 := by
  have ht : 0 < x.1.1 := by
    by_contra ht
    exact hx (by simp only [pressureFamily, ite_eq_right ht])
  have hs : nativePressureSource B N0 (I, k) I.1.val.1 (PhysicalClassBounds.cylindricalMap x) ≠ 0
      := by
    intro hz
    exact hx (by simp only [pressureFamily, ite_eq_left ht, hz, smul_zero])
  obtain ⟨l, hl, hI, _, hn⟩ := sourceFamily_nonzero _ (I, k) I.1.val.1
    (PhysicalClassBounds.cylindricalMap x) hs
  have hm : I.1.val.1 = BaseChartJets.cellBand l.2 :=
    (congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl).symm
  rw [hm, copyPressure_nativeAt, hl] at hn
  exact ⟨l, hl, hI, ht, hn⟩

/-- Base cells, constructed using `PeriodizedWaveBounds.nativeCells`. -/
noncomputable def baseCells (L : PhysicalWaveSum.BandLabel) :
    PeriodizedWaveBounds.Cells LiftPoint Frequency :=
  PeriodizedWaveBounds.nativeCells (fun _ => geometry L)
    (fun _ => (ActualSignedGeometry.clockWindow ActualPrimary.slots L.val.1).core)
    (fun _ => (ActualSignedGeometry.clockWindow ActualPrimary.slots L.val.1).core_compact)
    (fun _ => (ActualSignedGeometry.clockWindow_injective ActualPrimary.slots
        ActualPrimary.vectors_det
      ActualPrimary.outgoing.data.h_pos.le L.property (gap L)).mono
        (Set.image_mono (ActualSignedGeometry.clockWindow ActualPrimary.slots
            L.val.1).core_subset_outer))

/-- Slow cell, with branches according to `hL : L ∈ active (B := B) (N0 := N0)`. -/
noncomputable def slowCell (L : PhysicalWaveSum.BandLabel) : Set LiftPoint :=
  if hL : L ∈ active (B := B) (N0 := N0) then slowInput ⁻¹'
    ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared (selected L hL).2
  else ∅

theorem slowCell_closed (L : PhysicalWaveSum.BandLabel) :
    IsClosed (slowCell (B := B) (N0 := N0) L) := by
  unfold slowCell
  split_ifs with hL
  · exact (ActualGaussianCoverage.actualSlowCore_closed _ _ _ _).preimage slowInput_continuous
  · exact isClosed_empty

/-- Closed slow support is retained alongside the individual native
rectangle.  Phase bounds are never requested outside this support. -/
noncomputable def cells (L : PhysicalWaveSum.BandLabel) :
    PeriodizedWaveBounds.Cells LiftPoint Frequency where
  carrier n k := (baseCells L).carrier n k ∩ slowCell (B := B) (N0 := N0) L
  closed n k := ((baseCells L).closed n k).inter (slowCell_closed L)
  locallyFinite n := ((baseCells L).locallyFinite n).subset (fun _ => inter_subset_left)
  unique n i j x hi hj := (baseCells L).unique n i j x hi.1 hj.1

theorem cells_bandLabel (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : LiftPoint) :
    x ∈ (cells (B := B) (N0 := N0) (bandLabel l)).carrier n k ↔
      (nativeAt (bandLabel l) k x).2 ∈ (ActualPrimary.clockWindow l.2).core ∧
      (nativeAt (bandLabel l) k x).1 ∈
        ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
          (ActualPrimary.choice B N0).prepared l.2 := by
  have hl : bandLabel l ∈ active (B := B) (N0 := N0) := ⟨l, rfl⟩
  simp only [cells, baseCells, PeriodizedWaveBounds.nativeCells, PeriodizedWaveBounds.nativeCell,
    slowCell, dite_eq_left hl, selected_eq, mem_inter_iff, Set.mem_ofPred_eq, mem_preimage,
    nativeAt]
  rfl

/-- Potential cells, bundling `cells`, `support`, `obtain`, `have` and the required
compatibility proofs. -/
noncomputable def potentialCells (B N0 : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (potentialFamily B N0 i) where
  cells := cells (B := B) (N0 := N0)
  support I k x hx := by
    obtain ⟨l, hl, _, _, hn⟩ := potential_amplitude_data i k I x hx
    have hi := cut_pair_support l (nativeAt I.1 k x) (Or.inl hn)
    rw [← hl, cells_bandLabel (B := B) (N0 := N0)]
    simpa only [hl] using And.intro hi.2.2.2 hi.2.2.1

/-- Pressure cells, bundling `cells`, `support`, `obtain`, `have` and the required compatibility
proofs. -/
noncomputable def pressureCells (B N0 : ℕ) :
    PhysicalCopyBounds.SupportCells (pressureFamily B N0) where
  cells := cells (B := B) (N0 := N0)
  support I k x hx := by
    obtain ⟨l, hl, _, _, hn⟩ := pressure_amplitude_data k I x hx
    have hi := cut_pair_support l (nativeAt I.1 k x) (Or.inr hn)
    rw [← hl, cells_bandLabel (B := B) (N0 := N0)]
    simpa only [hl] using And.intro hi.2.2.2 hi.2.2.1

end SupportedCells

section PhysicalSupport

variable {B N0 : ℕ}

/-- Inner radius, given by `PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4`. -/
noncomputable def innerRadius : ℝ := PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4
/-- Outer radius, given by `2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal`. -/
noncomputable def outerRadius : ℝ := 2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal

theorem innerRadius_pos : 0 < innerRadius :=
  div_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) (by norm_num)

theorem cut_pair_mask (l : SignedLabel B N0) (x : ActualSignedGeometry.Native)
    (hne : cutNativeVelocity l x ≠ 0 ∨ cutNativePressure l x ≠ 0) :
    ActualPrimary.spatialMask l.2 x.1 ≠ 0 := by
  intro hm
  have hv : ActualPrimary.rawVelocity l.1 l.2 x = 0 := by
    simp [ActualPrimary.rawVelocity, PartitionedCovariance.amplitude, hm]
  have hp := ActualPrimary.rawPressure_zero_of_velocity_zero l.1 l.2 x hv
  rcases hne with hne | hne
  · apply hne
    simp [cutNativeVelocity, ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, ActualPrimary.outerRawVelocity, hv]
  · apply hne
    simp [cutNativePressure, ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, ActualPrimary.outerRawPressure, hp]

theorem cut_pair_domain (l : SignedLabel B N0) (L : PhysicalWaveSum.BandLabel)
    (k : Frequency) (x : LiftPoint) (ht : 0 < x.1.1)
    (hne : cutNativeVelocity l (nativeAt L k x) ≠ 0 ∨ cutNativePressure l (nativeAt L k x) ≠ 0) :
    PhysicalClassBounds.cylindricalMap x ∈ strip.domain := by
  have hd := cut_pair_support l (nativeAt L k x) hne
  apply (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal region _).mpr
  exact ⟨⟨ht, hd.2.1⟩, hd.1⟩

theorem cut_pair_annulus (l : SignedLabel B N0) (L : PhysicalWaveSum.BandLabel)
    (k : Frequency) (x : LiftPoint) (ht : 0 < x.1.1)
    (hne : cutNativeVelocity l (nativeAt L k x) ≠ 0 ∨ cutNativePressure l (nativeAt L k x) ≠ 0) :
    PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus innerRadius outerRadius ∧
      ‖PhysicalGraphBounds.liftZT x‖ ≤ 2 := by
  have hd := cut_pair_support l (nativeAt L k x) hne
  let q := SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.1, x.1.2.2.2)
  have hqlo : (1 / 2 : ℝ) < q := hd.2.1.1
  have hqhi : q < 2 := hd.2.1.2
  have hq : 0 < q := lt_trans (by norm_num) hqlo
  have hs := Real.sqrt_pos.mpr hq
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq.le).mpr (by nlinarith)
  have hshi : Real.sqrt q ≤ 2 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by linarith)
  have hradius : WaveEdgeExtension.nativeRadius ActualPrimary.h (nativeAt L k x) =
      PolarCharts.radius (PhysicalGraphBounds.liftXY x) / Real.sqrt q := by
    rw [WaveEdgeExtension.nativeRadius_eq_qLength]
    rfl
  rw [hradius] at hd
  have hrlo : PrimaryTargetBounds.leftRadius ActualPrimary.nominal * Real.sqrt q <
      PolarCharts.radius (PhysicalGraphBounds.liftXY x) :=
    (lt_div_iff₀ hs).mp hd.1.1
  have hrhi : PolarCharts.radius (PhysicalGraphBounds.liftXY x) <
      PrimaryTargetBounds.rightRadius ActualPrimary.nominal * Real.sqrt q :=
    (div_lt_iff₀ hs).mp hd.1.2
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := ha.trans (PrimaryTargetBounds.radii_ordered ActualPrimary.nominal)
  have hnhi : ‖PhysicalGraphBounds.liftXY x‖ ≤ outerRadius := by
    apply (PolarCharts.norm_le_radius _).trans
    change _ ≤ 2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal
    nlinarith
  have hnlo : innerRadius ≤ ‖PhysicalGraphBounds.liftXY x‖ := by
    have hh := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.liftXY x)
    change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 ≤ _
    nlinarith
  refine ⟨⟨?_, hnlo⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hnhi
  · have hz := ActualSignedPhysicalData.normalized_slow_norm
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half ht hqlo.le hqhi.le
    change max ‖x.1.2.2.2‖ ‖x.1.1‖ ≤ 2
    change max ‖x.1.1‖ ‖x.1.2.2.2‖ ≤ 2 at hz
    simpa only [max_comm] using hz

theorem liftXY_common (h : ℝ) (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w) =
      PhysicalGraphBounds.scaledRadial n w := by
  exact PhysicalGraphBounds.liftXY_physicalLift h n w

theorem liftZT_common (h : ℝ) (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    PhysicalGraphBounds.liftZT (PhysicalWaveSum.commonLift h n d w) =
      PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w) := rfl

theorem slowInput_common (h : ℝ) (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    slowInput (PhysicalWaveSum.commonLift h n d w) =
      ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph h n 0 w) := rfl

theorem carrier_center (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    (carrier (B := B) (N0 := N0) L k).center =
      ActualSignedPhysicalData.center (h := ActualPrimary.h) L.val k := by
  by_cases hL : L ∈ active (B := B) (N0 := N0)
  · rw [carrier, dite_eq_left hL, selectedCarrier_center]
    have he : spatialLabel (selected (B := B) (N0 := N0) L hL) = L.val :=
      congrArg Subtype.val (selected_label (B := B) (N0 := N0) L hL)
    rw [he]
  · simp only [carrier, dite_eq_right hL, ActualSignedPhysicalData.carrier]

theorem carrier_integer (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    ∃ m : ℤ, (ChartScales.carrier ActualPrimary.h L.val.1 : ℝ) *
      (carrier (B := B) (N0 := N0) L k).angular = m := by
  by_cases hL : L ∈ active (B := B) (N0 := N0)
  · refine ⟨PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared (selected L hL).1 (selected L hL).2, ?_⟩
    rw [carrier, dite_eq_left hL, ← selected_band L hL]
    exact PrimaryGeometryAssembly.carrier_mul_phase_p _ _ _ ActualPrimary.slots.radius_pos _ _
  · exact ⟨0, by simp [carrier, hL, ActualSignedPhysicalData.carrier]⟩

theorem gap_bound (L : PhysicalWaveSum.BandLabel) : gap L ≤ CommonWindow.gap ActualPrimary.h := by
  have hh := CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le
      L.val.1
  unfold gap
  omega

theorem gap_native (L : PhysicalWaveSum.BandLabel) : gap L ≤ ChartScales.nativeIndex
    ActualPrimary.h L.val.1 :=
  Nat.sub_le _ _

theorem physicalPosition_graph (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    ActualPrimary.physicalPosition n (PhysicalMeanJetBounds.graph ActualPrimary.h n d w) =
      PhysicalWaveSum.physicalPosition w := by
  funext i
  fin_cases i
  · change Real.sqrt (ChartScales.Q n) * (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).1 =
      PolarCharts.radius (PhysicalGraphBounds.radialProjection w)
    rw [PhysicalMeanJetBounds.graph_radius, ← PhysicalGraphBounds.unscale_radial n w,
      PolarCharts.radius_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _), Real.sqrt_eq_rpow]
  · change ChartScales.Q n ^ CoordinateAlgebra.D ActualPrimary.h *
      (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1.2 = w.2 2
    rw [PhysicalMeanJetBounds.graph_slow, ← mul_assoc,
      ← Real.rpow_add (ChartScales.Q_pos n)]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
  · change ChartScales.Q n * (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1.1 = 1 - w.1
    rw [PhysicalMeanJetBounds.graph_slow, mul_div_cancel₀ _ (ChartScales.Q_pos n).ne']

theorem physicalScale_graph (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    ActualPrimary.physicalScale n (PhysicalMeanJetBounds.graph ActualPrimary.h n d w) =
      PhysicalWaveSum.physicalQ ActualPrimary.h w := by
  change ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) _ = _
  rw [PhysicalMeanJetBounds.graph_q_eq ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n d hw,
    mul_div_cancel₀ _ (ChartScales.Q_pos n).ne']

theorem spatialMask_physical (l : SignedLabel B N0) (d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    ActualPrimary.spatialMask l.2 (slowInput (PhysicalWaveSum.commonLift ActualPrimary.h
      (BaseChartJets.cellBand l.2) d w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D ActualPrimary.h) (bandLabel l).val
        (PhysicalWaveSum.physicalParams ActualPrimary.h w) := by
  let x := PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) d w
  have he := ActualPrimaryCovariance.nativePoint_mask (BaseChartJets.cellBand l.2) (x := x)
    (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h (BaseChartJets.cellBand l.2) d hw) l.2
  have hp : ActualPrimaryCovariance.nativePoint (BaseChartJets.cellBand l.2) x l.2 =
      slowInput (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) d w) :=
    ActualPrimary.nativeSlow_toAbsolute l.2 x
  rw [hp] at he
  dsimp only [x] at he
  rw [physicalPosition_graph, physicalScale_graph _ _ hw] at he
  exact he

end PhysicalSupport

section PhysicalFamilies

variable {B N0 : ℕ}

theorem width_physical (L : PhysicalWaveSum.BandLabel) (k : Frequency)
    (w : ProblemStatement.SpaceTime)
    (hc : (geometry L).coordinates k
      (PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w).2 ∈
        (ActualSignedGeometry.clockWindow ActualPrimary.slots L.val.1).core) :
    |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph ActualPrimary.h L.val.1 w -
      (carrier (B := B) (N0 := N0) L k).center)| ≤ ActualPrimary.slots.radius := by
  rw [carrier_center (B := B) (N0 := N0)]
  have hh := ActualSignedPhysicalData.width_on_core ActualPrimary.slots L.val (gap L) k
    (PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w).2 hc
  rw [← PhysicalCopyBounds.nativeGraph_eq_cover_commonLift] at hh
  exact hh

theorem potential_support (B N0 : ℕ) (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialFamily B N0 i) innerRadius outerRadius
      ActualPrimary.h ActualPrimary.slots.radius 2 (CommonWindow.gap ActualPrimary.h) where
  gap_le := gap_bound
  gap_native := gap_native
  angular_integer := fun k L => carrier_integer L k
  geometry_support k I w hv := by
    obtain ⟨l, hl, _, ht, hn⟩ := potential_amplitude_data i k I _ hv
    have hi := cut_pair_annulus l I.1 k _ ht (Or.inl hn)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [liftXY_common] using hi.1
    · simpa only [liftZT_common] using hi.2
    · apply width_physical
      have hc := (cut_pair_support l (nativeAt I.1 k _) (Or.inl hn)).2.2.2
      have he : BaseChartJets.cellBand l.2 = I.1.val.1 :=
        congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl
      change (geometry I.1).coordinates k _ ∈
        (ActualSignedGeometry.clockWindow ActualPrimary.slots (BaseChartJets.cellBand l.2)).core
            at hc
      rwa [he] at hc
  mask_support k I w hw hv := by
    obtain ⟨l, hl, _, _, hn⟩ := potential_amplitude_data i k I _ hv
    have hm := cut_pair_mask l (nativeAt I.1 k _) (Or.inl hn)
    change ActualPrimary.spatialMask l.2 (slowInput (PhysicalWaveSum.commonLift
      ActualPrimary.h I.1.val.1 (gap I.1) w)) ≠ 0 at hm
    have he : BaseChartJets.cellBand l.2 = I.1.val.1 :=
      congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl
    rw [← he, spatialMask_physical l _ hw] at hm
    simpa only [hl] using hm

theorem pressure_support (B N0 : ℕ) :
    LocalPhysicalCopyBounds.SupportData (pressureFamily B N0) innerRadius outerRadius
      ActualPrimary.h ActualPrimary.slots.radius 2 (CommonWindow.gap ActualPrimary.h) where
  gap_le := gap_bound
  gap_native := gap_native
  angular_integer := fun k L => carrier_integer L k
  geometry_support k I w hv := by
    obtain ⟨l, hl, _, ht, hn⟩ := pressure_amplitude_data k I _ hv
    have hi := cut_pair_annulus l I.1 k _ ht (Or.inr hn)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [liftXY_common] using hi.1
    · simpa only [liftZT_common] using hi.2
    · apply width_physical
      have hc := (cut_pair_support l (nativeAt I.1 k _) (Or.inr hn)).2.2.2
      have he : BaseChartJets.cellBand l.2 = I.1.val.1 :=
        congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl
      change (geometry I.1).coordinates k _ ∈
        (ActualSignedGeometry.clockWindow ActualPrimary.slots (BaseChartJets.cellBand l.2)).core
            at hc
      rwa [he] at hc
  mask_support k I w hw hv := by
    obtain ⟨l, hl, _, _, hn⟩ := pressure_amplitude_data k I _ hv
    have hm := cut_pair_mask l (nativeAt I.1 k _) (Or.inr hn)
    change ActualPrimary.spatialMask l.2 (slowInput (PhysicalWaveSum.commonLift
      ActualPrimary.h I.1.val.1 (gap I.1) w)) ≠ 0 at hm
    have he : BaseChartJets.cellBand l.2 = I.1.val.1 :=
      congrArg (fun L : PhysicalWaveSum.BandLabel => L.val.1) hl
    rw [← he, spatialMask_physical l _ hw] at hm
    simpa only [hl] using hm

/-- The actual initial primary potential.  The physical construction is
zero on the unused future side of the preterminal domain. -/
noncomputable def potential (B N0 : ℕ) : ProblemStatement.VelocityField :=
  PhysicalCopyBounds.vectorSum (potentialFamily B N0) innerRadius ActualPrimary.h
      ActualPrimary.slots.radius

/-- Pressure, defined pointwise by `((pressureFamily B N0).sum innerRadius ActualPrimary.h
ActualPrimary.slots.radius w).re`. -/
noncomputable def pressure (B N0 : ℕ) : ProblemStatement.PressureField :=
  fun w => ((pressureFamily B N0).sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w).re

/-- Copy potential, bundling `Copy`, `harmonics`, `family`, `inner` and the required
compatibility proofs. -/
noncomputable def copyPotential (B N0 : ℕ) : MixedAxisPreservation.CopyPotential ActualPrimary.h
    where
  Copy := Frequency
  harmonics := 1
  family := potentialFamily B N0
  inner := innerRadius
  outer := outerRadius
  width := ActualPrimary.slots.radius
  axialRadius := 2
  gap := CommonWindow.gap ActualPrimary.h
  inner_pos := innerRadius_pos
  support := potential_support B N0
  cells := potentialCells B N0

theorem copyPotential_field (B N0 : ℕ) : (copyPotential B N0).field = potential B N0 := rfl

end PhysicalFamilies

section NativeProfiles

variable {B N0 : ℕ}

/-- Profile region, with branches according to `hL : L ∈ active (B := B) (N0 := N0)`. -/
noncomputable def profileRegion (L : PhysicalWaveSum.BandLabel) : Set PhaseCalculus.Slow :=
  if hL : L ∈ active (B := B) (N0 := N0) then
    (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).carrier
      (selected L hL).2
  else ∅

theorem profileRegion_open (L : PhysicalWaveSum.BandLabel) :
    IsOpen (profileRegion (B := B) (N0 := N0) L) := by
  unfold profileRegion
  split_ifs
  · exact (PrimaryGeometryAssembly.domain _ _).isOpen _
  · exact isOpen_empty

theorem carrierProfiles :
    PhaseJetBounds.PolynomialJets
      (PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => profileRegion (B := B) (N0 :=
          N0) L)
        (fun _ L => profileRegion_open L))
      (fun i p => ((carrier (B := B) (N0 := N0) i.2 i.1).F p,
        (carrier (B := B) (N0 := N0) i.2 i.1).G p)) := by
  have hfg := (ActualPrimary.phases B N0 0).baseF.pair (ActualPrimary.phases B N0 0).baseG
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hL : i.2 ∈ active (B := B) (N0 := N0)
    · change ContDiffOn ℝ ∞ (fun p => ((carrier (B := B) (N0 := N0) i.2 i.1).F p,
        (carrier (B := B) (N0 := N0) i.2 i.1).G p)) (profileRegion (B := B) (N0 := N0) i.2)
      simp only [carrier, profileRegion, dite_eq_left hL]
      exact hfg.smooth (selected i.2 hL).2
    · intro p hp
      have hfalse : False := by
        simp only [PhysicalCopyBounds.copyBandDomain, profileRegion, dite_eq_right hL,
            mem_empty_iff_false] at hp
      exact hfalse.elim
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hfg.bound m
    refine ⟨C, hC, p, ?_⟩
    intro i j hj x hx
    by_cases hL : i.2 ∈ active (B := B) (N0 := N0)
    · change x ∈ profileRegion (B := B) (N0 := N0) i.2 at hx
      simp only [profileRegion, dite_eq_left hL] at hx
      change ‖iteratedFDeriv ℝ j (fun p => ((carrier (B := B) (N0 := N0) i.2 i.1).F p,
        (carrier (B := B) (N0 := N0) i.2 i.1).G p)) x‖ ≤
        C * ChartScales.S i.2.val.1 ^ p
      rw [carrier, dite_eq_left hL, ← selected_band i.2 hL]
      exact hb (selected i.2 hL).2 j hj x hx
    · have hfalse : False := by
        simp only [PhysicalCopyBounds.copyBandDomain, profileRegion, dite_eq_right hL,
            mem_empty_iff_false] at hx
      exact hfalse.elim

theorem profileRegion_contains (L : PhysicalWaveSum.BandLabel) (k : Frequency)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hc : PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w ∈
      (cells (B := B) (N0 := N0) L).carrier L.val.1 k)
    (j : PolarCharts.Index)
    (hj : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PolarCharts.chartDomain innerRadius j) :
    LocalPhysicalCopyBounds.slotSlow ((carrier (B := B) (N0 := N0) L k).withChart j)
      innerRadius ActualPrimary.h L.val.1 ActualPrimary.slots.radius w ∈ profileRegion (B := B) (N0
          := N0) L := by
  have hs := hc.2
  by_cases hL : L ∈ active (B := B) (N0 := N0)
  · change _ ∈ slowCell (B := B) (N0 := N0) L at hs
    simp only [slowCell, dite_eq_left hL, mem_preimage] at hs
    rw [ActualSignedPhysicalData.slotSlow_eq_nativeSlow innerRadius_pos
      (carrier (B := B) (N0 := N0) L k) ActualPrimary.h L.val.1 ActualPrimary.slots.radius j w hj]
    simp only [profileRegion, dite_eq_left hL]
    rw [← slowInput_common ActualPrimary.h L.val.1 (gap L) w]
    exact ActualGaussianCoverage.actualSlowCore_inside ActualPrimary.certificate
        ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared (selected (B := B) (N0 := N0) L hL).2 hs
      (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h L.val.1 (gap L) hw)
  · simp only [slowCell, dite_eq_right hL, mem_empty_iff_false] at hs

/-- Potential carrier, bundling `region`, `open_region`, `jets`, `contains`. -/
noncomputable def potentialCarrier (B N0 : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.CarrierBounds (potentialFamily B N0 i) (potentialCells B N0 i)
      innerRadius outerRadius ActualPrimary.h ActualPrimary.slots.radius where
  region _ L := profileRegion L
  open_region _ L := profileRegion_open L
  jets := carrierProfiles
  contains k I w hw _ _ hc j hj := profileRegion_contains (B := B) (N0 := N0) I.1 k w hw hc j hj

/-- Pressure carrier, bundling `region`, `open_region`, `jets`, `contains`. -/
noncomputable def pressureCarrier (B N0 : ℕ) :
    PhysicalCopyBounds.CarrierBounds (pressureFamily B N0) (pressureCells B N0)
      innerRadius outerRadius ActualPrimary.h ActualPrimary.slots.radius where
  region _ L := profileRegion L
  open_region _ L := profileRegion_open L
  jets := carrierProfiles
  contains k I w hw _ _ hc j hj := profileRegion_contains (B := B) (N0 := N0) I.1 k w hw hc j hj

end NativeProfiles

section SourceCharts

variable {B N0 : ℕ}

/-- Source strip, given by `CartesianCopySource.pullStrip strip innerRadius outerRadius
innerRadius_pos`. -/
noncomputable def sourceStrip : StripData LiftPoint :=
  CartesianCopySource.pullStrip strip innerRadius outerRadius innerRadius_pos

/-- Potential source, given by `CartesianCopySource.rotatedSource (nativePotentialSource B N0)
I.2 n x I.1`. -/
noncomputable def potentialSource (B N0 : ℕ) (I : Fin 3 × SourceIndex)
    (n : ℕ) (x : LiftPoint) : ℂ :=
  CartesianCopySource.rotatedSource (nativePotentialSource B N0) I.2 n x I.1

/-- Pressure source, given by `nativePressureSource B N0 I n (PhysicalClassBounds.cylindricalMap
x)`. -/
noncomputable def pressureSource (B N0 : ℕ) (I : SourceIndex)
    (n : ℕ) (x : LiftPoint) : ℂ :=
  nativePressureSource B N0 I n (PhysicalClassBounds.cylindricalMap x)

theorem potentialSource_bounds (B N0 : ℕ) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip ActualPrimary.h 1
      (fun (_ : Fin 3 × SourceIndex) _ x => Real.sqrt (sourceStrip.zeta x))
      (potentialSource B N0) :=
  ActualSignedPhysicalData.componentSourceBounds (CartesianCopySource.sourceBounds_rotated
    (b := outerRadius) innerRadius_pos (nativePotentialSource_bounds (B := B) (N0 := N0)))

theorem pressureSource_bounds (B N0 : ℕ) :
    LocalPhysicalCopyBounds.LocalSourceBounds sourceStrip ActualPrimary.h 1
      (fun (_ : SourceIndex) _ x => Real.sqrt (sourceStrip.zeta x))
      (pressureSource B N0) :=
  CartesianCopySource.sourceBounds_pullback (b := outerRadius) innerRadius_pos
    (nativePressureSource_bounds (B := B) (N0 := N0))

theorem cut_pair_source_domain (l : SignedLabel B N0) (L : PhysicalWaveSum.BandLabel)
    (k : Frequency) (x : LiftPoint) (ht : 0 < x.1.1)
    (hne : cutNativeVelocity l (nativeAt L k x) ≠ 0 ∨ cutNativePressure l (nativeAt L k x) ≠ 0) :
    x ∈ sourceStrip.domain := by
  have hg := (cut_pair_annulus l L k x ht hne).1
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ outerRadius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1
  have hl : innerRadius ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.2
  refine ⟨⟨?_, ?_⟩, cut_pair_domain l L k x ht hne⟩
  · change innerRadius / 2 < _
    linarith [innerRadius_pos]
  · change _ < outerRadius + 1
    linarith

theorem potential_source_domain (B N0 : ℕ) (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (potentialFamily B N0 i).amplitude k I x ≠ 0) : x ∈ sourceStrip.domain := by
  obtain ⟨l, _, _, ht, hn⟩ := potential_amplitude_data i k I x hx
  exact cut_pair_source_domain l I.1 k x ht (Or.inl hn)

theorem pressure_source_domain (B N0 : ℕ) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (pressureFamily B N0).amplitude k I x ≠ 0) : x ∈ sourceStrip.domain := by
  obtain ⟨l, _, _, ht, hn⟩ := pressure_amplitude_data k I x hx
  exact cut_pair_source_domain l I.1 k x ht (Or.inr hn)

theorem sourceStrip_time {x : LiftPoint} (hx : x ∈ sourceStrip.domain) : 0 < x.1.1 :=
  BaseContextAssembly.nativeStrip_time ActualPrimary.nominal region hx.2

theorem potential_amplitude_source (B N0 : ℕ) (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) :
    EqOn ((potentialFamily B N0 i).amplitude k I)
      (fun x => ChartScales.Q I.1.val.1 ^ (-ActualPrimary.h) •
        potentialSource B N0 (i, I, k) I.1.val.1 x) sourceStrip.domain := by
  intro x hx
  simp only [potentialFamily, ite_eq_left (sourceStrip_time hx)]
  rfl

theorem pressure_amplitude_source (B N0 : ℕ) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) :
    EqOn ((pressureFamily B N0).amplitude k I)
      (fun x => ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        pressureSource B N0 (I, k) I.1.val.1 x) sourceStrip.domain := by
  intro x hx
  simp only [pressureFamily, ite_eq_left (sourceStrip_time hx)]
  rfl

/-- The identity chart only needs its formula on the genuine source
domain.  Its closure condition follows from actual amplitude support. -/
noncomputable def identitySourceChartOn {N : ℕ} {K I : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (hc : PhysicalCopyBounds.SupportCells f)
    {a b h r Z σ : ℝ} {gap : ℕ} (ha : 0 < a)
    (hs : LocalPhysicalCopyBounds.SupportData f a b h r Z gap)
    (s : StripData LiftPoint) (source : I → ℕ → LiftPoint → ℂ)
    (idx : K → PhysicalWaveSum.WaveIndex N → I)
    (he : ∀ k J, EqOn (f.amplitude k J)
      (fun x => ChartScales.Q J.1.val.1 ^ σ • source (idx k J) J.1.val.1 x) s.domain)
    (hd : ∀ k J x, f.amplitude k J x ≠ 0 → x ∈ s.domain) :
    LocalPhysicalCopyBounds.CommonChart f hc a b h r σ source where
  sourceIndex := idx
  map _ _ := id
  domain _ _ := s.domain
  open_domain _ _ := s.isOpen_domain
  smooth _ _ := contDiffOn_id
  positive_jets m := by
    refine ⟨1, le_rfl, 0, ?_⟩
    intro k J x hx j hj hjm
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
        (ContinuousLinearMap.id ℝ LiftPoint) x hj).trans (by simp)
  amplitude_eq := he
  contains k J z _ _ _ _ hz := by
    have hrad := (hs.tsupport_geometry J k hz).1
    have hm := (PhysicalWaveSum.commonLift_smoothAt h J.1.val.1 (f.gap J.1)
      (PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
          hrad))).continuousAt
    exact hm.continuousWithinAt.mem_closure hz
      (fun y hy => hd k J _ (PhysicalWaveSum.globalWave_ne_zero_amp hy))

/-- Potential chart, constructed using `identitySourceChartOn`. -/
noncomputable def potentialChart (B N0 : ℕ) (i : Fin 3) :
    LocalPhysicalCopyBounds.CommonChart (potentialFamily B N0 i) (potentialCells B N0 i)
      innerRadius outerRadius ActualPrimary.h ActualPrimary.slots.radius (-ActualPrimary.h)
      (potentialSource B N0) :=
  identitySourceChartOn _ _ innerRadius_pos (potential_support B N0 i) sourceStrip _
    (fun k I => (i, I, k)) (potential_amplitude_source B N0 i) (potential_source_domain B N0 i)

/-- Pressure chart, constructed using `identitySourceChartOn`. -/
noncomputable def pressureChart (B N0 : ℕ) :
    LocalPhysicalCopyBounds.CommonChart (pressureFamily B N0) (pressureCells B N0)
      innerRadius outerRadius ActualPrimary.h ActualPrimary.slots.radius
      (-(2 * CoordinateAlgebra.A ActualPrimary.h)) (pressureSource B N0) :=
  identitySourceChartOn _ _ innerRadius_pos (pressure_support B N0) sourceStrip _
    (fun k I => (I, k)) (pressure_amplitude_source B N0) (pressure_source_domain B N0)

theorem carrier_frequencies (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    |(carrier (B := B) (N0 := N0) L k).angular| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |(carrier (B := B) (N0 := N0) L k).axial| ≤ ActualPhaseJetBounds.phaseSize B N0 ∧
    |(carrier (B := B) (N0 := N0) L k).radial| ≤ ActualPhaseJetBounds.phaseSize B N0 := by
  by_cases hL : L ∈ active (B := B) (N0 := N0)
  · simp only [carrier, dite_eq_left hL, selectedCarrier, ActualSignedPhysicalData.carrier]
    exact ActualPhaseJetBounds.phase_constants_bound (selected L hL)
  · simp only [carrier, dite_eq_right hL, ActualSignedPhysicalData.carrier, abs_zero]
    have hP := (ActualPhaseJetBounds.one_le_phaseSize (B := B) (N0 := N0)).trans' zero_le_one
    exact ⟨hP, hP, hP⟩

end SourceCharts

section ActualRegularity

variable {B N0 : ℕ}

/-- Native past, given by `{x | 0 < x.1 ∧ 0 < x.2.1.1}`. -/
noncomputable def nativePast : Set LocalSignedRequest.Point :=
  {x | 0 < x.1 ∧ 0 < x.2.1.1}

theorem sourceFamily_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (SignedLabel B N0 × Frequency) → ℕ → LocalSignedRequest.Point → E)
    (hf : ∀ l n, ContDiffOn ℝ ∞ (f l n) nativePast)
    (I : SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (sourceFamily f I n) nativePast := by
  by_cases hn : n = I.1.1.val.1
  · cases hc : sourceChoice (B := B) (N0 := N0) I with
    | none => rw [sourceFamily_eq_zero _ _ _ (Or.inr hc)]; exact contDiffOn_const
    | some l => rw [sourceFamily_eq_some _ _ _ hn l hc]; exact hf l n
  · rw [sourceFamily_eq_zero _ _ _ (Or.inl hn)]
    exact contDiffOn_const

theorem nativePotentialSource_smooth (B N0 : ℕ) (I : SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (nativePotentialSource B N0 I n) nativePast := by
  apply sourceFamily_smooth
  intro l n
  exact (InitialNativeRegularity.copyPotentialCoefficient_smooth l.1 l.2 n).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => hx)

theorem nativePressureSource_smooth (B N0 : ℕ) (I : SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (nativePressureSource B N0 I n) nativePast := by
  apply sourceFamily_smooth
  intro l n
  exact (InitialNativeRegularity.copyPressureCoefficient_smooth_radial l.1 l.2 n).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => hx)

/-- Padded past, given by `PhysicalClassBounds.cylindricalDomain innerRadius outerRadius ∩ {x |
0 < x.1.1}`. -/
noncomputable def paddedPast : Set LiftPoint :=
  PhysicalClassBounds.cylindricalDomain innerRadius outerRadius ∩ {x | 0 < x.1.1}

theorem paddedPast_open : IsOpen paddedPast :=
  (PhysicalClassBounds.cylindricalDomain_open _ _).inter
    (isOpen_lt continuous_const continuous_fst.fst)

theorem paddedPast_map : MapsTo PhysicalClassBounds.cylindricalMap paddedPast nativePast := by
  intro x hx
  refine ⟨?_, hx.2⟩
  exact Real.sqrt_pos.mpr (PhysicalGraphBounds.sum_sq_pos
    (PhysicalClassBounds.cylindricalDomain_axisFree innerRadius_pos hx.1))

theorem potential_amplitude_smooth (B N0 : ℕ) (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((potentialFamily B N0 i).amplitude k I) paddedPast := by
  have hm : ContDiffOn ℝ ∞ PhysicalClassBounds.cylindricalMap paddedPast :=
    (PhysicalClassBounds.cylindricalMap_smooth innerRadius_pos).mono inter_subset_left
  have hsrc := (nativePotentialSource_smooth B N0 (I, k) I.1.val.1).comp hm paddedPast_map
  have hrot : ContDiffOn ℝ ∞ (fun x : LiftPoint =>
      CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)) paddedPast :=
    CartesianCopySource.rotationMap_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
      (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree innerRadius_pos hx.1)
  have hv := (ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn
    (hrot.clm_apply hsrc)
  apply (hv.const_smul (ChartScales.Q I.1.val.1 ^ (-ActualPrimary.h))).congr
  intro x hx
  have ht : 0 < x.1.1 := hx.2
  simp only [potentialFamily, ite_eq_left ht]
  rfl

theorem pressure_amplitude_smooth (B N0 : ℕ) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((pressureFamily B N0).amplitude k I) paddedPast := by
  have hm : ContDiffOn ℝ ∞ PhysicalClassBounds.cylindricalMap paddedPast :=
    (PhysicalClassBounds.cylindricalMap_smooth innerRadius_pos).mono inter_subset_left
  have hsrc := (nativePressureSource_smooth B N0 (I, k) I.1.val.1).comp hm paddedPast_map
  apply (hsrc.const_smul (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A
      ActualPrimary.h)))).congr
  intro x hx
  have ht : 0 < x.1.1 := hx.2
  simp only [pressureFamily, ite_eq_left ht, Function.comp_apply]

theorem commonLift_mem_paddedPast (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus innerRadius
        outerRadius) :
    PhysicalWaveSum.commonLift ActualPrimary.h n d w ∈ paddedPast := by
  refine ⟨?_, PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h n d hw⟩
  change innerRadius / 2 < ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h
      n d w)‖ ∧
    ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h n d w)‖ < outerRadius +
        1
  rw [liftXY_common]
  have hu : ‖PhysicalGraphBounds.scaledRadial n w‖ ≤ outerRadius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hann.1
  have hl : innerRadius ≤ ‖PhysicalGraphBounds.scaledRadial n w‖ := hann.2
  exact ⟨by linarith [innerRadius_pos], by linarith⟩

theorem potentialSmooth (B N0 : ℕ) (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialFamily B N0 i) innerRadius ActualPrimary.h
      ActualPrimary.slots.radius := by
  let hr := potential_support B N0 i
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open paddedPast_open
      (potential_amplitude_smooth B N0 i k I)
      (commonLift_mem_paddedPast _ _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (potentialCells B N0 i).term_tsupport_mem innerRadius_pos I k
      (hr.tsupport_geometry I k ht).1 ht
    have hp := profileRegion_contains (B := B) (N0 := N0) I.1 k w hw hc j hj
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (profileRegion_open I.1)
        ((carrierProfiles (B := B) (N0 := N0)).smooth (k, I.1)).fst hp,
      LocalPhysicalCopyBounds.SmoothNear.of_open (profileRegion_open I.1)
        ((carrierProfiles (B := B) (N0 := N0)).smooth (k, I.1)).snd hp⟩

theorem pressureSmooth (B N0 : ℕ) :
    LocalPhysicalCopyBounds.SmoothData (pressureFamily B N0) innerRadius ActualPrimary.h
      ActualPrimary.slots.radius := by
  let hr := pressure_support B N0
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open paddedPast_open
      (pressure_amplitude_smooth B N0 k I)
      (commonLift_mem_paddedPast _ _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (pressureCells B N0).term_tsupport_mem innerRadius_pos I k
      (hr.tsupport_geometry I k ht).1 ht
    have hp := profileRegion_contains (B := B) (N0 := N0) I.1 k w hw hc j hj
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (profileRegion_open I.1)
        ((carrierProfiles (B := B) (N0 := N0)).smooth (k, I.1)).fst hp,
      LocalPhysicalCopyBounds.SmoothNear.of_open (profileRegion_open I.1)
        ((carrierProfiles (B := B) (N0 := N0)).smooth (k, I.1)).snd hp⟩

end ActualRegularity

section PhysicalData

/-- Actual initial potential copies with their proved support, local
regularity and uniform native jets. -/
noncomputable def potentialWaveData (B N0 : ℕ) :
    PhysicalStageBounds.WaveData ActualPrimary.h LiftPoint (Fin 3 × SourceIndex) Frequency (Fin 3)
        where
  lowerRadius := innerRadius
  upperRadius := outerRadius
  nativeWidth := ActualPrimary.slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := 1
  shift := -ActualPrimary.h
  harmonics := 1
  gapBound := CommonWindow.gap ActualPrimary.h
  lower_pos := innerRadius_pos
  width_nonneg := ActualPrimary.slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight _ _ x := Real.sqrt (sourceStrip.zeta x)
  source := potentialSource B N0
  source_bounds := potentialSource_bounds B N0
  copies := potentialFamily B N0
  cells := potentialCells B N0
  chart := potentialChart B N0
  chart_maps _ _ _ := fun _ hx => hx
  carrier := potentialCarrier B N0
  support := potential_support B N0
  smooth := potentialSmooth B N0
  frequencies _ k L := carrier_frequencies L k

/-- The pressure has the same copied source construction and its actual
physical pressure factor. -/
noncomputable def pressureWaveData (B N0 : ℕ) :
    PhysicalStageBounds.WaveData ActualPrimary.h LiftPoint SourceIndex Frequency Unit where
  lowerRadius := innerRadius
  upperRadius := outerRadius
  nativeWidth := ActualPrimary.slots.radius
  slowBound := 2
  frequencyBound := ActualPhaseJetBounds.phaseSize B N0
  alpha := 1
  shift := -(2 * CoordinateAlgebra.A ActualPrimary.h)
  harmonics := 1
  gapBound := CommonWindow.gap ActualPrimary.h
  lower_pos := innerRadius_pos
  width_nonneg := ActualPrimary.slots.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := ActualPhaseJetBounds.one_le_phaseSize
  strip := sourceStrip
  weight _ _ x := Real.sqrt (sourceStrip.zeta x)
  source := pressureSource B N0
  source_bounds := pressureSource_bounds B N0
  copies _ := pressureFamily B N0
  cells _ := pressureCells B N0
  chart _ := pressureChart B N0
  chart_maps _ _ _ := fun _ hx => hx
  carrier _ := pressureCarrier B N0
  support _ := pressure_support B N0
  smooth _ := pressureSmooth B N0
  frequencies _ k L := carrier_frequencies L k

theorem potentialWaveData_vector (B N0 : ℕ) :
    (potentialWaveData B N0).vector = potential B N0 := rfl

theorem pressureWaveData_pressure (B N0 : ℕ) :
    (pressureWaveData B N0).pressure = pressure B N0 := rfl

theorem potential_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (potential B N0) PhysicalWaveSum.preterminal :=
  (potentialWaveData B N0).vector_smooth ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half

theorem pressure_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (pressure B N0) PhysicalWaveSum.preterminal :=
  (pressureWaveData B N0).pressure_smooth ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half

end PhysicalData

section LiteralCopies

variable {B N0 : ℕ}

/-- Positive index, given by `ActualSignedPhysicalData.positiveIndex (bandLabel l)`. -/
noncomputable def positiveIndex (l : SignedLabel B N0) : PhysicalWaveSum.WaveIndex 1 :=
  ActualSignedPhysicalData.positiveIndex (bandLabel l)

theorem positiveIndex_band (l : SignedLabel B N0) :
    (positiveIndex l).1.val.1 = BaseChartJets.cellBand l.2 := rfl

theorem copyAmplitude_summable (l : SignedLabel B N0) (n : ℕ) (x : Point) :
    Summable (fun k => copyAmplitude l k n x) := by
  let hfin := ((copyCells l).locallyFinite n).point_finite (nativeOfFull x)
  apply summable_of_ne_finset_zero (s := hfin.toFinset)
  intro k hk
  by_contra hn
  apply hk
  exact hfin.mem_toFinset.mpr (copied_support _ _ cut_native_velocity_support l n k hn)

theorem cut_amplitude_self (l : SignedLabel B N0) (x : Point) :
    (cutCoefficients l).amplitude (BaseChartJets.cellBand l.2) x =
      ∑' k, copyAmplitude l k (BaseChartJets.cellBand l.2) x := by
  let m := BaseChartJets.cellBand l.2
  have hn : near l m := near_self l
  have hs (l : SignedLabel B N0) (y : Native)
      (hy : CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1 l.2 y) ≠ 0) :
      y.2 ∈ (ActualPrimary.clockWindow l.2).core := by
    apply ActualPrimary.attachedRawVelocity_core l.1 l.2 y
    intro hz
    exact hy (by rw [hz, map_zero])
  have hu : periodized (CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
        (ActualPrimary.attachedRawVelocity l.1 l.2 y)) l m (nativeOfFull x) =
      (ActualPrimary.chartCoefficients l.1 l.2).amplitude m x := by
    rw [ActualPrimary.chartCoefficients_amplitude_copies l.1 l.2 m (CommonWindow.index_le hn.2)]
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_left hn, ←
        tsum_const_smul'']
    rw [coefficientScale_eq]
    rfl
  have he := periodized_cut_eq (CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
      (ActualPrimary.attachedRawVelocity l.1 l.2 y)) hs l m (nativeOfFull x) x.2
  change _ = ActualPrimary.chartCutoff l.1 l.2 m x • _ at he
  rw [hu] at he
  exact he.symm

theorem cut_pressure_self (l : SignedLabel B N0) (x : Point) :
    (cutCoefficients l).pressure (BaseChartJets.cellBand l.2) x =
      ∑' k, copyPressureCoefficient l k (BaseChartJets.cellBand l.2) x := by
  let m := BaseChartJets.cellBand l.2
  have hn : near l m := near_self l
  have hu : periodized (2 * CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)
      l m (nativeOfFull x) = (ActualPrimary.chartCoefficients l.1 l.2).pressure m x := by
    rw [ActualPrimary.chartCoefficients_pressure_copies l.1 l.2 m (CommonWindow.index_le hn.2)]
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_left hn, ←
        tsum_const_smul'']
    rw [coefficientScale_eq]
    rfl
  have he := periodized_cut_eq (2 * CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)
    (fun l y => ActualPrimary.attachedRawPressure_core l.1 l.2 y) l m (nativeOfFull x) x.2
  change _ = ActualPrimary.chartCutoff l.1 l.2 m x • _ at he
  rw [hu] at he
  exact he.symm

theorem potentialCoefficient_self (l : SignedLabel B N0) (x : Point) :
    potentialCoefficient l (BaseChartJets.cellBand l.2) x =
      ∑' k, copyPotentialCoefficient l k (BaseChartJets.cellBand l.2) x := by
  let m := BaseChartJets.cellBand l.2
  let A := ActualSignedPhysicalData.potentialMap ((cutCoefficients l).frequency m)
    ((cutCoefficients l).normal fullStrip (directions B) m x)
  change A ((cutCoefficients l).amplitude m x) = ∑' k, A (copyAmplitude l k m x)
  rw [cut_amplitude_self, ContinuousLinearMap.map_tsum _ (copyAmplitude_summable l m x)]

theorem nativePotentialSource_active (l : SignedLabel B N0) (k : Frequency) :
    nativePotentialSource B N0 (positiveIndex l, k) (BaseChartJets.cellBand l.2) =
      fun x => copyPotentialCoefficient l k (BaseChartJets.cellBand l.2) (x, 0) := by
  have hl : bandLabel l ∈ active (B := B) (N0 := N0) := ⟨l, rfl⟩
  apply sourceFamily_eq_some _ _ _ rfl (l, k)
  simp only [sourceChoice, positiveIndex, ActualSignedPhysicalData.positiveIndex,
    dite_eq_left hl, selected_eq, ite_true]

theorem nativePressureSource_active (l : SignedLabel B N0) (k : Frequency) :
    nativePressureSource B N0 (positiveIndex l, k) (BaseChartJets.cellBand l.2) =
      fun x => copyPressureCoefficient l k (BaseChartJets.cellBand l.2) (x, 0) := by
  have hl : bandLabel l ∈ active (B := B) (N0 := N0) := ⟨l, rfl⟩
  apply sourceFamily_eq_some _ _ _ rfl (l, k)
  simp only [sourceChoice, positiveIndex, ActualSignedPhysicalData.positiveIndex,
    dite_eq_left hl, selected_eq, ite_true]

theorem dynamics_copyPoint_self (l : SignedLabel B N0) (k : Frequency) (x : Point) :
    ActualPrimaryDynamics.copyPoint l.1 l.2 (BaseChartJets.cellBand l.2) k x =
      ((nativeOfFull x).1, (geometry (bandLabel l)).coordinates k (nativeOfFull x).2) := by
  change (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute (BaseChartJets.cellBand l.2) x.1),
    (ActualPrimary.geometry l.1 l.2).coordinates k
      (ActualPrimary.toAbsolute (BaseChartJets.cellBand l.2) x.1).2) = _
  rw [ActualPrimary.chart_nativePoint l.1 l.2 _ (CommonWindow.index_le (near_self l).2)]
  exact copyPoint_self l k (nativeOfFull x)

/-- Polar point, given by `PhysicalResidualTZ.swapCylinder (ActualSignedPhysicalData.cylinderAt
a j x)`. -/
noncomputable def polarPoint (a : ℝ) (j : PolarCharts.Index) (x : LiftPoint) : Point :=
  PhysicalResidualTZ.swapCylinder (ActualSignedPhysicalData.cylinderAt a j x)

theorem polarPoint_fst {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a j) :
    (polarPoint a j x).1 = PhysicalClassBounds.cylindricalMap x := by
  have hh := ActualSignedPhysicalData.cylinderAt_fst ha j hx
  exact congrArg PhysicalResidualTZ.swapSlow hh

theorem slotPoint_polar (l : SignedLabel B N0) (k : Frequency)
    (a : ℝ) (j : PolarCharts.Index) (x : LiftPoint) :
    ActualPrimaryDynamics.slotPoint l.1 l.2 (BaseChartJets.cellBand l.2) k (polarPoint a j x) =
      ActualSignedGeometry.slotCoordinates (geometry (bandLabel l)) k
        (ActualSignedPhysicalData.cylinderAt a j x) := by
  rw [ActualPrimaryDynamics.slotPoint, dynamics_copyPoint_self]
  rfl

theorem phase_polar (l : SignedLabel B N0) (k : Frequency)
    (a : ℝ) (j : PolarCharts.Index) (x : LiftPoint)
    (hc : (geometry (bandLabel l)).coordinates k x.2 ∈ (ActualPrimary.clockWindow l.2).core) :
    (cutCoefficients l).phase (BaseChartJets.cellBand l.2) (polarPoint a j x) =
      ((selectedCarrier l k).withChart j).phase a ActualPrimary.h (BaseChartJets.cellBand l.2)
        ActualPrimary.slots.radius (PhysicalWaveSum.upLift (gap (bandLabel l)) x) := by
  have hk : (ActualPrimaryDynamics.copyPoint l.1 l.2 (BaseChartJets.cellBand l.2) k
      (polarPoint a j x)).2 ∈ (ActualPrimary.clockWindow l.2).core := by
    rw [dynamics_copyPoint_self]
    exact hc
  have he := (ActualPrimaryDynamics.phase_germ l.1 l.2 (BaseChartJets.cellBand l.2) k hk).eq_of_nhds
  rw [div_self (PartitionedCovariance.actual_carrier_ne_zero _ _), one_mul, slotPoint_polar] at he
  rw [show ((selectedCarrier l k).withChart j).phase a ActualPrimary.h (BaseChartJets.cellBand l.2)
      ActualPrimary.slots.radius (PhysicalWaveSum.upLift (gap (bandLabel l)) x) =
      ActualPrimaryDynamics.nativePhase l.1 l.2
        (ActualSignedGeometry.slotCoordinates (geometry (bandLabel l)) k
          (ActualSignedPhysicalData.cylinderAt a j x)) from
    ActualSignedPhysicalData.carrier_phase_eq_native ActualPrimary.slots (spatialLabel l)
      (gap (bandLabel l)) k _ _ _ _ _ a j x]
  exact he

end LiteralCopies

section PhysicalCopyIdentities

variable {B N0 : ℕ}

theorem copyPotential_fast (l : SignedLabel B N0) (k : Frequency) {x : Point}
    (hx : copyPotentialCoefficient l k (BaseChartJets.cellBand l.2) x ≠ 0) :
    (geometry (bandLabel l)).coordinates k x.1.2.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  have hc : nativeOfFull x ∈ (copyCells l).carrier (BaseChartJets.cellBand l.2) k := by
    by_contra hc
    exact hx (copyPotential_zero_germ l k _ hc).eq_of_nhds
  exact hc

theorem copyPressure_fast (l : SignedLabel B N0) (k : Frequency) {x : Point}
    (hx : copyPressureCoefficient l k (BaseChartJets.cellBand l.2) x ≠ 0) :
    (geometry (bandLabel l)).coordinates k x.1.2.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  have hc : nativeOfFull x ∈ (copyCells l).carrier (BaseChartJets.cellBand l.2) k := by
    by_contra hc
    exact hx (copyPressure_zero_germ l k _ hc).eq_of_nhds
  exact hc

theorem up_commonLift (h : ℝ) (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    PhysicalWaveSum.upLift d (PhysicalWaveSum.commonLift h n d w) =
      PhysicalGraphBounds.physicalLift h n w := PhysicalWaveSum.up_down d _

theorem graph_aux_common (h : ℝ) (n d : ℕ) (w : ProblemStatement.SpaceTime) :
    (PhysicalMeanJetBounds.graph h n d w).2.2 = (PhysicalWaveSum.commonLift h n d w).2 := rfl

theorem potential_amplitude_active (l : SignedLabel B N0) (k : Frequency) (i : Fin 3)
    (x : LiftPoint) (ht : 0 < x.1.1) :
    (potentialFamily B N0 i).amplitude k (positiveIndex l) x =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
        (CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)
          (copyPotentialCoefficient l k (BaseChartJets.cellBand l.2)
            (PhysicalClassBounds.cylindricalMap x, 0))) i := by
  simp only [potentialFamily, ite_eq_left ht, CartesianCopySource.rotatedSource,
    positiveIndex_band, nativePotentialSource_active]

theorem pressure_amplitude_active (l : SignedLabel B N0) (k : Frequency)
    (x : LiftPoint) (ht : 0 < x.1.1) :
    (pressureFamily B N0).amplitude k (positiveIndex l) x =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        copyPressureCoefficient l k (BaseChartJets.cellBand l.2)
          (PhysicalClassBounds.cylindricalMap x, 0) := by
  simp only [pressureFamily, ite_eq_left ht, positiveIndex_band, nativePressureSource_active]

theorem potential_term (l : SignedLabel B N0) (k : Frequency) (i : Fin 3)
    (w : ProblemStatement.SpaceTime) :
    (potentialFamily B N0 i).term innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) k w =
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius
        ((selectedCarrier l k).withChart
          (PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
              (BaseChartJets.cellBand l.2) w)))
        ((potentialFamily B N0 i).amplitude k (positiveIndex l)) 1 w := by
  change PhysicalWaveSum.globalWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
    (gap (bandLabel l)) ActualPrimary.slots.radius (carrier (bandLabel l) k) _ 1 w = _
  rw [carrier_bandLabel]
  rfl

theorem pressure_term (l : SignedLabel B N0) (k : Frequency) (w : ProblemStatement.SpaceTime) :
    (pressureFamily B N0).term innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) k w =
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius
        ((selectedCarrier l k).withChart
          (PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
              (BaseChartJets.cellBand l.2) w)))
        ((pressureFamily B N0).amplitude k (positiveIndex l)) 1 w := by
  change PhysicalWaveSum.globalWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
    (gap (bandLabel l)) ActualPrimary.slots.radius (carrier (bandLabel l) k) _ 1 w = _
  rw [carrier_bandLabel]
  rfl

theorem potential_commonWave (l : SignedLabel B N0) (k : Frequency) (i : Fin 3)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
        :
    PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
      (gap (bandLabel l)) ActualPrimary.slots.radius ((selectedCarrier l k).withChart j)
      ((potentialFamily B N0 i).amplitude k (positiveIndex l)) 1 w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
        (CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w))
          (copyPotentialCoefficient l k (BaseChartJets.cellBand l.2)
            (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
                (bandLabel l)) w, 0))) i) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius j
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  rw [PhysicalWaveSum.commonWave,
    potential_amplitude_active l k i _ (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h
      (BaseChartJets.cellBand l.2) (gap (bandLabel l)) hw)]
  simp only [Int.cast_one, mul_one]
  by_cases hz : copyPotentialCoefficient l k (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w, 0) = 0
  · simp only [show PhysicalClassBounds.cylindricalMap
        (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w) =
        PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w from rfl,
      hz, map_zero, Pi.zero_apply, smul_zero, zero_mul]
  · have hf := copyPotential_fast l k (x :=
        (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w, 0)) hz
    change (geometry (bandLabel l)).coordinates k
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w).2.2 ∈ _ at hf
    rw [graph_aux_common] at hf
    have hp := phase_polar l k innerRadius j
      (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w)
      hf
    rw [up_commonLift] at hp
    rw [← hp]
    rfl

theorem pressure_commonWave (l : SignedLabel B N0) (k : Frequency)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
        :
    PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
      (gap (bandLabel l)) ActualPrimary.slots.radius ((selectedCarrier l k).withChart j)
      ((pressureFamily B N0).amplitude k (positiveIndex l)) 1 w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        copyPressureCoefficient l k (BaseChartJets.cellBand l.2)
          (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w, 0)) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius j
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  rw [PhysicalWaveSum.commonWave,
    pressure_amplitude_active l k _ (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h
      (BaseChartJets.cellBand l.2) (gap (bandLabel l)) hw)]
  simp only [Int.cast_one, mul_one]
  by_cases hz : copyPressureCoefficient l k (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w, 0) = 0
  · simp only [show PhysicalClassBounds.cylindricalMap
        (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w) =
        PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w from rfl,
      hz, smul_zero, zero_mul]
  · have hf := copyPressure_fast l k (x :=
        (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w, 0)) hz
    change (geometry (bandLabel l)).coordinates k
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w).2.2 ∈ _ at hf
    rw [graph_aux_common] at hf
    have hp := phase_polar l k innerRadius j
      (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w)
      hf
    rw [up_commonLift] at hp
    rw [← hp]
    rfl

theorem potential_rotated_sum (l : SignedLabel B N0) (x : Point)
    (Y : PhysicalGraphBounds.Plane) (i : Fin 3) :
    (∑' k, (CartesianCopySource.rotationMap Y
      (copyPotentialCoefficient l k (BaseChartJets.cellBand l.2) x)) i) =
      (CartesianCopySource.rotationMap Y (potentialCoefficient l (BaseChartJets.cellBand l.2) x)) i
          := by
  let A := ActualSignedPhysicalData.potentialMap ((cutCoefficients l).frequency
      (BaseChartJets.cellBand l.2))
    ((cutCoefficients l).normal fullStrip (directions B) (BaseChartJets.cellBand l.2) x)
  have hs : Summable (fun k => copyPotentialCoefficient l k (BaseChartJets.cellBand l.2) x) :=
    A.summable (copyAmplitude_summable l _ x)
  let R : ComplexVector →L[ℝ] ℂ := (ContinuousLinearMap.proj i).comp
      (CartesianCopySource.rotationMap Y)
  rw [potentialCoefficient_self]
  exact (R.map_tsum hs).symm

theorem potential_periodized (l : SignedLabel B N0) (i : Fin 3)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal) :
    (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
        (CartesianCopySource.rotationMap (PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand
            l.2) w)
          (potentialCoefficient l (BaseChartJets.cellBand l.2)
            (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
                (bandLabel l)) w, 0))) i) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius
          (PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
              (BaseChartJets.cellBand l.2) w))
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [potential_term, potential_commonWave l _ i _ w hw, liftXY_common]
  rw [tsum_mul_right, tsum_const_smul'', potential_rotated_sum]

theorem pressure_periodized (l : SignedLabel B N0)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal) :
    (pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        (cutCoefficients l).pressure (BaseChartJets.cellBand l.2)
          (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w, 0)) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius
          (PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
              (BaseChartJets.cellBand l.2) w))
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [pressure_term, pressure_commonWave l _ _ w hw]
  rw [tsum_mul_right, tsum_const_smul'', ← cut_pressure_self]

end PhysicalCopyIdentities

section ExactExteriorSupport

variable {B N0 : ℕ}

/-- Physical X, given by `PhysicalWaveSum.physicalPosition w 0 ^ 2 / (2 *
PhysicalWaveSum.physicalQ ActualPrimary.h w)`. -/
noncomputable def physicalX (w : ProblemStatement.SpaceTime) : ℝ :=
  PhysicalWaveSum.physicalPosition w 0 ^ 2 / (2 * PhysicalWaveSum.physicalQ ActualPrimary.h w)

theorem cut_pair_physicalX (l : SignedLabel B N0) (L : PhysicalWaveSum.BandLabel)
    (k : Frequency) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hne : cutNativeVelocity l (nativeAt L k
        (PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w)) ≠ 0 ∨
      cutNativePressure l (nativeAt L k
        (PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w)) ≠ 0) :
    physicalX w ∈ Ioo (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
  let x := PhysicalWaveSum.commonLift ActualPrimary.h L.val.1 (gap L) w
  have ht : 0 < x.1.1 := PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h L.val.1 (gap L) hw
  have hd := cut_pair_support l (nativeAt L k x) hne
  have hx := cut_pair_domain l L k x ht hne
  have hX := ActualPrimaryCovariance.physicalPosition_normalized L.val.1 hx
  change ActualPrimary.physicalPosition L.val.1 (PhysicalMeanJetBounds.graph ActualPrimary.h
      L.val.1 (gap L) w) 0 ^ 2 /
      (2 * ActualPrimary.physicalScale L.val.1 (PhysicalMeanJetBounds.graph ActualPrimary.h L.val.1
          (gap L) w)) = _ at hX
  rw [physicalPosition_graph, physicalScale_graph _ _ hw] at hX
  have hr := PrimaryTargetBounds.profileRadius_sq (F := ActualPrimary.outgoing)
    (p := slowInput x) ht
  change WaveEdgeExtension.nativeRadius ActualPrimary.h (nativeAt L k x) ^ 2 / 2 = _ at hr
  have he : physicalX w = WaveEdgeExtension.nativeRadius ActualPrimary.h (nativeAt L k x) ^ 2 / 2 :=
    hX.trans hr.symm
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hrad := ha.trans hd.1.1
  have hla : (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) ^ 2 =
      2 * NominalConeAssembly.activeLeft ActualPrimary.nominal :=
    Real.sq_sqrt (mul_nonneg (by
        norm_num) (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal).le)
  have hlb : (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ^ 2 =
      2 * NominalConeAssembly.activeRight ActualPrimary.nominal :=
    Real.sq_sqrt (mul_nonneg (by
        norm_num) (LeadingStressWeights.activeRight_pos ActualPrimary.nominal).le)
  have hlo := mul_pos (sub_pos.mpr hd.1.1) (add_pos hrad ha)
  have hhi := mul_pos (sub_pos.mpr hd.1.2) (add_pos hb hrad)
  rw [he]
  constructor <;> nlinarith

theorem potential_amplitude_zero_exterior (B N0 : ℕ) (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hX : physicalX w ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    (potentialFamily B N0 i).amplitude k I
      (PhysicalWaveSum.commonLift ActualPrimary.h I.1.val.1 (gap I.1) w) = 0 := by
  by_contra hn
  obtain ⟨l, _, _, _, hraw⟩ := potential_amplitude_data i k I _ hn
  have hx := cut_pair_physicalX l I.1 k w hw (Or.inl hraw)
  exact hX ⟨hx.1.le, hx.2.le⟩

theorem pressure_amplitude_zero_exterior (B N0 : ℕ) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hX : physicalX w ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    (pressureFamily B N0).amplitude k I
      (PhysicalWaveSum.commonLift ActualPrimary.h I.1.val.1 (gap I.1) w) = 0 := by
  by_contra hn
  obtain ⟨l, _, _, _, hraw⟩ := pressure_amplitude_data k I _ hn
  have hx := cut_pair_physicalX l I.1 k w hw (Or.inr hraw)
  exact hX ⟨hx.1.le, hx.2.le⟩

theorem copy_sum_zero_of_amplitudes_zero {N : ℕ} {K : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (a h r : ℝ) (w : ProblemStatement.SpaceTime)
    (hz : ∀ I k, f.amplitude k I (PhysicalWaveSum.commonLift h I.1.val.1 (f.gap I.1) w) = 0) :
    f.sum a h r w = 0 := by
  have ht : ∀ I k, f.term a h r I k w = 0 := fun I k => PhysicalWaveSum.globalWave_eq_zero (hz I k)
  simp only [PhysicalCopyBounds.CopyFamily.sum, PhysicalCopyBounds.CopyFamily.periodized,
    ht, tsum_zero, finsum_zero]

theorem potential_zero_exterior (B N0 : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hX : physicalX w ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)) : potential B N0 w = 0 := by
  have hz (i : Fin 3) := copy_sum_zero_of_amplitudes_zero (potentialFamily B N0 i)
    innerRadius ActualPrimary.h ActualPrimary.slots.radius w
    (fun I k => potential_amplitude_zero_exterior B N0 i k I hw hX)
  simp only [potential, PhysicalCopyBounds.vectorSum, hz, map_zero, Finset.sum_const_zero]

theorem pressure_zero_exterior (B N0 : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hX : physicalX w ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)) : pressure B N0 w = 0 := by
  have hz := copy_sum_zero_of_amplitudes_zero (pressureFamily B N0)
    innerRadius ActualPrimary.h ActualPrimary.slots.radius w
    (fun I k => pressure_amplitude_zero_exterior B N0 k I hw hX)
  exact congrArg Complex.re hz

end ExactExteriorSupport

theorem normal_withCutoff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : LinearWaveBounds.WaveCoefficients D) (χ : ℕ → D → ℝ)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D) (n : ℕ) :
    (a.withCutoff χ).normal s d n = a.normal s d n := rfl

theorem cut_normal_lifted {B N0 : ℕ} (l : SignedLabel B N0) (n : ℕ) (x : Point) :
    (cutCoefficients l).normal fullStrip (directions B) n (PhysicalResidualTZ.swapCylinder x) =
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
          (CommonWindow.index ActualPrimary.h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
          (CommonWindow.index ActualPrimary.h n)).axial
        (ActualPrimaryCoherence.liftedPhase l.1 l.2 n) x := by
  change ((ActualPrimary.chartCoefficients l.1 l.2).withCutoff
    (ActualPrimary.chartCutoff l.1 l.2)).normal fullStrip (directions B) n _ = _
  rw [normal_withCutoff]
  exact ActualPrimaryCoherence.chart_normal_lifted region l.1 l.2 n x

section PhysicalCoordinates

theorem graph_cartesian_forward (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0) :
    PhysicalMeanJetBounds.graph h n d (z.1, CylindricalResidual.chart z.2) =
      (PhysicalResidualTZ.swapCylinder
        ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n - d)).map z)).1 := by
  have hR : 0 < ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0 :=
    mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr
  have hradius : PhysicalClassBounds.cartesianRadius
      (PhysicalGraphBounds.scaledRadial n (z.1, CylindricalResidual.chart z.2)) =
      ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0 := by
    rw [ActualSignedPhysicalData.scaledRadial_forward]
    exact (PolarCharts.radius_polar _ _).trans (abs_of_pos hR)
  have hp : PhysicalGraphBounds.radialProjection (z.1, CylindricalResidual.chart z.2) =
      PolarCharts.polar (z.2 0, z.2 1) := by
    simp [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart, PolarCharts.polar]
  have hy := congrArg Prod.snd (PhysicalWaveSum.commonLift_formula h n d hd
    (z.1, CylindricalResidual.chart z.2))
  change (CommonCoverSolve.coverPower d).symm
      (PhysicalGraphBounds.nativeGraph h n (z.1, CylindricalResidual.chart z.2)) = _ at hy
  rw [PhysicalGraphBounds.radialProfile, ActualSignedPhysicalData.radiusPower_eq_radius,
    hp, PolarCharts.radius_polar, abs_of_pos hr] at hy
  rw [PhysicalMeanJetBounds.graph, Function.comp_apply,
      PhysicalClassBounds.cylindricalMap_commonLift,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos n) h _ hr, hradius, hy]
  simp only [PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
    CylindricalResidual.chart, AxisymmetricResidual.pack_two]

theorem polarPoint_common_forward (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0)
    (hangle : z.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hchart : PhysicalGraphBounds.scaledRadial n (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j) :
    polarPoint a j (PhysicalWaveSum.commonLift h n d (z.1, CylindricalResidual.chart z.2)) =
      PhysicalResidualTZ.swapCylinder
        ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n - d)).map z) := by
  apply Prod.ext
  · rw [polarPoint_fst ha j (by simpa only [liftXY_common] using hchart)]
    exact graph_cartesian_forward h n d hd z hr
  · have he := congrArg (fun q : PhysicalResidualBridge.Cylinder => q.2)
      (ActualSignedPhysicalData.cylinderAt_physical_forward h n ha j z hr hangle hchart)
    change (PolarCharts.chart a j (PhysicalGraphBounds.liftXY
      (PhysicalWaveSum.commonLift h n d (z.1, CylindricalResidual.chart z.2)))).2 = z.2 1
    change (PolarCharts.chart a j (PhysicalGraphBounds.liftXY
      (PhysicalGraphBounds.physicalLift h n (z.1, CylindricalResidual.chart z.2)))).2 = z.2 1 at he
    rw [liftXY_common]
    rw [PhysicalGraphBounds.liftXY_physicalLift] at he
    exact he

theorem commonIndex_gap (L : PhysicalWaveSum.BandLabel) :
    ChartScales.nativeIndex ActualPrimary.h L.val.1 - gap L =
      CommonWindow.index ActualPrimary.h L.val.1 :=
  Nat.sub_sub_self (CommonWindow.index_le_native ActualPrimary.h L.val.1)

variable {B N0 : ℕ}

theorem liftedPotential_eq_mode (l : SignedLabel B N0) (n : ℕ) (x : Point) :
    CurlClassBounds.vectorPotential ((cutCoefficients l).frequency n)
      PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
          ActualPrimary.h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
          ActualPrimary.h n)).axial
      (ActualPrimaryCoherence.liftedPhase l.1 l.2 n) (ActualPrimaryCoherence.liftedAmplitude l.1
          l.2 n) x =
      HarmonicCalculus.vectorMode ((cutCoefficients l).frequency n) ((cutCoefficients l).phase n)
        (potentialCoefficient l n) (PhysicalResidualTZ.swapCylinder x) := by
  have hn := cut_normal_lifted l n x
  have ha : ActualPrimaryCoherence.liftedAmplitude l.1 l.2 n x =
      (cutCoefficients l).amplitude n (PhysicalResidualTZ.swapCylinder x) := rfl
  have hp : ActualPrimaryCoherence.liftedPhase l.1 l.2 n x =
      (cutCoefficients l).phase n (PhysicalResidualTZ.swapCylinder x) := rfl
  ext i
  simp only [CurlClassBounds.vectorPotential, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode, CurlClassBounds.coefficient, potentialCoefficient,
    HarmonicCalculus.carrier, ← hn, ha, hp]


theorem physicalPotential_eq_mode (l : SignedLabel B N0) (n : ℕ)
    {z : ProblemStatement.SpaceTime} (ht : z.1 < 1) (hr : 0 < z.2 0) :
    ActualPrimaryCoherence.physicalPotential l.1 l.2 z =
      ChartScales.Q n ^ (-ActualPrimary.h) •
        HarmonicCalculus.vectorMode ((cutCoefficients l).frequency n) ((cutCoefficients l).phase n)
          (potentialCoefficient l n) (PhysicalResidualTZ.swapCylinder
            ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
              (CommonWindow.index ActualPrimary.h n)).map z)) := by
  have he := PhysicalCurlCovariance.referencePotential_eq_on (ChartScales.Q_pos n) ActualPrimary.h
    (CommonWindow.index ActualPrimary.h n) ActualPrimaryCoherence.liftedDomain_open one_ne_zero
    (ActualPrimary.chartCoefficients_frequency_pos l.1 l.2 n).ne'
    (ActualPrimaryCoherence.liftedPhase_smooth l.1 l.2 n)
    (ActualPrimaryCoherence.liftedAmplitude l.1 l.2 n)
    (ActualPrimaryCoherence.physicalPhase l.1 l.2) (ActualPrimaryCoherence.physicalAmplitude l.1
        l.2)
    (fun z hz => by
        simpa only [one_mul] using ActualPrimaryCoherence.physicalPhase_eq l.1 l.2 n hz.1)
    (fun z hz => ActualPrimaryCoherence.physicalAmplitude_eq l.1 l.2 n hz.1)
    (ActualPrimaryCoherence.physical_source n ht hr)
  exact he.trans (congrArg (fun v : ComplexVector => ChartScales.Q n ^ (-ActualPrimary.h) • v)
    (liftedPotential_eq_mode l n _))

theorem potentialCoefficient_angle (l : SignedLabel B N0) (x : LocalSignedRequest.Point) (θ : ℝ) :
    potentialCoefficient l (BaseChartJets.cellBand l.2) (x, θ) =
      potentialCoefficient l (BaseChartJets.cellBand l.2) (x, 0) := by
  rw [potentialCoefficient_self, potentialCoefficient_self]
  apply tsum_congr
  intro k
  exact InitialNativeRegularity.copyPotentialCoefficient_angle l k _ x θ

theorem potentialCoefficient_polar (l : SignedLabel B N0) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a j) :
    potentialCoefficient l (BaseChartJets.cellBand l.2) (polarPoint a j x) =
      potentialCoefficient l (BaseChartJets.cellBand l.2) (PhysicalClassBounds.cylindricalMap x, 0)
          := by
  have he := potentialCoefficient_angle l (polarPoint a j x).1 (polarPoint a j x).2
  change potentialCoefficient l (BaseChartJets.cellBand l.2) (polarPoint a j x) =
    potentialCoefficient l (BaseChartJets.cellBand l.2) ((polarPoint a j x).1, 0) at he
  rwa [polarPoint_fst ha j hx] at he

theorem commonIndex_gap_selected (l : SignedLabel B N0) :
    ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2) - gap (bandLabel l) =
      CommonWindow.index ActualPrimary.h (BaseChartJets.cellBand l.2) := commonIndex_gap (bandLabel
          l)

end PhysicalCoordinates

section PrimaryFieldIdentities

variable {B N0 : ℕ}

theorem potential_periodized_of_chart (l : SignedLabel B N0) (i : Fin 3)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PolarCharts.chartDomain innerRadius j) :
    (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
        (CartesianCopySource.rotationMap (PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand
            l.2) w)
          (potentialCoefficient l (BaseChartJets.cellBand l.2)
            (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
                (bandLabel l)) w, 0))) i) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius j
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  have hc := PhysicalWaveSum.chooseChart_valid innerRadius_pos hann
  have he (k : Frequency) :
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius
        ((selectedCarrier l k).withChart (PhysicalWaveSum.chooseChart innerRadius
          (PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w)))
        ((potentialFamily B N0 i).amplitude k (positiveIndex l)) 1 w =
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius ((selectedCarrier l k).withChart j)
        ((potentialFamily B N0 i).amplitude k (positiveIndex l)) 1 w := by
    obtain ⟨m, hm⟩ := carrier_integer (B := B) (N0 := N0) (bandLabel l) k
    rw [carrier_bandLabel] at hm
    exact PhysicalWaveSum.commonWave_charts_agree innerRadius_pos ActualPrimary.h
      (BaseChartJets.cellBand l.2) (gap (bandLabel l)) ActualPrimary.slots.radius
      (selectedCarrier l k) ((potentialFamily B N0 i).amplitude k (positiveIndex l)) 1 w m hm _ j
          hc hj
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [potential_term, he, potential_commonWave l _ i j w hw, liftXY_common]
  rw [tsum_mul_right, tsum_const_smul'', potential_rotated_sum]

theorem pressure_periodized_of_chart (l : SignedLabel B N0)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PolarCharts.chartDomain innerRadius j) :
    (pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        (cutCoefficients l).pressure (BaseChartJets.cellBand l.2)
          (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w, 0)) *
      HarmonicCalculus.carrier ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius j
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w)) := by
  have hc := PhysicalWaveSum.chooseChart_valid innerRadius_pos hann
  have he (k : Frequency) :
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius
        ((selectedCarrier l k).withChart (PhysicalWaveSum.chooseChart innerRadius
          (PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w)))
        ((pressureFamily B N0).amplitude k (positiveIndex l)) 1 w =
      PhysicalWaveSum.commonWave innerRadius ActualPrimary.h (BaseChartJets.cellBand l.2)
        (gap (bandLabel l)) ActualPrimary.slots.radius ((selectedCarrier l k).withChart j)
        ((pressureFamily B N0).amplitude k (positiveIndex l)) 1 w := by
    obtain ⟨m, hm⟩ := carrier_integer (B := B) (N0 := N0) (bandLabel l) k
    rw [carrier_bandLabel] at hm
    exact PhysicalWaveSum.commonWave_charts_agree innerRadius_pos ActualPrimary.h
      (BaseChartJets.cellBand l.2) (gap (bandLabel l)) ActualPrimary.slots.radius
      (selectedCarrier l k) ((pressureFamily B N0).amplitude k (positiveIndex l)) 1 w m hm _ j hc hj
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [pressure_term, he, pressure_commonWave l _ j w hw]
  rw [tsum_mul_right, tsum_const_smul'', ← cut_pressure_self]

theorem potential_periodized_mode (l : SignedLabel B N0) (i : Fin 3)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PolarCharts.chartDomain innerRadius j) :
    (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
        ActualSignedPhysicalData.rotateCoefficient (PhysicalGraphBounds.scaledRadial
            (BaseChartJets.cellBand l.2) w)
          (HarmonicCalculus.vectorMode ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
            ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
            (potentialCoefficient l (BaseChartJets.cellBand l.2))
            (polarPoint innerRadius j
              (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
                  (bandLabel l)) w))) i := by
  have hc : PhysicalGraphBounds.liftXY
      (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w) ∈
        PolarCharts.chartDomain innerRadius j := by simpa only [liftXY_common] using hj
  rw [potential_periodized_of_chart l i j w hw hann hj]
  rw [ActualSignedPhysicalData.rotateCoefficient_vectorMode,
    potentialCoefficient_polar l innerRadius_pos j hc, ActualSignedPhysicalData.cartesian_rotation]
  exact smul_mul_assoc _ _ _

theorem pressureCoefficient_polar (l : SignedLabel B N0) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a j) :
    (cutCoefficients l).pressure n (polarPoint a j x) =
      (cutCoefficients l).pressure n (PhysicalClassBounds.cylindricalMap x, 0) := by
  have he : (cutCoefficients l).pressure n (polarPoint a j x) =
      (cutCoefficients l).pressure n ((polarPoint a j x).1, 0) := rfl
  rwa [polarPoint_fst ha j hx] at he

theorem pressure_periodized_mode (l : SignedLabel B N0)
    (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PolarCharts.chartDomain innerRadius j) :
    (pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
        (positiveIndex l) w =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) •
        HarmonicCalculus.mode ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
          ((cutCoefficients l).phase (BaseChartJets.cellBand l.2))
          ((cutCoefficients l).pressure (BaseChartJets.cellBand l.2))
          (polarPoint innerRadius j
            (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
                (bandLabel l)) w)) := by
  have hc : PhysicalGraphBounds.liftXY
      (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w) ∈
        PolarCharts.chartDomain innerRadius j := by simpa only [liftXY_common] using hj
  rw [pressure_periodized_of_chart l j w hw hann hj, HarmonicCalculus.mode,
    pressureCoefficient_polar l _ innerRadius_pos j hc]
  exact smul_mul_assoc _ _ _

theorem potential_periodized_cartesian (l : SignedLabel B N0) (i : Fin 3)
    (j : PolarCharts.Index) (z : ProblemStatement.SpaceTime) (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hangle : z.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) (z.1,
        CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) (z.1,
        CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain innerRadius j) :
    ((potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (positiveIndex l) (z.1, CylindricalResidual.chart z.2)).re =
      ActualPrimaryCoherence.cartesianPotential l.1 l.2 (z.1, CylindricalResidual.chart z.2) i := by
  let w := (z.1, CylindricalResidual.chart z.2)
  have hmap := polarPoint_common_forward ActualPrimary.h (BaseChartJets.cellBand l.2)
    (gap (bandLabel l)) (gap_native (bandLabel l)) innerRadius_pos j z hr hangle hj
  rw [commonIndex_gap_selected] at hmap
  have hc : PhysicalGraphBounds.liftXY
      (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w) ∈
        PolarCharts.chartDomain innerRadius j := by simpa only [liftXY_common] using hj
  have ha : (PolarCharts.chart innerRadius j
      (PhysicalGraphBounds.liftXY
        (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w))).2 = z.2 1 :=
    congrArg Prod.snd hmap
  have hp := physicalPotential_eq_mode l (BaseChartJets.cellBand l.2) ht hr
  have he := ActualSignedPhysicalData.rotateCoefficient_chart_re innerRadius_pos j hc
    (ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-ActualPrimary.h) •
      HarmonicCalculus.vectorMode ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
        ((cutCoefficients l).phase (BaseChartJets.cellBand l.2)) (potentialCoefficient l
            (BaseChartJets.cellBand l.2))
        (polarPoint innerRadius j
          (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
              l)) w))) i
  rw [ActualSignedPhysicalData.rotateCoefficient_real_smul, Pi.smul_apply] at he
  rw [ha, hmap, ← hp] at he
  rw [potential_periodized_mode l i j (z.1, CylindricalResidual.chart z.2) ht hann hj, hmap]
  have hcart := ActualPrimaryCoherence.globalPotential_forward
      (ActualPrimaryCoherence.physicalAxisRadius_pos l.2)
    (ActualPrimaryCoherence.physicalPotential l.1 l.2)
    (ActualPrimaryCoherence.physicalPotential_periodic l.1 l.2)
    (ActualPrimaryCoherence.physicalPotential_zero_axis l.1 l.2) (z := z) hr
  have hh := he.trans (congrArg (fun v : ProblemStatement.Space => v i) hcart).symm
  simp only [liftXY_common, w] at hh ⊢
  exact hh

theorem pressure_periodized_physical (l : SignedLabel B N0)
    (j : PolarCharts.Index) (z : ProblemStatement.SpaceTime) (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hangle : z.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) (z.1,
        CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius)
    (hj : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) (z.1,
        CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain innerRadius j) :
    ((pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (positiveIndex l) (z.1, CylindricalResidual.chart z.2)).re =
      ActualPrimaryCoherence.physicalPressure l.1 l.2 z := by
  have hmap := polarPoint_common_forward ActualPrimary.h (BaseChartJets.cellBand l.2)
    (gap (bandLabel l)) (gap_native (bandLabel l)) innerRadius_pos j z hr hangle hj
  rw [commonIndex_gap_selected] at hmap
  rw [pressure_periodized_mode l j (z.1, CylindricalResidual.chart z.2) ht hann hj, hmap]
  rw [Complex.smul_re]
  change ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)) *
    (ActualPrimary.piece region l.1 l.2).pressure (BaseChartJets.cellBand l.2)
      (PhysicalResidualTZ.swapCylinder ((PhysicalResidualBridge.commonGraph (ChartScales.Q
          (BaseChartJets.cellBand l.2))
        ActualPrimary.h (CommonWindow.index ActualPrimary.h (BaseChartJets.cellBand l.2))).map z))
            = _
  rw [ActualPrimaryCoherence.piece_physical_pressure region l.1 l.2 _ hr, ← mul_assoc,
    ← Real.rpow_add (ChartScales.Q_pos _), neg_add_cancel, Real.rpow_zero, one_mul]

end PrimaryFieldIdentities

section GlobalPrimaryPotential

/-- Scaled representative as an element of `ProblemStatement.SpaceTime`. -/
noncomputable def scaledRepresentative (a : ℝ) (j : PolarCharts.Index) (n : ℕ)
    (w : ProblemStatement.SpaceTime) : ProblemStatement.SpaceTime :=
  (w.1, AxisymmetricResidual.pack
    (ChartScales.Q n ^ (1 / 2 : ℝ) * (PolarCharts.chart a j (PhysicalGraphBounds.scaledRadial n
        w)).1)
    (PolarCharts.chart a j (PhysicalGraphBounds.scaledRadial n w)).2 (w.2 2))

theorem scaledRepresentative_spec {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    (w : ProblemStatement.SpaceTime)
    (hj : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    (scaledRepresentative a j n w).1 = w.1 ∧
    0 < (scaledRepresentative a j n w).2 0 ∧
    (scaledRepresentative a j n w).2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
    ((scaledRepresentative a j n w).1, CylindricalResidual.chart (scaledRepresentative a j n w).2)
        = w := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [scaledRepresentative, AxisymmetricResidual.pack_zero]
    rw [ActualSignedPhysicalData.chart_radius ha j hj]
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)
        (ActualSignedPhysicalData.chart_radius_pos ha j hj)
  · simp only [scaledRepresentative, AxisymmetricResidual.pack_one,
      PolarCharts.chart_eq_localChart ha j hj, PolarCharts.localChart_apply, add_sub_cancel_right]
    exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  · have he := (congrArg (fun y : PhysicalGraphBounds.Plane => ChartScales.Q n ^ (1 / 2 : ℝ) • y)
        (PolarCharts.polar_chart ha j hj)).trans (PhysicalGraphBounds.unscale_radial n w)
    apply Prod.ext
    · rfl
    ext i
    fin_cases i
    · simpa [scaledRepresentative, CylindricalResidual.chart,
        PhysicalGraphBounds.radialProjection_apply,
        PolarCharts.polar, mul_assoc] using congrArg Prod.fst he
    · simpa [scaledRepresentative, CylindricalResidual.chart,
        PhysicalGraphBounds.radialProjection_apply,
        PolarCharts.polar, mul_assoc] using congrArg Prod.snd he
    · simp [scaledRepresentative, CylindricalResidual.chart]

theorem exists_scaledRepresentative (n : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    ∃ z : ProblemStatement.SpaceTime, z.1 = w.1 ∧ 0 < z.2 0 ∧
      (z.1, CylindricalResidual.chart z.2) = w := by
  have hn : PhysicalGraphBounds.scaledRadial n w ≠ 0 := by
    intro h
    apply hw
    rw [← PhysicalGraphBounds.unscale_radial n w, h, smul_zero]
  let a := ‖PhysicalGraphBounds.scaledRadial n w‖
  have ha : 0 < a := norm_pos_iff.mpr hn
  have hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a a :=
    ⟨by simp only [Metric.mem_closedBall, dist_zero_right]; exact le_rfl,
      by change a ≤ ‖PhysicalGraphBounds.scaledRadial n w‖; exact le_rfl⟩
  let j := PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial n w)
  have hj := PhysicalWaveSum.chooseChart_valid ha hann
  have hz := scaledRepresentative_spec ha j n w hj
  exact ⟨scaledRepresentative a j n w, hz.1, hz.2.1, hz.2.2.2⟩

variable {B N0 : ℕ}

theorem cartesianPotential_zero_of_common_zero (l : SignedLabel B N0)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hz : potentialCoefficient l (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w, 0) = 0) :
    ActualPrimaryCoherence.cartesianPotential l.1 l.2 w = 0 := by
  by_cases haxis : PhysicalGraphBounds.radialProjection w = 0
  · apply (PhysicalCurlCovariance.globalCartesianPotential_zero_germ
      (ActualPrimaryCoherence.physicalAxisRadius_pos l.2)
      (ActualPrimaryCoherence.physicalPotential_zero_axis l.1 l.2) ?_).eq_of_nhds
    simpa [haxis, PolarCharts.radius] using ActualPrimaryCoherence.physicalAxisRadius_pos l.2
  · obtain ⟨z, ht, hr, hb⟩ := exists_scaledRepresentative (BaseChartJets.cellBand l.2) w haxis
    have hg := graph_cartesian_forward ActualPrimary.h (BaseChartJets.cellBand l.2)
      (gap (bandLabel l)) (gap_native (bandLabel l)) z hr
    rw [commonIndex_gap_selected, hb] at hg
    have hpnt : PhysicalResidualTZ.swapCylinder
        ((PhysicalResidualBridge.commonGraph (ChartScales.Q (BaseChartJets.cellBand l.2))
            ActualPrimary.h
          (CommonWindow.index ActualPrimary.h (BaseChartJets.cellBand l.2))).map z) =
        (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel
            l)) w, z.2 1) :=
      Prod.ext hg.symm rfl
    have hphys : ActualPrimaryCoherence.physicalPotential l.1 l.2 z = 0 := by
      rw [physicalPotential_eq_mode l _ (by simp only [ht]; exact hw) hr, hpnt]
      ext i
      simp only [Pi.smul_apply, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
        potentialCoefficient_angle, hz, Pi.zero_apply, zero_mul, smul_zero]
    have he := ActualPrimaryCoherence.globalPotential_forward
        (ActualPrimaryCoherence.physicalAxisRadius_pos l.2)
      (ActualPrimaryCoherence.physicalPotential l.1 l.2)
      (ActualPrimaryCoherence.physicalPotential_periodic l.1 l.2)
      (ActualPrimaryCoherence.physicalPotential_zero_axis l.1 l.2) (z := z) hr
    have hzero : PhysicalCurlCovariance.realVector (0 : ComplexVector) = 0 := by
      ext i
      simp
    simp only [hphys, hzero, map_zero, hb] at he
    exact he

theorem potentialCoefficient_zero_off_annulus (l : SignedLabel B N0)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∉
      PhysicalGraphBounds.annulus innerRadius outerRadius) :
    potentialCoefficient l (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w, 0) = 0 := by
  apply potentialCoefficient_zero
  rw [cut_amplitude_self]
  refine (tsum_congr ?_).trans tsum_zero
  intro k
  by_contra hk
  have he := copyAmplitude_nativeAt l k
    (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l)) w)
  change copyAmplitude l k (BaseChartJets.cellBand l.2)
    (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
        w, 0) = _ at he
  rw [he] at hk
  have h := cut_pair_annulus l (bandLabel l) k _
    (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
        (bandLabel l)) hw) (Or.inl hk)
  exact hann (by simpa only [liftXY_common] using h.1)

/-- Every actual periodized initial potential is the pre-existing
Cartesian primary potential, including the zero region and the axis. -/
theorem potential_periodized_eq (l : SignedLabel B N0) (i : Fin 3)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal) :
    ((potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (positiveIndex l) w).re = ActualPrimaryCoherence.cartesianPotential l.1 l.2 w i := by
  by_cases hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius
  · let j := PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
      (BaseChartJets.cellBand l.2) w)
    have hj := PhysicalWaveSum.chooseChart_valid innerRadius_pos hann
    let z := scaledRepresentative innerRadius j (BaseChartJets.cellBand l.2) w
    have hz : z.1 = w.1 ∧ 0 < z.2 0 ∧
        z.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
        (z.1, CylindricalResidual.chart z.2) = w :=
      scaledRepresentative_spec innerRadius_pos j (BaseChartJets.cellBand l.2) w hj
    have he := potential_periodized_cartesian l i j z (by
        simp only [hz.1]; exact hw) hz.2.1 hz.2.2.1
      (by simpa only [hz.2.2.2] using hann) (by simpa only [hz.2.2.2] using hj)
    simpa only [hz.2.2.2] using he
  · have hp := potentialCoefficient_zero_off_annulus l w hw hann
    have hz := cartesianPotential_zero_of_common_zero l w hw hp
    rw [potential_periodized l i w hw, hp, hz]
    simp [map_zero, smul_zero, zero_mul, Complex.zero_re]

end GlobalPrimaryPotential

section GlobalPrimaryPressure

variable {B N0 : ℕ}

/-- Physical pressure coefficient, constructed using `ActualPrimary.periodicGaussian`. -/
noncomputable def physicalPressureCoefficient (l : SignedLabel B N0)
    (z : ProblemStatement.SpaceTime) : ℂ :=
  ActualPrimary.periodicGaussian l.1 l.2 (ActualPrimaryCoherence.physicalLift z).1.2 •
    ActualPrimary.absolutePressure l.1 l.2 (ActualPrimaryCoherence.physicalLift z).1

theorem physicalPressureCoefficient_invariant (l : SignedLabel B N0) :
    CopyAngularInvariance.Invariant ActualPrimaryCoherence.physicalAngular
        (physicalPressureCoefficient l) := by
  intro x t
  unfold physicalPressureCoefficient
  rw [ActualPrimaryCoherence.physicalLift_angular]
  simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]

theorem physicalPressure_mode (l : SignedLabel B N0) (z : ProblemStatement.SpaceTime) :
    ActualPrimaryCoherence.physicalPressure l.1 l.2 z =
      (HarmonicCalculus.mode 1 (ActualPrimaryCoherence.physicalPhase l.1 l.2)
        (physicalPressureCoefficient l) z).re := rfl

theorem physicalPressure_periodic (l : SignedLabel B N0) (t r z : ℝ) :
    Periodic (fun θ => ActualPrimaryCoherence.physicalPressure l.1 l.2
      (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi) := by
  have hh := PhysicalParticularWave.mode_fullTurn
    (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 l.2)
    (ActualPrimaryCoherence.physicalPhase_angular l.1 l.2)
    (physicalPressureCoefficient_invariant l) (one_mul _)
  intro θ
  change ActualPrimaryCoherence.physicalPressure l.1 l.2
      (t, AxisymmetricResidual.pack r (θ + 2 * Real.pi) z) =
    ActualPrimaryCoherence.physicalPressure l.1 l.2 (t, AxisymmetricResidual.pack r θ z)
  rw [physicalPressure_mode, physicalPressure_mode]
  apply congrArg Complex.re
  simpa only [ActualPrimaryCoherence.physicalAngular, PhysicalParticularWave.angle_translate_pack]
      using
    hh (t, AxisymmetricResidual.pack r θ z)

theorem space_pack (q : ProblemStatement.Space) :
    AxisymmetricResidual.pack (q 0) (q 1) (q 2) = q := by
  ext i
  fin_cases i <;> simp

theorem physicalPressure_eq_of_chart_eq (l : SignedLabel B N0)
    {z z' : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) (hr' : 0 < z'.2 0)
    (he : (z.1, CylindricalResidual.chart z.2) = (z'.1, CylindricalResidual.chart z'.2)) :
    ActualPrimaryCoherence.physicalPressure l.1 l.2 z =
      ActualPrimaryCoherence.physicalPressure l.1 l.2 z' := by
  have ht0 := congrArg (fun w : ProblemStatement.SpaceTime => w.1) he
  have ht : z.1 = z'.1 := ht0
  have hz : z.2 2 = z'.2 2 := by
    simpa [CylindricalResidual.chart] using congrArg (fun x : ProblemStatement.SpaceTime => x.2 2)
        he
  have hpolar : PolarCharts.polar (z.2 0, z.2 1) = PolarCharts.polar (z'.2 0, z'.2 1) := by
    simpa [PhysicalGraphBounds.radialProjection_apply, CylindricalResidual.chart,
        PolarCharts.polar] using
      congrArg PhysicalGraphBounds.radialProjection he
  have hrad : z.2 0 = z'.2 0 := by
    have hh := congrArg PolarCharts.radius hpolar
    simpa only [PolarCharts.radius_polar, abs_of_pos hr, abs_of_pos hr'] using hh
  let f : TorusInverse.Plane → ℝ := fun q => ActualPrimaryCoherence.physicalPressure l.1 l.2
    (z'.1, AxisymmetricResidual.pack q.1 q.2 (z'.2 2))
  have hval := ActualPrimaryCoherence.periodic_value_of_polar_eq f
    (fun r => physicalPressure_periodic l z'.1 r (z'.2 2)) hr'.ne' hrad hpolar
  calc
    _ = f (z.2 0, z.2 1) := by
      apply congrArg (ActualPrimaryCoherence.physicalPressure l.1 l.2)
      apply Prod.ext
      · exact ht
      · change z.2 = AxisymmetricResidual.pack (z.2 0) (z.2 1) (z'.2 2)
        rw [← hz, space_pack]
    _ = f (z'.2 0, z'.2 1) := hval
    _ = _ := by
      change ActualPrimaryCoherence.physicalPressure l.1 l.2
        (z'.1, AxisymmetricResidual.pack (z'.2 0) (z'.2 1) (z'.2 2)) = _
      rw [space_pack]

theorem pressureCoefficient_zero_off_annulus (l : SignedLabel B N0)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∉
      PhysicalGraphBounds.annulus innerRadius outerRadius) :
    (cutCoefficients l).pressure (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
          w, 0) = 0 := by
  rw [cut_pressure_self]
  refine (tsum_congr ?_).trans tsum_zero
  intro k
  by_contra hk
  have he := copyPressure_nativeAt l k
    (PhysicalWaveSum.commonLift ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l)) w)
  change copyPressureCoefficient l k (BaseChartJets.cellBand l.2)
    (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
        w, 0) = _ at he
  rw [he] at hk
  have h := cut_pair_annulus l (bandLabel l) k _
    (PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h (BaseChartJets.cellBand l.2) (gap
        (bandLabel l)) hw) (Or.inr hk)
  exact hann (by simpa only [liftXY_common] using h.1)

theorem physicalPressure_zero_of_common_zero (l : SignedLabel B N0)
    (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0)
    (hz : (cutCoefficients l).pressure (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
        (z.1, CylindricalResidual.chart z.2), 0) = 0) :
    ActualPrimaryCoherence.physicalPressure l.1 l.2 z = 0 := by
  have hg := graph_cartesian_forward ActualPrimary.h (BaseChartJets.cellBand l.2)
    (gap (bandLabel l)) (gap_native (bandLabel l)) z hr
  rw [commonIndex_gap_selected] at hg
  have hpnt : PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q (BaseChartJets.cellBand l.2))
          ActualPrimary.h
        (CommonWindow.index ActualPrimary.h (BaseChartJets.cellBand l.2))).map z) =
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
        (z.1, CylindricalResidual.chart z.2), z.2 1) := Prod.ext hg.symm rfl
  have he := ActualPrimaryCoherence.piece_physical_pressure region l.1 l.2 (BaseChartJets.cellBand
      l.2) hr
  rw [hpnt] at he
  have hp : (cutCoefficients l).pressure (BaseChartJets.cellBand l.2)
      (PhysicalMeanJetBounds.graph ActualPrimary.h (BaseChartJets.cellBand l.2) (gap (bandLabel l))
        (z.1, CylindricalResidual.chart z.2), z.2 1) = 0 := hz
  change (HarmonicCalculus.mode ((cutCoefficients l).frequency (BaseChartJets.cellBand l.2))
    ((cutCoefficients l).phase (BaseChartJets.cellBand l.2)) ((cutCoefficients l).pressure
        (BaseChartJets.cellBand l.2))
      _).re = _ at he
  simp only [HarmonicCalculus.mode, hp, zero_mul, Complex.zero_re] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _).ne'

/-- The actual periodized pressure agrees with the original cylindrical
pressure on every positive-radius physical chart, with all angular
branches identified by the proved integer harmonic periodicity. -/
theorem pressure_periodized_eq (l : SignedLabel B N0)
    (z : ProblemStatement.SpaceTime) (ht : z.1 < 1) (hr : 0 < z.2 0) :
    ((pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (positiveIndex l) (z.1, CylindricalResidual.chart z.2)).re =
      ActualPrimaryCoherence.physicalPressure l.1 l.2 z := by
  let w := (z.1, CylindricalResidual.chart z.2)
  by_cases hann : PhysicalGraphBounds.scaledRadial (BaseChartJets.cellBand l.2) w ∈
      PhysicalGraphBounds.annulus innerRadius outerRadius
  · let j := PhysicalWaveSum.chooseChart innerRadius (PhysicalGraphBounds.scaledRadial
      (BaseChartJets.cellBand l.2) w)
    have hj := PhysicalWaveSum.chooseChart_valid innerRadius_pos hann
    let q := scaledRepresentative innerRadius j (BaseChartJets.cellBand l.2) w
    have hq : q.1 = w.1 ∧ 0 < q.2 0 ∧
        q.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
        (q.1, CylindricalResidual.chart q.2) = w :=
      scaledRepresentative_spec innerRadius_pos j (BaseChartJets.cellBand l.2) w hj
    have he := pressure_periodized_physical l j q (by simpa only [hq.1] using ht) hq.2.1 hq.2.2.1
      (by simpa only [hq.2.2.2] using hann) (by simpa only [hq.2.2.2] using hj)
    have hp := physicalPressure_eq_of_chart_eq l hq.2.1 hr hq.2.2.2
    simpa only [hq.2.2.2] using he.trans hp
  · have hp := pressureCoefficient_zero_off_annulus l w ht hann
    have hz := physicalPressure_zero_of_common_zero l z hr hp
    rw [pressure_periodized l w ht, hp, hz]
    simp only [smul_zero, zero_mul, Complex.zero_re]

end GlobalPrimaryPressure


section FiniteAggregation

variable {B N0 : ℕ}

/-- Primary index, given by `positiveIndex (l.2, l.1)`. -/
noncomputable def primaryIndex (l : ActualPrimary.Label B N0 × Fin 2) :
    PhysicalWaveSum.WaveIndex 1 := positiveIndex (l.2, l.1)

theorem primaryIndex_injective : Injective (primaryIndex (B := B) (N0 := N0)) := by
  intro l l' h
  have he : bandLabel (l.2, l.1) = bandLabel (l'.2, l'.1) := congrArg Prod.fst h
  have hh := bandLabel_injective he
  exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)

theorem eq_primaryIndex_of_data (l : SignedLabel B N0) (I : PhysicalWaveSum.WaveIndex 1)
    (hl : bandLabel l = I.1) (hi : I.2.val = 1) : primaryIndex (l.2, l.1) = I := by
  apply Prod.ext hl
  apply Subtype.ext
  exact hi.symm

theorem periodized_nonzero_copy {H : ℕ} {K : Type*} (f : PhysicalCopyBounds.CopyFamily H K)
    (a h r0 : ℝ) (I : PhysicalWaveSum.WaveIndex H) (w : ProblemStatement.SpaceTime)
    (hn : f.periodized a h r0 I w ≠ 0) : ∃ k, f.term a h r0 I k w ≠ 0 := by
  by_contra! hz
  apply hn
  simp only [PhysicalCopyBounds.CopyFamily.periodized, hz, tsum_zero]

theorem potential_periodized_index (i : Fin 3) (I : PhysicalWaveSum.WaveIndex 1)
    (w : ProblemStatement.SpaceTime)
    (hn : (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h
      ActualPrimary.slots.radius I w ≠ 0) :
    ∃ l : ActualPrimary.Label B N0 × Fin 2, primaryIndex l = I := by
  obtain ⟨k, hk⟩ := periodized_nonzero_copy _ _ _ _ _ _ hn
  obtain ⟨l, hl, hi, _, _⟩ := potential_amplitude_data i k I _
    (PhysicalWaveSum.globalWave_ne_zero_amp hk)
  exact ⟨(l.2, l.1), eq_primaryIndex_of_data l I hl hi⟩

theorem pressure_periodized_index (I : PhysicalWaveSum.WaveIndex 1)
    (w : ProblemStatement.SpaceTime)
    (hn : (pressureFamily B N0).periodized innerRadius ActualPrimary.h
      ActualPrimary.slots.radius I w ≠ 0) :
    ∃ l : ActualPrimary.Label B N0 × Fin 2, primaryIndex l = I := by
  obtain ⟨k, hk⟩ := periodized_nonzero_copy _ _ _ _ _ _ hn
  obtain ⟨l, hl, hi, _, _⟩ := pressure_amplitude_data k I _
    (PhysicalWaveSum.globalWave_ne_zero_amp hk)
  exact ⟨(l.2, l.1), eq_primaryIndex_of_data l I hl hi⟩

theorem periodized_sum_eq_active (f : PhysicalCopyBounds.CopyFamily 1 Frequency)
    (hsource : ∀ I w, f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0 →
      ∃ l : ActualPrimary.Label B N0 × Fin 2, primaryIndex l = I)
    (hsupport : ∀ I w, w ∈ PhysicalWaveSum.preterminal →
      f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0 →
      PhysicalWaveSum.physicalParams ActualPrimary.h w ∈
        PhysicalWaveSum.labelRegion (CoordinateAlgebra.D ActualPrimary.h) I.1.val)
    (n d : ℕ) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    f.sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius (primaryIndex l) w := by
  classical
  let s := ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n
  calc
    _ = ∑ I ∈ s.image primaryIndex,
        f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w := by
      apply finsum_eq_sum_of_support_subset
      intro I hI
      obtain ⟨l, hl⟩ := hsource I w hI
      refine Finset.mem_image.mpr ⟨l, ?_, hl⟩
      have hm := hsupport I w hw hI
      rw [← hl] at hm
      change (PhysicalWaveSum.physicalQ ActualPrimary.h w, PhysicalWaveSum.physicalPosition w) ∈ _
          at hm
      rw [← physicalScale_graph n d hw, ← physicalPosition_graph n d w] at hm
      exact ActualPrimary.activeLabels_cover n hx l.1 l.2 hm
    _ = _ := Finset.sum_image (fun l _ l' _ he => primaryIndex_injective he)

theorem potential_sum_eq_active (i : Fin 3) (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    (potentialFamily B N0 i).sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
          (primaryIndex l) w :=
  periodized_sum_eq_active _ (potential_periodized_index i)
    (potential_support B N0 i).periodized_support n d w hw hx

theorem pressure_sum_eq_active (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    (pressureFamily B N0).sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        (pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
          (primaryIndex l) w :=
  periodized_sum_eq_active _ pressure_periodized_index
    (pressure_support B N0).periodized_support n d w hw hx

theorem vectorSum_apply {H : ℕ} {K : Type*} (f : Fin 3 → PhysicalCopyBounds.CopyFamily H K)
    (a h r0 : ℝ) (w : ProblemStatement.SpaceTime) (i : Fin 3) :
    PhysicalCopyBounds.vectorSum f a h r0 w i = ((f i).sum a h r0 w).re := by
  unfold PhysicalCopyBounds.vectorSum
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [PhysicalWaveSum.realCoordinate_apply,
    ProblemStatement.coordinateVector]

theorem graph_smooth_of_strip (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    ContDiffAt ℝ ∞ (PhysicalMeanJetBounds.graph ActualPrimary.h n d) w := by
  have hr := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hx
  have hne : PhysicalGraphBounds.scaledRadial n w ≠ 0 := by
    intro he
    rw [PhysicalMeanJetBounds.graph_radius, he] at hr
    simp [PolarCharts.radius] at hr
  let a := ‖PhysicalGraphBounds.scaledRadial n w‖
  have ha : 0 < a := norm_pos_iff.mpr hne
  have hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a a := by
    constructor
    · change dist (PhysicalGraphBounds.scaledRadial n w) 0 ≤ a
      rw [dist_zero_right]
    · change a ≤ ‖PhysicalGraphBounds.scaledRadial n w‖
      exact le_rfl
  exact PhysicalMeanJetBounds.graph_smoothAt ha ActualPrimary.h n d hann

theorem spatialCurl_finset_sum {I : Type*} (s : Finset I)
    (A : I → ProblemStatement.VelocityField) {w : ProblemStatement.SpaceTime}
    (hA : ∀ i ∈ s, DifferentiableAt ℝ (A i) w) :
    SpatialCurl.spatialCurl (fun z => ∑ i ∈ s, A i z) w =
      ∑ i ∈ s, SpatialCurl.spatialCurl (A i) w := by
  have hs : ∀ i ∈ s, DifferentiableAt ℝ (fun x : ProblemStatement.Space => A i (w.1, x)) w.2 := by
    intro i hi
    exact (hA i hi).comp w.2 ((differentiableAt_const w.1).prodMk differentiableAt_id)
  unfold SpatialCurl.spatialCurl SpatialCurl.curl
  rw [fderiv_fun_sum hs, map_sum]

theorem primary_cartesianCurl_sum (s : Finset (ActualPrimary.Label B N0 × Fin 2))
    {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal) :
    SpatialCurl.spatialCurl
      (fun z => ∑ l ∈ s, ActualPrimaryCoherence.cartesianPotential l.2 l.1 z) w =
      ∑ l ∈ s, ActualPrimaryCoherence.cartesianVelocity l.2 l.1 w := by
  apply spatialCurl_finset_sum
  intro l hl
  exact ((ActualPrimaryCoherence.cartesianPotential_smooth l.2 l.1).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)).differentiableAt (by simp)

/-- The constructed global potential is the literal finite primary sum on
every valid current-band chart. -/
theorem potential_eq_active (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    potential B N0 w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianPotential l.2 l.1 w := by
  ext i
  change PhysicalCopyBounds.vectorSum (potentialFamily B N0) innerRadius ActualPrimary.h
    ActualPrimary.slots.radius w i = _
  rw [vectorSum_apply, potential_sum_eq_active i n d w hw hx]
  change Complex.reCLM (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
    (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (primaryIndex l) w) =
    AxisymmetricFields.projection i (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion
        B N0 n,
      ActualPrimaryCoherence.cartesianPotential l.2 l.1 w)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact potential_periodized_eq (l.2, l.1) i w hw

/-- The same fixed finite family represents the potential on a full
spacetime neighborhood; hence its spatial curl may be taken termwise. -/
theorem potential_germ_eq_active (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    potential B N0 =ᶠ[𝓝 w] fun z =>
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianPotential l.2 l.1 z := by
  have hn := (graph_smooth_of_strip n d hx).continuousAt (strip.isOpen_domain.mem_nhds hx)
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw, hn] with z hzt hzx
  exact potential_eq_active n d z hzt hzx

theorem curl_eq_active (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    SpatialCurl.spatialCurl (potential B N0) w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianVelocity l.2 l.1 w := by
  rw [PhysicalCurlCovariance.spatialCurl_congr (potential_germ_eq_active n d hw hx)]
  exact primary_cartesianCurl_sum _ hw

theorem pressure_eq_active (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2) ∈ strip.domain) :
    pressure B N0 (z.1, CylindricalResidual.chart z.2) =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.physicalPressure l.2 l.1 z := by
  change Complex.reCLM ((pressureFamily B N0).sum innerRadius ActualPrimary.h
    ActualPrimary.slots.radius (z.1, CylindricalResidual.chart z.2)) = _
  rw [pressure_sum_eq_active n d (z.1, CylindricalResidual.chart z.2) ht hx, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact pressure_periodized_eq (l.2, l.1) z ht hr

/-- Exact normalized velocity of the initialized primary aggregate. The
right side is the curl of the actual Cartesian potential constructed above. -/
theorem velocity_chart (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2) ∈ strip.domain) (i : Fin 3) :
    (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
      (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).velocity n
        (PhysicalResidualTZ.swapCylinder
          ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
            (CommonWindow.index ActualPrimary.h n)).map z)) i) =
      ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h *
        CylindricalResidual.frame (-(z.2 1))
          (SpatialCurl.spatialCurl (potential B N0) (z.1, CylindricalResidual.chart z.2)) i := by
  rw [curl_eq_active n d (w := (z.1, CylindricalResidual.chart z.2)) ht hx]
  change _ = ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h *
    AxisymmetricFields.projection i
      (CylindricalResidual.frame (-(z.2 1))
        (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
          ActualPrimaryCoherence.cartesianVelocity l.2 l.1 (z.1, CylindricalResidual.chart z.2)))
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact ActualPrimaryCoherence.piece_cartesian_velocity ActualPrimary.standardRegion l.2 l.1 n ht
      hr i

theorem pressure_chart (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hx : PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2) ∈ strip.domain) :
    (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
      (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).pressure n
        (PhysicalResidualTZ.swapCylinder
          ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
            (CommonWindow.index ActualPrimary.h n)).map z))) =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h) *
        pressure B N0 (z.1, CylindricalResidual.chart z.2) := by
  rw [pressure_eq_active n d z ht hr hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact ActualPrimaryCoherence.piece_physical_pressure ActualPrimary.standardRegion l.2 l.1 n hr


end FiniteAggregation


section FullSlowDomain

theorem physicalX_eq_profileRadius_sq (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    physicalX w = (PrimaryTargetBounds.profileRadius ActualPrimary.h
      (BaseContextAssembly.slowCoordinates (PhysicalMeanJetBounds.graph ActualPrimary.h n d w))) ^
          2 / 2 := by
  let x := PhysicalMeanJetBounds.graph ActualPrimary.h n d w
  have hq : 0 < SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) x.2.1 := by
    change 0 < SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h)
      (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1
    rw [PhysicalMeanJetBounds.graph_q_eq ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half n d hw]
    exact div_pos (PhysicalWaveSum.physicalQ_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw) (ChartScales.Q_pos n)
  have hprofile : PrimaryTargetBounds.profileRadius ActualPrimary.h
      (BaseContextAssembly.slowCoordinates x) =
      x.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) x.2.1) := by
    rw [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq]
    rfl
  change physicalX w = (PrimaryTargetBounds.profileRadius ActualPrimary.h
    (BaseContextAssembly.slowCoordinates x)) ^ 2 / 2
  rw [hprofile]
  unfold physicalX
  rw [← physicalPosition_graph n d w, ← physicalScale_graph n d hw]
  change (Real.sqrt (ChartScales.Q n) * x.1) ^ 2 /
    (2 * (ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) x.2.1)) = _
  rw [mul_pow, Real.sq_sqrt (ChartScales.Q_pos n).le, div_pow, Real.sq_sqrt hq.le]
  field_simp [(ChartScales.Q_pos n).ne', hq.ne']

theorem graph_mem_strip_of_activeX (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier)
    (hX : physicalX w ∈ Ioo (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ ActualPrimaryBounds.strip.domain := by
  let x := PhysicalMeanJetBounds.graph ActualPrimary.h n d w
  let r := PrimaryTargetBounds.profileRadius ActualPrimary.h (BaseContextAssembly.slowCoordinates x)
  have hr : 0 ≤ r := by
    apply div_nonneg
    · change 0 ≤ (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).1
      rw [PhysicalMeanJetBounds.graph_radius]
      exact PolarCharts.radius_nonneg _
    · exact Real.sqrt_nonneg _
  have he : physicalX w = r ^ 2 / 2 := physicalX_eq_profileRadius_sq n d hw
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have ha2 : (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) ^ 2 =
      2 * NominalConeAssembly.activeLeft ActualPrimary.nominal := by
    rw [PrimaryTargetBounds.leftRadius, Real.sq_sqrt]
    exact mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal).le
  have hb2 : (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ^ 2 =
      2 * NominalConeAssembly.activeRight ActualPrimary.nominal := by
    rw [PrimaryTargetBounds.rightRadius, Real.sq_sqrt]
    exact mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos ActualPrimary.nominal).le
  have hlo : PrimaryTargetBounds.leftRadius ActualPrimary.nominal < r := by
    apply (sq_lt_sq₀ ha.le hr).mp
    rw [ha2]
    rw [he] at hX
    linarith [hX.1]
  have hhi : r < PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by
    apply (sq_lt_sq₀ hr hb.le).mp
    rw [hb2]
    rw [he] at hX
    linarith [hX.2]
  exact (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
      x).mpr
    ⟨hs, hlo, hhi⟩


variable {B N0 : ℕ}

theorem potential_periodized_activeX (i : Fin 3) (I : PhysicalWaveSum.WaveIndex 1)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hn : (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h
      ActualPrimary.slots.radius I w ≠ 0) :
    physicalX w ∈ Ioo (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
  obtain ⟨k, hk⟩ := periodized_nonzero_copy _ _ _ _ _ _ hn
  obtain ⟨l, _, _, _, hn⟩ := potential_amplitude_data i k I _
    (PhysicalWaveSum.globalWave_ne_zero_amp hk)
  exact cut_pair_physicalX l I.1 k w hw (Or.inl hn)

theorem pressure_periodized_activeX (I : PhysicalWaveSum.WaveIndex 1)
    (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hn : (pressureFamily B N0).periodized innerRadius ActualPrimary.h
      ActualPrimary.slots.radius I w ≠ 0) :
    physicalX w ∈ Ioo (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
  obtain ⟨k, hk⟩ := periodized_nonzero_copy _ _ _ _ _ _ hn
  obtain ⟨l, _, _, _, hn⟩ := pressure_amplitude_data k I _
    (PhysicalWaveSum.globalWave_ne_zero_amp hk)
  exact cut_pair_physicalX l I.1 k w hw (Or.inr hn)

theorem periodized_sum_eq_active_of_support (f : PhysicalCopyBounds.CopyFamily 1 Frequency)
    (hsource : ∀ I w, f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0 →
      ∃ l : ActualPrimary.Label B N0 × Fin 2, primaryIndex l = I)
    (hsupport : ∀ I w, w ∈ PhysicalWaveSum.preterminal →
      f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0 →
      PhysicalWaveSum.physicalParams ActualPrimary.h w ∈
        PhysicalWaveSum.labelRegion (CoordinateAlgebra.D ActualPrimary.h) I.1.val)
    (n d : ℕ) (w : ProblemStatement.SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hstrip : ∀ I, f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0 →
      PhysicalMeanJetBounds.graph ActualPrimary.h n d w ∈ strip.domain) :
    f.sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius (primaryIndex l) w := by
  classical
  by_cases h : ∃ I, f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w ≠ 0
  · obtain ⟨I, hI⟩ := h
    exact periodized_sum_eq_active f hsource hsupport n d w hw (hstrip I hI)
  · have hz : ∀ I, f.periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius I w = 0 := by
      simpa only [not_exists, not_not] using h
    simp only [PhysicalCopyBounds.CopyFamily.sum, hz, finsum_zero, Finset.sum_const_zero]

theorem potential_sum_eq_active_slow (i : Fin 3) (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier) :
    (potentialFamily B N0 i).sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
          (primaryIndex l) w := by
  apply periodized_sum_eq_active_of_support _ (potential_periodized_index i)
    (potential_support B N0 i).periodized_support n d w hw
  intro I hI
  exact graph_mem_strip_of_activeX n d hw hs (potential_periodized_activeX i I w hw hI)

theorem pressure_sum_eq_active_slow (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier) :
    (pressureFamily B N0).sum innerRadius ActualPrimary.h ActualPrimary.slots.radius w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        (pressureFamily B N0).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
          (primaryIndex l) w := by
  apply periodized_sum_eq_active_of_support _ pressure_periodized_index
    (pressure_support B N0).periodized_support n d w hw
  intro I hI
  exact graph_mem_strip_of_activeX n d hw hs (pressure_periodized_activeX I w hw hI)

/-- The finite primary identity holds throughout the slow chart, including
both radial edges and every positive exterior radius. -/
theorem potential_eq_active_slow (n d : ℕ) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier) :
    potential B N0 w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianPotential l.2 l.1 w := by
  ext i
  change PhysicalCopyBounds.vectorSum (potentialFamily B N0) innerRadius ActualPrimary.h
    ActualPrimary.slots.radius w i = _
  rw [vectorSum_apply, potential_sum_eq_active_slow i n d w hw hs]
  change Complex.reCLM (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
    (potentialFamily B N0 i).periodized innerRadius ActualPrimary.h ActualPrimary.slots.radius
      (primaryIndex l) w) =
    AxisymmetricFields.projection i (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion
        B N0 n,
      ActualPrimaryCoherence.cartesianPotential l.2 l.1 w)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact potential_periodized_eq (l.2, l.1) i w hw

theorem potential_germ_eq_active_slow (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier) :
    potential B N0 =ᶠ[𝓝 w] fun z =>
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianPotential l.2 l.1 z := by
  have hn : ∀ᶠ z in 𝓝 w,
      (PhysicalMeanJetBounds.graph ActualPrimary.h n d z).2.1 ∈
          ActualPrimary.standardRegion.carrier :=
    (PhysicalMeanJetBounds.graph_slow_continuous ActualPrimary.h n d).continuousAt
      (ActualPrimary.standardRegion.isOpen.mem_nhds hs)
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw, hn] with z hzt hzs
  exact potential_eq_active_slow n d z hzt hzs

theorem curl_eq_active_slow (n d : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d w).2.1 ∈
        ActualPrimary.standardRegion.carrier) :
    SpatialCurl.spatialCurl (potential B N0) w =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.cartesianVelocity l.2 l.1 w := by
  rw [PhysicalCurlCovariance.spatialCurl_congr (potential_germ_eq_active_slow n d hw hs)]
  exact primary_cartesianCurl_sum _ hw

theorem pressure_eq_active_slow (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ ActualPrimary.standardRegion.carrier) :
    pressure B N0 (z.1, CylindricalResidual.chart z.2) =
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        ActualPrimaryCoherence.physicalPressure l.2 l.1 z := by
  change Complex.reCLM ((pressureFamily B N0).sum innerRadius ActualPrimary.h
    ActualPrimary.slots.radius (z.1, CylindricalResidual.chart z.2)) = _
  rw [pressure_sum_eq_active_slow n d (z.1, CylindricalResidual.chart z.2) ht hs, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact pressure_periodized_eq (l.2, l.1) z ht hr

/-- Full positive-radius version of the initial velocity chart identity.
Only slow-chart membership is required; the radial edges are included. -/
theorem velocity_chart_slow (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ ActualPrimary.standardRegion.carrier) (i : Fin 3)
          :
    (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
      (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).velocity n
        (PhysicalResidualTZ.swapCylinder
          ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
            (CommonWindow.index ActualPrimary.h n)).map z)) i) =
      ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h *
        CylindricalResidual.frame (-(z.2 1))
          (SpatialCurl.spatialCurl (potential B N0) (z.1, CylindricalResidual.chart z.2)) i := by
  rw [curl_eq_active_slow n d (w := (z.1, CylindricalResidual.chart z.2)) ht hs]
  change _ = ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h *
    AxisymmetricFields.projection i
      (CylindricalResidual.frame (-(z.2 1))
        (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
          ActualPrimaryCoherence.cartesianVelocity l.2 l.1 (z.1, CylindricalResidual.chart z.2)))
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact ActualPrimaryCoherence.piece_cartesian_velocity ActualPrimary.standardRegion l.2 l.1 n ht
      hr i

theorem pressure_chart_slow (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hs : (PhysicalMeanJetBounds.graph ActualPrimary.h n d
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ ActualPrimary.standardRegion.carrier) :
    (∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
      (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).pressure n
        (PhysicalResidualTZ.swapCylinder
          ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
            (CommonWindow.index ActualPrimary.h n)).map z))) =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h) *
        pressure B N0 (z.1, CylindricalResidual.chart z.2) := by
  rw [pressure_eq_active_slow n d z ht hr hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact ActualPrimaryCoherence.piece_physical_pressure ActualPrimary.standardRegion l.2 l.1 n hr


end FullSlowDomain

end NavierStokes.InitialPhysicalData
