/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage

/-!
# Preservation of the actual closed carrier of a harmonic label

The support argument uses the whole native Volterra path.  A pointwise
zero of the source is not used as a zero of its particular solution.
The Gaussian clock cutoff supplies the temporal boundary of the carrier;
the source supplies its slow and transverse boundaries.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.LabelSupportPreservation

open Set Function Filter WeightedClasses
open HarmonicCalculus LinearWaveBounds PeriodizedWaveBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryPulseBounds
open scoped Topology ContDiff BigOperators ComplexConjugate

section CopyGerms

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A zero raw amplitude gives a zero corrected amplitude as a germ,
including every derivative in the literal curl correction. -/
theorem corrected_zero_of_raw (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) {n : ℕ} {i : I} {x : D}
    (ha : a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have hl : (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ha] with y hy
    change a.cutoff n i y • a.amplitude n i y = 0
    rw [hy, smul_zero]
  have h := ParticularWaveAssembly.realizedCoefficient_germ hl
    (a.background.frequency n) (a.background.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (a.background.phase n)
  simp only [realizedCoefficient_zero] at h
  exact h

omit [NormedSpace ℝ D] in
theorem localized_pressure_zero_of_raw (a : CopyData D I)
    {n : ℕ} {i : I} {x : D} (hp : a.pressure n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.localized i).pressure n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hp] with y hy
  change (a.cutoff n i y : ℂ) * a.pressure n i y = 0
  rw [hy, mul_zero]

/-- The uncovered source is retained.  Either a zero cutoff or two zero
raw fields in every covering copy suffices for the three assembled fields. -/
theorem common_zero_germs_of_native (a : CopyData D I) (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hf : a.source n =ᶠ[𝓝 x] fun _ => 0)
    (hnative : ∀ i, x ∈ K.carrier n i →
      (a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧
         (a.pressure n i =ᶠ[𝓝 x] fun _ => 0))) :
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGaussian d n =ᶠ[𝓝 x] fun _ => 0) := by
  classical
  by_cases hc : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hc
    have hu := a.commonCorrected_amplitude_germ K hs s d n hi
    have hp := a.common_pressure_germ K hs n hi
    have hG := a.globalGaussian_germ K hs d n hi
    rcases hnative i hi with hz | ⟨hz, hpz⟩
    · refine ⟨hu.trans (a.corrected_zero_germ s d hz),
        hp.trans (a.localized_zero_germs hz).2, hG.trans ?_⟩
      have ht := a.localTail_zero_germ d hz
      filter_upwards [ht, hf] with y hty hfy
      rw [a.localGaussian_eq, hty, hfy, smul_zero, add_zero]
    · exact ⟨hu.trans (corrected_zero_of_raw a s d hz),
        hp.trans (localized_pressure_zero_of_raw a hpz),
        hG.trans (a.localGaussian_zero_of_fields d hz hf)⟩
  · have hn : ∀ i, x ∉ K.carrier n i := fun i hi => hc ⟨i, hi⟩
    exact ⟨a.commonCorrected_zero_germ K hs s d hn,
      (a.common_zero_germs K hs hn).2,
      (a.globalGaussian_uncovered_germ K hs d hn).trans hf⟩

end CopyGerms

section NativeGeometry

/-- Outside the closed Gaussian source window, the actual cutoff is
identically zero on a neighborhood, even inside the padded clock cell. -/
theorem nativeCutoff_source_time_zero_germ {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) {z : Plane}
    (hz : z.2 ∉ Icc ((L / c) / 6) (5 * (L / c) / 6)) :
    ActualGaussianCoverage.nativeCutoff r L hr hL c =ᶠ[𝓝 z] fun _ => 0 := by
  have hlen : 0 < L / c := div_pos hL hc
  have hd : 1 / 3 < |z.2 / (L / c) - 1 / 2| := by
    by_contra! h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    have hlow : (1 / 6 : ℝ) ≤ z.2 / (L / c) := by linarith
    have hhigh : z.2 / (L / c) ≤ (5 / 6 : ℝ) := by linarith
    have hl := (le_div_iff₀ hlen).mp hlow
    have hh := (div_le_iff₀ hlen).mp hhigh
    exact hz ⟨by nlinarith, by nlinarith⟩
  have hd' : 1 / 3 < |c * z.2 / L - 1 / 2| := by
    simpa only [ActualGaussianCoverage.normalized_clock hL.ne' hc.ne'] using hd
  have ht : Continuous (fun y : Plane => c * y.2 / L) :=
    (continuous_const.mul continuous_snd).div_const L
  have hg := (GaussianTailFlat.profile_eventually_zero hd').comp_tendsto ht.continuousAt
  filter_upwards [hg] with y hy
  simp only [comp_def] at hy
  simp only [ActualGaussianCoverage.nativeCutoff, GaussianTailFlat.slotCutoff, hy, mul_zero]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The actual projected particular pressure also vanishes near a path
of zero source.  The time coordinate is in the open integration interval. -/
theorem complexCopyPressure_zero_germ (t : TangentData P ProblemStatement.Space)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency) (frequency : ℝ)
    {f : P × Plane → ComplexVector} {x : P × Plane}
    (heta : (g.coordinates k x.2).2 ∈ Ioo a b)
    (hf : ∀ v ∈ Icc a b, f =ᶠ[𝓝 (x.1, g.path k x.2 v)] fun _ => 0) :
    complexCopyPressure t f g hab k frequency =ᶠ[𝓝 x] fun _ => 0 := by
  have hall := ActualGaussianCoverage.whole_path_zero_germ g k hf
  have ht : Continuous (fun y : P × Plane => (g.coordinates k y.2).2) :=
    (g.coordinates_contDiff k).continuous.snd.comp continuous_snd
  have htime : ∀ᶠ y in 𝓝 x, (g.coordinates k y.2).2 ∈ Ioo a b :=
    ht.continuousAt (isOpen_Ioo.mem_nhds heta)
  filter_upwards [hall, htime] with y hy hty
  exact complexCopyPressure_zero_of_path t f g hab k frequency y.1 y.2 hy ⟨hty.1.le, hty.2.le⟩

end NativeGeometry

section Particular

open ActualGaussianCoverage

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)
  (base : Label → WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
  (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
    (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))

include hS hsupport

theorem data_pressure_zero_germ (l : Label) (n : ℕ) (k : Frequency)
    {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ s.domain)
    (htime : ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2).2
        ∈
      Ioo 0 (ScaledActualParticularControl.length F clock l n))
    (hpath : ∀ v ∈ Icc 0 (ScaledActualParticularControl.length F clock l n),
      (x.1.1, (ScaledActualParticularControl.geometry reference gap clock l n).path k x.2 v) ∉
        sourceRegions F clock reference gap r S l n) :
    (data F clock reference gap r hr base tangent ctx u b G A j l).pressure n k
      =ᶠ[𝓝 x] fun _ => 0 := by
  apply complexCopyPressure_zero_germ _ _ _ _ _ htime
  intro v hv
  exact data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j
    s S hS hsupport l n (x := (x.1, _)) hx (hpath v hv)

/-- The exact particular solve retains the smaller source cell, even
though its raw cutoff is supported on a larger padded cell. -/
theorem data_native_zero_alternative
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (l : Label) (n : ℕ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : x.1.1 ∈ s.domain)
    (hk : x ∈ nativeCell (ScaledActualParticularControl.geometry reference gap clock l n)
      (outerFamily F clock r l n) k)
    (hn : (x.1.1, x.2) ∉ sourceRegions F clock reference gap r S l n) :
    ((data F clock reference gap r hr base tangent ctx u b G A j l).cutoff n k
      =ᶠ[𝓝 x] fun _ => 0) ∨
    (((data F clock reference gap r hr base tangent ctx u b G A j l).amplitude n k
      =ᶠ[𝓝 x] fun _ => 0) ∧
     ((data F clock reference gap r hr base tangent ctx u b G A j l).pressure n k
      =ᶠ[𝓝 x] fun _ => 0)) := by
  let g := ScaledActualParticularControl.geometry reference gap clock l n
  have hi : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell (r l n) (F.L (l,n)) (clock.value l n)) :=
    transported_outer_injective (reference l n) (gap l n) (hr l n) (F.L_pos (l,n))
      (clock.value_pos l n) (hinj l n)
  have hk' : g.coordinates k x.2 ∈ outerCell (r l n) (F.L (l,n)) (clock.value l n) := hk
  by_cases ht : (g.coordinates k x.2).2 ∈ Ioo 0 (ScaledActualParticularControl.length F clock l n)
  · have hzero (hpath : ∀ v ∈ Icc 0 (ScaledActualParticularControl.length F clock l n),
        (x.1.1, g.path k x.2 v) ∉ sourceRegions F clock reference gap r S l n) :
        ((data F clock reference gap r hr base tangent ctx u b G A j l).amplitude n k
          =ᶠ[𝓝 x] fun _ => 0) ∧
        ((data F clock reference gap r hr base tangent ctx u b G A j l).pressure n k
          =ᶠ[𝓝 x] fun _ => 0) :=
      ⟨data_amplitude_zero_germ F clock reference gap r hr base tangent ctx u b G A j
          s S hS hsupport l n k hx hpath,
       data_pressure_zero_germ F clock reference gap r hr base tangent ctx u b G A j
          s S hS hsupport l n k hx ht hpath⟩
    by_cases hp : x.1.1 ∈ S l n
    · by_cases hxi : (g.coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n)
      · left
        have htime : (g.coordinates k x.2).2 ∉
            Icc ((F.L (l,n) / clock.value l n) / 6) (5 * (F.L (l,n) / clock.value l n) / 6) := by
          intro hv
          apply hn
          refine ⟨hp, mem_iUnion.mpr ⟨k, ?_⟩⟩
          exact ⟨hxi, hv⟩
        exact (nativeCutoff_source_time_zero_germ (hr l n) (F.L_pos (l,n))
          (clock.value_pos l n) htime).comp_tendsto
            ((g.coordinates_contDiff k).continuous.comp continuous_snd).continuousAt
      · right
        apply hzero
        intro v hv hh
        obtain ⟨i, hi'⟩ := mem_iUnion.mp hh.2
        exact path_sourceCell_excluded g (hr l n) (F.L_pos (l,n)) (clock.value_pos l n)
          hi hk' hxi v hv i hi'
    · right
      exact hzero (fun _ _ hh => hp hh.1)
  · left
    exact (nativeCutoff_time_zero_germ (hr l n) (F.L_pos (l,n)) (clock.value_pos l n)
        ht).comp_tendsto
      ((g.coordinates_contDiff k).continuous.comp continuous_snd).continuousAt

/-- All three literal particular output fields have zero germs off the
incoming label carrier. This is independent of every numerical jet bound. -/
theorem particular_zero_germs
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (outStrip : StripData ((P × ℝ) × Plane)) (d : GraphDirections ((P × ℝ) × Plane))
    (l : Label) (n : ℕ) {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ s.domain)
    (hn : (x.1.1, x.2) ∉ sourceRegions F clock reference gap r S l n) :
    (((data F clock reference gap r hr base tangent ctx u b G A j l).commonCorrected outStrip
        d).amplitude n
      =ᶠ[𝓝 x] fun _ => 0) ∧
    ((data F clock reference gap r hr base tangent ctx u b G A j l).common.pressure n
      =ᶠ[𝓝 x] fun _ => 0) ∧
    ((data F clock reference gap r hr base tangent ctx u b G A j l).globalGaussian d n
      =ᶠ[𝓝 x] fun _ => 0) := by
  apply common_zero_germs_of_native
    (data F clock reference gap r hr base tangent ctx u b G A j l)
    (cells F clock reference gap r hr hinj l)
    (data_cutoff_support F clock reference gap r hr base tangent ctx u b G A j l) outStrip d
    (data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j
      s S hS hsupport l n hx hn)
  intro k hk
  exact data_native_zero_alternative F clock reference gap r hr base tangent ctx u b G A j
    s S hS hsupport hinj l n k hx hk hn

end Particular

section Signed

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The same copy data as the signed update: the inverse-quotient
amplitude, its projected homogeneous pressure, and zero inhomogeneous source. -/
noncomputable def signedCopyData (base : WaveCoefficients D) (s : StripData D)
    (d : GraphDirections D) (matrix : I → ℕ → D → SignedWaveUpdate.Mat2)
    (target : I → ℕ → D → SignedWaveUpdate.Vec2)
    (request : ℕ → D → SignedWaveUpdate.Vec2) (mask : I → ℕ → D → ℝ)
    (fundamental normalMotion : I → ℕ → D → ProblemStatement.Space)
    (action : I → ℕ → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space)
    (cutoff : I → ℕ → D → ℝ) (column : Fin 2) : CopyData D I where
  background := base
  amplitude n i := (SignedWaveUpdate.coefficients base s d (matrix i) (target i) request
    (mask i) (fundamental i) (normalMotion i) (action i) column).amplitude n
  pressure n i := (SignedWaveUpdate.coefficients base s d (matrix i) (target i) request
    (mask i) (fundamental i) (normalMotion i) (action i) column).pressure n
  cutoff n i := cutoff i n
  source := fun _ _ => 0

variable (base : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
  (matrix : I → ℕ → D → SignedWaveUpdate.Mat2)
  (target : I → ℕ → D → SignedWaveUpdate.Vec2)
  (request : ℕ → D → SignedWaveUpdate.Vec2) (mask : I → ℕ → D → ℝ)
  (fundamental normalMotion : I → ℕ → D → ProblemStatement.Space)
  (action : I → ℕ → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space)
  (cutoff : I → ℕ → D → ℝ) (column : Fin 2)

theorem signed_raw_zero_of_mask (n : ℕ) (i : I) (x : D) (hm : mask i n x = 0) :
    (signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
        column).amplitude n i x = 0 ∧
    (signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
        column).pressure n i x = 0 := by
  simp [signedCopyData, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, SignedWaveUpdate.signedVector,
        SignedWaveUpdate.signedScalar,
    hm, ParticularWaveBounds.projectedPressure, TangentProjection.pressureCoefficient]

theorem signed_zero_germs_of_mask_germs (K : Cells D I)
    (hcutoff : ∀ n i, support (cutoff i n) ⊆ K.carrier n i)
    {n : ℕ} {x : D} (hm : ∀ i, mask i n =ᶠ[𝓝 x] fun _ => 0) :
    (((signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
        column).commonCorrected s d).amplitude n
      =ᶠ[𝓝 x] fun _ => 0) ∧
    ((signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
        column).common.pressure n
      =ᶠ[𝓝 x] fun _ => 0) ∧
    ((signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
        column).globalGaussian d n
      =ᶠ[𝓝 x] fun _ => 0) := by
  apply common_zero_germs_of_native _ K hcutoff s d (Filter.EventuallyEq.refl _ _)
  intro i _
  right
  constructor
  · filter_upwards [hm i] with y hy
    exact (signed_raw_zero_of_mask base s d matrix target request mask fundamental normalMotion
        action cutoff column n i y hy).1
  · filter_upwards [hm i] with y hy
    exact (signed_raw_zero_of_mask base s d matrix target request mask fundamental normalMotion
        action cutoff column n i y hy).2

end Signed

section ClosedSupport

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [Zero E]

omit [NormedSpace ℝ D] in
/-- Relative support on an open physical domain gives ambient zero germs
outside a closed carrier. No off-domain totalization is constrained. -/
theorem zero_germ_of_local_support {U K : Set D} (hU : IsOpen U) (hK : IsClosed K)
    {f : D → E} (hs : U ∩ support f ⊆ K) {x : D} (hx : x ∈ U) (hn : x ∉ K) :
    f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hU.mem_nhds hx, hK.isOpen_compl.mem_nhds hn] with y hy hny
  by_contra hz
  exact hny (hs ⟨hy, hz⟩)

end ClosedSupport

section CoefficientSupport

open HarmonicSourceSupport HarmonicResidual HarmonicMeanInteraction
open HarmonicFields ErrorHarmonics

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pair_input_support {U K : Set D} (j : ℤ) {f : D → ℂ}
    (hf : ∀ x, x ∈ U → x ∉ K → f x = 0) :
    NonzeroSupportedOn U K (realCoefficients (conjugatePair j f)) := by
  apply NonzeroSupportedOn.realProjection
  intro m hm x hx hn
  simp [ParticularWaveAssembly.pair_apply, hf x hx hn]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- A coefficient assembly needs only the literal amplitude values at
the zero-angle section. It needs no global angular independence premise. -/
theorem modeBlock_inputSupport {U : Set D} {K : ℕ → Set D}
    (j : ℤ) (frequency : ℕ → ℝ) (phase : ℕ → D → ℝ) (angularFrequency : ℕ → ℤ)
    {v g : ℕ → D → ComplexVector} {p : ℕ → D → ℂ}
    (hv : ∀ n x, x ∈ U → x ∉ K n → v n x = 0)
    (hp : ∀ n x, x ∈ U → x ∉ K n → p n x = 0)
    (hg : ∀ n x, x ∈ U → x ∉ K n → g n x = 0) :
    InputSupportOn U K (ParticularWaveAssembly.modeBlock j frequency phase angularFrequency v p)
      (ParticularWaveAssembly.modeBlock j frequency phase angularFrequency g (fun _ _ =>
          0)).velocity
      0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    apply pair_input_support
    intro x hx hn
    simp only [hv n x hx hn, Pi.zero_apply]
  · intro n
    exact pair_input_support j (hp n)
  · intro n i
    apply pair_input_support
    intro x hx hn
    simp only [hg n x hx hn, Pi.zero_apply]
  · intro n i m hm x hx hn
    simp [realCoefficients_apply]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The actual carrier-retaining update preserves the very same support
set; in particular, axisymmetric aliases are not added to a label. -/
theorem inputSupport_addBlock {U : Set D} {K : ℕ → Set D}
    {a b : CorrectionState.HarmonicBlock D} {G H A : BlockCoefficients D}
    (ha : InputSupportOn U K a G A) (hb : InputSupportOn U K b H 0) :
    InputSupportOn U K (HarmonicWaveInteraction.addBlock a b) (G + H) A := by
  refine ⟨?_, ?_, ?_, ha.aliasError⟩
  · intro n i
    change NonzeroSupportedOn U (K n) (realCoefficients (a.velocity n i + b.velocity n i))
    rw [realCoefficients_add]
    exact (ha.velocity n i).add (hb.velocity n i)
  · intro n
    change NonzeroSupportedOn U (K n) (realCoefficients (a.pressure n + b.pressure n))
    rw [realCoefficients_add]
    exact (ha.pressure n).add (hb.pressure n)
  · intro n i
    change NonzeroSupportedOn U (K n) (realCoefficients (G n i + H n i))
    rw [realCoefficients_add]
    exact (ha.gaussian n i).add (hb.gaussian n i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem inputSupport_two_updates {U : Set D} {K : ℕ → Set D}
    {a b c : CorrectionState.HarmonicBlock D} {G H J A : BlockCoefficients D}
    (ha : InputSupportOn U K a G A) (hb : InputSupportOn U K b H 0)
    (hc : InputSupportOn U K c J 0) :
    InputSupportOn U K (HarmonicWaveInteraction.addBlock (HarmonicWaveInteraction.addBlock a b) c)
      (G + H + J) A :=
  inputSupport_addBlock (inputSupport_addBlock ha hb) hc

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem real_supported_sum {ι : Type} {U K : Set D} (L : Finset ι)
    (f : ι → HarmonicFields.Coefficients D)
    (hf : ∀ l ∈ L, NonzeroSupportedOn U K (realCoefficients (f l))) :
    NonzeroSupportedOn U K (realCoefficients (∑ l ∈ L, f l)) := by
  classical
  induction L using Finset.induction_on with
  | empty =>
      intro j hj x hx hn
      simp [realCoefficients_apply]
  | @insert l L hl ih =>
      rw [Finset.sum_insert hl, realCoefficients_add]
      exact (hf l (Finset.mem_insert_self _ _)).add
        (ih (fun m hm => hf m (Finset.mem_insert_of_mem hm)))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem inputSupport_sumBlock {ι : Type} {U : Set D} {K : ℕ → Set D}
    (L : Finset ι) (frequency : ℕ → ℝ) (phase : ℕ → D → ℝ) (angularFrequency : ℕ → ℤ)
    (blocks : ι → CorrectionState.HarmonicBlock D) (gaussians : ι → BlockCoefficients D)
    (hs : ∀ l ∈ L, InputSupportOn U K (blocks l) (gaussians l) 0) :
    InputSupportOn U K (sumBlock L frequency phase angularFrequency blocks)
      (fun n i => ∑ l ∈ L, gaussians l n i) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    exact real_supported_sum L (fun l => (blocks l).velocity n i) (fun l hl => (hs l hl).velocity n
        i)
  · intro n
    exact real_supported_sum L (fun l => (blocks l).pressure n) (fun l hl => (hs l hl).pressure n)
  · intro n i
    exact real_supported_sum L (fun l => gaussians l n i) (fun l hl => (hs l hl).gaussian n i)
  · intro n i m hm x hx hn
    simp [realCoefficients_apply]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem assembledBlock_inputSupport {U : Set D} {K : ℕ → Set D}
    (N : ℕ) (frequency : ℕ → ℝ) (phase : ℕ → D → ℝ) (angularFrequency : ℕ → ℤ)
    {v g : ℤ → ℕ → D → ComplexVector} {p : ℤ → ℕ → D → ℂ}
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n x, x ∈ U → x ∉ K n → v j n x = 0)
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n x, x ∈ U → x ∉ K n → p j n x = 0)
    (hg : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n x, x ∈ U → x ∉ K n → g j n x = 0) :
    InputSupportOn U K (ParticularWaveAssembly.assembledBlock N frequency phase angularFrequency v
        p)
      (ParticularWaveAssembly.assembledBlock N frequency phase angularFrequency g (fun _ _ _ =>
          0)).velocity
      0 :=
  inputSupport_sumBlock _ _ _ _ _ _ (fun j hj =>
    modeBlock_inputSupport j frequency phase angularFrequency (hv j hj) (hp j hj) (hg j hj))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem blockOfCoefficients_inputSupport {U : Set D} {K : ℕ → Set D}
    (a : WaveCoefficients (D × ℝ)) (angularFrequency : ℕ → ℤ)
    {g : ℕ → D × ℝ → ComplexVector}
    (hv : ∀ n x, x ∈ U → x ∉ K n → a.amplitude n (x, 0) = 0)
    (hp : ∀ n x, x ∈ U → x ∉ K n → a.pressure n (x, 0) = 0)
    (hg : ∀ n x, x ∈ U → x ∉ K n → g n (x, 0) = 0) :
    InputSupportOn U K (SignedWaveUpdate.blockOfCoefficients a angularFrequency)
      (SignedWaveUpdate.coefficientBlock a.frequency (fun n x => a.phase n (x, 0)) angularFrequency
        (fun n x => g n (x, 0)) (fun _ _ => 0)).velocity 0 :=
  modeBlock_inputSupport 1 a.frequency (fun n x => a.phase n (x, 0)) angularFrequency hv hp hg

end CoefficientSupport

section ParticularAssembly

open ActualGaussianCoverage

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)
  (base : Label → WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane))
  (s : StripData P) (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
  (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
    (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))
  (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
    ((fun z => (reference l n).center + (reference l n).basis z) ''
      (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
  (outStrip : StripData ((P × ℝ) × Plane)) (d : GraphDirections ((P × ℝ) × Plane))

include hS hsupport hinj

/-- A single actual particular mode, with its actual Gaussian error,
has the same carrier as its incoming label. -/
theorem particular_mode_inputSupport (j : ℤ) (l : Label) :
    HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ) (sourceRegions F clock reference gap r
        S l)
      (ParticularWaveAssembly.nativeModeBlock j (b l)
        ((data F clock reference gap r hr base tangent ctx u b G A j l).commonCorrected outStrip d))
      (ParticularWaveAssembly.nativeModeBlock j (b l)
        { base l with
          amplitude := (data F clock reference gap r hr base tangent ctx u b G A j
              l).globalGaussian d
          pressure := fun _ _ => 0 }).velocity 0 := by
  apply modeBlock_inputSupport
  · intro n x hx hn
    exact (particular_zero_germs F clock reference gap r hr base tangent ctx u b G A j
      s S hS hsupport hinj outStrip d l n (x := ((x.1, 0), x.2)) hx.1 hn).1.self_of_nhds
  · intro n x hx hn
    exact (particular_zero_germs F clock reference gap r hr base tangent ctx u b G A j
      s S hS hsupport hinj outStrip d l n (x := ((x.1, 0), x.2)) hx.1 hn).2.1.self_of_nhds
  · intro n x hx hn
    exact (particular_zero_germs F clock reference gap r hr base tangent ctx u b G A j
      s S hS hsupport hinj outStrip d l n (x := ((x.1, 0), x.2)) hx.1 hn).2.2.self_of_nhds

/-- Finite reassembly of all signed particular modes retains the fixed
label carrier, with no growth or derivative estimate as an input. -/
theorem particular_assembled_inputSupport (N : ℕ) (l : Label) :
    HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ) (sourceRegions F clock reference gap r
        S l)
      (ErrorHarmonics.sumBlock (ParticularWaveAssembly.modes N)
        (b l).frequency (b l).phase (b l).angularFrequency (fun j =>
          ParticularWaveAssembly.nativeModeBlock j (b l)
            ((data F clock reference gap r hr base tangent ctx u b G A j l).commonCorrected
                outStrip d)))
      (fun n i => ∑ j ∈ ParticularWaveAssembly.modes N,
        (ParticularWaveAssembly.nativeModeBlock j (b l)
          { base l with
            amplitude := (data F clock reference gap r hr base tangent ctx u b G A j
                l).globalGaussian d
            pressure := fun _ _ => 0 }).velocity n i) 0 := by
  apply inputSupport_sumBlock
  intro j _
  exact particular_mode_inputSupport F clock reference gap r hr base tangent ctx u b G A
    s S hS hsupport hinj outStrip d j l

end ParticularAssembly

section SignedAssembly

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  (base : WaveCoefficients (D × ℝ)) (s : StripData (D × ℝ)) (d : GraphDirections (D × ℝ))
  (matrix : I → ℕ → D × ℝ → SignedWaveUpdate.Mat2)
  (target : I → ℕ → D × ℝ → SignedWaveUpdate.Vec2)
  (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) (mask : I → ℕ → D × ℝ → ℝ)
  (fundamental normalMotion : I → ℕ → D × ℝ → ProblemStatement.Space)
  (action : I → ℕ → D × ℝ → ProblemStatement.Space →L[ℝ] ProblemStatement.Space)
  (cutoff : I → ℕ → D × ℝ → ℝ) (column : Fin 2)

/-- Local support of the actual signed masks supplies the new block's
support. Mask support is the only hypothesis on the inverse quotient,
fundamental, and projected pressure; their numerical size is immaterial. -/
theorem signed_inputSupport (outer : Cells (D × ℝ) I)
    (hcutoff : ∀ n i, support (cutoff i n) ⊆ outer.carrier n i)
    {U : Set D} {K : ℕ → Set D} (hU : IsOpen U) (hK : ∀ n, IsClosed (K n))
    (hmask : ∀ n i, (U ×ˢ (univ : Set ℝ)) ∩ support (mask i n) ⊆ Prod.fst ⁻¹' K n)
    (angularFrequency : ℕ → ℤ) :
    HarmonicSourceSupport.InputSupportOn U K
      (SignedWaveUpdate.blockOfCoefficients
        ((signedCopyData base s d matrix target request mask fundamental normalMotion action cutoff
            column).commonCorrected s d)
        angularFrequency)
      (SignedWaveUpdate.coefficientBlock base.frequency (fun n x => base.phase n (x, 0))
          angularFrequency
        (fun n x => (signedCopyData base s d matrix target request mask fundamental normalMotion
            action cutoff column).globalGaussian d n (x, 0))
        (fun _ _ => 0)).velocity 0 := by
  have hzero (n : ℕ) (x : D) (hx : x ∈ U) (hn : x ∉ K n) :=
    signed_zero_germs_of_mask_germs base s d matrix target request mask fundamental normalMotion
        action cutoff column
      outer hcutoff (n := n) (x := (x, 0)) (fun i =>
        zero_germ_of_local_support (hU.prod isOpen_univ) ((hK n).preimage continuous_fst)
          (hmask n i) ⟨hx, mem_univ _⟩ hn)
  apply blockOfCoefficients_inputSupport
  · intro n x hx hn
    exact (hzero n x hx hn).1.self_of_nhds
  · intro n x hx hn
    exact (hzero n x hx hn).2.1.self_of_nhds
  · intro n x hx hn
    exact (hzero n x hx hn).2.2.self_of_nhds

end SignedAssembly

section TransportedMask

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Clock transport of a native mask keeps the actual source window.
The primitive mask may contain all radial and dyadic slow cutoffs. -/
theorem transported_mask_support (χ : P →L[ℝ] Q) (g : Geometry) (k : Frequency)
    {S : Set Q} {r L c : ℝ} (hc : 0 < c) {mask : Q × Plane → ℝ}
    (hm : support mask ⊆ S ×ˢ ActualGaussianCoverage.sourceCell r L 1) :
    support (fun x : P × Plane => mask
      (χ x.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k x.2))) ⊆
      ActualGaussianCoverage.sourceRegion (χ ⁻¹' S) g r L c := by
  intro x hx
  have hs := hm hx
  exact ⟨hs.1, mem_iUnion.mpr ⟨k, (ActualGaussianCoverage.mem_sourceCell_clock hc _).mpr hs.2⟩⟩

/-- The slow pullback and the locally finite native union form one closed
carrier. This is the closure used by the next residual-source calculation. -/
theorem transported_carrier_closed (χ : P →L[ℝ] Q) (g : Geometry)
    {S : Set Q} (hS : IsClosed S) (r L c : ℝ) :
    IsClosed (ActualGaussianCoverage.sourceRegion (χ ⁻¹' S) g r L c) :=
  ActualGaussianCoverage.sourceRegion_closed (hS.preimage χ.continuous) g r L c

theorem transported_mask_tsupport (χ : P →L[ℝ] Q) (g : Geometry) (k : Frequency)
    {S : Set Q} (hS : IsClosed S) {r L c : ℝ} (hc : 0 < c) {mask : Q × Plane → ℝ}
    (hm : support mask ⊆ S ×ˢ ActualGaussianCoverage.sourceCell r L 1) :
    tsupport (fun x : P × Plane => mask
      (χ x.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k x.2))) ⊆
      ActualGaussianCoverage.sourceRegion (χ ⁻¹' S) g r L c :=
  closure_minimal (transported_mask_support χ g k hc hm) (transported_carrier_closed χ g hS r L c)

theorem transported_mask_zero_germ (χ : P →L[ℝ] Q) (g : Geometry) (k : Frequency)
    {S : Set Q} (hS : IsClosed S) {r L c : ℝ} (hc : 0 < c) {mask : Q × Plane → ℝ}
    (hm : support mask ⊆ S ×ˢ ActualGaussianCoverage.sourceCell r L 1)
    {x : P × Plane} (hx : x ∉ ActualGaussianCoverage.sourceRegion (χ ⁻¹' S) g r L c) :
    (fun y : P × Plane => mask
      (χ y.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k y.2))) =ᶠ[𝓝 x] fun _ => 0 :=
  zero_germ_of_support (transported_carrier_closed χ g hS r L c)
    (transported_mask_support χ g k hc hm) hx

end TransportedMask

end NavierStokes.LabelSupportPreservation
