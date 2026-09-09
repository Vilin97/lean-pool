/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization

@[expose] public section

/-!
# A common shrinking support for actual physical increments

Native outer radii, bounded by one fixed patch radius, give one physical
outer-support constant for every stage. Coherent means are represented in
a comparable native band; no physical support property is an input.
The zeroth support assertion concerns the finite initialization increment.
-/

noncomputable section

universe u

namespace NavierStokes.PhysicalStageSupport

open Set Function Filter ProblemStatement PhysicalStageBounds
open MixedDiagonalExtensions
open scoped Topology ContDiff BigOperators

section SupportAlgebra

variable {V : Type*} [NormedAddCommGroup V]

theorem support_mono {h C D qbig : ℝ} {f : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f) (hCD : C ≤ D) :
    SublevelShrinkingSupport h D qbig f := by
  intro w ht hq hn
  exact (hf w ht hq hn).trans (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _))

theorem support_congr {h C qbig : ℝ} {f g : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f)
    (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig)) :
    SublevelShrinkingSupport h C qbig g := by
  intro w ht hq hn
  apply hf w ht hq
  rwa [he ⟨ht, hq⟩]

theorem support_map_zero {E : Type*} [NormedAddCommGroup E]
    {h C qbig : ℝ} {f : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f)
    (T : SpaceTime → V → E) (hT : ∀ w, T w 0 = 0) :
    SublevelShrinkingSupport h C qbig (fun w => T w (f w)) := by
  intro w ht hq hn
  apply hf w ht hq
  intro hz
  exact hn (by simpa only [hz] using hT w)

theorem support_add {h C qbig : ℝ} {f g : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f)
    (hg : SublevelShrinkingSupport h C qbig g) :
    SublevelShrinkingSupport h C qbig (fun w => f w + g w) := by
  intro w ht hq hn
  by_cases hz : f w = 0
  · apply hg w ht hq
    intro hgz
    exact hn (by simp only [hz, hgz, add_zero])
  · exact hf w ht hq hz

theorem support_finset_sum {ι : Type*} {h C qbig : ℝ} {f : ι → SpaceTime → V}
    (s : Finset ι) (hf : ∀ i ∈ s, SublevelShrinkingSupport h C qbig (f i)) :
    SublevelShrinkingSupport h C qbig (fun w => ∑ i ∈ s, f i w) := by
  intro w ht hq hn
  by_contra hs
  apply hn
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  exact hs (hf i hi w ht hq hne)

end SupportAlgebra

/-- This constant is shared by the entire stage sequence. -/
noncomputable def outerConstant (R : ℝ) : ℝ := 4 * R * Real.sqrt 2

theorem outerConstant_pos {R : ℝ} (hR : 0 < R) : 0 < outerConstant R := by
  unfold outerConstant
  positivity

section Waves

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K J : Type*}

theorem wave_scalar_support (W : WaveData h D I K J) (i : J) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig (W.scalar i) := by
  apply support_mono
    (SublevelShrinkingSupport.of_global (localCopy_sum_support (W.support i)))
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem wave_vector_support (W : WaveData h D I K (Fin 3)) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig W.vector := by
  apply support_mono
    (SublevelShrinkingSupport.of_global (localCopy_vector_support W.support))
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem wave_pressure_support (W : WaveData h D I K Unit) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig W.pressure :=
  support_map_zero (wave_scalar_support W () hR) (fun _ z => z.re) (fun _ => rfl)

end Waves

section Means

variable {h degree : ℝ}

/-- Exact coherence and the native moving annulus supply the physical
support for the same scalar field on the common valid sublevel. -/
theorem mean_field_support (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q M.firstBand) (hR : M.upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig M.family.field := by
  intro w ht hqw hn
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  obtain ⟨n, hnN, hqn, hnq⟩ := PhysicalMeanJetBounds.exists_comparable_band
    M.firstBand hqpos (hqw.le.trans hq)
  have hlo : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
  have hu := M.region_covers (PhysicalMeanJetBounds.graph_slow_normalized
    hh hh1 n (M.family.gap n) ht hlo hnq.le)
  have hann := M.family.annulus_on_tsupport hh hh1 M.lower_pos M.radii_lt M.region_open
    M.support n hnN ht hu hlo hnq.le (subset_tsupport _ hn)
  have hb := AnnularEndpoint.radius_le_of_scaled_annulus hann hnq.le
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The Cartesian angular reconstruction is pointwise zero-preserving. -/
theorem mean_angular_support (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q M.firstBand) (hR : M.upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig M.family.angularField := by
  exact support_map_zero (mean_field_support M hh hh1 hq hR)
    (fun w c => c • PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w))
    (fun _ => zero_smul _ _)

end Means

section CoherentMeans

variable {h degree : ℝ} {N gap : ℕ} {U : Set PhysicalGraphBounds.Plane}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected comparable band lies in the actual open normalized
window `(1/2,2)`. No enlargement of the native mean domain is required. -/
theorem comparable_graph_mem (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (ht : w.1 < 1)
    (hlo : PhysicalWaveSum.physicalQ h w ≤ ChartScales.Q n)
    (hhi : ChartScales.Q n < 2 * PhysicalWaveSum.physicalQ h w) :
    (PhysicalMeanJetBounds.graph h n d w).2.1 ∈
      PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 := by
  refine ⟨PhysicalMeanJetBounds.graph_time_pos h n d ht, ?_⟩
  rw [PhysicalMeanJetBounds.graph_q_eq hh hh1 n d ht]
  have hQ := ChartScales.Q_pos n
  constructor
  · apply (lt_div_iff₀ hQ).mpr
    linarith
  · apply (div_lt_iff₀ hQ).mpr
    linarith

theorem coherent_field_support (D : PhysicalMeanJetBounds.CoherentFamily h degree N gap U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b qbig R : ℝ}
    (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (hq : qbig ≤ ChartScales.Q N) (hR : b ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig D.field := by
  intro w ht hqw hn
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  obtain ⟨n, hnN, hqn, hnq⟩ := PhysicalMeanJetBounds.exists_comparable_band
    N hqpos (hqw.le.trans hq)
  have hlo : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
  have hu := hcover (comparable_graph_mem hh hh1 n (D.gap n) ht hqn hnq)
  have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hnN ht hu hlo hnq.le
    (subset_tsupport _ hn)
  have hb := AnnularEndpoint.radius_le_of_scaled_annulus hann hnq.le
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem coherent_angular_support (D : PhysicalMeanJetBounds.CoherentFamily h degree N gap U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b qbig R : ℝ}
    (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (hq : qbig ≤ ChartScales.Q N) (hR : b ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig D.angularField :=
  support_map_zero (coherent_field_support D hh hh1 ha hab hU hcover hs hq hR)
    (fun w c => c • PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w))
    (fun _ => zero_smul _ _)

end CoherentMeans

section Increments

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

theorem potentialIncrement_support (W : WaveData h D I K (Fin 3))
    (M : MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hW : W.upperRadius ≤ 2 * R) (hM : M.upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig (potentialIncrement W M) :=
  support_add (wave_vector_support W hW) (mean_angular_support M hh hh1 hq hM)

theorem pressureIncrement_support (W : WaveData h D I K Unit)
    (M : MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hW : W.upperRadius ≤ 2 * R) (hM : M.upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig (pressureIncrement W M) :=
  support_add (wave_pressure_support W hW) (mean_field_support M hh hh1 hq hM)

end Increments

section Families

variable {h : ℝ}
  {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- Numeric bounds on the native radial endpoints. The same `R` occurs
at every stage, including stage zero. -/
structure NativeOuterBounds (R : ℝ)
    (WA : ℕ → WaveData h DA IA KA (Fin 3))
    (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
    (WP : ℕ → WaveData h DP IP KP Unit)
    (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h)) : Prop where
  potentialWave : ∀ j, (WA j).upperRadius ≤ 2 * R
  potentialMean : ∀ j, (MA j).upperRadius ≤ R
  directMean : ∀ j, (MB j).upperRadius ≤ R
  pressureWave : ∀ j, (WP j).upperRadius ≤ 2 * R
  pressureMean : ∀ j, (MP j).upperRadius ≤ R

variable
  (WA : ℕ → WaveData h DA IA KA (Fin 3))
  (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
  (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
  (WP : ℕ → WaveData h DP IP KP Unit)
  (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h))

theorem NativeOuterBounds.radius_pos {R : ℝ}
    (H : NativeOuterBounds R WA MA MB WP MP) : 0 < R :=
  ((MA 0).lower_pos.trans (MA 0).radii_lt).trans_le (H.potentialMean 0)

/-- All three increment families share this explicit constant, independently
of stage-dependent harmonics, native bands, cover gaps, and jet constants. -/
theorem all_increment_support (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (hqP : ∀ j, qbig ≤ ChartScales.Q (MP j).firstBand)
    (H : NativeOuterBounds R WA MA MB WP MP) :
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (potentialIncrement (WA j) (MA j))) ∧
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (directStages MB j)) ∧
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (pressureIncrement (WP j) (MP j))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact potentialIncrement_support (WA j) (MA j) hh hh1 (hqA j)
      (H.potentialWave j) (H.potentialMean j)
  · intro j
    exact mean_angular_support (MB j) hh hh1 (hqB j) (H.directMean j)
  · intro j
    exact pressureIncrement_support (WP j) (MP j) hh hh1 (hqP j)
      (H.pressureWave j) (H.pressureMean j)

theorem exists_common_support (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (hqP : ∀ j, qbig ≤ ChartScales.Q (MP j).firstBand)
    (H : NativeOuterBounds R WA MA MB WP MP) :
    ∃ C : ℝ, 0 < C ∧
      (∀ j, SublevelShrinkingSupport h C qbig (potentialIncrement (WA j) (MA j))) ∧
      (∀ j, SublevelShrinkingSupport h C qbig (directStages MB j)) ∧
      (∀ j, SublevelShrinkingSupport h C qbig (pressureIncrement (WP j) (MP j))) :=
  ⟨outerConstant R, outerConstant_pos (H.radius_pos WA MA MB WP MP),
    all_increment_support WA MA MB WP MP hh hh1 hqA hqB hqP H⟩

/-- The common-radius conclusion is preserved by literal representations
of the five families supplied to `MixedCandidateAssembly`.
The initial field is the finite change, without the base potential. -/
theorem candidate_support_inputs (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (hqP : ∀ j, qbig ≤ ChartScales.Q (MP j).firstBand)
    (H : NativeOuterBounds R WA MA MB WP MP)
    (initial : MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h
      qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h
      qbig))
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hInitial : EqOn initial.field (potentialIncrement (WA 0) (MA 0))
      (CutStageEstimates.physicalSublevel h qbig))
    (hStages : ∀ j, EqOn (stages j).field (potentialIncrement (WA (j + 1)) (MA (j + 1)))
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : ∀ j, EqOn (LocalAngularDiagonal.rawSeries D j) (directStages MB j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hpInitial : EqOn pInitial (pressureIncrement (WP 0) (MP 0))
      (CutStageEstimates.physicalSublevel h qbig))
    (hpStages : ∀ j, EqOn (pStages j) (pressureIncrement (WP (j + 1)) (MP (j + 1)))
      (CutStageEstimates.physicalSublevel h qbig)) :
    SublevelShrinkingSupport h (outerConstant R) qbig initial.field ∧
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (stages j).field) ∧
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (LocalAngularDiagonal.rawSeries D j)) ∧
    SublevelShrinkingSupport h (outerConstant R) qbig pInitial ∧
    (∀ j, SublevelShrinkingSupport h (outerConstant R) qbig (pStages j)) := by
  obtain ⟨hA, hB, hP⟩ := all_increment_support WA MA MB WP MP hh hh1 hqA hqB hqP H
  exact ⟨support_congr (hA 0) hInitial.symm,
    fun j => support_congr (hA (j + 1)) (hStages j).symm,
    fun j => support_congr (hB j) (hDirect j).symm,
    support_congr (hP 0) hpInitial.symm,
    fun j => support_congr (hP (j + 1)) (hpStages j).symm⟩

end Families

section InitializedSequences

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

theorem potentialStages_positive_support (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3)) (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand)
    (hW : ∀ j, (W j).upperRadius ≤ 2 * R) (hM : ∀ j, (M j).upperRadius ≤ R)
    (j : ℕ) (hj : j ≠ 0) :
    SublevelShrinkingSupport h (outerConstant R) qbig (potentialStages base W M j) := by
  rw [potentialStages, addBaseAtZero_pos _ _ (by omega : 1 ≤ j)]
  exact potentialIncrement_support (W j) (M j) hh hh1 (hq j) (hW j) (hM j)

theorem pressureStages_positive_support (base : PressureField)
    (W : ℕ → WaveData h D I K Unit) (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand)
    (hW : ∀ j, (W j).upperRadius ≤ 2 * R) (hM : ∀ j, (M j).upperRadius ≤ R)
    (j : ℕ) (hj : j ≠ 0) :
    SublevelShrinkingSupport h (outerConstant R) qbig (pressureStages base W M j) := by
  rw [pressureStages, addBaseAtZero_pos _ _ (by omega : 1 ≤ j)]
  exact pressureIncrement_support (W j) (M j) hh hh1 (hq j) (hW j) (hM j)

/-- Subtracting the base from initialized stage zero leaves exactly its
finite supported potential increment. -/
theorem potentialStages_initial_support (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3)) (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q (M 0).firstBand)
    (hW : (W 0).upperRadius ≤ 2 * R) (hM : (M 0).upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig
      (fun w => potentialStages base W M 0 w - base w) := by
  convert! potentialIncrement_support (W 0) (M 0) hh hh1 hq hW hM using 1
  funext w
  simp only [potentialStages_zero, potentialIncrement, add_sub_cancel_left]

theorem pressureStages_initial_support (base : PressureField)
    (W : ℕ → WaveData h D I K Unit) (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q (M 0).firstBand)
    (hW : (W 0).upperRadius ≤ 2 * R) (hM : (M 0).upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig
      (fun w => pressureStages base W M 0 w - base w) := by
  convert! pressureIncrement_support (W 0) (M 0) hh hh1 hq hW hM using 1
  funext w
  simp only [pressureStages_zero, pressureIncrement, add_sub_cancel_left]

end InitializedSequences

section FixedPatch

noncomputable def geometryOuterConstant (G : SignedMeanGain.Geometry) : ℝ :=
  outerConstant G.patch.b

theorem geometryOuterConstant_pos (G : SignedMeanGain.Geometry) : 0 < geometryOuterConstant G :=
  outerConstant_pos (G.patch.a_pos.trans G.patch.a_lt_b)

/-- The concrete common constant for the manuscript's fixed actual patch. -/
noncomputable def actualOuterConstant : ℝ := geometryOuterConstant ActualInitialization.geometry

theorem actualOuterConstant_pos : 0 < actualOuterConstant :=
  geometryOuterConstant_pos _

theorem actualOuterConstant_eq :
    actualOuterConstant = 4 * PrimaryTargetBounds.rightRadius
      CorrectionInitialization.ActualPrimary.nominal * Real.sqrt 2 := rfl

/-- A literal coherent family on the fixed actual mean domain has the
same outer constant as the wave increments. -/
theorem actual_coherent_support {degree : ℝ} {N gap : ℕ}
    (D : PhysicalMeanJetBounds.CoherentFamily CorrectionInitialization.ActualPrimary.h degree N gap
      CorrectionInitialization.ActualPrimary.standardRegion.carrier ℝ)
    (hs : PhysicalMeanJetBounds.NativeSupport CorrectionInitialization.ActualPrimary.h
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b N
      CorrectionInitialization.ActualPrimary.standardRegion.carrier D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      D.field ∧
    SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      D.angularField := by
  have hcover : PhysicalMeanDomain.normalizedSlowDomain
      (2 * CorrectionInitialization.ActualPrimary.h) (1 / 2) 2 ⊆
      CorrectionInitialization.ActualPrimary.standardRegion.carrier := fun _ hx => hx
  exact ⟨coherent_field_support D
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
      CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      ActualInitialization.geometry.patch.a_pos ActualInitialization.geometry.patch.a_lt_b
      CorrectionInitialization.ActualPrimary.standardRegion.isOpen hcover hs hq le_rfl,
    coherent_angular_support D
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
      CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      ActualInitialization.geometry.patch.a_pos ActualInitialization.geometry.patch.a_lt_b
      CorrectionInitialization.ActualPrimary.standardRegion.isOpen hcover hs hq le_rfl⟩

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

theorem actual_patch_support
    (WA : ℕ → WaveData CorrectionInitialization.ActualPrimary.h DA IA KA (Fin 3))
    (MA : ℕ → MeanData CorrectionInitialization.ActualPrimary.h
      (CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h - 1 / 2))
    (MB : ℕ → MeanData CorrectionInitialization.ActualPrimary.h
      (CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h))
    (WP : ℕ → WaveData CorrectionInitialization.ActualPrimary.h DP IP KP Unit)
    (MP : ℕ → MeanData CorrectionInitialization.ActualPrimary.h
      (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h))
    {qbig : ℝ}
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (hqP : ∀ j, qbig ≤ ChartScales.Q (MP j).firstBand)
    (H : NativeOuterBounds ActualInitialization.geometry.patch.b WA MA MB WP MP) :
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (potentialIncrement (WA j) (MA j))) ∧
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (directStages MB j)) ∧
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (pressureIncrement (WP j) (MP j))) :=
  all_increment_support WA MA MB WP MP
    CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
    CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half hqA hqB hqP H

/-- The actual mean-domain type retains the strict normalized range
`(1/2,2)` used by the construction. -/
abbrev ActualMeanFamily (degree : ℝ) (N gap : ℕ) :=
  PhysicalMeanJetBounds.CoherentFamily CorrectionInitialization.ActualPrimary.h degree N gap
    CorrectionInitialization.ActualPrimary.standardRegion.carrier ℝ

/-- Native support on the single fixed actual patch. -/
abbrev ActualNativeSupport {degree : ℝ} {N gap : ℕ} (D : ActualMeanFamily degree N gap) :=
  PhysicalMeanJetBounds.NativeSupport CorrectionInitialization.ActualPrimary.h
    ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b N
    CorrectionInitialization.ActualPrimary.standardRegion.carrier D.native

/-- One constant for the literal coherent mean families and actual wave
representations. This is the valid-domain alternative to `MeanData`'s wider
cover interface. Stage zero is included in each increment family. -/
theorem actual_coherent_families_support
    (WA : ℕ → WaveData CorrectionInitialization.ActualPrimary.h DA IA KA (Fin 3))
    (WP : ℕ → WaveData CorrectionInitialization.ActualPrimary.h DP IP KP Unit)
    {NA GA NB GB NP GP : ℕ → ℕ}
    (MA : ∀ j, ActualMeanFamily (CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h - 1 /
      2)
      (NA j) (GA j))
    (MB : ∀ j, ActualMeanFamily (CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h)
      (NB j) (GB j))
    (MP : ∀ j, ActualMeanFamily (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h)
      (NP j) (GP j))
    (hsA : ∀ j, ActualNativeSupport (MA j))
    (hsB : ∀ j, ActualNativeSupport (MB j))
    (hsP : ∀ j, ActualNativeSupport (MP j))
    {qbig : ℝ}
    (hqA : ∀ j, qbig ≤ ChartScales.Q (NA j))
    (hqB : ∀ j, qbig ≤ ChartScales.Q (NB j))
    (hqP : ∀ j, qbig ≤ ChartScales.Q (NP j))
    (hWA : ∀ j, (WA j).upperRadius ≤ 2 * ActualInitialization.geometry.patch.b)
    (hWP : ∀ j, (WP j).upperRadius ≤ 2 * ActualInitialization.geometry.patch.b) :
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (fun w => (WA j).vector w + (MA j).angularField w)) ∧
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (MB j).angularField) ∧
    (∀ j, SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig
      (fun w => (WP j).pressure w + (MP j).field w)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact support_add (wave_vector_support (WA j) (hWA j))
      (actual_coherent_support (MA j) (hsA j) (hqA j)).2
  · intro j
    exact (actual_coherent_support (MB j) (hsB j) (hqB j)).2
  · intro j
    exact support_add (wave_pressure_support (WP j) (hWP j))
      (actual_coherent_support (MP j) (hsP j) (hqP j)).1

end FixedPatch

end NavierStokes.PhysicalStageSupport
