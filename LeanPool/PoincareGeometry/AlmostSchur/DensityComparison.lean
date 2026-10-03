/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.NormalizedMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Uniform comparison of coordinate density measures

On a compact subset of a chart target, positivity and continuity give finite
two-sided comparison with coordinate Lebesgue measure. No identification with
Hausdorff measure is used.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

/-- A positive continuous density on a compact set has finite two-sided
measure comparison constants. Empty compact sets are allowed. -/
theorem compact_density_measure_comparison
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {K : Set X} (hK : IsCompact K) (hmK : MeasurableSet K)
    (ρ : X → ℝ) (hc : ContinuousOn ρ K) (hp : ∀ x ∈ K, 0 < ρ x) :
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧
      μ.restrict K ≤ A • (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K ∧
      (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K ≤ B • μ.restrict K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, by simp, by simp, by simp, by simp⟩
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hc
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hc
  have hapos : 0 < ρ a := hp a ha
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ a)
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hapos)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hlo : c • μ.restrict K ≤
      (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K := by
    rw [restrict_withDensity hmK, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hmK] with x hx
    exact ENNReal.ofReal_le_ofReal (hmin hx)
  have hhi : (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K ≤
      ENNReal.ofReal (ρ b) • μ.restrict K := by
    rw [restrict_withDensity hmK, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hmK] with x hx
    exact ENNReal.ofReal_le_ofReal (hmax hx)
  refine ⟨c⁻¹, ENNReal.ofReal (ρ b), ENNReal.inv_ne_top.mpr hc0,
    ENNReal.ofReal_ne_top, ?_, hhi⟩
  have h := smul_le_smul_left c⁻¹ hlo
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] using h

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- The actual metric density has finite two-sided comparison with its
coordinate Haar measure on every compact subset of a chart target. -/
theorem coordinateDensity_measure_comparison (μ : Measure E)
    (b : Module.Basis ι ℝ E) (c : M) {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ (extChartAt I c).target) :
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧
      μ.restrict K ≤ A • (μ.withDensity (fun z => ENNReal.ofReal
        (matrixDensity (coordinateMetric (I := I) b c z)))).restrict K ∧
      (μ.withDensity (fun z => ENNReal.ofReal
        (matrixDensity (coordinateMetric (I := I) b c z)))).restrict K ≤ B • μ.restrict K :=
  compact_density_measure_comparison μ hK hK.measurableSet _
    ((continuousOn_coordinateDensity b c).mono hsub)
    (fun z hz => coordinateMetric_density_pos b c z (hsub hz))

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

/-- The pushforward of normalized Riemannian volume restricted to a chart
source is exactly the basis-normalized density measure on its target. -/
theorem map_riemannianVolume_restrict_chart (b : Module.Basis ι ℝ E) (c : M) :
    Measure.map (extChartAt I c)
        ((riemannianVolume (I := I)).restrict (extChartAt I c).source) =
      (b.addHaar.withDensity (fun z => ENNReal.ofReal
        (matrixDensity (coordinateMetric (I := I) b c z)))).restrict
          (extChartAt I c).target := by
  let φ := extChartAt I c
  have hs : MeasurableSet φ.source := (isOpen_extChartAt_source (I := I) c).measurableSet
  have hcont : Continuous (φ.source.domRestrict φ) :=
    (continuousOn_extChartAt (I := I) c).domRestrict
  have hae : AEMeasurable φ ((riemannianVolume (I := I)).restrict φ.source) :=
    aemeasurable_restrict_of_measurable_subtype hs hcont.measurable
  ext t ht
  have hpre : MeasurableSet (φ ⁻¹' t ∩ φ.source) := by
    have heq : Subtype.val '' ((φ.source.domRestrict φ) ⁻¹' t) = φ ⁻¹' t ∩ φ.source := by
      ext x
      simp only [mem_image, mem_preimage, mem_inter_iff]
      constructor
      · rintro ⟨⟨y, hy⟩, hyt, rfl⟩
        exact ⟨hyt, hy⟩
      · rintro ⟨hxt, hxs⟩
        exact ⟨⟨x, hxs⟩, hxt, rfl⟩
    rw [← heq]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image' (hcont.measurable ht)
  have himage : φ '' (φ ⁻¹' t ∩ φ.source) = t ∩ φ.target := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxt, hxs⟩, rfl⟩
      exact ⟨hxt, φ.map_source hxs⟩
    · rintro ⟨hzt, hzs⟩
      refine ⟨φ.symm z, ⟨?_, φ.map_target hzs⟩, φ.right_inv hzs⟩
      simpa only [mem_preimage, φ.right_inv hzs] using hzt
  rw [Measure.map_apply_of_aemeasurable hae ht, Measure.restrict_apply' hs,
    riemannianVolume_apply b c hpre inter_subset_right,
    Measure.restrict_apply ht, withDensity_apply _
      (ht.inter (isOpen_extChartAt_target (I := I) c).measurableSet)]
  simp only [chartMetricLIntegral, mul_one]
  change (∫⁻ z in φ '' (φ ⁻¹' t ∩ φ.source), _ ∂b.addHaar) = _
  rw [himage]

end Coordinates

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

/-- The chart pushforward of actual normalized volume and Euclidean volume
have finite two-sided domination on compact chart subsets. These are the
measure hypotheses needed for chartwise Sobolev transport. -/
theorem chartPushforward_measure_comparison (c : M) {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ (extChartAt I c).target) :
    let ν := Measure.map (extChartAt I c)
      ((riemannianVolume (I := I)).restrict (extChartAt I c).source)
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧
      (volume : Measure E).restrict K ≤ A • ν.restrict K ∧
      ν.restrict K ≤ B • (volume : Measure E).restrict K := by
  classical
  dsimp only
  let b := stdOrthonormalBasis ℝ E
  rw [map_riemannianVolume_restrict_chart b.toBasis c,
    Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hsub,
    b.addHaar_eq_volume]
  exact coordinateDensity_measure_comparison volume b.toBasis c hK hsub

end Euclidean

end AlmostSchur
