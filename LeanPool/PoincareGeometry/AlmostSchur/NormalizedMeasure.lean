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

public import LeanPool.PoincareGeometry.AlmostSchur.MetricRegularity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Normalization of Riemannian density measure -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Changing a coordinate basis scales its Gram density by the absolute
determinant of the basis transformation. -/
theorem coordinateDensity_map_basis (b : Module.Basis ι ℝ E) (P : E ≃L[ℝ] E)
    (c : M) (y : E) :
    matrixDensity (coordinateMetric (I := I) (b.map P.toLinearEquiv) c y) =
      |P.toLinearMap.det| * matrixDensity (coordinateMetric (I := I) b c y) := by
  unfold coordinateMetric tangentChartGram tangentTrivializationGram
  simp only [Module.Basis.map_apply]
  have hg := gram_linear_comp b
    ((trivializationAt E (TangentSpace I) c).symmL ℝ ((extChartAt I c).symm y))
    P.toContinuousLinearMap
  erw [hg]
  rw [matrixDensity_congruence, LinearMap.det_toMatrix]
  rfl

/-- The basis Lebesgue measure scales by the reciprocal determinant. -/
theorem basis_addHaar_map_eq (b : Module.Basis ι ℝ E) (P : E ≃L[ℝ] E) :
    (b.map P.toLinearEquiv).addHaar =
      ENNReal.ofReal |P.toLinearMap.det⁻¹| • b.addHaar := by
  rw [← b.map_addHaar P]
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar b.addHaar P.toLinearEquiv.isUnit_det'.ne_zero

/-- The two scaling factors cancel, so the normalized coordinate density
measure is unchanged under a basis transformation. -/
theorem coordinateDensityMeasure_map_basis (b : Module.Basis ι ℝ E) (P : E ≃L[ℝ] E)
    (c : M) :
    (b.map P.toLinearEquiv).addHaar.withDensity (fun y => ENNReal.ofReal
      (matrixDensity (coordinateMetric (I := I) (b.map P.toLinearEquiv) c y))) =
    b.addHaar.withDensity (fun y => ENNReal.ofReal
      (matrixDensity (coordinateMetric (I := I) b c y))) := by
  rw [basis_addHaar_map_eq]
  simp_rw [coordinateDensity_map_basis, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [withDensity_smul_measure]
  rw [show (fun y => ENNReal.ofReal |P.toLinearMap.det| *
      ENNReal.ofReal (matrixDensity (coordinateMetric (I := I) b c y))) =
    ENNReal.ofReal |P.toLinearMap.det| •
      (fun y => ENNReal.ofReal (matrixDensity (coordinateMetric (I := I) b c y))) from rfl]
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
    inv_mul_cancel₀ P.toLinearEquiv.isUnit_det'.ne_zero, abs_one, ENNReal.ofReal_one, one_smul]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Reindexing a basis does not change its metric density. -/
theorem coordinateDensity_reindex (b : Module.Basis ι ℝ E) (e : ι ≃ κ)
    (c : M) (y : E) :
    matrixDensity (coordinateMetric (I := I) (b.reindex e) c y) =
      matrixDensity (coordinateMetric (I := I) b c y) := by
  have h : coordinateMetric (I := I) (b.reindex e) c y =
      Matrix.reindex e e (coordinateMetric (I := I) b c y) := by
    ext i j
    simp [coordinateMetric, tangentChartGram, tangentTrivializationGram]
    rfl
  rw [h, matrixDensity, Matrix.det_reindex_self]
  rfl

/-- The normalized coordinate measure is independent of the basis and its
index type. -/
theorem coordinateDensityMeasure_basis_independent
    (b : Module.Basis ι ℝ E) (b' : Module.Basis κ ℝ E) (c : M) :
    b.addHaar.withDensity (fun y => ENNReal.ofReal
      (matrixDensity (coordinateMetric (I := I) b c y))) =
    b'.addHaar.withDensity (fun y => ENNReal.ofReal
      (matrixDensity (coordinateMetric (I := I) b' c y))) := by
  let e := b.indexEquiv b'
  let P := (b.equiv b' e).toContinuousLinearEquiv
  have h := coordinateDensityMeasure_map_basis (I := I) b P c
  have hb : b.map P.toLinearEquiv = b'.reindex e.symm := b.map_equiv b' e
  rw [hb, Module.Basis.addHaar_reindex] at h
  simp_rw [coordinateDensity_reindex] at h
  exact h.symm

variable [MeasurableSpace M] [BorelSpace M]

/-- Normalized chart measures are independent of the coordinate basis. -/
theorem chartMetricMeasure_basis_independent
    (b : Module.Basis ι ℝ E) (b' : Module.Basis κ ℝ E) (c : M) :
    chartMetricMeasure (I := I) b.addHaar b c = chartMetricMeasure (I := I) b'.addHaar b' c := by
  unfold chartMetricMeasure
  rw [coordinateDensityMeasure_basis_independent b b' c]

variable [Nonempty M] [LindelofSpace M]

/-- The normalized global measure is basis-independent. -/
theorem metricDensityMeasure_basis_independent
    (b : Module.Basis ι ℝ E) (b' : Module.Basis κ ℝ E) :
    metricDensityMeasure (I := I) (M := M) b.addHaar b =
      metricDensityMeasure (I := I) (M := M) b'.addHaar b' := by
  apply metricDensityMeasure_unique b'.addHaar b'
  intro c
  rw [metricDensityMeasure_restrict, chartMetricMeasure_basis_independent b b' c]

/-- Riemannian volume normalized by the basis Lebesgue measure. Although a
basis is chosen internally, the following theorem removes that choice. -/
def riemannianVolume : Measure M :=
  let b := Module.finBasis ℝ E
  metricDensityMeasure (I := I) b.addHaar b

/-- Every basis computes the same normalized Riemannian volume. -/
theorem riemannianVolume_eq (b : Module.Basis ι ℝ E) :
    riemannianVolume (I := I) (M := M) = metricDensityMeasure (I := I) b.addHaar b :=
  metricDensityMeasure_basis_independent _ b

/-- Chartwise characterization of normalized Riemannian volume. -/
theorem riemannianVolume_apply (b : Module.Basis ι ℝ E) (c : M) {s : Set M}
    (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source) :
    riemannianVolume (I := I) s = chartMetricLIntegral (I := I) b.addHaar b c s (fun _ => 1) := by
  rw [riemannianVolume_eq b, metricDensityMeasure_apply b.addHaar b c hs hc]

variable [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- Normalized Riemannian volume is positive on nonempty open sets. -/
theorem riemannianVolume_open_pos {s : Set M} (hs : IsOpen s) (hne : s.Nonempty) :
    0 < riemannianVolume (I := I) s :=
  metricDensityMeasure_open_pos _ _ hs hne

/-- A nonempty compact Hausdorff manifold has finite positive normalized
Riemannian volume for every continuous Riemannian metric. -/
theorem riemannianVolume_finite_positive [T2Space M] [CompactSpace M] :
    0 < riemannianVolume (I := I) (M := M) univ ∧
      riemannianVolume (I := I) (M := M) univ < ∞ :=
  ⟨metricDensityMeasure_univ_pos _ _, metricDensityMeasure_univ_lt_top _ _⟩

end AlmostSchur
