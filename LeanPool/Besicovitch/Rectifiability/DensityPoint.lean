/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.BadConvexThickening
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# A density point outside the enlarged holes

Lebesgue differentiation lets us choose the point outside the seven-diameter enlargements so that
the mass missing from the compact core is linearly small in every sufficiently small ball.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- A straight measure assigns at most `2r` mass to a closed ball of radius `r`. -/
theorem IsStraightMeasure.measure_closedBall_le {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    (hmu : IsStraightMeasure mu) (z : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    mu (Metric.closedBall z r) ≤ ENNReal.ofReal (2 * r) := by
  apply (hmu _ measurableSet_closedBall).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hxz : dist x z ≤ r := Metric.mem_closedBall.mp hx
  have hzy : dist z y ≤ r := by simpa [dist_comm] using Metric.mem_closedBall.mp hy
  exact (dist_triangle x z y).trans (by linarith)

/-- A lower ball-mass bound and a small loss outside the core leave a core point in the outer
annulus. -/
theorem annulus_inter_nonempty {mu : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure mu]
    (hmu : IsStraightMeasure mu) {F : Set (EuclideanSpace ℝ (Fin 2))}
    {z : (EuclideanSpace ℝ (Fin 2))} {sigma alpha rho : ℝ}
    (hsigma : 0 < sigma) (halpha_pos : 0 < alpha) (halpha : alpha < 28) (hrho : 0 < rho)
    (hball : ENNReal.ofReal (2 * sigma * rho) < mu (Metric.ball z rho))
    (hloss : mu (Metric.ball z rho \ F) < ENNReal.ofReal (sigma * alpha / 28 * rho)) :
    ((Metric.ball z rho \ Metric.ball z (sigma * rho / 2)) ∩ F).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hsubset : Metric.ball z rho ⊆
      (Metric.ball z rho \ F) ∪ Metric.ball z (sigma * rho / 2) := by
    intro x hx
    by_cases hxF : x ∈ F
    · by_cases hxinner : x ∈ Metric.ball z (sigma * rho / 2)
      · exact Or.inr hxinner
      · have : x ∈ (Metric.ball z rho \ Metric.ball z (sigma * rho / 2)) ∩ F :=
          ⟨⟨hx, hxinner⟩, hxF⟩
        rw [hempty] at this
        exact this.elim
    · exact Or.inl ⟨hx, hxF⟩
  have hinner : mu (Metric.ball z (sigma * rho / 2)) ≤ ENNReal.ofReal (sigma * rho) := by
    calc
      mu (Metric.ball z (sigma * rho / 2)) ≤
          mu (Metric.closedBall z (sigma * rho / 2)) :=
        measure_mono Metric.ball_subset_closedBall
      _ ≤ ENNReal.ofReal (2 * (sigma * rho / 2)) :=
        hmu.measure_closedBall_le z (sigma * rho / 2)
      _ = ENNReal.ofReal (sigma * rho) := by ring_nf
  have hupper : mu (Metric.ball z rho) < ENNReal.ofReal (2 * sigma * rho) := by
    calc
      mu (Metric.ball z rho) ≤
          mu (Metric.ball z rho \ F) + mu (Metric.ball z (sigma * rho / 2)) :=
        (measure_mono hsubset).trans (measure_union_le _ _)
      _ < ENNReal.ofReal (sigma * alpha / 28 * rho) +
          ENNReal.ofReal (sigma * rho) :=
        ENNReal.add_lt_add_of_lt_of_le (measure_ne_top mu _) hloss hinner
      _ = ENNReal.ofReal (sigma * alpha / 28 * rho + sigma * rho) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (2 * sigma * rho) := by
        apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2
        have halpha' : alpha / 28 < 1 := (div_lt_one (by norm_num)).2 halpha
        nlinarith [mul_lt_mul_of_pos_left halpha' (mul_pos hsigma hrho)]
  exact (not_lt_of_ge hball.le) hupper

/-- At a density point of `F`, straightness makes the mass outside `F` smaller than any prescribed
positive linear function of the radius. -/
theorem exists_scale_measure_ball_sdiff_lt
    {mu : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure mu]
    (hmu : IsStraightMeasure mu) {F : Set (EuclideanSpace ℝ (Fin 2))}
    {z : (EuclideanSpace ℝ (Fin 2))}
    (hdensity : Tendsto
      (fun r ↦ mu (Fᶜ ∩ Metric.closedBall z r) / mu (Metric.closedBall z r))
      (𝓝[>] 0) (𝓝 0)) {k : ℝ} (hk : 0 < k) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ r : ℝ, 0 < r → r < scale →
      mu (Metric.ball z r \ F) < ENNReal.ofReal (k * r) := by
  have hepsilon : 0 < ENNReal.ofReal (k / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have heventually : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      mu (Fᶜ ∩ Metric.closedBall z r) / mu (Metric.closedBall z r) <
        ENNReal.ofReal (k / 2) :=
    hdensity.eventually (Iio_mem_nhds hepsilon)
  obtain ⟨neighborhood, hneighborhood, hsubset⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp heventually
  obtain ⟨scale, hscale, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨scale, hscale, fun r hr hrscale ↦ ?_⟩
  have hr_mem : r ∈ neighborhood ∩ Ioi (0 : ℝ) := by
    refine ⟨hball ?_, hr⟩
    simpa [Real.dist_eq, abs_of_pos hr] using hrscale
  have hratio := hsubset hr_mem
  have hset : Metric.ball z r \ F ⊆ Fᶜ ∩ Metric.closedBall z r := by
    intro x hx
    exact ⟨hx.2, Metric.ball_subset_closedBall hx.1⟩
  by_cases hball_zero : mu (Metric.closedBall z r) = 0
  · have houtside_zero : mu (Metric.ball z r \ F) = 0 :=
      measure_mono_null hset (measure_mono_null inter_subset_right hball_zero)
    rw [houtside_zero]
    exact ENNReal.ofReal_pos.2 (mul_pos hk hr)
  · have hnumerator : mu (Fᶜ ∩ Metric.closedBall z r) <
        ENNReal.ofReal (k / 2) * mu (Metric.closedBall z r) := by
      exact (ENNReal.div_lt_iff (Or.inl hball_zero)
        (Or.inl (measure_ne_top mu _))).mp hratio
    calc
      mu (Metric.ball z r \ F) ≤ mu (Fᶜ ∩ Metric.closedBall z r) := measure_mono hset
      _ < ENNReal.ofReal (k / 2) * mu (Metric.closedBall z r) := hnumerator
      _ ≤ ENNReal.ofReal (k / 2) * ENNReal.ofReal (2 * r) := by
        gcongr
        exact hmu.measure_closedBall_le z r
      _ = ENNReal.ofReal (k * r) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ k / 2)]
        congr 1
        ring

/-- One may choose the point outside all seven-diameter enlargements to be a density point of the
compact core. -/
theorem exists_densityPoint_not_mem_sevenDiameterThickening
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsFiniteMeasure mu] (hmu : IsStraightMeasure mu) {F : Set (EuclideanSpace ℝ (Fin 2))}
    (hF : MeasurableSet F) {alpha : ℝ} (halpha : 0 < alpha)
    {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha)
    (hcountable : chosen.Countable) (hdisjoint : chosen.PairwiseDisjoint id)
    (houtside : mu Fᶜ < ENNReal.ofReal (alpha / 15) * mu F) {k : ℝ} (hk : 0 < k) :
    ∃ z ∈ F,
      (∀ V : chosen, z ∉ diameterThickening 7 (V : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∃ scale : ℝ, 0 < scale ∧ ∀ r : ℝ, 0 < r → r < scale →
        mu (Metric.ball z r \ F) < ENNReal.ofReal (k * r) := by
  let U := ⋃ V : chosen, diameterThickening 7 (V : Set (EuclideanSpace ℝ (Fin 2)))
  have hU_open : IsOpen U := isOpen_iUnion fun V ↦
    isOpen_diameterThickening 7 (V : Set (EuclideanSpace ℝ (Fin 2)))
  have hmeasure : mu U < mu F :=
    measure_iUnion_sevenDiameterThickening_lt hmu hF halpha hchosen hcountable
      hdisjoint houtside
  have hremaining_ne : mu (F \ U) ≠ 0 := by
    intro hzero
    have hdecomposition := measure_sdiff_add_inter (μ := mu) F hU_open.measurableSet
    rw [hzero, zero_add] at hdecomposition
    have hle : mu F ≤ mu U := by
      rw [← hdecomposition]
      exact measure_mono inter_subset_right
    exact (not_le_of_gt hmeasure) hle
  have hae := _root_.Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet mu hF.compl
  have hae_remaining : ∀ᵐ z ∂mu.restrict (F \ U),
      Tendsto (fun r ↦ mu (Fᶜ ∩ Metric.closedBall z r) / mu (Metric.closedBall z r))
        (𝓝[>] 0) (𝓝 ((Fᶜ).indicator 1 z)) :=
    ae_mono Measure.restrict_le_self hae
  obtain ⟨z, hz, hzdensity⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hremaining_ne hae_remaining
  have hindicator : (Fᶜ).indicator (1 : (EuclideanSpace ℝ (Fin 2)) → ℝ≥0∞) z = 0 := by
    simp [hz.1]
  rw [hindicator] at hzdensity
  obtain ⟨scale, hscale, hsmall⟩ :=
    exists_scale_measure_ball_sdiff_lt hmu hzdensity hk
  refine ⟨z, hz.1, ?_, scale, hscale, hsmall⟩
  intro V hzV
  exact hz.2 (mem_iUnion_of_mem V hzV)

end LeanPool.Besicovitch
