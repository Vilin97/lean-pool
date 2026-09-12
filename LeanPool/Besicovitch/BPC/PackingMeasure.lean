/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Basic
public import LeanPool.Besicovitch.Geometry.BallUnion
public import LeanPool.Besicovitch.SixPoint.Configuration

/-!
# Measure estimates for two-color ball packings

This file bounds the mass of a finite two-color ball packing by its union and leakage.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LeanPool.Besicovitch

/-- The union of the supported balls of one color. -/
def colorBallUnion (support : Finset SixPointIndex)
    (center : support → (EuclideanSpace ℝ (Fin 2)))
    (radius : support → ℝ) (color : SixPointColor) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i : {i : support // i.1.1 = color}, Metric.ball (center i.1) (radius i.1)

/-- Membership in a color ball union is witnessed by a supported index of that color. -/
@[simp]
theorem mem_colorBallUnion {support : Finset SixPointIndex}
    {center : support → (EuclideanSpace ℝ (Fin 2))}
    {radius : support → ℝ} {color : SixPointColor} {x : (EuclideanSpace ℝ (Fin 2))} :
    x ∈ colorBallUnion support center radius color ↔
      ∃ i : support, i.1.1 = color ∧ x ∈ Metric.ball (center i) (radius i) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i.1, i.2, hi⟩
  · rintro ⟨i, hcolor, hi⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, hcolor⟩, hi⟩

/-- The full ball union is the union of its red and blue parts. -/
theorem finiteBallUnion_eq_union_colorBallUnion (support : Finset SixPointIndex)
    (center : support → (EuclideanSpace ℝ (Fin 2))) (radius : support → ℝ) :
    finiteBallUnion support center radius = colorBallUnion support center radius .red ∪
      colorBallUnion support center radius .blue := by
  ext x
  simp only [mem_finiteBallUnion, mem_union, mem_colorBallUnion]
  constructor
  · rintro ⟨i, hi⟩
    cases hcolor : i.1.1
    · exact Or.inl ⟨i, hcolor, hi⟩
    · exact Or.inr ⟨i, hcolor, hi⟩
  · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩

/-- A single-color finite ball union is open. -/
theorem isOpen_colorBallUnion (support : Finset SixPointIndex)
    (center : support → (EuclideanSpace ℝ (Fin 2)))
    (radius : support → ℝ) (color : SixPointColor) :
    IsOpen (colorBallUnion support center radius color) :=
  isOpen_iUnion fun _ ↦ Metric.isOpen_ball

/-- A single-color finite ball union is measurable. -/
theorem measurableSet_colorBallUnion (support : Finset SixPointIndex)
    (center : support → (EuclideanSpace ℝ (Fin 2))) (radius : support → ℝ)
    (color : SixPointColor) :
    MeasurableSet (colorBallUnion support center radius color) :=
  (isOpen_colorBallUnion support center radius color).measurableSet

/-- The measure of a disjoint single-color ball union is the sum of its ball measures. -/
theorem measure_colorBallUnion {support : Finset SixPointIndex}
    (center : support → (EuclideanSpace ℝ (Fin 2)))
    (radius : support → ℝ) (color : SixPointColor) (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (hdisjoint : ∀ i j : support, i ≠ j → i.1.1 = j.1.1 →
      Disjoint (Metric.ball (center i) (radius i)) (Metric.ball (center j) (radius j))) :
    μ (colorBallUnion support center radius color) =
      ∑ i : {i : support // i.1.1 = color}, μ (Metric.ball (center i.1) (radius i.1)) := by
  rw [colorBallUnion, measure_iUnion]
  · exact tsum_fintype _
  · intro i j hij
    apply hdisjoint i.1 j.1
    · exact fun h ↦ hij (Subtype.ext h)
    · exact i.2.trans j.2.symm
  · exact fun _ ↦ measurableSet_ball

/-- Red-blue ball overlap lies outside both center sets. -/
theorem inter_colorBallUnion_subset_sdiff {support : Finset SixPointIndex}
    (center : support → (EuclideanSpace ℝ (Fin 2))) (radius : support → ℝ)
    (e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2)))
    (he : ∀ color, (e color).Nonempty) (hcenter : ∀ i, center i ∈ e i.1.1)
    (hradius : ∀ i, radius i ≤ (setEDist (e .red) (e .blue)).toReal) :
    colorBallUnion support center radius .red ∩ colorBallUnion support center radius .blue ⊆
      finiteBallUnion support center radius \ (e .red ∪ e .blue) := by
  rintro x ⟨hxred, hxblue⟩
  obtain ⟨i, hired, hxi⟩ := mem_colorBallUnion.mp hxred
  obtain ⟨j, hjblue, hxj⟩ := mem_colorBallUnion.mp hxblue
  have hred : Disjoint (Metric.ball (center i) (radius i)) (e .blue) := by
    apply ball_disjoint_of_le_setEDist_toReal (he .red) (he .blue)
    · simpa [hired] using hcenter i
    · exact hradius i
  have hblue : Disjoint (Metric.ball (center j) (radius j)) (e .red) := by
    apply ball_disjoint_of_le_setEDist_toReal (he .blue) (he .red)
    · simpa [hjblue] using hcenter j
    · rw [setEDist_comm]
      exact hradius j
  refine ⟨mem_finiteBallUnion.mpr ⟨i, hxi⟩, ?_⟩
  rw [mem_union, not_or]
  exact ⟨hblue.notMem_of_mem_left hxj, hred.notMem_of_mem_left hxi⟩

/-- The total ball mass is bounded by the union mass plus the mass outside both center sets. -/
theorem sum_measure_ball_le_union_add_leakage {support : Finset SixPointIndex}
    (center : support → (EuclideanSpace ℝ (Fin 2))) (radius : support → ℝ)
    (e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2)))
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (he : ∀ color, (e color).Nonempty)
    (hcenter : ∀ i, center i ∈ e i.1.1)
    (hradius : ∀ i, radius i ≤ (setEDist (e .red) (e .blue)).toReal)
    (hdisjoint : ∀ i j : support, i ≠ j → i.1.1 = j.1.1 →
      Disjoint (Metric.ball (center i) (radius i)) (Metric.ball (center j) (radius j))) :
    (∑ i : support, μ (Metric.ball (center i) (radius i))) ≤
      μ (finiteBallUnion support center radius) +
        μ (finiteBallUnion support center radius \ (e .red ∪ e .blue)) := by
  have hmeasure (color : SixPointColor) :=
    measure_colorBallUnion center radius color μ hdisjoint
  have hsum : (∑ i : support, μ (Metric.ball (center i) (radius i))) =
      μ (colorBallUnion support center radius .red) +
        μ (colorBallUnion support center radius .blue) := by
    calc
      _ = ∑ color : SixPointColor, ∑ i : {i : support // i.1.1 = color},
          μ (Metric.ball (center i.1) (radius i.1)) :=
        (Fintype.sum_fiberwise (fun i : support ↦ i.1.1)
          (fun i ↦ μ (Metric.ball (center i) (radius i)))).symm
      _ = ∑ color : SixPointColor, μ (colorBallUnion support center radius color) := by
        apply Finset.sum_congr rfl
        intro color _
        exact (hmeasure color).symm
      _ = _ := by
        rw [show (Finset.univ : Finset SixPointColor) = {.red, .blue} by
          ext color
          cases color <;> simp]
        simp
  rw [hsum, ← measure_union_add_inter _
    (measurableSet_colorBallUnion support center radius .blue)]
  rw [← finiteBallUnion_eq_union_colorBallUnion]
  exact add_le_add le_rfl (measure_mono <|
    inter_colorBallUnion_subset_sdiff center radius e he hcenter hradius)

/-- Density, straightness, and a leakage bound control the total supported radius. -/
theorem density_sum_lt_one_add_leakage_mul_ediam {support : Finset SixPointIndex}
    (hsupport : support.Nonempty) (center : support → (EuclideanSpace ℝ (Fin 2)))
    (radius : support → ℝ) (e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2)))
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {β scale : ℝ} {leakage : ℝ≥0∞}
    (hβ : 0 ≤ β) (he : ∀ color, (e color).Nonempty)
    (hcenter : ∀ i, center i ∈ e i.1.1) (hradius_pos : ∀ i, 0 < radius i)
    (hradius_lt : ∀ i, radius i < scale)
    (hradius_le : ∀ i, radius i ≤ (setEDist (e .red) (e .blue)).toReal)
    (hdisjoint : ∀ i j : support, i ≠ j → i.1.1 = j.1.1 →
      Disjoint (Metric.ball (center i) (radius i)) (Metric.ball (center j) (radius j)))
    (hdensity : ∀ x ∈ e .red ∪ e .blue, ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * β * r) < μ (Metric.ball x r)) (hμ : IsStraightMeasure μ)
    (hleakage : μ (finiteBallUnion support center radius \ (e .red ∪ e .blue)) ≤
      leakage * Metric.ediam (finiteBallUnion support center radius)) :
    ENNReal.ofReal (2 * β * ∑ i : support, radius i) <
      (1 + leakage) * Metric.ediam (finiteBallUnion support center radius) := by
  have hdensity_ball (i : support) : ENNReal.ofReal (2 * β * radius i) <
      μ (Metric.ball (center i) (radius i)) := by
    apply hdensity (center i)
    · cases hcolor : i.1.1
      · exact Or.inl (by simpa [hcolor] using hcenter i)
      · exact Or.inr (by simpa [hcolor] using hcenter i)
    · exact hradius_pos i
    · exact hradius_lt i
  have hdensity_sum : (∑ i : support, ENNReal.ofReal (2 * β * radius i)) <
      ∑ i : support, μ (Metric.ball (center i) (radius i)) := by
    apply ENNReal.sum_lt_sum_of_nonempty
    · obtain ⟨index, hindex⟩ := hsupport
      exact ⟨⟨index, hindex⟩, Finset.mem_univ _⟩
    · exact fun i _ ↦ hdensity_ball i
  have hmass := sum_measure_ball_le_union_add_leakage center radius e μ he hcenter
    hradius_le hdisjoint
  have hupper : (∑ i : support, μ (Metric.ball (center i) (radius i))) ≤
      (1 + leakage) * Metric.ediam (finiteBallUnion support center radius) := by
    calc
      _ ≤ μ (finiteBallUnion support center radius) +
          μ (finiteBallUnion support center radius \ (e .red ∪ e .blue)) := hmass
      _ ≤ Metric.ediam (finiteBallUnion support center radius) +
          leakage * Metric.ediam (finiteBallUnion support center radius) :=
        add_le_add (hμ _ <| measurableSet_finiteBallUnion center radius) hleakage
      _ = _ := by ring
  have hofReal : ENNReal.ofReal (2 * β * ∑ i : support, radius i) =
      ∑ i : support, ENNReal.ofReal (2 * β * radius i) := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Finset.mul_sum]
    · exact fun i _ ↦ mul_nonneg (mul_nonneg (by norm_num) hβ) (hradius_pos i).le
  rw [hofReal]
  exact hdensity_sum.trans_le hupper

end LeanPool.Besicovitch
