/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Defs
public import LeanPool.Besicovitch.Geometry.ConvexEnlargement
public import LeanPool.Besicovitch.Rectifiability.Selection

/-!
# Bad convex sets

A bad convex set meets the compact density core but contains disproportionately much measure
outside it. These are the holes used in the continuum construction.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace LeanPool.Besicovitch

/-- Open convex sets meeting `F` whose mass outside `F` exceeds `alpha` times their diameter. -/
def badConvexSets (mu : Measure (EuclideanSpace ℝ (Fin 2)))
    (F : Set (EuclideanSpace ℝ (Fin 2))) (alpha : ℝ) :
    Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {V | IsOpen V ∧ Convex ℝ V ∧ (V ∩ F).Nonempty ∧
    ENNReal.ofReal alpha * Metric.ediam V < mu (V \ F)}

@[simp]
theorem mem_badConvexSets {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F V : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} :
    V ∈ badConvexSets mu F alpha ↔ IsOpen V ∧ Convex ℝ V ∧ (V ∩ F).Nonempty ∧
      ENNReal.ofReal alpha * Metric.ediam V < mu (V \ F) :=
  Iff.rfl

/-- A bad convex set with positive leakage coefficient is bounded. -/
theorem isBounded_of_mem_badConvexSets {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F V : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} (halpha : 0 < alpha)
    (hV : V ∈ badConvexSets mu F alpha) : IsBounded V := by
  rcases hV with ⟨_, _, _, hleakage⟩
  rw [Metric.isBounded_iff_ediam_ne_top]
  intro htop
  have hcoefficient : ENNReal.ofReal alpha ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 halpha
  have hproduct : ENNReal.ofReal alpha * Metric.ediam V = ∞ := by
    simp [htop, hcoefficient]
  rw [hproduct] at hleakage
  exact (not_lt_of_ge le_top) hleakage

/-- A nonempty open bad convex set has positive diameter. -/
theorem diam_pos_of_mem_badConvexSets {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F V : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} (halpha : 0 < alpha)
    (hV : V ∈ badConvexSets mu F alpha) : 0 < Metric.diam V := by
  have hV_nonempty : V.Nonempty := hV.2.2.1.mono inter_subset_left
  obtain ⟨x, hx⟩ := hV_nonempty
  obtain ⟨y, hy, hyx⟩ :=
    preperfect_iff_nhds.mp hV.1.preperfect x hx univ (by simp)
  exact Metric.diam_pos (nontrivial_of_mem_mem_ne hx hy.2 hyx.symm)
    (isBounded_of_mem_badConvexSets halpha hV)

/-- The total mass supplies a uniform real diameter bound for all bad convex sets. -/
theorem diam_lt_measure_univ_div_of_mem_badConvexSets {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsFiniteMeasure mu] {F V : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} (halpha : 0 < alpha)
    (hV : V ∈ badConvexSets mu F alpha) :
    Metric.diam V < (mu Set.univ).toReal / alpha := by
  have hbounded := isBounded_of_mem_badConvexSets halpha hV
  have hed_finite : Metric.ediam V ≠ ∞ := Metric.isBounded_iff_ediam_ne_top.mp hbounded
  have hproduct_finite : ENNReal.ofReal alpha * Metric.ediam V ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hed_finite
  have hmass_finite : mu (V \ F) ≠ ∞ := measure_ne_top mu _
  have hreal : alpha * Metric.diam V < (mu (V \ F)).toReal := by
    have h := (ENNReal.toReal_lt_toReal hproduct_finite hmass_finite).2 hV.2.2.2
    simpa [ENNReal.toReal_ofReal halpha.le, Metric.diam] using h
  have hmass_le : (mu (V \ F)).toReal ≤ (mu Set.univ).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono (subset_univ _))
  apply (lt_div_iff₀ halpha).2
  nlinarith

/-- A BPC witness becomes bad after replacing it by its open convex hull and lowering the
coefficient. -/
theorem openConvexHull_mem_badConvexSets {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F U : Set (EuclideanSpace ℝ (Fin 2))}
    {alpha tau : ℝ} (halpha_tau : alpha ≤ tau) (hU_open : IsOpen U)
    (hUF : (U ∩ F).Nonempty)
    (hleakage : ENNReal.ofReal tau * Metric.ediam U < mu (U \ F)) :
    openConvexHull U ∈ badConvexSets mu F alpha := by
  have hsubset : U ⊆ openConvexHull U := subset_openConvexHull hU_open
  refine ⟨isOpen_openConvexHull U, convex_openConvexHull U, ?_, ?_⟩
  · exact hUF.mono (inter_subset_inter hsubset Subset.rfl)
  calc
    ENNReal.ofReal alpha * Metric.ediam (openConvexHull U) =
        ENNReal.ofReal alpha * Metric.ediam U := by rw [ediam_openConvexHull hU_open]
    _ ≤ ENNReal.ofReal tau * Metric.ediam U := by
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal halpha_tau) _
    _ < mu (U \ F) := hleakage
    _ ≤ mu (openConvexHull U \ F) :=
      measure_mono (sdiff_subset_sdiff hsubset Subset.rfl)

/-- The bad convex sets have a countable disjoint scale-dominating subfamily. -/
theorem exists_countable_disjoint_badConvexSets
    {mu : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure mu]
    (F : Set (EuclideanSpace ℝ (Fin 2))) {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ chosen ⊆ badConvexSets mu F alpha, chosen.PairwiseDisjoint id ∧ chosen.Countable ∧
      ∀ V ∈ badConvexSets mu F alpha, ∃ W ∈ chosen,
        (V ∩ W).Nonempty ∧ Metric.diam V < 2 * Metric.diam W := by
  exact exists_countable_disjoint_subfamily (badConvexSets mu F alpha)
    (fun _ hV ↦ hV.1) (fun _ hV ↦ hV.2.2.1.mono inter_subset_left)
    (fun _ hV ↦ isBounded_of_mem_badConvexSets halpha hV)
    ((mu Set.univ).toReal / alpha)
    (fun _ hV ↦ (diam_lt_measure_univ_div_of_mem_badConvexSets halpha hV).le)

end LeanPool.Besicovitch
