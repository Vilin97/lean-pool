/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Measure.DensityBasic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Uniform lower-density sets

The set `uniformDensitySet μ A γ m` consists of the points of `A` where the lower ball-mass
bound at level `γ` holds at every positive rational radius below `1 / (m + 1)`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- Ball mass is a measurable function of the center for an s-finite measure on the plane. -/
theorem measurable_measure_ball (mu : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite mu] (r : ℝ) :
    Measurable fun x ↦ mu (Metric.ball x r) := by
  let ballRelation : Set ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) :=
    {p | dist p.1 p.2 < r}
  have relation_measurable : MeasurableSet ballRelation := by
    exact measurableSet_lt measurable_dist measurable_const
  have h := measurable_measure_prodMk_left (ν := mu) relation_measurable
  convert h using 1
  funext x
  congr 1
  ext y
  simp only [ballRelation, mem_setOf_eq, mem_preimage, Metric.mem_ball]
  rw [dist_comm]

/-- Points with a uniform rational-radius lower mass bound. -/
def uniformDensitySet (mu : Measure (EuclideanSpace ℝ (Fin 2)))
    (A : Set (EuclideanSpace ℝ (Fin 2))) (γ : ℝ) (m : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x ∈ A | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / (m + 1 : ℝ) →
    ENNReal.ofReal (2 * γ * (q : ℝ)) ≤ mu (Metric.ball x q)}

/-- Uniform density sets are measurable. -/
theorem measurableSet_uniformDensitySet (mu : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite mu]
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (γ : ℝ) (m : ℕ) :
    MeasurableSet (uniformDensitySet mu A γ m) := by
  rw [show uniformDensitySet mu A γ m =
      A ∩ ⋂ q : ℚ, ⋂ (_ : 0 < (q : ℝ)), ⋂ (_ : (q : ℝ) < 1 / (m + 1 : ℝ)),
        {x | ENNReal.ofReal (2 * γ * (q : ℝ)) ≤ mu (Metric.ball x q)} by
    ext x
    simp only [uniformDensitySet, mem_setOf_eq, mem_inter_iff, mem_iInter]]
  refine hA.inter <| MeasurableSet.iInter fun q ↦ MeasurableSet.iInter fun _ ↦
    MeasurableSet.iInter fun _ ↦ ?_
  exact measurableSet_le measurable_const (measurable_measure_ball mu q)

/-- A strict lower-density bound places a point in some uniform density set. -/
theorem exists_mem_uniformDensitySet_of_lt_lowerOneDensity
    {A : Set (EuclideanSpace ℝ (Fin 2))} {x : (EuclideanSpace ℝ (Fin 2))} {γ : ℝ}
    (hx : x ∈ A) (hγ : 0 ≤ γ) (hdensity : ENNReal.ofReal γ < lowerOneDensity A x) :
    ∃ m : ℕ, x ∈ uniformDensitySet (μH[1].restrict A) A γ m := by
  obtain ⟨scale, hscale, hmass⟩ :=
    lowerOneDensity_eventually_ball_measure_gt hγ hdensity
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hscale
  refine ⟨m, hx, fun q hq hq_small ↦ ?_⟩
  rw [restrict_hausdorffMeasure_ball]
  exact (hmass q hq (hq_small.trans hm)).le

/-- Membership at level `γ` gives strict ball bounds at every lower nonnegative level. -/
theorem uniformDensitySet_ball_measure_gt {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {A : Set (EuclideanSpace ℝ (Fin 2))} {β γ : ℝ}
    {m : ℕ} {x : (EuclideanSpace ℝ (Fin 2))} (hβ : 0 ≤ β) (hβγ : β < γ)
    (hx : x ∈ uniformDensitySet mu A γ m) {r : ℝ} (hr : 0 < r)
    (hr_small : r < 1 / (m + 1 : ℝ)) :
    ENNReal.ofReal (2 * β * r) < mu (Metric.ball x r) := by
  have hγ : 0 < γ := hβ.trans_lt hβγ
  have hratio : β / γ < 1 := (div_lt_one hγ).2 hβγ
  have hlower : β / γ * r < r := by
    nlinarith [mul_lt_mul_of_pos_right hratio hr]
  obtain ⟨q : ℚ, hq_lower, hq_upper⟩ := exists_rat_btwn hlower
  have hq_pos : 0 < (q : ℝ) := by
    have hratio_nonneg : 0 ≤ β / γ := div_nonneg hβ hγ.le
    nlinarith [mul_nonneg hratio_nonneg hr.le]
  have hq_small : (q : ℝ) < 1 / (m + 1 : ℝ) := hq_upper.trans hr_small
  have hreal : 2 * β * r < 2 * γ * (q : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_left hq_lower hγ
    field_simp at hscaled
    nlinarith
  have hofReal : ENNReal.ofReal (2 * β * r) <
      ENNReal.ofReal (2 * γ * (q : ℝ)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
  exact hofReal.trans_le <| (hx.2 q hq_pos hq_small).trans <|
    measure_mono (Metric.ball_subset_ball hq_upper.le)

end LeanPool.Besicovitch
