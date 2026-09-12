/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.BadConvexThickening

/-!
# Localizing bad convex sets

A selected bad set whose three-diameter enlargement meets a small continuum must itself lie in
the doubled ball, provided the centre was chosen outside its seven-diameter enlargement.
-/

@[expose] public section

noncomputable section

open Bornology Set

namespace LeanPool.Besicovitch

/-- Selected holes whose `p`-diameter enlargements meet a set. -/
def touchingBadConvexSets (p : ℝ)
    (chosen : Set (Set (EuclideanSpace ℝ (Fin 2))))
    (C : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {V | V ∈ chosen ∧ (diameterThickening p V ∩ C).Nonempty}

/-- A hole touching the local continuum is contained in the doubled localization ball. -/
theorem subset_ball_two_mul_of_diameterThickening_three_inter
    {V C : Set (EuclideanSpace ℝ (Fin 2))}
    (hV : IsBounded V) {z : (EuclideanSpace ℝ (Fin 2))} {rho : ℝ}
    (hz : z ∉ diameterThickening 7 V) (hC : C ⊆ Metric.closedBall z rho)
    (htouch : (diameterThickening 3 V ∩ C).Nonempty) :
    V ⊆ Metric.ball z (2 * rho) := by
  obtain ⟨x, hxthickening, hxC⟩ := htouch
  rw [diameterThickening, Metric.mem_thickening_iff] at hxthickening
  obtain ⟨w₂, hw₂V, hxw₂⟩ := hxthickening
  have hxz : dist x z ≤ rho := by
    simpa [dist_comm] using hC hxC
  intro w₁ hw₁V
  rw [Metric.mem_ball]
  by_contra hw₁
  have hzw₁ : 2 * rho ≤ dist z w₁ := by simpa [dist_comm] using not_lt.mp hw₁
  have hw₂w₁ : dist w₂ w₁ ≤ Metric.diam V :=
    Metric.dist_le_diam_of_mem hV hw₂V hw₁V
  have hxw₁ : dist x w₁ < 4 * Metric.diam V := by
    calc
      dist x w₁ ≤ dist x w₂ + dist w₂ w₁ := dist_triangle _ _ _
      _ < 3 * Metric.diam V + Metric.diam V := add_lt_add_of_lt_of_le hxw₂ hw₂w₁
      _ = 4 * Metric.diam V := by ring
  have hrho_diam : rho < 4 * Metric.diam V := by
    have htriangle : dist z w₁ ≤ dist z x + dist x w₁ := dist_triangle _ _ _
    rw [dist_comm z x] at htriangle
    nlinarith
  have hzw₂ : dist z w₂ < 7 * Metric.diam V := by
    have htriangle : dist z w₂ ≤ dist z x + dist x w₂ := dist_triangle _ _ _
    rw [dist_comm z x] at htriangle
    nlinarith
  apply hz
  rw [diameterThickening, Metric.mem_thickening_iff]
  exact ⟨w₂, hw₂V, hzw₂⟩

/-- The selected holes touching the local continuum charge only the doubled ball. -/
theorem mul_tsum_ediam_touchingBadConvexSets_le
    {mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))} (hF : MeasurableSet F)
    {alpha : ℝ} (halpha : 0 < alpha) {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id)
    {C : Set (EuclideanSpace ℝ (Fin 2))} {z : (EuclideanSpace ℝ (Fin 2))} {rho : ℝ}
    (hz : ∀ V : chosen, z ∉ diameterThickening 7 (V : Set (EuclideanSpace ℝ (Fin 2))))
    (hC : C ⊆ Metric.closedBall z rho) :
    ENNReal.ofReal alpha *
        ∑' V : touchingBadConvexSets 3 chosen C,
          Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) ≤
      mu (Metric.ball z (2 * rho) \ F) := by
  let touching := touchingBadConvexSets 3 chosen C
  have hlocal_subset : touching ⊆ chosen := fun _ hV ↦ hV.1
  have hlocal_bad : touching ⊆ badConvexSets mu F alpha := hlocal_subset.trans hchosen
  have hlocal_countable : touching.Countable := hcountable.mono hlocal_subset
  have hlocal_disjoint : touching.PairwiseDisjoint id := by
    intro V hV W hW hVW
    exact hdisjoint hV.1 hW.1 hVW
  apply mul_tsum_ediam_badConvexSets_le_measure hF hlocal_bad hlocal_countable
    hlocal_disjoint
  intro V hV
  apply subset_ball_two_mul_of_diameterThickening_three_inter
    (isBounded_of_mem_badConvexSets halpha (hchosen hV.1))
  · exact hz ⟨V, hV.1⟩
  · exact hC
  · exact hV.2

/-- The three-diameter enlargements touching the local continuum have total diameter smaller than
the continuum itself. -/
theorem tsum_ediam_touchingBadConvexSets_lt_ediam
    {mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))} (hF : MeasurableSet F)
    {alpha sigma : ℝ} (halpha : 0 < alpha) (hsigma : 0 < sigma)
    {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha)
    (hcountable : chosen.Countable) (hdisjoint : chosen.PairwiseDisjoint id)
    {C : Set (EuclideanSpace ℝ (Fin 2))} {z : (EuclideanSpace ℝ (Fin 2))} {rho : ℝ}
    (hrho : 0 < rho)
    (hz : ∀ V : chosen, z ∉ diameterThickening 7 (V : Set (EuclideanSpace ℝ (Fin 2))))
    (hC : C ⊆ Metric.closedBall z rho)
    (houtside : mu (Metric.ball z (2 * rho) \ F) <
      ENNReal.ofReal alpha * ENNReal.ofReal (sigma * rho / 14))
    (hCdiam : ENNReal.ofReal (sigma * rho / 2) ≤ Metric.ediam C) :
    ∑' V : touchingBadConvexSets 3 chosen C,
        Metric.ediam (diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2)))) <
          Metric.ediam C := by
  have hpacking := mul_tsum_ediam_touchingBadConvexSets_le hF halpha hchosen hcountable
    hdisjoint hz hC
  have hsum : (∑' V : touchingBadConvexSets 3 chosen C,
      Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) < ENNReal.ofReal (sigma * rho / 14) := by
    exact lt_of_mul_lt_mul_left (hpacking.trans_lt houtside) (by positivity)
  calc
    (∑' V : touchingBadConvexSets 3 chosen C,
        Metric.ediam (diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) ≤
        ∑' V : touchingBadConvexSets 3 chosen C,
          ENNReal.ofReal 7 * Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) :=
      ENNReal.tsum_le_tsum fun V ↦ by
        convert ediam_diameterThickening_le (by norm_num : (0 : ℝ) ≤ 3)
          (isBounded_of_mem_badConvexSets halpha (hchosen V.property.1)) using 1
        all_goals norm_num
    _ = ENNReal.ofReal 7 *
        ∑' V : touchingBadConvexSets 3 chosen C,
          Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) :=
      ENNReal.tsum_mul_left
    _ < ENNReal.ofReal 7 * ENNReal.ofReal (sigma * rho / 14) :=
      ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hsum
    _ = ENNReal.ofReal (sigma * rho / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7)]
      congr 1
      field_simp
      ring
    _ ≤ Metric.ediam C := hCdiam

end LeanPool.Besicovitch
