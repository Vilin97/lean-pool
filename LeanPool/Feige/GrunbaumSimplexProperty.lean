/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.GrunbaumWeightedForm
import LeanPool.Feige.SimplexMeasure

/-!
# The Grünbaum property for the standard simplex
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace Feige

noncomputable section

/-- The `α = 0` Grünbaum case of Theorem 2.2 supplies the strict
upper-halfspace property required by the `δ = 1` Feige reduction in every
positive dimension. -/
theorem simplexCentroidHalfspaceProperty_fin_succ (d : ℕ) :
    SimplexCentroidHalfspaceProperty (ι := Fin (d + 1)) := by
  intro y hy hsum
  simp only [Fintype.card_fin] at hsum ⊢
  have hsum' :
      (((d + 1 : ℕ) : ℝ) + 1) ≤ ∑ i, y i := by
    simpa using hsum
  let L : Grunbaum.SimplexE (d + 1) →L[ℝ] ℝ :=
    euclideanSimplexLinearForm y
  have hsum_pos : 0 < ∑ i, y i := by
    have hdim : 0 < (((d + 1 : ℕ) : ℝ) + 1) := by positivity
    exact hdim.trans_le hsum'
  have hL : L ≠ 0 :=
    euclideanSimplexLinearForm_ne_zero_of_sum_pos hsum_pos
  have hnegL : -L ≠ 0 := neg_ne_zero.mpr hL
  have hcentroid :
      (-L) (Grunbaum.simplexFullBody d).centroid ≤ (-1 : ℝ) := by
    have hc := one_le_euclideanSimplexLinearForm_centroid y hsum'
    change -L (Grunbaum.simplexFullBody d).centroid ≤ -1
    linarith
  have hg :=
    Grunbaum.grunbaum_centroid_halfspace_functional
      (Grunbaum.simplexFullBody d) (-L) hnegL (-1) hcentroid
  have hg_closed :
      Grunbaum.grunbaumConstant d ≤
        (volume
          (Grunbaum.simplexSet (d + 1) ∩
            {x : Grunbaum.SimplexE (d + 1) | 1 ≤ L x}) /
          volume (Grunbaum.simplexSet (d + 1))).toReal := by
    change Grunbaum.grunbaumConstant d ≤
      (volume
        (Grunbaum.simplexSet (d + 1) ∩
          ((-L) ⁻¹' Iic (-1))) /
        volume (Grunbaum.simplexSet (d + 1))).toReal at hg
    have hset :
        ((-L) ⁻¹' Iic (-1)) =
          {x : Grunbaum.SimplexE (d + 1) | 1 ≤ L x} := by
      ext x
      simp
    rw [hset] at hg
    exact hg
  have hstrict :
      volume
          (Grunbaum.simplexSet (d + 1) ∩
            {x : Grunbaum.SimplexE (d + 1) | 1 ≤ L x}) =
        volume
          (Grunbaum.simplexSet (d + 1) ∩
            {x : Grunbaum.SimplexE (d + 1) | 1 < L x}) :=
    Grunbaum.volume_inter_le_eq_volume_inter_lt
      (Grunbaum.simplexSet (d + 1))
      (Grunbaum.isClosed_simplexSet (d + 1)).measurableSet
      L hL 1
  rw [hstrict] at hg_closed
  have hA :
      MeasurableSet
        {x : Grunbaum.SimplexE (d + 1) | 1 < L x} :=
    measurableSet_lt measurable_const L.measurable
  have htransport :=
    volume_simplexSet_inter_eq_volume_fullSimplex_inter_preimage
      (d + 1) hA
  have hpreimage :
      simplexToEuclidean (d + 1) ⁻¹'
          {x : Grunbaum.SimplexE (d + 1) | 1 < L x} =
        {x : Fin (d + 1) → ℝ | 1 < simplexLinearForm y x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, L,
      euclideanSimplexLinearForm_comp_simplexToEuclidean]
  rw [hpreimage] at htransport
  rw [htransport, volume_simplexSet_eq_volume_fullSimplex] at hg_closed
  rw [grunbaumConstant_eq_sharpConstant] at hg_closed
  have hevent :
      MeasurableSet
        {x : Fin (d + 1) → ℝ | 1 < simplexLinearForm y x} :=
    measurableSet_lt measurable_const
      (Finset.measurable_fun_sum Finset.univ fun i _ ↦
        measurable_const.mul (measurable_pi_apply i))
  unfold Measure.real
  rw [simplexUniformMeasure_apply hevent]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_div] at hg_closed
  simpa only [div_eq_mul_inv, mul_comm, inter_comm] using hg_closed

/-- Positive-dimensional form with the dimension supplied as an arbitrary
positive natural number. -/
theorem simplexCentroidHalfspaceProperty_fin
    {n : ℕ} (hn : 0 < n) :
    SimplexCentroidHalfspaceProperty (ι := Fin n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa [Nat.succ_eq_add_one] using
    simplexCentroidHalfspaceProperty_fin_succ d

end

end Feige
