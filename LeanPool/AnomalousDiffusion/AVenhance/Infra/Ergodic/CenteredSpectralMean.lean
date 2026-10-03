/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.CenteredSpectralFlow

/-! Centering preserves the homogeneous dual seminorm. Finite sums are repaired
using the mean of the actual total, rather than individual product means. -/

@[expose] public section

namespace AVenhance.Infra.Ergodic
open MeasureTheory Homogenization
noncomputable section

/-- Remove the actual cell mean. -/
def centerCell {d : ℕ} (h : Vec d → ℝ) : Vec d → ℝ :=
  fun x => h x - cellAverage h

theorem cellAverage_centerCell {d : ℕ} {h : Vec d → ℝ}
    (hh : LocallyIntegrable h (volume : Measure (Vec d))) :
    cellAverage (centerCell h) = 0 := by
  have he : centerCell h = fun x => h x + (-cellAverage h) := by
    funext x; simp [centerCell, sub_eq_add_neg]
  rw [he, cellAverage_add_of_locallyIntegrable hh continuous_const.locallyIntegrable,
    cellAverage_const]
  exact add_neg_cancel _

theorem homogeneousHMinusOneNorm_centerCell_eq {d : ℕ} {h : Vec d → ℝ}
    (hh : LocallyIntegrable h (volume : Measure (Vec d))) :
    homogeneousHMinusOneNorm (centerCell h) = homogeneousHMinusOneNorm h := by
  unfold homogeneousHMinusOneNorm
  apply iSup_congr
  intro φ
  have he : (fun x => centerCell h x * φ.val x) =
      fun x => h x * φ.val x + (-cellAverage h) * φ.val x := by
    funext x; dsimp [centerCell]; ring
  rw [he, cellAverage_add_of_locallyIntegrable
    (hh.mul_continuous φ.property.1.continuous)
    (show LocallyIntegrable (fun x => (-cellAverage h) * φ.val x) volume from
      (φ.property.1.continuous.const_mul _).locallyIntegrable)]
  have hc : cellAverage (fun x => (-cellAverage h) * φ.val x) =
      (-cellAverage h) * cellAverage φ.val := by
    unfold cellAverage torusFunction
    exact integral_const_mul _ _
  rw [hc, φ.property.2.2.1, mul_zero, add_zero]

/-- Triangle inequality for an actual finite collection of locally integrable data. -/
theorem homogeneousHMinusOneNorm_finset_sum_le {d : ℕ} {ι : Type*}
    (s : Finset ι) (h : ι → Vec d → ℝ)
    (hh : ∀ i ∈ s, LocallyIntegrable (h i) (volume : Measure (Vec d))) :
    homogeneousHMinusOneNorm (fun x => ∑ i ∈ s, h i x) ≤
      ∑ i ∈ s, homogeneousHMinusOneNorm (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousHMinusOneNorm, cellAverage_const]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (homogeneousHMinusOneNorm_add_le_of_locallyIntegrable
      (hh a (by simp)) (locallyIntegrable_finsetSum s
        (fun i hi => hh i (by simp [hi])))).trans
      (add_le_add le_rfl (ih (fun i hi => hh i (by simp [hi]))))

end
end AVenhance.Infra.Ergodic
