/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.ProjectionCharacterization

/-! # Negative -/

namespace Homogenization

open scoped BigOperators ENNReal

/-!
Finite-depth concrete negative/circ cube Besov seminorms.

This file freezes the first block-average-facing negative Besov layer used later
in testing and coarse-graining arguments. As on the positive side, the scale
parameter is encoded by a depth `j : ℕ` relative to a fixed parent cube `Q`, and
the outer aggregation is truncated at a finite depth.

At this checkpoint we only record the concrete circ quantities. The genuine
duality-based negative Besov seminorms and their comparison theorems belong in
`Duality.lean`.
-/

@[simp] theorem descendantsAverage_const {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  have hD : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hcard : (((descendantsAtDepth Q j).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD)
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

noncomputable def cubeBesovCircDepthAverage {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => ‖cubeAverage R u‖ ^ p.toReal

noncomputable def cubeBesovCircDepthWeight {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ) : ℝ :=
  (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ s

noncomputable def cubeBesovCircDepthSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovCircDepthWeight Q s j * (cubeBesovCircDepthAverage Q p u j) ^ (1 / p.toReal)

noncomputable def cubeBesovCircPartialSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  (Finset.sum (Finset.range (N + 1))
    fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal) ^ (1 / q.toReal)

noncomputable def cubeBesovCircPartialSeminormTop {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩ (fun j => cubeBesovCircDepthSeminorm Q s p u j)

noncomputable def cubeBesovCircPartialNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovCircPartialSeminorm Q s p q N u

noncomputable def cubeBesovCircPartialNormTop {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovCircPartialSeminormTop Q s p N u

@[simp] theorem cubeBesovCircDepthAverage_depth_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    cubeBesovCircDepthAverage Q p u 0 = ‖cubeAverage Q u‖ ^ p.toReal := by
  unfold cubeBesovCircDepthAverage descendantsAverage
  simp

@[simp] theorem cubeBesovCircDepthWeight_depth_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    cubeBesovCircDepthWeight Q s 0 = cubeBesovScaleWeight (-s) Q := by
  unfold cubeBesovCircDepthWeight cubeBesovScaleWeight
  simp

theorem cubeBesovCircDepthAverage_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovCircDepthAverage Q p u j := by
  unfold cubeBesovCircDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR =>
    Real.rpow_nonneg (norm_nonneg _) _

theorem cubeBesovCircDepthWeight_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    0 ≤ cubeBesovCircDepthWeight Q s j := by
  unfold cubeBesovCircDepthWeight
  have hQ : 0 ≤ cubeScaleFactor Q := le_of_lt <| by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow : 0 ≤ (3 : ℝ) ^ j := by positivity
  exact Real.rpow_nonneg (div_nonneg hQ hpow) _

theorem cubeBesovCircDepthSeminorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovCircDepthSeminorm Q s p u j := by
  unfold cubeBesovCircDepthSeminorm
  exact mul_nonneg (cubeBesovCircDepthWeight_nonneg Q s j)
    (Real.rpow_nonneg (cubeBesovCircDepthAverage_nonneg Q p u j) _)

theorem cubeBesovCircPartialSeminorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovCircPartialSeminorm Q s p q N u := by
  unfold cubeBesovCircPartialSeminorm
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (cubeBesovCircDepthSeminorm_nonneg Q s p u j) _)
    _

theorem cubeBesovCircPartialSeminormTop_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovCircPartialSeminormTop Q s p N u := by
  unfold cubeBesovCircPartialSeminormTop
  exact le_trans (cubeBesovCircDepthSeminorm_nonneg Q s p u 0)
    (Finset.le_sup' (f := fun j => cubeBesovCircDepthSeminorm Q s p u j) (by simp))

theorem cubeBesovCircPartialNorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovCircPartialNorm Q s p q N u :=
  cubeBesovCircPartialSeminorm_nonneg Q s p q N u

theorem cubeBesovCircPartialNormTop_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovCircPartialNormTop Q s p N u :=
  cubeBesovCircPartialSeminormTop_nonneg Q s p N u

theorem cubeBesovCircDepthAverage_eq_descendantsAverage_projection {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) (hp : p ≠ 0) :
    cubeBesovCircDepthAverage Q p u j =
      descendantsAverage Q j (fun R =>
        (cubeLpNorm R p (cubeProjection Q j u)) ^ p.toReal) := by
  classical
  unfold cubeBesovCircDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeLpNorm_cubeProjection_eq_abs_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (p := p) (f := u) hR hp]

@[simp] theorem cubeBesovCircDepthAverage_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (c : ℝ) (j : ℕ) :
    cubeBesovCircDepthAverage Q p (fun _ => c) j = ‖c‖ ^ p.toReal := by
  unfold cubeBesovCircDepthAverage
  simp [descendantsAverage_const, cubeAverage_const]

@[simp] theorem cubeBesovCircDepthAverage_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircDepthAverage Q p (fun _ => (0 : ℝ)) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  simp [cubeBesovCircDepthAverage_const, hpPos.ne']

@[simp] theorem cubeBesovCircDepthSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircDepthSeminorm Q s p (fun _ => (0 : ℝ)) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpInv : (1 / p.toReal) ≠ 0 := one_div_ne_zero hpPos.ne'
  unfold cubeBesovCircDepthSeminorm
  rw [cubeBesovCircDepthAverage_zero (Q := Q) (p := p) (j := j) hp0 hpTop]
  rw [Real.zero_rpow hpInv, mul_zero]

@[simp] theorem cubeBesovCircPartialSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovCircPartialSeminorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  have hqPos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqTop
  unfold cubeBesovCircPartialSeminorm
  simp [cubeBesovCircDepthSeminorm_zero, hp0, hpTop, hqPos.ne']

@[simp] theorem cubeBesovCircPartialSeminormTop_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircPartialSeminormTop Q s p N (fun _ => (0 : ℝ)) = 0 := by
  refine le_antisymm ?_ (cubeBesovCircPartialSeminormTop_nonneg Q s p N (fun _ => (0 : ℝ)))
  unfold cubeBesovCircPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovCircDepthSeminorm Q s p (fun _ => (0 : ℝ)) j) ?_
  intro j hj
  simp [cubeBesovCircDepthSeminorm_zero, hp0, hpTop]

@[simp] theorem cubeBesovCircPartialNorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovCircPartialNorm Q s p q N (fun _ => (0 : ℝ)) = 0 :=
  cubeBesovCircPartialSeminorm_zero Q s p q N hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovCircPartialNormTop_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircPartialNormTop Q s p N (fun _ => (0 : ℝ)) = 0 :=
  cubeBesovCircPartialSeminormTop_zero Q s p N hp0 hpTop

end Homogenization
