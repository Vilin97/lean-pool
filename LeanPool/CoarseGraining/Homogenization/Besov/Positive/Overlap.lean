/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive
public import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp

/-! # Overlap -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

/-!
## Explicit overlapping positive Besov seminorms

These definitions implement the scale-local overlapping positive Besov
oscillation and the finite-depth overlapping truncations. The full
infinite-depth wrappers are the manuscript-facing scalar objects under
boundedness/regularity hypotheses, while the unqualified `cubeBesov*` names
above remain the existing disjoint descendant definitions.
-/

noncomputable def cubeBesovOverlapOscillation {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  ScalarOverlap.cubeLpNorm S p
    (fun x => u x - ScalarOverlap.cubeAverage S u)

noncomputable def cubeBesovOverlapDepthAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  ScalarOverlap.centersAverage Q j fun S =>
    (cubeBesovOverlapOscillation S p u) ^ p.toReal

noncomputable def cubeBesovOverlapDepthWeight {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthWeight Q s j

noncomputable def cubeBesovOverlapDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovOverlapDepthWeight Q s j *
    (cubeBesovOverlapDepthAverage Q p u j) ^ (1 / p.toReal)

noncomputable def cubeBesovOverlapPartialSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ := by
  exact
    (Finset.sum (Finset.range (N + 1))
      (fun j => (cubeBesovOverlapDepthSeminorm Q s p u j) ^ q.toReal)) ^
        (1 / q.toReal)

noncomputable def cubeBesovOverlapPartialSeminormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩
    (fun j => cubeBesovOverlapDepthSeminorm Q s p u j)

noncomputable def cubeBesovOverlapPartialNorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovOverlapPartialSeminorm Q s p q N u +
    cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

noncomputable def cubeBesovOverlapPartialNormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) : ℝ :=
  cubeBesovOverlapPartialSeminormTop Q s p N u +
    cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

@[simp] theorem cubeBesovOverlapOscillation_middleChildCube {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    cubeBesovOverlapOscillation (ScalarOverlap.middleChildCube Q) p u =
      cubeBesovOscillation Q p u := by
  unfold cubeBesovOverlapOscillation cubeBesovOscillation cubeFluctuation
  simp

theorem cubeBesovOverlapOscillation_nonneg {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    0 ≤ cubeBesovOverlapOscillation S p u :=
  ScalarOverlap.cubeLpNorm_nonneg S p
    (fun x => u x - ScalarOverlap.cubeAverage S u)

theorem cubeBesovOverlapDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovOverlapDepthAverage Q p u j := by
  unfold cubeBesovOverlapDepthAverage
  exact ScalarOverlap.centersAverage_nonneg Q j _ fun S _hS =>
    Real.rpow_nonneg (cubeBesovOverlapOscillation_nonneg S p u) _

theorem cubeBesovOverlapDepthWeight_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    0 ≤ cubeBesovOverlapDepthWeight Q s j := by
  unfold cubeBesovOverlapDepthWeight cubeBesovDepthWeight
  have hQ : 0 ≤ cubeScaleFactor Q := le_of_lt <| by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow : 0 ≤ (3 : ℝ) ^ j := by positivity
  exact Real.rpow_nonneg (div_nonneg hQ hpow) _

theorem cubeBesovOverlapDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovOverlapDepthSeminorm Q s p u j := by
  unfold cubeBesovOverlapDepthSeminorm
  exact mul_nonneg (cubeBesovOverlapDepthWeight_nonneg Q s j)
    (Real.rpow_nonneg (cubeBesovOverlapDepthAverage_nonneg Q p u j) _)

theorem cubeBesovOverlapPartialSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    0 ≤ cubeBesovOverlapPartialSeminorm Q s p q N u := by
  unfold cubeBesovOverlapPartialSeminorm
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (cubeBesovOverlapDepthSeminorm_nonneg Q s p u j) _)
    _

theorem cubeBesovOverlapPartialSeminormTop_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    0 ≤ cubeBesovOverlapPartialSeminormTop Q s p N u := by
  unfold cubeBesovOverlapPartialSeminormTop
  exact le_trans (cubeBesovOverlapDepthSeminorm_nonneg Q s p u 0)
    (Finset.le_sup' (f := fun j => cubeBesovOverlapDepthSeminorm Q s p u j)
      (by simp))

theorem cubeBesovOverlapPartialNorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    0 ≤ cubeBesovOverlapPartialNorm Q s p q N u := by
  unfold cubeBesovOverlapPartialNorm
  exact add_nonneg
    (cubeBesovOverlapPartialSeminorm_nonneg Q s p q N u)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem cubeBesovOverlapPartialNormTop_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    0 ≤ cubeBesovOverlapPartialNormTop Q s p N u := by
  unfold cubeBesovOverlapPartialNormTop
  exact add_nonneg
    (cubeBesovOverlapPartialSeminormTop_nonneg Q s p N u)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

@[simp] theorem cubeBesovOverlapOscillation_const {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (c : ℝ) (hp0 : p ≠ 0) :
    cubeBesovOverlapOscillation S p (fun _ => c) = 0 := by
  unfold cubeBesovOverlapOscillation
  have havg : ScalarOverlap.cubeAverage S (fun _ : Vec d => c) = c := by
    simp
  simpa [havg] using
    ScalarOverlap.cubeLpNorm_zero (S := S) (p := p) (E := ℝ) hp0

@[simp] theorem cubeBesovOverlapOscillation_zero {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (hp0 : p ≠ 0) :
    cubeBesovOverlapOscillation S p (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapOscillation_const
    (S := S) (p := p) (c := (0 : ℝ)) hp0

@[simp] theorem cubeBesovOverlapDepthAverage_const {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (c : ℝ) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapDepthAverage Q p (fun _ => c) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  calc
    cubeBesovOverlapDepthAverage Q p (fun _ => c) j =
        ScalarOverlap.centersAverage Q j (fun _ => (0 : ℝ)) := by
          unfold cubeBesovOverlapDepthAverage
          simp [cubeBesovOverlapOscillation_const, hp0, hpPos.ne']
    _ = 0 := by
          simpa using ScalarOverlap.centersAverage_const Q j (0 : ℝ)

@[simp] theorem cubeBesovOverlapDepthAverage_zero {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapDepthAverage Q p (fun _ => (0 : ℝ)) j = 0 := by
  simpa using cubeBesovOverlapDepthAverage_const
    (Q := Q) (p := p) (c := (0 : ℝ)) (j := j) hp0 hpTop

@[simp] theorem cubeBesovOverlapDepthAverage_depth_zero {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    cubeBesovOverlapDepthAverage Q p u 0 =
      (cubeBesovOscillation Q p u) ^ p.toReal := by
  unfold cubeBesovOverlapDepthAverage ScalarOverlap.centersAverage
  simp

private theorem sum_range_succ_mono_of_nonneg {f : ℕ → ℝ}
    (h_nonneg : ∀ j : ℕ, 0 ≤ f j) {N M : ℕ} (hNM : N ≤ M) :
    (Finset.range (N + 1)).sum f ≤ (Finset.range (M + 1)).sum f := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hNM))
  · intro j _hjM _hjN
    exact h_nonneg j

private theorem sup'_range_succ_mono {f : ℕ → ℝ} {N M : ℕ} (hNM : N ≤ M) :
    (Finset.range (N + 1)).sup' ⟨0, by simp⟩ f ≤
      (Finset.range (M + 1)).sup' ⟨0, by simp⟩ f := by
  classical
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := f) ?_
  intro j hj
  exact Finset.le_sup' (s := Finset.range (M + 1)) (f := f)
    (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hNM)))

theorem cubeBesovOverlapPartialSeminorm_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : 0 < q.toReal) :
    Monotone fun N : ℕ => cubeBesovOverlapPartialSeminorm Q s p q N u := by
  intro N M hNM
  unfold cubeBesovOverlapPartialSeminorm
  have hsumN_nonneg :
      0 ≤ (Finset.range (N + 1)).sum
        (fun j => (cubeBesovOverlapDepthSeminorm Q s p u j) ^ q.toReal) := by
    exact Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (cubeBesovOverlapDepthSeminorm_nonneg Q s p u j) _
  have hsum_le :
      (Finset.range (N + 1)).sum
          (fun j => (cubeBesovOverlapDepthSeminorm Q s p u j) ^ q.toReal) ≤
        (Finset.range (M + 1)).sum
          (fun j => (cubeBesovOverlapDepthSeminorm Q s p u j) ^ q.toReal) := by
    exact sum_range_succ_mono_of_nonneg
      (fun j =>
        Real.rpow_nonneg (cubeBesovOverlapDepthSeminorm_nonneg Q s p u j) _)
      hNM
  exact Real.rpow_le_rpow hsumN_nonneg hsum_le (one_div_pos.mpr hq).le

theorem cubeBesovOverlapPartialSeminormTop_mono_N {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    Monotone fun N : ℕ => cubeBesovOverlapPartialSeminormTop Q s p N u := by
  intro N M hNM
  unfold cubeBesovOverlapPartialSeminormTop
  exact sup'_range_succ_mono
    (f := fun j => cubeBesovOverlapDepthSeminorm Q s p u j) hNM

theorem cubeBesovOverlapPartialNorm_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : 0 < q.toReal) :
    Monotone fun N : ℕ => cubeBesovOverlapPartialNorm Q s p q N u := by
  intro N M hNM
  unfold cubeBesovOverlapPartialNorm
  exact add_le_add (cubeBesovOverlapPartialSeminorm_mono_N Q s p q u hq hNM) le_rfl

theorem cubeBesovOverlapPartialNormTop_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    Monotone fun N : ℕ => cubeBesovOverlapPartialNormTop Q s p N u := by
  intro N M hNM
  unfold cubeBesovOverlapPartialNormTop
  exact add_le_add (cubeBesovOverlapPartialSeminormTop_mono_N Q s p u hNM) le_rfl

@[simp] theorem cubeBesovOverlapDepthSeminorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : ℝ) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapDepthSeminorm Q s p (fun _ => u) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpInv : (1 / p.toReal) ≠ 0 := one_div_ne_zero hpPos.ne'
  unfold cubeBesovOverlapDepthSeminorm
  rw [cubeBesovOverlapDepthAverage_const
    (Q := Q) (p := p) (c := u) (j := j) hp0 hpTop]
  rw [Real.zero_rpow hpInv, mul_zero]

@[simp] theorem cubeBesovOverlapDepthSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapDepthSeminorm Q s p (fun _ => (0 : ℝ)) j = 0 := by
  simpa using cubeBesovOverlapDepthSeminorm_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) (j := j) hp0 hpTop

@[simp] theorem cubeBesovOverlapPartialSeminorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapPartialSeminorm Q s p q N (fun _ => u) = 0 := by
  have hqPos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqTop
  unfold cubeBesovOverlapPartialSeminorm
  simp [cubeBesovOverlapDepthSeminorm_const, hp0, hpTop, hqPos.ne']

@[simp] theorem cubeBesovOverlapPartialSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapPartialSeminorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapPartialSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (N := N) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovOverlapPartialSeminormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapPartialSeminormTop Q s p N (fun _ => u) = 0 := by
  refine le_antisymm ?_
    (cubeBesovOverlapPartialSeminormTop_nonneg Q s p N (fun _ => u))
  unfold cubeBesovOverlapPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovOverlapDepthSeminorm Q s p (fun _ => u) j) ?_
  intro j hj
  simp [cubeBesovOverlapDepthSeminorm_const, hp0, hpTop]

@[simp] theorem cubeBesovOverlapPartialSeminormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapPartialSeminormTop Q s p N (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapPartialSeminormTop_const
    (Q := Q) (s := s) (p := p) (N := N) (u := (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovOverlapPartialNorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapPartialNorm Q s p q N (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovOverlapPartialNorm
  rw [cubeBesovOverlapPartialSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (N := N) (u := u)
    hp0 hpTop hq0 hqTop]
  simp [cubeAverage_const]

@[simp] theorem cubeBesovOverlapPartialNorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapPartialNorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovOverlapPartialNorm_const
    (Q := Q) (s := s) (p := p) (q := q) (N := N) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop]
  simp

@[simp] theorem cubeBesovOverlapPartialNormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapPartialNormTop Q s p N (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovOverlapPartialNormTop
  rw [cubeBesovOverlapPartialSeminormTop_const
    (Q := Q) (s := s) (p := p) (N := N) (u := u) hp0 hpTop]
  simp [cubeAverage_const]

@[simp] theorem cubeBesovOverlapPartialNormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapPartialNormTop Q s p N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovOverlapPartialNormTop_const
    (Q := Q) (s := s) (p := p) (N := N) (u := (0 : ℝ)) hp0 hpTop]
  simp

end Homogenization
