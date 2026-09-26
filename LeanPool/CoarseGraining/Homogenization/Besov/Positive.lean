/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Basic

/-! # Positive -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

/-!
Finite disjoint positive-order cube Besov seminorms.

This file intentionally contains only the descendant-based positive Besov core.
Scalar overlap definitions and full `sSup` wrappers live in narrow downstream
modules so ordinary importers of `Besov.Positive` do not pay for overlap geometry.
-/

noncomputable def cubeBesovDepthAverage {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => (cubeBesovOscillation R p u) ^ p.toReal

noncomputable def cubeBesovDepthWeight {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ) : ℝ :=
  (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s)

noncomputable def cubeBesovDepthSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthWeight Q s j * (cubeBesovDepthAverage Q p u j) ^ (1 / p.toReal)

noncomputable def cubeBesovPartialSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ := by
  exact
    (Finset.sum (Finset.range (N + 1))
      (fun j => (cubeBesovDepthSeminorm Q s p u j) ^ q.toReal)) ^ (1 / q.toReal)

noncomputable def cubeBesovPartialSeminormTop {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩ (fun j => cubeBesovDepthSeminorm Q s p u j)

noncomputable def cubeBesovPartialNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminorm Q s p q N u + cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

noncomputable def cubeBesovPartialNormTop {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminormTop Q s p N u + cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

/-!
## Explicit disjoint positive Besov names

These names disambiguate the legacy descendant-based positive Besov pieces from
the overlap-based `cubeBesovOverlap*` family in downstream modules. The unqualified
`cubeBesov*` names remain as compatibility aliases for existing theorem
statements until the public API flip gate.
-/

noncomputable abbrev cubeBesovDisjointDepthAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthAverage Q p u j

noncomputable abbrev cubeBesovDisjointDepthWeight {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthWeight Q s j

noncomputable abbrev cubeBesovDisjointDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthSeminorm Q s p u j

noncomputable abbrev cubeBesovDisjointPartialSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminorm Q s p q N u

noncomputable abbrev cubeBesovDisjointPartialSeminormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminormTop Q s p N u

noncomputable abbrev cubeBesovDisjointPartialNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialNorm Q s p q N u

noncomputable abbrev cubeBesovDisjointPartialNormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialNormTop Q s p N u

@[simp] theorem cubeBesovDepthAverage_depth_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    cubeBesovDepthAverage Q p u 0 = (cubeBesovOscillation Q p u) ^ p.toReal := by
  unfold cubeBesovDepthAverage descendantsAverage
  simp

@[simp] theorem cubeBesovDepthWeight_depth_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    cubeBesovDepthWeight Q s 0 = cubeBesovScaleWeight s Q := by
  unfold cubeBesovDepthWeight cubeBesovScaleWeight
  simp

theorem cubeBesovDepthAverage_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovDepthAverage Q p u j := by
  unfold cubeBesovDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR =>
    Real.rpow_nonneg (cubeBesovOscillation_nonneg R p u) _

theorem cubeBesovDepthWeight_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    0 ≤ cubeBesovDepthWeight Q s j := by
  unfold cubeBesovDepthWeight
  have hQ : 0 ≤ cubeScaleFactor Q := le_of_lt <| by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow : 0 ≤ (3 : ℝ) ^ j := by positivity
  exact Real.rpow_nonneg (div_nonneg hQ hpow) _

theorem cubeBesovDepthSeminorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovDepthSeminorm Q s p u j := by
  unfold cubeBesovDepthSeminorm
  exact mul_nonneg (cubeBesovDepthWeight_nonneg Q s j)
    (Real.rpow_nonneg (cubeBesovDepthAverage_nonneg Q p u j) _)

theorem cubeBesovPartialSeminorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovPartialSeminorm Q s p q N u := by
  unfold cubeBesovPartialSeminorm
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (cubeBesovDepthSeminorm_nonneg Q s p u j) _)
    _

theorem cubeBesovPartialSeminormTop_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovPartialSeminormTop Q s p N u := by
  unfold cubeBesovPartialSeminormTop
  exact le_trans (cubeBesovDepthSeminorm_nonneg Q s p u 0)
    (Finset.le_sup' (f := fun j => cubeBesovDepthSeminorm Q s p u j) (by simp))

theorem cubeBesovPartialNorm_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovPartialNorm Q s p q N u := by
  unfold cubeBesovPartialNorm
  exact add_nonneg
    (cubeBesovPartialSeminorm_nonneg Q s p q N u)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem cubeBesovPartialNormTop_nonneg {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ cubeBesovPartialNormTop Q s p N u := by
  unfold cubeBesovPartialNormTop
  exact add_nonneg
    (cubeBesovPartialSeminormTop_nonneg Q s p N u)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

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

theorem cubeBesovPartialSeminorm_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : 0 < q.toReal) :
    Monotone fun N : ℕ => cubeBesovPartialSeminorm Q s p q N u := by
  intro N M hNM
  unfold cubeBesovPartialSeminorm
  have hsumN_nonneg :
      0 ≤ (Finset.range (N + 1)).sum
        (fun j => (cubeBesovDepthSeminorm Q s p u j) ^ q.toReal) := by
    exact Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (cubeBesovDepthSeminorm_nonneg Q s p u j) _
  have hsum_le :
      (Finset.range (N + 1)).sum
          (fun j => (cubeBesovDepthSeminorm Q s p u j) ^ q.toReal) ≤
        (Finset.range (M + 1)).sum
          (fun j => (cubeBesovDepthSeminorm Q s p u j) ^ q.toReal) := by
    exact sum_range_succ_mono_of_nonneg
      (fun j => Real.rpow_nonneg (cubeBesovDepthSeminorm_nonneg Q s p u j) _)
      hNM
  exact Real.rpow_le_rpow hsumN_nonneg hsum_le (one_div_pos.mpr hq).le

theorem cubeBesovPartialSeminormTop_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    Monotone fun N : ℕ => cubeBesovPartialSeminormTop Q s p N u := by
  intro N M hNM
  unfold cubeBesovPartialSeminormTop
  exact sup'_range_succ_mono (f := fun j => cubeBesovDepthSeminorm Q s p u j) hNM

theorem cubeBesovPartialNorm_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : 0 < q.toReal) :
    Monotone fun N : ℕ => cubeBesovPartialNorm Q s p q N u := by
  intro N M hNM
  unfold cubeBesovPartialNorm
  exact add_le_add (cubeBesovPartialSeminorm_mono_N Q s p q u hq hNM) le_rfl

theorem cubeBesovPartialNormTop_mono_N {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    Monotone fun N : ℕ => cubeBesovPartialNormTop Q s p N u := by
  intro N M hNM
  unfold cubeBesovPartialNormTop
  exact add_le_add (cubeBesovPartialSeminormTop_mono_N Q s p u hNM) le_rfl

@[simp] theorem cubeBesovDepthAverage_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : ℝ) (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDepthAverage Q p (fun _ => u) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  unfold cubeBesovDepthAverage descendantsAverage
  simp [cubeBesovOscillation_const, hpPos.ne']

@[simp] theorem cubeBesovDepthAverage_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDepthAverage Q p (fun _ => (0 : ℝ)) j = 0 := by
  simpa using cubeBesovDepthAverage_const (Q := Q) (p := p) (u := (0 : ℝ)) (j := j) hp0 hpTop

@[simp] theorem cubeBesovDepthSeminorm_const {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : ℝ) (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDepthSeminorm Q s p (fun _ => u) j = 0 := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpInv : (1 / p.toReal) ≠ 0 := one_div_ne_zero hpPos.ne'
  unfold cubeBesovDepthSeminorm
  rw [cubeBesovDepthAverage_const (Q := Q) (p := p) (u := u) (j := j) hp0 hpTop]
  rw [Real.zero_rpow hpInv, mul_zero]

@[simp] theorem cubeBesovDepthSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (j : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDepthSeminorm Q s p (fun _ => (0 : ℝ)) j = 0 := by
  simpa using cubeBesovDepthSeminorm_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) (j := j) hp0 hpTop

@[simp] theorem cubeBesovPartialSeminorm_const {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovPartialSeminorm Q s p q N (fun _ => u) = 0 := by
  have hqPos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqTop
  unfold cubeBesovPartialSeminorm
  simp [cubeBesovDepthSeminorm_const, hp0, hpTop, hqPos.ne']

@[simp] theorem cubeBesovPartialSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovPartialSeminorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovPartialSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (N := N) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovPartialSeminormTop_const {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : ℝ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovPartialSeminormTop Q s p N (fun _ => u) = 0 := by
  refine le_antisymm ?_ (cubeBesovPartialSeminormTop_nonneg Q s p N (fun _ => u))
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s p (fun _ => u) j) ?_
  intro j hj
  simp [cubeBesovDepthSeminorm_const, hp0, hpTop]

@[simp] theorem cubeBesovPartialSeminormTop_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovPartialSeminormTop Q s p N (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovPartialSeminormTop_const
    (Q := Q) (s := s) (p := p) (N := N) (u := (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovPartialNorm_const {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovPartialNorm Q s p q N (fun _ => u) = cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovPartialNorm
  rw [cubeBesovPartialSeminorm_const (Q := Q) (s := s) (p := p) (q := q) (N := N)
    (u := u) hp0 hpTop hq0 hqTop]
  simp [cubeAverage_const]

@[simp] theorem cubeBesovPartialNorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovPartialNorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovPartialNorm_const (Q := Q) (s := s) (p := p) (q := q) (N := N)
    (u := (0 : ℝ)) hp0 hpTop hq0 hqTop]
  simp

@[simp] theorem cubeBesovPartialNormTop_const {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (u : ℝ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovPartialNormTop Q s p N (fun _ => u) = cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovPartialNormTop
  rw [cubeBesovPartialSeminormTop_const (Q := Q) (s := s) (p := p) (N := N) (u := u) hp0 hpTop]
  simp [cubeAverage_const]

@[simp] theorem cubeBesovPartialNormTop_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (N : ℕ) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovPartialNormTop Q s p N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovPartialNormTop_const (Q := Q) (s := s) (p := p) (N := N)
    (u := (0 : ℝ)) hp0 hpTop]
  simp


end Homogenization
