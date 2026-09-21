/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Projection

/-! # Positive Besov Localize -/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

open scoped BigOperators ENNReal

/-!
# Legacy finite positive Besov localization

This file records bounded scalar `q = 2` localization helpers for the legacy
disjoint, finite-truncation/real-`sSup` compatibility lane.  They are not
statements about the manuscript's exact overlapping `ENNReal` definitions.
The unscaled full finite norm contains a cube-average term, so its unscaled
localization statement is stated for the finite seminorm part.  The scaled form
controls the full finite norm by the parent `positiveBesovPartialNormTwo`.
-/

namespace Legacy

private theorem cubeBesovDepthWeight_eq_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : Cube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (s : ℝ) (n : ℕ) :
    cubeBesovDepthWeight R s n = cubeBesovDepthWeight Q s (j + n) := by
  have hbase :
      cubeScaleFactor R / (3 : ℝ) ^ n =
        cubeScaleFactor Q / (3 : ℝ) ^ (j + n) := by
    rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
    rw [pow_add]
    field_simp
  simp [cubeBesovDepthWeight, hbase]

private theorem sq_cubeBesovDepthSeminorm_two {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ) :
    (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 =
      (cubeBesovDepthWeight Q s j) ^ 2 *
        cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j := by
  have hA : 0 ≤ cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j :=
    cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞) u j
  calc
    (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2
        =
          (cubeBesovDepthWeight Q s j *
            (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^
              (1 / ((2 : ℝ≥0∞).toReal))) ^ 2 := by
              simp [cubeBesovDepthSeminorm]
    _ =
        (cubeBesovDepthWeight Q s j) ^ 2 *
          ((cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^
            (1 / ((2 : ℝ≥0∞).toReal))) ^ 2 := by
          ring
    _ =
        (cubeBesovDepthWeight Q s j) ^ 2 *
          cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j := by
          congr 1
          have htwo : ((2 : ℝ≥0∞).toReal : ℝ) = 2 := by norm_num
          rw [htwo]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
          norm_num

private theorem cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u =
      Real.sqrt (∑ j ∈ Finset.range (N + 1),
        (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) := by
  unfold cubeBesovPartialSeminorm
  norm_num [Real.sqrt_eq_rpow]

private theorem sq_cubeBesovPartialSeminorm_two_two {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    (cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2 =
      ∑ j ∈ Finset.range (N + 1),
        (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 := by
  rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem positiveBesovPartialSeminormTwo_nonneg {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ positiveBesovPartialSeminormTwo Q s N u := by
  unfold positiveBesovPartialSeminormTwo
  exact cubeBesovPartialSeminorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

private theorem sq_positiveBesovPartialSeminormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    (positiveBesovPartialSeminormTwo Q s N u) ^ 2 =
      ∑ j ∈ Finset.range (N + 1),
        (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 := by
  simpa [positiveBesovPartialSeminormTwo] using
    sq_cubeBesovPartialSeminorm_two_two Q s N u

theorem positiveBesovPartialSeminormTwo_le_succ {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (N : ℕ) :
    positiveBesovPartialSeminormTwo Q s N u ≤
      positiveBesovPartialSeminormTwo Q s (N + 1) u := by
  have hsq :
      (positiveBesovPartialSeminormTwo Q s N u) ^ 2 ≤
        (positiveBesovPartialSeminormTwo Q s (N + 1) u) ^ 2 := by
    rw [sq_positiveBesovPartialSeminormTwo, sq_positiveBesovPartialSeminormTwo]
    have hsplit :
        Finset.sum (Finset.range (N + 2))
            (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) =
          Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) +
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u (N + 1)) ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_range_succ
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) (N + 1))
    calc
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2)
          ≤
        Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) +
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u (N + 1)) ^ 2 := by
              exact le_add_of_nonneg_right (sq_nonneg _)
      _ =
        Finset.sum (Finset.range (N + 2))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) := by
            rw [hsplit]
  have hN_nonneg :
      0 ≤ positiveBesovPartialSeminormTwo Q s N u :=
    positiveBesovPartialSeminormTwo_nonneg Q s N u
  have hSucc_nonneg :
      0 ≤ positiveBesovPartialSeminormTwo Q s (N + 1) u :=
    positiveBesovPartialSeminormTwo_nonneg Q s (N + 1) u
  have habs :
      |positiveBesovPartialSeminormTwo Q s N u| ≤
        |positiveBesovPartialSeminormTwo Q s (N + 1) u| :=
    sq_le_sq.mp hsq
  simpa [abs_of_nonneg hN_nonneg, abs_of_nonneg hSucc_nonneg] using habs

private theorem cubeBesovDepthAverage_add_eq_descendantsAverage {d : ℕ}
    (Q : Cube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j n : ℕ) :
    cubeBesovDepthAverage Q p u (j + n) =
      descendantsAverage Q j (fun R => cubeBesovDepthAverage R p u n) := by
  unfold cubeBesovDepthAverage
  simpa using
    (descendantsAverage_add_eq_descendantsAverage_descendantsAverage
      (Q := Q) (j := j) (n := n)
      (F := fun R => (cubeBesovOscillation R p u) ^ p.toReal))

private theorem descendantsAverage_sq_cubeBesovDepthSeminorm_two_eq_shifted {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j n : ℕ) :
    descendantsAverage Q j
        (fun R => (cubeBesovDepthSeminorm R s (2 : ℝ≥0∞) u n) ^ 2) =
      (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u (j + n)) ^ 2 := by
  calc
    descendantsAverage Q j
        (fun R => (cubeBesovDepthSeminorm R s (2 : ℝ≥0∞) u n) ^ 2)
        =
          descendantsAverage Q j
            (fun R =>
              (cubeBesovDepthWeight Q s (j + n)) ^ 2 *
                cubeBesovDepthAverage R (2 : ℝ≥0∞) u n) := by
            unfold descendantsAverage
            refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rw [sq_cubeBesovDepthSeminorm_two]
            rw [cubeBesovDepthWeight_eq_of_mem_descendantsAtDepth hR]
    _ =
        (cubeBesovDepthWeight Q s (j + n)) ^ 2 *
          descendantsAverage Q j
            (fun R => cubeBesovDepthAverage R (2 : ℝ≥0∞) u n) := by
          rw [descendantsAverage_mul_left Q j
            ((cubeBesovDepthWeight Q s (j + n)) ^ 2)
            (fun R => cubeBesovDepthAverage R (2 : ℝ≥0∞) u n)]
    _ =
        (cubeBesovDepthWeight Q s (j + n)) ^ 2 *
          cubeBesovDepthAverage Q (2 : ℝ≥0∞) u (j + n) := by
          rw [cubeBesovDepthAverage_add_eq_descendantsAverage]
    _ = (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u (j + n)) ^ 2 := by
          symm
          exact sq_cubeBesovDepthSeminorm_two Q s u (j + n)

/-- Legacy disjoint finite scalar `q = 2` positive Besov seminorms localize over
descendants. -/
theorem descendantsAverage_sq_cubeBesovPartialSeminormTwo_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ) :
    descendantsAverage Q j
      (fun R => (cubeBesovPartialSeminorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2) ≤
      (cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u) ^ 2 := by
  calc
    descendantsAverage Q j
        (fun R => (cubeBesovPartialSeminorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2)
        =
          descendantsAverage Q j
            (fun R => ∑ n ∈ Finset.range (N + 1),
              (cubeBesovDepthSeminorm R s (2 : ℝ≥0∞) u n) ^ 2) := by
            refine congrArg (descendantsAverage Q j) ?_
            funext R
            exact sq_cubeBesovPartialSeminorm_two_two R s N u
    _ =
        ∑ n ∈ Finset.range (N + 1),
          descendantsAverage Q j
            (fun R => (cubeBesovDepthSeminorm R s (2 : ℝ≥0∞) u n) ^ 2) := by
          rw [descendantsAverage_sum Q j (Finset.range (N + 1))
            (fun R n => (cubeBesovDepthSeminorm R s (2 : ℝ≥0∞) u n) ^ 2)]
    _ =
        ∑ n ∈ Finset.range (N + 1),
          (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u (j + n)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact descendantsAverage_sq_cubeBesovDepthSeminorm_two_eq_shifted Q s u j n
    _ =
        ∑ n ∈ Finset.Ico j (j + N + 1),
          (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u n) ^ 2 := by
          simpa [Nat.add_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun n => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u n) ^ 2)
              (m := j) (n := j + N + 1)).symm
    _ ≤
        ∑ n ∈ Finset.range (j + N + 1),
          (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u n) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
          · intro n hn hnot
            exact sq_nonneg _
    _ = (cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u) ^ 2 := by
          symm
          exact sq_cubeBesovPartialSeminorm_two_two Q s (j + N) u

theorem descendantsAverage_sq_positiveBesovPartialSeminormTwo_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ) :
    descendantsAverage Q j
      (fun R => (positiveBesovPartialSeminormTwo R s N u) ^ 2) ≤
      (positiveBesovPartialSeminormTwo Q s (j + N) u) ^ 2 := by
  simpa [positiveBesovPartialSeminormTwo] using
    descendantsAverage_sq_cubeBesovPartialSeminormTwo_le Q s u j N

theorem positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    positiveBesovPartialSeminormTwo Q s N u ≤
      positiveBesovPartialNormTwo Q s N u := by
  unfold positiveBesovPartialSeminormTwo positiveBesovPartialNormTwo
    cubeBesovDisjointPartialSeminorm cubeBesovDisjointPartialNorm cubeBesovPartialNorm
  exact le_add_of_nonneg_right
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem positiveBesovPartialNormTwo_nonneg {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    0 ≤ positiveBesovPartialNormTwo Q s N u := by
  unfold positiveBesovPartialNormTwo
  exact cubeBesovPartialNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

theorem positiveBesovPartialNormTwo_le_succ {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (N : ℕ) :
    positiveBesovPartialNormTwo Q s N u ≤
      positiveBesovPartialNormTwo Q s (N + 1) u := by
  unfold positiveBesovPartialNormTwo cubeBesovDisjointPartialNorm cubeBesovPartialNorm
  have hsemi :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u ≤
        cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) u := by
    simpa [positiveBesovPartialSeminormTwo] using
      positiveBesovPartialSeminormTwo_le_succ Q s u N
  exact add_le_add hsemi le_rfl

private theorem positiveBesovPartialNormTwo_zero_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    positiveBesovPartialNormTwo Q s 0 u ≤ positiveBesovPartialNormTwo Q s N u := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact ih.trans (positiveBesovPartialNormTwo_le_succ Q s u N)

/-- Legacy compatibility form: the localized finite scalar seminorm is bounded
by the parent finite positive Besov norm.  The corresponding unscaled statement
with local `positiveBesovPartialNormTwo` on the left is false for this
normalization; see the scaled full-norm localization below. -/
theorem descendantsAverage_sq_cubeBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ) :
    descendantsAverage Q j
      (fun R => (cubeBesovPartialSeminorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2) ≤
      (positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
  have hloc := descendantsAverage_sq_cubeBesovPartialSeminormTwo_le Q s u j N
  have hsemi :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u ≤
        positiveBesovPartialNormTwo Q s (j + N) u :=
    positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo Q s (j + N) u
  have hsemi_nonneg :
      0 ≤ cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u :=
    cubeBesovPartialSeminorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u
  have hnorm_nonneg : 0 ≤ positiveBesovPartialNormTwo Q s (j + N) u := by
    unfold positiveBesovPartialNormTwo
    exact cubeBesovPartialNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u
  have hsquares :
      (cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (j + N) u) ^ 2 ≤
        (positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
    nlinarith
  exact le_trans hloc hsquares

theorem descendantsAverage_sq_positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ) :
    descendantsAverage Q j
      (fun R => (positiveBesovPartialSeminormTwo R s N u) ^ 2) ≤
      (positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
  simpa [positiveBesovPartialSeminormTwo] using
    descendantsAverage_sq_cubeBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
      Q s u j N

private theorem descendantsAverage_add {d : ℕ} (Q : Cube d) (j : ℕ)
    (F G : Cube d → ℝ) :
    descendantsAverage Q j (fun R => F R + G R) =
      descendantsAverage Q j F + descendantsAverage Q j G := by
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, (F R + G R) =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, F R +
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, G R
  rw [Finset.sum_add_distrib]
  ring

private theorem cubeLpNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : Cube d) (p : ℝ≥0∞) (f g : Vec d → E)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    cubeLpNorm Q p (fun x => f x + g x) ≤
      cubeLpNorm Q p f + cubeLpNorm Q p g := by
  have hsum :
      MeasureTheory.eLpNorm (fun x => f x + g x) p (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) +
          MeasureTheory.eLpNorm g p (normalizedCubeMeasure Q) := by
    simpa using! MeasureTheory.eLpNorm_add_le hf.1 hg.1 hp
  have hsum_top :
      MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) +
        MeasureTheory.eLpNorm g p (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ne_of_lt hf.2, ne_of_lt hg.2⟩
  have htoReal := ENNReal.toReal_mono hsum_top hsum
  rw [ENNReal.toReal_add (ne_of_lt hf.2) (ne_of_lt hg.2)] at htoReal
  simpa [cubeLpNorm, ne_of_lt hf.2, ne_of_lt hg.2] using htoReal

private theorem cubeLpNorm_two_le_cubeBesovOscillation_add_norm_cubeAverage {d : ℕ}
    (Q : Cube d) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      cubeBesovOscillation Q (2 : ℝ≥0∞) u + ‖cubeAverage Q u‖ := by
  have hfluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    have hconst_neg :
        MeasureTheory.MemLp (fun _ : Vec d => -cubeAverage Q u)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const _
    have hsum := hu.add hconst_neg
    have hfun : (fun x => u x + (fun _ : Vec d => -cubeAverage Q u) x) =
        cubeFluctuation Q u := by
      funext x
      simp [cubeFluctuation, sub_eq_add_neg]
    simpa [hfun] using! hsum
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const _
  have htri :=
    cubeLpNorm_add_le Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
      (fun _ : Vec d => cubeAverage Q u) hfluct hconst (by norm_num)
  have hfun : (fun x => cubeFluctuation Q u x + (fun _ : Vec d => cubeAverage Q u) x) =
      u := by
    funext x
    simp [cubeFluctuation]
  have hconst_norm :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => cubeAverage Q u) =
        ‖cubeAverage Q u‖ := by
    rw [cubeLpNorm_const Q (2 : ℝ≥0∞) (cubeAverage Q u) (by norm_num)]
  simpa [cubeBesovOscillation, hfun, hconst_norm] using htri

private theorem cubeBesovDepthSeminorm_two_depth_zero_eq {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u 0 =
      cubeBesovScaleWeight s Q * cubeBesovOscillation Q (2 : ℝ≥0∞) u := by
  unfold cubeBesovDepthSeminorm
  rw [cubeBesovDepthWeight_depth_zero, cubeBesovDepthAverage_depth_zero]
  have hosc : 0 ≤ cubeBesovOscillation Q (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) u
  have htwo : ((2 : ℝ≥0∞).toReal : ℝ) = 2 := by norm_num
  rw [htwo]
  congr 1
  simpa [Real.rpow_natCast] using sq_rpow_half_eq_of_nonneg hosc

private theorem positiveBesovPartialNormTwo_zero_eq {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) :
    positiveBesovPartialNormTwo Q s 0 u =
      cubeBesovScaleWeight s Q * cubeBesovOscillation Q (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖ := by
  unfold positiveBesovPartialNormTwo cubeBesovDisjointPartialNorm
    cubeBesovPartialNorm cubeBesovPartialSeminorm
  norm_num
  rw [cubeBesovDepthSeminorm_two_depth_zero_eq]
  have hnonneg :
      0 ≤ cubeBesovScaleWeight s Q * cubeBesovOscillation Q (2 : ℝ≥0∞) u := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
      (cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) u)
  rw [sq_rpow_half_eq_of_nonneg hnonneg]

private theorem cubeBesovScaleWeight_mul_cubeLpNorm_two_le_positiveBesovPartialNormTwo_zero
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      positiveBesovPartialNormTwo Q s 0 u := by
  have h := cubeLpNorm_two_le_cubeBesovOscillation_add_norm_cubeAverage Q u hu
  have hw : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have hmul := mul_le_mul_of_nonneg_left h hw
  rw [positiveBesovPartialNormTwo_zero_eq]
  nlinarith

private theorem cubeBesovScaleWeight_mul_cubeLpNorm_two_le_positiveBesovPartialNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      positiveBesovPartialNormTwo Q s N u := by
  exact (cubeBesovScaleWeight_mul_cubeLpNorm_two_le_positiveBesovPartialNormTwo_zero
    Q s u hu).trans (positiveBesovPartialNormTwo_zero_le Q s N u)

/-- In the legacy lane, the scaled descendant cube-average term is controlled
by the parent weighted `L²` norm. -/
theorem descendantsAverage_sq_scaled_positiveBesovMeanTerm_le_weighted_l2 {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
      (fun R =>
        (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) ≤
      (cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
  let w : ℝ := cubeBesovScaleWeight s Q
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2 =
        (w * ‖cubeAverage R u‖) ^ 2 := by
    intro R hR
    have hscale :=
      cubeBesovScaleWeight_eq_mul_rpow_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) s hR
    have hcancel :
        Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            Real.rpow (3 : ℝ) (s * (j : ℝ)) = 1 := by
      have hprod :=
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)
          (-(s * (j : ℝ))) (s * (j : ℝ))
      have hsum : -(s * (j : ℝ)) + s * (j : ℝ) = 0 := by ring
      rw [hsum] at hprod
      norm_num at hprod
      simpa using hprod.symm
    have hlinear :
        Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            ((w * Real.rpow (3 : ℝ) (s * (j : ℝ))) * ‖cubeAverage R u‖) =
          w * ‖cubeAverage R u‖ := by
      calc
        Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            ((w * Real.rpow (3 : ℝ) (s * (j : ℝ))) * ‖cubeAverage R u‖)
            = (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
                Real.rpow (3 : ℝ) (s * (j : ℝ))) * (w * ‖cubeAverage R u‖) := by
                ring
        _ = 1 * (w * ‖cubeAverage R u‖) := by rw [hcancel]
        _ = w * ‖cubeAverage R u‖ := by ring
    calc
      (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2
          = (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
              ((w * Real.rpow (3 : ℝ) (s * (j : ℝ))) * ‖cubeAverage R u‖)) ^ 2 := by
              simp [w, hscale]
      _ = (w * ‖cubeAverage R u‖) ^ 2 := by rw [hlinear]
  have havg_eq :
      descendantsAverage Q j
        (fun R =>
          (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) =
        descendantsAverage Q j (fun R => (w * ‖cubeAverage R u‖) ^ 2) := by
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2 =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, (w * ‖cubeAverage R u‖) ^ 2
    congr 1
    exact Finset.sum_congr rfl hpoint
  have hcirc :
      descendantsAverage Q j (fun R => ‖cubeAverage R u‖ ^ 2) ≤
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    have h := cubeBesovCircDepthAverage_le_cubeLpNorm_rpow
      Q (2 : ℝ≥0∞) u j (by norm_num) (by norm_num) hu
    have htwo : ((2 : ℝ≥0∞).toReal : ℝ) = 2 := by norm_num
    simpa [cubeBesovCircDepthAverage, htwo] using h
  have hweighted :
      descendantsAverage Q j (fun R => (w * ‖cubeAverage R u‖) ^ 2) ≤
        (w * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    have hrewrite :
        descendantsAverage Q j (fun R => (w * ‖cubeAverage R u‖) ^ 2) =
          w ^ 2 * descendantsAverage Q j (fun R => ‖cubeAverage R u‖ ^ 2) := by
      calc
        descendantsAverage Q j (fun R => (w * ‖cubeAverage R u‖) ^ 2)
            = descendantsAverage Q j (fun R => w ^ 2 * ‖cubeAverage R u‖ ^ 2) := by
                refine congrArg (descendantsAverage Q j) ?_
                funext R
                ring
        _ = w ^ 2 * descendantsAverage Q j (fun R => ‖cubeAverage R u‖ ^ 2) := by
                rw [descendantsAverage_mul_left]
    calc
      descendantsAverage Q j (fun R => (w * ‖cubeAverage R u‖) ^ 2)
          = w ^ 2 * descendantsAverage Q j (fun R => ‖cubeAverage R u‖ ^ 2) :=
            hrewrite
      _ ≤ w ^ 2 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hcirc (sq_nonneg w)
      _ = (w * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by ring
  exact havg_eq.trans_le hweighted

theorem descendantsAverage_sq_scaled_positiveBesovMeanTerm_le_positiveBesovPartialNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j M : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
      (fun R =>
        (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) ≤
      (positiveBesovPartialNormTwo Q s M u) ^ 2 := by
  have hmean := descendantsAverage_sq_scaled_positiveBesovMeanTerm_le_weighted_l2 Q s u j hu
  have hLp := cubeBesovScaleWeight_mul_cubeLpNorm_two_le_positiveBesovPartialNormTwo Q s u M hu
  have hleft_nonneg :
      0 ≤ cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) u :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
  have hright_nonneg : 0 ≤ positiveBesovPartialNormTwo Q s M u :=
    positiveBesovPartialNormTwo_nonneg Q s M u
  have hsquares :
      (cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 ≤
        (positiveBesovPartialNormTwo Q s M u) ^ 2 := by
    nlinarith
  exact hmean.trans hsquares

theorem descendantsAverage_sq_scaled_positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ) (hs : 0 ≤ s) :
    descendantsAverage Q j
      (fun R =>
        (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          positiveBesovPartialSeminormTwo R s N u) ^ 2) ≤
      (positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
  let c : ℝ := Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hexp_nonpos : -(s * (j : ℝ)) ≤ 0 := by
    have hprod : 0 ≤ s * (j : ℝ) := mul_nonneg hs (Nat.cast_nonneg j)
    linarith
  have hc_le_one : c ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) hexp_nonpos
  have hc_sq_le_one : c ^ 2 ≤ 1 := by nlinarith
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (c * positiveBesovPartialSeminormTwo R s N u) ^ 2 ≤
        (positiveBesovPartialSeminormTwo R s N u) ^ 2 := by
    intro R hR
    calc
      (c * positiveBesovPartialSeminormTwo R s N u) ^ 2
          = c ^ 2 * (positiveBesovPartialSeminormTwo R s N u) ^ 2 := by ring
      _ ≤ 1 * (positiveBesovPartialSeminormTwo R s N u) ^ 2 := by
          exact mul_le_mul_of_nonneg_right hc_sq_le_one (sq_nonneg _)
      _ = (positiveBesovPartialSeminormTwo R s N u) ^ 2 := by ring
  have hscaled :
      descendantsAverage Q j
        (fun R => (c * positiveBesovPartialSeminormTwo R s N u) ^ 2) ≤
      descendantsAverage Q j
        (fun R => (positiveBesovPartialSeminormTwo R s N u) ^ 2) :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have hsemi :=
    descendantsAverage_sq_positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
      Q s u j N
  exact hscaled.trans hsemi

/-- Legacy scaled finite positive `q = 2` Besov norms localize over descendants. -/
theorem descendantsAverage_sq_scaled_positiveBesovPartialNormTwo_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j N : ℕ)
    (hs : 0 ≤ s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
      (fun R =>
        (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
          positiveBesovPartialNormTwo R s N u) ^ 2) ≤
      (2 * positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
  let c : ℝ := Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
  let B : ℝ := positiveBesovPartialNormTwo Q s (j + N) u
  have hsemi :=
    descendantsAverage_sq_scaled_positiveBesovPartialSeminormTwo_le_positiveBesovPartialNormTwo
      Q s u j N hs
  have hmean :=
    descendantsAverage_sq_scaled_positiveBesovMeanTerm_le_positiveBesovPartialNormTwo
      Q s u j (j + N) hu
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (c * positiveBesovPartialNormTwo R s N u) ^ 2 ≤
        2 * (c * positiveBesovPartialSeminormTwo R s N u) ^ 2 +
          2 * (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2 := by
    intro R hR
    have hnorm :
        positiveBesovPartialNormTwo R s N u =
          positiveBesovPartialSeminormTwo R s N u +
            cubeBesovScaleWeight s R * ‖cubeAverage R u‖ := by
      rfl
    rw [hnorm]
    nlinarith [sq_nonneg (c * positiveBesovPartialSeminormTwo R s N u -
      c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖))]
  have hsplit :
      descendantsAverage Q j (fun R => (c * positiveBesovPartialNormTwo R s N u) ^ 2) ≤
        descendantsAverage Q j
          (fun R =>
            2 * (c * positiveBesovPartialSeminormTwo R s N u) ^ 2 +
              2 * (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have hcombine :
      descendantsAverage Q j
          (fun R =>
            2 * (c * positiveBesovPartialSeminormTwo R s N u) ^ 2 +
              2 * (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) =
        2 * descendantsAverage Q j
          (fun R => (c * positiveBesovPartialSeminormTwo R s N u) ^ 2) +
        2 * descendantsAverage Q j
          (fun R => (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) := by
    rw [descendantsAverage_add]
    rw [descendantsAverage_mul_left, descendantsAverage_mul_left]
  calc
    descendantsAverage Q j (fun R => (c * positiveBesovPartialNormTwo R s N u) ^ 2)
        ≤ descendantsAverage Q j
          (fun R =>
            2 * (c * positiveBesovPartialSeminormTwo R s N u) ^ 2 +
              2 * (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) := hsplit
    _ = 2 * descendantsAverage Q j
          (fun R => (c * positiveBesovPartialSeminormTwo R s N u) ^ 2) +
        2 * descendantsAverage Q j
          (fun R => (c * (cubeBesovScaleWeight s R * ‖cubeAverage R u‖)) ^ 2) := hcombine
    _ ≤ 2 * B ^ 2 + 2 * B ^ 2 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (by simpa [c, B] using hsemi) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (by simpa [c, B] using hmean) (by norm_num)
    _ = (2 * positiveBesovPartialNormTwo Q s (j + N) u) ^ 2 := by
          simp [B]
          ring

theorem positiveBesovPartialNormTwo_le_normTwo_of_bddAbove {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u)) (N : ℕ) :
    positiveBesovPartialNormTwo Q s N u ≤ positiveBesovNormTwo Q s u := by
  cases N with
  | zero =>
      have h01 := positiveBesovPartialNormTwo_le_succ Q s u 0
      have h1 : positiveBesovPartialNormTwo Q s 1 u ≤ positiveBesovNormTwo Q s u := by
        change positiveBesovPartialNormTwo Q s 1 u ≤
          sSup (Set.range fun N : ℕ => positiveBesovPartialNormTwo Q s (N + 1) u)
        exact le_csSup hBdd ⟨0, rfl⟩
      exact h01.trans h1
  | succ N =>
      change positiveBesovPartialNormTwo Q s (N + 1) u ≤
        sSup (Set.range fun N : ℕ => positiveBesovPartialNormTwo Q s (N + 1) u)
      exact le_csSup hBdd ⟨N, rfl⟩

theorem positiveBesovNormTwo_nonneg_of_bddAbove {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u)) :
    0 ≤ positiveBesovNormTwo Q s u := by
  exact (positiveBesovPartialNormTwo_nonneg Q s 1 u).trans
    (positiveBesovPartialNormTwo_le_normTwo_of_bddAbove Q s u hBdd 1)

theorem tendsto_positiveBesovPartialNormTwo_succ_atTop {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u)) :
    Filter.Tendsto
      (fun N : ℕ => positiveBesovPartialNormTwo Q s (N + 1) u)
      Filter.atTop
      (nhds (positiveBesovNormTwo Q s u)) := by
  change Filter.Tendsto
    (fun N : ℕ => positiveBesovPartialNormTwo Q s (N + 1) u)
    Filter.atTop
    (nhds (sSup (Set.range fun N : ℕ =>
      positiveBesovPartialNormTwo Q s (N + 1) u)))
  exact
    tendsto_atTop_ciSup
      (monotone_nat_of_le_succ
        (fun N => positiveBesovPartialNormTwo_le_succ Q s u (N + 1)))
      hBdd

theorem tendsto_descendantsAverage_sq_scaled_positiveBesovPartialNormTwo_succ_atTop
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ) (c : ℝ)
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s (N + 1) u)) :
    Filter.Tendsto
      (fun N : ℕ =>
        descendantsAverage Q j
          (fun R => (c * positiveBesovPartialNormTwo R s (N + 1) u) ^ 2))
      Filter.atTop
      (nhds
        (descendantsAverage Q j
          (fun R => (c * positiveBesovNormTwo R s u) ^ 2))) := by
  unfold descendantsAverage
  exact
    Filter.Tendsto.const_mul ((descendantsAtDepth Q j).card : ℝ)⁻¹
      (tendsto_finsetSum (descendantsAtDepth Q j)
        (fun R hR =>
          ((tendsto_positiveBesovPartialNormTwo_succ_atTop
            R s u (hLocalBdd R hR)).const_mul c).pow 2))

/-- In the legacy real-`sSup` lane, infinite-depth scaled positive `q = 2`
Besov norms localize over descendants, provided the parent and local `sSup`s
are bounded above. -/
theorem descendantsAverage_sq_scaled_positiveBesovNormTwo_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ)
    (hs : 0 ≤ s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s (N + 1) u)) :
    descendantsAverage Q j
        (fun R =>
          (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            positiveBesovNormTwo R s u) ^ 2) ≤
      (2 * positiveBesovNormTwo Q s u) ^ 2 := by
  let c : ℝ := Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
  have hparent_nonneg : 0 ≤ positiveBesovNormTwo Q s u :=
    positiveBesovNormTwo_nonneg_of_bddAbove Q s u hParentBdd
  have hbound :
      ∀ N : ℕ,
        descendantsAverage Q j
            (fun R => (c * positiveBesovPartialNormTwo R s (N + 1) u) ^ 2) ≤
          (2 * positiveBesovNormTwo Q s u) ^ 2 := by
    intro N
    have hfinite := descendantsAverage_sq_scaled_positiveBesovPartialNormTwo_le
      Q s u j (N + 1) hs hu
    have hfinite' :
        descendantsAverage Q j
            (fun R => (c * positiveBesovPartialNormTwo R s (N + 1) u) ^ 2) ≤
          (2 * positiveBesovPartialNormTwo Q s (j + (N + 1)) u) ^ 2 := by
      simpa [c] using hfinite
    have hpartial_le :
        positiveBesovPartialNormTwo Q s (j + (N + 1)) u ≤
          positiveBesovNormTwo Q s u :=
      positiveBesovPartialNormTwo_le_normTwo_of_bddAbove
        Q s u hParentBdd (j + (N + 1))
    have hpartial_nonneg :
        0 ≤ positiveBesovPartialNormTwo Q s (j + (N + 1)) u :=
      positiveBesovPartialNormTwo_nonneg Q s (j + (N + 1)) u
    have hsquares :
        (2 * positiveBesovPartialNormTwo Q s (j + (N + 1)) u) ^ 2 ≤
          (2 * positiveBesovNormTwo Q s u) ^ 2 := by
      nlinarith
    exact hfinite'.trans hsquares
  have hlim :=
    tendsto_descendantsAverage_sq_scaled_positiveBesovPartialNormTwo_succ_atTop
      Q s u j c hLocalBdd
  exact le_of_tendsto' hlim hbound

/-- A scalar `L²` function on a cube is in `L²` for the normalized cube measure. -/
theorem memLp_normalizedCubeMeasure_of_memScalarL2_cubeSet {d : ℕ}
    (Q : Cube d) {u : Vec d → ℝ} (hu : MemScalarL2 (cubeSet Q) u) :
    MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have huCube :
      MeasureTheory.MemLp u (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemScalarL2, volumeMeasureOn] using hu
  exact
    huCube.of_measure_le_smul (c := ENNReal.ofReal ((cubeVolume Q)⁻¹))
      ENNReal.ofReal_ne_top (by rw [normalizedCubeMeasure, cubeMeasure])

/-- Cube-general form of the legacy positive Besov localization lemma. -/
theorem positiveBesovLocalize_cube {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hu : MemScalarL2 (cubeSet Q) u)
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s (N + 1) u)) :
    Real.sqrt
        (descendantsAverage Q j fun R =>
          (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            positiveBesovNormTwo R s u) ^ 2) ≤
      positiveBesovLocalizeConstant d * positiveBesovNormTwo Q s u := by
  have huNorm := memLp_normalizedCubeMeasure_of_memScalarL2_cubeSet Q hu
  have hsq := descendantsAverage_sq_scaled_positiveBesovNormTwo_le
    Q s u j hs.le huNorm hParentBdd hLocalBdd
  have hnorm_nonneg : 0 ≤ positiveBesovNormTwo Q s u :=
    positiveBesovNormTwo_nonneg_of_bddAbove Q s u hParentBdd
  have hrhs_nonneg : 0 ≤ 2 * positiveBesovNormTwo Q s u := by
    nlinarith
  calc
    Real.sqrt
        (descendantsAverage Q j fun R =>
          (Real.rpow (3 : ℝ) (-(s * (j : ℝ))) *
            positiveBesovNormTwo R s u) ^ 2)
        ≤ Real.sqrt ((2 * positiveBesovNormTwo Q s u) ^ 2) :=
          Real.sqrt_le_sqrt hsq
    _ = |2 * positiveBesovNormTwo Q s u| := by
          rw [Real.sqrt_sq_eq_abs]
    _ = positiveBesovLocalizeConstant d * positiveBesovNormTwo Q s u := by
          rw [abs_of_nonneg hrhs_nonneg]

/-- Legacy compatibility form associated with manuscript Lemma
`l.Besov.positive.localize.function.spaces`.  The normalized legacy positive
Besov norm of `u` on the origin cube `⌈_m` controls the geometrically
weighted root-mean-square of normalized legacy positive Besov norms on each
triadic descendant `z + ⌈_n` for `n ≤ m`. -/
theorem positiveBesovLocalize {d : ℕ} {s : ℝ} {m n : ℤ}
    (_hd : 1 ≤ d) (hs_pos : 0 < s) (_hs_lt_one : s < 1)
    (hnm : n ≤ m) (u : Vec d → ℝ)
    (hu : MemScalarL2 (cubeSet (originCube d m)) u)
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo (originCube d m) s N u))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s N u)) :
    Real.sqrt
        (descendantsAverage (originCube d m) (Int.toNat (m - n)) fun R =>
          (Real.rpow (3 : ℝ) (s * ((n - m : ℤ) : ℝ)) *
            positiveBesovNormTwo R s u) ^ 2) ≤
      positiveBesovLocalizeConstant d *
        positiveBesovNormTwo (originCube d m) s u := by
  have hdepth_nonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
  have hdepth_cast : ((Int.toNat (m - n) : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hdepth_nonneg)
  have hfactor :
      Real.rpow (3 : ℝ) (-(s * ((Int.toNat (m - n) : ℕ) : ℝ))) =
        Real.rpow (3 : ℝ) (s * ((n - m : ℤ) : ℝ)) := by
    congr 1
    rw [hdepth_cast]
    norm_num
    ring
  have hParentBdd_succ :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo (originCube d m) s (N + 1) u) := by
    rcases hParentBdd with ⟨B, hB⟩
    exact ⟨B, by rintro x ⟨N, rfl⟩; exact hB ⟨N + 1, rfl⟩⟩
  have hLocalBdd_succ :
      ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s (N + 1) u) := by
    intro R hR
    rcases hLocalBdd R hR with ⟨B, hB⟩
    exact ⟨B, by rintro x ⟨N, rfl⟩; exact hB ⟨N + 1, rfl⟩⟩
  rw [← hfactor]
  exact positiveBesovLocalize_cube (Q := originCube d m) (s := s) (u := u)
    (j := Int.toNat (m - n)) hs_pos hu hParentBdd_succ hLocalBdd_succ

end Legacy

end

end Ch01
end Book
end Homogenization
