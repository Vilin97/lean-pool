/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.FullCirc

/-! # Local Multiscale -/

namespace Homogenization

open scoped BigOperators ENNReal

variable {d : ℕ}

/-! # Local Multiscale Vector Poincare Estimates -/

/-- Depthwise vector version of the multiscale Poincare-to-Besov bookkeeping.

The local input controls oscillation by a sum of componentwise local circ
partial norms; after averaging over descendants, the component and depth sums
shift to the parent cube. -/
theorem cubeBesovDepthSeminorm_two_le_weighted_shifted_sum_components_of_vector_local_circ_bound_poincare
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (j N : ℕ) (hC : 0 ≤ C)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ i : Fin d,
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => G x i)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := by
  classical
  let I : Finset (Fin d × ℕ) :=
    (Finset.univ : Finset (Fin d)).product (Finset.range (N + 1))
  let S : TriadicCube d → ℝ := fun R =>
    ∑ p ∈ I,
      cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2
  have hlocalS : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤ C * S R := by
    intro R hR
    calc
      cubeBesovOscillation R (2 : ℝ≥0∞) u
          ≤ C * ∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
                (fun x => G x i) := hlocal R hR
      _ = C * S R := by
            congr 1
            simp [S, I, cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm,
              Finset.sum_product]
  have hS_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ S R := by
    intro R hR
    exact Finset.sum_nonneg fun p hp =>
      cubeBesovCircDepthSeminorm_nonneg R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2
  have hsq_bound :
      descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2) ≤
        descendantsAverage Q j (fun R => (C * S R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hosc_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
    have hCS_nonneg : 0 ≤ C * S R := mul_nonneg hC (hS_nonneg R hR)
    nlinarith [hlocalS R hR, hosc_nonneg, hCS_nonneg]
  have hleft_nonneg :
      0 ≤ descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot_bound :
      (descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^
          (1 / 2 : ℝ) ≤
        (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hleft_nonneg hsq_bound (by positivity)
  have hfactor :
      descendantsAverage Q j (fun R => (C * S R) ^ 2) =
        C ^ 2 * descendantsAverage Q j (fun R => (S R) ^ 2) := by
    calc
      descendantsAverage Q j (fun R => (C * S R) ^ 2)
          = descendantsAverage Q j (fun R => C ^ 2 * (S R) ^ 2) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              ring
      _ = C ^ 2 * descendantsAverage Q j (fun R => (S R) ^ 2) := by
            rw [descendantsAverage_mul_left Q j (C ^ 2) (fun R => (S R) ^ 2)]
  have hSsq_nonneg : 0 ≤ descendantsAverage Q j (fun R => (S R) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot_factor :
      (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) =
        C * (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [hfactor, Real.mul_rpow (sq_nonneg C) hSsq_nonneg]
    congr 1
    rw [sq_rpow_half_eq_of_nonneg hC]
  have hM :
      (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) ≤
        ∑ p ∈ I,
          (descendantsAverage Q j
            (fun R =>
              (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
                (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact descendantsAverage_L2_sum_le_sum_descendantsAverage_L2 Q j I
      (fun R p =>
        cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2)
      (fun R hR p hp =>
        cubeBesovCircDepthSeminorm_nonneg R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2)
  have hshift :
      ∀ p ∈ I,
        (descendantsAverage Q j
          (fun R =>
            (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
              (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ) =
          cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
    intro p hp
    have hnonneg :
        0 ≤ cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => G x p.1) (j + p.2) :=
      cubeBesovCircDepthSeminorm_nonneg Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2)
    rw [descendantsAverage_sq_cubeBesovCircDepthSeminorm_eq_shifted]
    exact sq_rpow_half_eq_of_nonneg hnonneg
  have hsum_reindex :
      ∑ p ∈ I,
        (descendantsAverage Q j
          (fun R =>
            (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
              (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ)
        =
      ∑ p ∈ I,
        cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact hshift p hp
  have hweighted :
      ∑ p ∈ I,
        cubeBesovDepthWeight Q s j *
          cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2)
        =
      ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := by
    simp [I, Finset.sum_product,
      cubeBesovDepthWeight_mul_cubeBesovCircDepthSeminorm_shift_eq_geom_mul]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  have hCweight_nonneg : 0 ≤ C * cubeBesovDepthWeight Q s j :=
    mul_nonneg hC hweight_nonneg
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        = cubeBesovDepthWeight Q s j *
            (descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^
              (1 / 2 : ℝ) := by
              simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage]
    _ ≤ cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hroot_bound hweight_nonneg
    _ = cubeBesovDepthWeight Q s j *
          (C * (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ)) := by
            rw [hroot_factor]
    _ = C * cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) := by
            ring
    _ ≤ C * cubeBesovDepthWeight Q s j *
          (∑ p ∈ I,
            (descendantsAverage Q j
              (fun R =>
                (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
                  (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hM hCweight_nonneg
    _ = C * cubeBesovDepthWeight Q s j *
          ∑ p ∈ I,
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
            rw [hsum_reindex]
    _ = C * ∑ p ∈ I,
          cubeBesovDepthWeight Q s j *
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
            rw [mul_assoc, Finset.mul_sum]
    _ = C * ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := by
            rw [hweighted]

/-- Finite-depth `q = ∞` vector local-multiscale Poincare-to-Besov bound. -/
theorem CubeLocalMultiscalePoincareVectorEstimate.partialSeminormTop_two_le_geometric_mul_sum
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareVectorEstimate Q C u G M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        ∑ i : Fin d,
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
            (fun x => G x i) := by
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (M + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ?_
  intro j hj
  have hj_le : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdepth :
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
        C * ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1),
          ((3 : ℝ) ^ (-s)) ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n) := by
    exact
      cubeBesovDepthSeminorm_two_le_weighted_shifted_sum_components_of_vector_local_circ_bound_poincare
        Q s C u G j (M - j) hC (by
          intro R hR
          exact hlocal j hj R hR)
  let r : ℝ := (3 : ℝ) ^ (-s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_r :
      ∑ n ∈ Finset.range (M - j + 1), r ^ n ≤ (1 - r)⁻¹ := by
    exact geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one
  have hcomponent :
      ∀ i : Fin d,
        ∑ n ∈ Finset.range (M - j + 1),
          r ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n) ≤
        (1 - r)⁻¹ *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
            (fun x => G x i) := by
    intro i
    have hsum_shift :
        ∑ n ∈ Finset.range (M - j + 1),
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) ≤
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
          (fun x => G x i) := by
      simpa [Nat.add_sub_of_le hj_le] using
        shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
          Q (1 - s) (2 : ℝ≥0∞) j (M - j) (fun x => G x i)
    have hweighted :
        ∑ n ∈ Finset.range (M - j + 1),
          r ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n) ≤
        (∑ n ∈ Finset.range (M - j + 1), r ^ n) *
          (∑ n ∈ Finset.range (M - j + 1),
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n)) := by
      exact sum_mul_le_mul_sum_of_nonneg
        (s := Finset.range (M - j + 1))
        (f := fun n => r ^ n)
        (g := fun n =>
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n))
        (fun n hn => pow_nonneg hr_nonneg n)
        (fun n hn =>
          cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n))
    calc
      ∑ n ∈ Finset.range (M - j + 1),
          r ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n)
          ≤ (∑ n ∈ Finset.range (M - j + 1), r ^ n) *
              (∑ n ∈ Finset.range (M - j + 1),
                cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
                  (fun x => G x i) (j + n)) := hweighted
      _ ≤ (1 - r)⁻¹ *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x i) := by
            exact mul_le_mul hsum_r hsum_shift
              (Finset.sum_nonneg fun n hn =>
                cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞)
                  (fun x => G x i) (j + n))
              (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
  have hsum_components :
      ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1),
          r ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n) ≤
        ∑ i : Fin d,
          (1 - r)⁻¹ *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hcomponent i
  have hinv_sum :
      ∑ i : Fin d,
          (1 - r)⁻¹ *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x i)
        =
      (1 - r)⁻¹ *
        ∑ i : Fin d,
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
            (fun x => G x i) := by
    rw [Finset.mul_sum]
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        ≤ C * ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1),
            r ^ n *
              cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
                (fun x => G x i) (j + n) := by
          simpa [r] using hdepth
    _ ≤ C * ((1 - r)⁻¹ *
          ∑ i : Fin d,
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x i)) := by
          exact mul_le_mul_of_nonneg_left
            (le_trans hsum_components (le_of_eq hinv_sum)) hC
    _ = C * (1 - r)⁻¹ *
          ∑ i : Fin d,
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x i) := by
          ring

/-- Finite-depth fluctuation form of the vector local-multiscale
Poincare-to-Besov bound. -/
theorem CubeLocalMultiscalePoincareVectorEstimate.fluctuation_partialNormTop_two_le_geometric_mul_sum
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareVectorEstimate Q C (cubeFluctuation Q u) G M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        ∑ i : Fin d,
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
            (fun x => G x i) := by
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (N := M)
    (u := cubeFluctuation Q u) (cubeAverage_cubeFluctuation Q u)]
  exact hlocal.partialSeminormTop_two_le_geometric_mul_sum hs hC

end Homogenization
