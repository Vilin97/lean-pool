/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Descendants

/-! # Bounds -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

theorem cubeBesovDepthWeight_mul_cubeBesovCircDepthSeminorm_shift_eq_geom_mul {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j n : ℕ) :
    cubeBesovDepthWeight Q s j * cubeBesovCircDepthSeminorm Q 1 p u (j + n) =
      ((3 : ℝ) ^ (-s)) ^ n * cubeBesovCircDepthSeminorm Q (1 - s) p u (j + n) := by
  have hQ : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hbase_pos : 0 < cubeScaleFactor Q / (3 : ℝ) ^ (j + n) := by
    exact div_pos hQ (by positivity)
  set A : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ (j + n)
  have hA_pos : 0 < A := hbase_pos
  have hsplit :
      cubeScaleFactor Q / (3 : ℝ) ^ j = A * (3 : ℝ) ^ n := by
    dsimp [A]
    rw [pow_add]
    field_simp
  have hgeom :
      ((3 : ℝ) ^ n) ^ (-s) = ((3 : ℝ) ^ (-s)) ^ n := by
    have hthree_nat : (3 : ℝ) ^ n = (3 : ℝ) ^ (n : ℝ) := by
      symm
      rw [Real.rpow_natCast]
    calc
      ((3 : ℝ) ^ n) ^ (-s)
          = ((3 : ℝ) ^ (n : ℝ)) ^ (-s) := by rw [hthree_nat]
      _ = (3 : ℝ) ^ ((n : ℝ) * (-s)) := by
            rw [Real.rpow_mul (by positivity)]
      _ = (3 : ℝ) ^ ((-s) * n) := by rw [mul_comm]
      _ = ((3 : ℝ) ^ (-s)) ^ (n : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]
      _ = ((3 : ℝ) ^ (-s)) ^ n := by
            rw [Real.rpow_natCast]
  unfold cubeBesovCircDepthSeminorm
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  calc
    cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q 1 (j + n)
        = (A * (3 : ℝ) ^ n) ^ (-s) * A := by
              simp [cubeBesovDepthWeight, cubeBesovCircDepthWeight, hsplit, A]
    _ = (A ^ (-s) * ((3 : ℝ) ^ n) ^ (-s)) * A := by
            rw [Real.mul_rpow (le_of_lt hA_pos) (by positivity)]
    _ = ((3 : ℝ) ^ n) ^ (-s) * (A ^ (-s) * A) := by
            ring
    _ = ((3 : ℝ) ^ n) ^ (-s) * A ^ (1 - s) := by
            congr 1
            calc
              A ^ (-s) * A = A ^ (-s) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = A ^ ((-s) + 1) := by
                    rw [← Real.rpow_add hA_pos]
              _ = A ^ (1 - s) := by
                    congr 1
                    ring
    _ = ((3 : ℝ) ^ (-s)) ^ n * cubeBesovCircDepthWeight Q (1 - s) (j + n) := by
          rw [hgeom]
          simp [cubeBesovCircDepthWeight, A]

theorem cubeBesovDepthSeminorm_two_le_weighted_shifted_of_local_circ_bound {d : ℕ}
    (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (j N : ℕ)
    (hC : 0 ≤ C)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * ∑ n ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (-s)) ^ n * cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) g (j + n) := by
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        ≤ C * cubeBesovDepthWeight Q s j *
            ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
              exact cubeBesovDepthSeminorm_two_le_sum_shifted_of_local_circ_bound
                Q s C u g j N hC hlocal
    _ = C * ∑ n ∈ Finset.range (N + 1),
          cubeBesovDepthWeight Q s j *
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
          rw [mul_assoc, Finset.mul_sum]
    _ = C * ∑ n ∈ Finset.range (N + 1),
          ((3 : ℝ) ^ (-s)) ^ n * cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) g (j + n) := by
          refine congrArg (fun t : ℝ => C * t) ?_
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [cubeBesovDepthWeight_mul_cubeBesovCircDepthSeminorm_shift_eq_geom_mul]

theorem cubeBesovDepthWeight_mul_sum_shifted_cubeBesovCircDepthSeminorm_one_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (g : Vec d → ℝ) (j N : ℕ)
    (hs : 0 ≤ s) :
    cubeBesovDepthWeight Q s j *
      ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 p g (j + n) ≤
      ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q (1 - s) p g (j + n) := by
  have hr_nonneg : 0 ≤ (3 : ℝ) ^ (-s) := by
    exact Real.rpow_nonneg (by positivity) _
  have hr_le_one : (3 : ℝ) ^ (-s) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  calc
    cubeBesovDepthWeight Q s j *
        ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 p g (j + n)
        = ∑ n ∈ Finset.range (N + 1),
            ((3 : ℝ) ^ (-s)) ^ n * cubeBesovCircDepthSeminorm Q (1 - s) p g (j + n) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [cubeBesovDepthWeight_mul_cubeBesovCircDepthSeminorm_shift_eq_geom_mul]
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          1 * cubeBesovCircDepthSeminorm Q (1 - s) p g (j + n) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hpow_le : ((3 : ℝ) ^ (-s)) ^ n ≤ 1 := pow_le_one₀ hr_nonneg hr_le_one
          exact mul_le_mul_of_nonneg_right hpow_le
            (cubeBesovCircDepthSeminorm_nonneg Q (1 - s) p g (j + n))
    _ = ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q (1 - s) p g (j + n) := by
          simp

theorem cubeBesovDepthSeminorm_two_le_geometric_mul_cubeBesovCircPartialNorm_of_local_circ_bound
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (j N : ℕ)
    (hs : 0 < s) (hC : 0 ≤ C)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g := by
  let r : ℝ := (3 : ℝ) ^ (-s)
  let a : ℕ → ℝ := fun n => cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) g (j + n)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_r :
      ∑ n ∈ Finset.range (N + 1), r ^ n ≤ (1 - r)⁻¹ := by
    exact geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one
  have ha_nonneg : ∀ n ∈ Finset.range (N + 1), 0 ≤ a n := by
    intro n hn
    exact cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞) g (j + n)
  have hweighted :
      ∑ n ∈ Finset.range (N + 1), r ^ n * a n ≤
        (∑ n ∈ Finset.range (N + 1), r ^ n) * (∑ n ∈ Finset.range (N + 1), a n) := by
    exact sum_mul_le_mul_sum_of_nonneg
      (s := Finset.range (N + 1))
      (f := fun n => r ^ n)
      (g := a)
      (fun n hn => pow_nonneg hr_nonneg n)
      ha_nonneg
  have ha_sum_nonneg : 0 ≤ ∑ n ∈ Finset.range (N + 1), a n := by
    exact Finset.sum_nonneg ha_nonneg
  have hinv_nonneg : 0 ≤ (1 - r)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hshift :
      ∑ n ∈ Finset.range (N + 1), a n ≤
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g := by
    exact shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
      Q (1 - s) (2 : ℝ≥0∞) j N g
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        ≤ C * ∑ n ∈ Finset.range (N + 1), r ^ n * a n := by
            simpa [r, a] using
              cubeBesovDepthSeminorm_two_le_weighted_shifted_of_local_circ_bound
                Q s C u g j N hC hlocal
    _ ≤ C * ((∑ n ∈ Finset.range (N + 1), r ^ n) * (∑ n ∈ Finset.range (N + 1), a n)) := by
          exact mul_le_mul_of_nonneg_left hweighted hC
    _ ≤ C * ((1 - r)⁻¹ * (∑ n ∈ Finset.range (N + 1), a n)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsum_r ha_sum_nonneg) hC
    _ ≤ C * ((1 - r)⁻¹ *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hshift hinv_nonneg) hC
    _ = C * (1 - r)⁻¹ *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g := by
          ring

theorem cubeBesovDepthSeminorm_two_le_cubeBesovCircPartialNorm_of_local_circ_bound
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (j N : ℕ)
    (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g := by
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        ≤ C * cubeBesovDepthWeight Q s j *
            ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
              exact cubeBesovDepthSeminorm_two_le_sum_shifted_of_local_circ_bound
                Q s C u g j N hC hlocal
    _ ≤ C * ∑ n ∈ Finset.range (N + 1),
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) g (j + n) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left
              (cubeBesovDepthWeight_mul_sum_shifted_cubeBesovCircDepthSeminorm_one_le
                Q s (2 : ℝ≥0∞) g j N hs) hC)
    _ ≤ C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (j + N) g := by
          exact mul_le_mul_of_nonneg_left
            (shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
              Q (1 - s) (2 : ℝ≥0∞) j N g) hC

theorem cubeBesovPartialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm_of_local_circ_bound
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (M : ℕ)
    (hs : 0 < s) (hC : 0 ≤ C)
    (hlocal : ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (M - j + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
        C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (M + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ?_
  intro j hj
  have hj_le : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdepth :=
    cubeBesovDepthSeminorm_two_le_geometric_mul_cubeBesovCircPartialNorm_of_local_circ_bound
      Q s C u g j (M - j) hs hC (hlocal j hj)
  simpa [Nat.add_sub_of_le hj_le] using hdepth

theorem cubeBesovPartialSeminormTop_two_le_cubeBesovCircPartialNorm_of_local_circ_bound
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (M : ℕ)
    (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hlocal : ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (M - j + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (M + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ?_
  intro j hj
  have hj_le : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdepth :=
    cubeBesovDepthSeminorm_two_le_cubeBesovCircPartialNorm_of_local_circ_bound
      Q s C u g j (M - j) hs hC (hlocal j hj)
  simpa [Nat.add_sub_of_le hj_le] using hdepth

theorem cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (havg : cubeAverage Q u = 0) :
    cubeBesovPartialNormTop Q s p N u = cubeBesovPartialSeminormTop Q s p N u := by
  unfold cubeBesovPartialNormTop
  simp [havg]

theorem CubeMultiscalePoincareInput.partialSeminormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M)
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact cubeBesovPartialSeminormTop_two_le_cubeBesovCircPartialNorm_of_local_circ_bound
    Q s C u g M hs hC hinput

theorem CubeMultiscalePoincareInput.partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact
    cubeBesovPartialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm_of_local_circ_bound
      Q s C u g M hs hC hinput

theorem CubeMultiscalePoincareInput.partialNormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M)
    (havg : cubeAverage Q u = 0) (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (N := M) (u := u) havg]
  exact hinput.partialSeminormTop_two_le_cubeBesovCircPartialNorm hs hC

theorem CubeMultiscalePoincareInput.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M)
    (havg : cubeAverage Q u = 0) (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (N := M) (u := u) havg]
  exact hinput.partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm hs hC

theorem CubeLocalMultiscalePoincareEstimate.partialSeminormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C u g M)
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.to_input.partialSeminormTop_two_le_cubeBesovCircPartialNorm hs hC

theorem CubeLocalMultiscalePoincareEstimate.partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C u g M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.to_input.partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm hs hC

theorem CubeLocalMultiscalePoincareEstimate.partialNormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C u g M)
    (havg : cubeAverage Q u = 0) (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.to_input.partialNormTop_two_le_cubeBesovCircPartialNorm havg hs hC

theorem CubeLocalMultiscalePoincareEstimate.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C u g M)
    (havg : cubeAverage Q u = 0) (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.to_input.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm havg hs hC

theorem CubeLocalMultiscalePoincareEstimate.fluctuation_partialNormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      C * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.partialNormTop_two_le_cubeBesovCircPartialNorm
    (havg := cubeAverage_cubeFluctuation Q u) hs hC

theorem CubeLocalMultiscalePoincareEstimate.fluctuation_partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hlocal.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    (havg := cubeAverage_cubeFluctuation Q u) hs hC

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.partialSeminormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact (hproj.to_input hg hC).partialSeminormTop_two_le_cubeBesovCircPartialNorm hs (by positivity)

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact (hproj.to_input hg hC).partialSeminormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    hs (by positivity)

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.partialNormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q u = 0) (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact (hproj.to_input hg hC).partialNormTop_two_le_cubeBesovCircPartialNorm
    havg hs (by positivity)

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q u = 0) (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact (hproj.to_input hg hC).partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    havg hs (by positivity)

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.fluctuation_partialNormTop_two_le_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hproj.partialNormTop_two_le_cubeBesovCircPartialNorm
    hg (havg := cubeAverage_cubeFluctuation Q u) hs hC

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.fluctuation_partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hproj.partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm
    hg (havg := cubeAverage_cubeFluctuation Q u) hs hC

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.fluctuation_partialNormTop_two_le_note_constant_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 ≤ s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hproj.fluctuation_partialNormTop_two_le_cubeBesovCircPartialNorm hg hs hC

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.fluctuation_partialNormTop_two_le_note_rhs
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  exact hproj.fluctuation_partialNormTop_two_le_geometric_mul_cubeBesovCircPartialNorm hg hs hC


end Homogenization
