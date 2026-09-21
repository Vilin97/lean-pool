/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions

/-! # Bounds -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeBesovScaleWeight_neg_mul_cubeBesovDepthWeight_eq_rpow_three_weight {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovScaleWeight (-s) Q * cubeBesovDepthWeight Q s j =
      Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
  have hQ : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow : 0 < (3 : ℝ) ^ j := by positivity
  calc
    cubeBesovScaleWeight (-s) Q * cubeBesovDepthWeight Q s j
        = (cubeScaleFactor Q) ^ s * ((cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹) ^ s := by
            simp [cubeBesovScaleWeight, cubeBesovDepthWeight, Real.rpow_neg_eq_inv_rpow]
    _ = (cubeScaleFactor Q) ^ s * (((3 : ℝ) ^ j / cubeScaleFactor Q) ^ s) := by
          congr 1
          field_simp [hQ.ne', hpow.ne']
    _ = (cubeScaleFactor Q * ((3 : ℝ) ^ j / cubeScaleFactor Q)) ^ s := by
          symm
          exact Real.mul_rpow hQ.le (div_nonneg (by positivity) hQ.le)
    _ = ((3 : ℝ) ^ j) ^ s := by
          congr 1
          field_simp [hQ.ne']
    _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
          simpa [mul_comm] using
            (Real.rpow_natCast_mul (by positivity : 0 ≤ (3 : ℝ)) j s).symm

theorem cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveScalarDepthSeminorm Q s v j =
      cubeBesovScaleWeight (-s) Q * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
  have havg :
      cubeBesovPositiveScalarDepthAverage Q v j =
        cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j := by
    simp [cubeBesovPositiveScalarDepthAverage, cubeBesovDepthAverage]
  have havg_nonneg :
      0 ≤ cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j :=
    cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞) v j
  calc
    cubeBesovPositiveScalarDepthSeminorm Q s v j
        = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j) := by
              rw [cubeBesovPositiveScalarDepthSeminorm, havg]
    _ = cubeBesovScaleWeight (-s) Q *
          (cubeBesovDepthWeight Q s j *
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j)) := by
          rw [← cubeBesovScaleWeight_neg_mul_cubeBesovDepthWeight_eq_rpow_three_weight Q s j]
          ring
    _ = cubeBesovScaleWeight (-s) Q * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
          congr 1
          simp [cubeBesovDepthSeminorm, Real.sqrt_eq_rpow]

theorem cubeBesovPositiveScalarPartialSeminormTwo_eq_scaleWeight_neg_mul_cubeBesovPartialSeminorm_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v =
      cubeBesovScaleWeight (-s) Q * cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N v := by
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v
        = Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2) := by
              rfl
    _ = Real.sqrt (∑ j ∈ Finset.range (N + 1),
          (cubeBesovScaleWeight (-s) Q * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j) ^ 2) := by
          refine congrArg Real.sqrt ?_
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
    _ = cubeBesovScaleWeight (-s) Q *
          Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j) ^ 2) := by
          exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1))
            (cubeBesovScaleWeight (-s) Q)
            (fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j)
            hscale_nonneg
    _ = cubeBesovScaleWeight (-s) Q *
          cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N v := by
          rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]

theorem CubeMultiscalePoincareInput.partialSeminorm_two_two_le_geometric_mul_cubeBesovCircPartialNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M)
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ *
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
  let r : ℝ := (3 : ℝ) ^ (-s)
  let a : ℕ → ℝ := fun k => cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) g k
  let A : ℕ → ℕ → ℝ := fun j n => if j + n ≤ M then r ^ n * a (j + n) else 0
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_r :
      ∑ n ∈ Finset.range (M + 1), r ^ n ≤ (1 - r)⁻¹ := by
    exact geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one
  have hA_nonneg :
      ∀ j ∈ Finset.range (M + 1), ∀ n ∈ Finset.range (M + 1), 0 ≤ A j n := by
    intro j hj n hn
    by_cases hjn : j + n ≤ M
    · simp [A, hjn]
      exact mul_nonneg (pow_nonneg hr_nonneg n)
        (cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞) g (j + n))
    · simp [A, hjn]
  have hinner :
      ∀ j ∈ Finset.range (M + 1),
        ∑ n ∈ Finset.range (M + 1), A j n =
          ∑ n ∈ Finset.range (M - j + 1), r ^ n * a (j + n) := by
    intro j hj
    have hsubset : Finset.range (M - j + 1) ⊆ Finset.range (M + 1) := by
      intro n hn
      have hnlt : n < M - j + 1 := Finset.mem_range.mp hn
      exact Finset.mem_range.mpr (by omega)
    calc
      ∑ n ∈ Finset.range (M + 1), A j n
          = ∑ n ∈ Finset.range (M - j + 1), A j n := by
              symm
              refine Finset.sum_subset hsubset ?_
              intro n hn hnot
              have hnlt : n < M + 1 := Finset.mem_range.mp hn
              have hnotlt : ¬ n < M - j + 1 := by
                simpa [Finset.mem_range] using hnot
              have hjn : ¬ j + n ≤ M := by
                omega
              simp [A, hjn]
        _ = ∑ n ∈ Finset.range (M - j + 1), r ^ n * a (j + n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnlt : n < M - j + 1 := Finset.mem_range.mp hn
            have hjle : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hjn : j + n ≤ M := by
              omega
            simp [A, hjn]
  have hdepth :
      ∀ j ∈ Finset.range (M + 1),
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
          C * ∑ n ∈ Finset.range (M + 1), A j n := by
    intro j hj
    calc
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
          ≤ C * ∑ n ∈ Finset.range (M - j + 1), r ^ n * a (j + n) := by
              simpa [r, a] using
                cubeBesovDepthSeminorm_two_le_weighted_shifted_of_local_circ_bound
                  Q s C u g j (M - j) hC (hinput.bound j hj)
      _ = C * ∑ n ∈ Finset.range (M + 1), A j n := by
            rw [hinner j hj]
  have hsq_bound :
      ∑ j ∈ Finset.range (M + 1), (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 ≤
        ∑ j ∈ Finset.range (M + 1), (C * ∑ n ∈ Finset.range (M + 1), A j n) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hleft_nonneg : 0 ≤ cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j :=
      cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) u j
    have hright_nonneg : 0 ≤ C * ∑ n ∈ Finset.range (M + 1), A j n := by
      exact mul_nonneg hC (Finset.sum_nonneg fun n hn => hA_nonneg j hj n hn)
    nlinarith [hdepth j hj, hleft_nonneg, hright_nonneg]
  have hcolumns :
      ∀ n ∈ Finset.range (M + 1),
        Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j n) ^ 2) ≤
          r ^ n * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
    intro n hn
    have hcol_nonneg : ∀ j ∈ Finset.range (M + 1), 0 ≤ A j n := by
      intro j hj
      exact hA_nonneg j hj n hn
    have hsum_col :
        ∑ j ∈ Finset.range (M + 1), A j n =
          ∑ j ∈ Finset.range (M - n + 1), r ^ n * a (j + n) := by
      have hsubset : Finset.range (M - n + 1) ⊆ Finset.range (M + 1) := by
        intro j hj
        have hjlt : j < M - n + 1 := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      calc
        ∑ j ∈ Finset.range (M + 1), A j n
            = ∑ j ∈ Finset.range (M - n + 1), A j n := by
                symm
                refine Finset.sum_subset hsubset ?_
                intro j hj hnot
                have hjlt : j < M + 1 := Finset.mem_range.mp hj
                have hnotlt : ¬ j < M - n + 1 := by
                  simpa [Finset.mem_range] using hnot
                have hjn : ¬ j + n ≤ M := by
                  omega
                simp [A, hjn]
        _ = ∑ j ∈ Finset.range (M - n + 1), r ^ n * a (j + n) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hjlt : j < M - n + 1 := Finset.mem_range.mp hj
              have hnle : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
              have hjn : j + n ≤ M := by
                omega
              simp [A, hjn]
    calc
      Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j n) ^ 2)
          ≤ ∑ j ∈ Finset.range (M + 1), A j n :=
            sqrt_sum_sq_le_sum (Finset.range (M + 1)) (fun j => A j n) hcol_nonneg
      _ = ∑ j ∈ Finset.range (M - n + 1), r ^ n * a (j + n) := hsum_col
      _ = r ^ n * ∑ j ∈ Finset.range (M - n + 1), a (j + n) := by
            rw [Finset.mul_sum]
      _ ≤ r ^ n * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr_nonneg n)
            have hnle : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            simpa [a, Nat.add_comm, Nat.add_sub_of_le hnle] using
              shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
                Q (1 - s) (2 : ℝ≥0∞) n (M - n) g
  have hcolsum :
      ∑ n ∈ Finset.range (M + 1),
        Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j n) ^ 2) ≤
          ∑ n ∈ Finset.range (M + 1),
            r ^ n * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hcolumns n hn
  have hcircnonneg :
      0 ≤ cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g :=
    cubeBesovCircPartialNorm_nonneg Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g
  calc
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M u
        = Real.sqrt (∑ j ∈ Finset.range (M + 1),
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) := by
              rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (M + 1),
          (C * ∑ n ∈ Finset.range (M + 1), A j n) ^ 2) := by
            exact Real.sqrt_le_sqrt hsq_bound
    _ = C * Real.sqrt (∑ j ∈ Finset.range (M + 1),
          (∑ n ∈ Finset.range (M + 1), A j n) ^ 2) := by
            exact sqrt_sum_sq_const_mul_eq (Finset.range (M + 1)) C
              (fun j => ∑ n ∈ Finset.range (M + 1), A j n) hC
    _ ≤ C * ∑ n ∈ Finset.range (M + 1),
          Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j n) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact sqrt_sum_sq_sum_le_sum_sqrt_sum_sq
              (Finset.range (M + 1)) (Finset.range (M + 1)) A hA_nonneg
    _ ≤ C * ∑ n ∈ Finset.range (M + 1),
          r ^ n * cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
            exact mul_le_mul_of_nonneg_left hcolsum hC
    _ = C * ((∑ n ∈ Finset.range (M + 1), r ^ n) *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g) := by
            rw [Finset.sum_mul]
    _ ≤ C * ((1 - r)⁻¹ *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsum_r hcircnonneg) hC
    _ = C * (1 - r)⁻¹ *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
            ring

theorem cubeBesovDepthSeminorm_two_le_weighted_shifted_sum_components_of_vector_local_circ_bound
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

theorem CubeLocalMultiscalePoincareVectorEstimate.partialSeminorm_two_two_le_geometric_mul_card_mul_of_component_bound
    {d : ℕ} {Q : TriadicCube d} {s C Bcirc : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareVectorEstimate Q C u G M)
    (hs : 0 < s) (hC : 0 ≤ C) (hBcirc : 0 ≤ Bcirc)
    (hcirc : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M u ≤
      C * (1 - (3 : ℝ) ^ (-s))⁻¹ * ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
  classical
  let r : ℝ := (3 : ℝ) ^ (-s)
  let a : Fin d → ℕ → ℝ := fun i k =>
    cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) (fun x => G x i) k
  let I : Finset (Fin d × ℕ) :=
    (Finset.univ : Finset (Fin d)).product (Finset.range (M + 1))
  let A : ℕ → Fin d × ℕ → ℝ := fun j p =>
    if j + p.2 ≤ M then r ^ p.2 * a p.1 (j + p.2) else 0
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_r :
      ∑ n ∈ Finset.range (M + 1), r ^ n ≤ (1 - r)⁻¹ := by
    exact geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one
  have hA_nonneg :
      ∀ j ∈ Finset.range (M + 1), ∀ p ∈ I, 0 ≤ A j p := by
    intro j hj p hp
    by_cases hjp : j + p.2 ≤ M
    · simp [A, hjp]
      exact mul_nonneg (pow_nonneg hr_nonneg p.2)
        (cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞)
          (fun x => G x p.1) (j + p.2))
    · simp [A, hjp]
  have hinner :
      ∀ j ∈ Finset.range (M + 1),
        ∑ p ∈ I, A j p =
          ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1), r ^ n * a i (j + n) := by
    intro j hj
    have hsubset : Finset.range (M - j + 1) ⊆ Finset.range (M + 1) := by
      intro n hn
      have hnlt : n < M - j + 1 := Finset.mem_range.mp hn
      exact Finset.mem_range.mpr (by omega)
    calc
      ∑ p ∈ I, A j p
          = ∑ i : Fin d, ∑ n ∈ Finset.range (M + 1), A j (i, n) := by
              simp [I, Finset.sum_product]
      _ = ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1), A j (i, n) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_subset hsubset ?_
            intro n hn hnot
            have hnlt : n < M + 1 := Finset.mem_range.mp hn
            have hnotlt : ¬ n < M - j + 1 := by
              simpa [Finset.mem_range] using hnot
            have hjn : ¬ j + n ≤ M := by
              omega
            simp [A, hjn]
      _ = ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1), r ^ n * a i (j + n) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnlt : n < M - j + 1 := Finset.mem_range.mp hn
            have hjle : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hjn : j + n ≤ M := by
              omega
            simp [A, hjn]
  have hdepth :
      ∀ j ∈ Finset.range (M + 1),
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
          C * ∑ p ∈ I, A j p := by
    intro j hj
    calc
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
          ≤ C * ∑ i : Fin d, ∑ n ∈ Finset.range (M - j + 1),
              r ^ n * a i (j + n) := by
              simpa [r, a] using
                cubeBesovDepthSeminorm_two_le_weighted_shifted_sum_components_of_vector_local_circ_bound
                  Q s C u G j (M - j) hC (by
                    intro R hR
                    exact hlocal j hj R hR)
      _ = C * ∑ p ∈ I, A j p := by
            rw [hinner j hj]
  have hsq_bound :
      ∑ j ∈ Finset.range (M + 1), (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 ≤
        ∑ j ∈ Finset.range (M + 1), (C * ∑ p ∈ I, A j p) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hleft_nonneg : 0 ≤ cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j :=
      cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) u j
    have hright_nonneg : 0 ≤ C * ∑ p ∈ I, A j p := by
      exact mul_nonneg hC (Finset.sum_nonneg fun p hp => hA_nonneg j hj p hp)
    nlinarith [hdepth j hj, hleft_nonneg, hright_nonneg]
  have hcolumns :
      ∀ p ∈ I,
        Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j p) ^ 2) ≤
          r ^ p.2 * Bcirc := by
    intro p hp
    have hp_range : p.2 ∈ Finset.range (M + 1) := (Finset.mem_product.mp hp).2
    have hcol_nonneg : ∀ j ∈ Finset.range (M + 1), 0 ≤ A j p := by
      intro j hj
      exact hA_nonneg j hj p hp
    have hsum_col :
        ∑ j ∈ Finset.range (M + 1), A j p =
          ∑ j ∈ Finset.range (M - p.2 + 1), r ^ p.2 * a p.1 (j + p.2) := by
      have hsubset : Finset.range (M - p.2 + 1) ⊆ Finset.range (M + 1) := by
        intro j hj
        have hjlt : j < M - p.2 + 1 := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      calc
        ∑ j ∈ Finset.range (M + 1), A j p
            = ∑ j ∈ Finset.range (M - p.2 + 1), A j p := by
                symm
                refine Finset.sum_subset hsubset ?_
                intro j hj hnot
                have hjlt : j < M + 1 := Finset.mem_range.mp hj
                have hnotlt : ¬ j < M - p.2 + 1 := by
                  simpa [Finset.mem_range] using hnot
                have hjp : ¬ j + p.2 ≤ M := by
                  omega
                simp [A, hjp]
        _ = ∑ j ∈ Finset.range (M - p.2 + 1), r ^ p.2 * a p.1 (j + p.2) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hjlt : j < M - p.2 + 1 := Finset.mem_range.mp hj
              have hple : p.2 ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)
              have hjp : j + p.2 ≤ M := by
                omega
              simp [A, hjp]
    calc
      Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j p) ^ 2)
          ≤ ∑ j ∈ Finset.range (M + 1), A j p :=
            sqrt_sum_sq_le_sum (Finset.range (M + 1)) (fun j => A j p) hcol_nonneg
      _ = ∑ j ∈ Finset.range (M - p.2 + 1), r ^ p.2 * a p.1 (j + p.2) := hsum_col
      _ = r ^ p.2 * ∑ j ∈ Finset.range (M - p.2 + 1), a p.1 (j + p.2) := by
            rw [Finset.mul_sum]
      _ ≤ r ^ p.2 *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
              (fun x => G x p.1) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr_nonneg p.2)
            have hple : p.2 ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)
            simpa [a, Nat.add_comm, Nat.add_sub_of_le hple] using
              shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
                Q (1 - s) (2 : ℝ≥0∞) p.2 (M - p.2) (fun x => G x p.1)
      _ ≤ r ^ p.2 * Bcirc := by
            exact mul_le_mul_of_nonneg_left (hcirc p.1) (pow_nonneg hr_nonneg p.2)
  have hcolsum :
      ∑ p ∈ I,
        Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j p) ^ 2) ≤
          ∑ p ∈ I, r ^ p.2 * Bcirc := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hcolumns p hp
  have hpairsum :
      ∑ p ∈ I, r ^ p.2 * Bcirc =
        (Fintype.card (Fin d) : ℝ) *
          ((∑ n ∈ Finset.range (M + 1), r ^ n) * Bcirc) := by
    simp [I, Finset.sum_product, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hpairsum_bound :
      ∑ p ∈ I, r ^ p.2 * Bcirc ≤
        (Fintype.card (Fin d) : ℝ) * ((1 - r)⁻¹ * Bcirc) := by
    rw [hpairsum]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsum_r hBcirc) hcard_nonneg
  calc
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M u
        = Real.sqrt (∑ j ∈ Finset.range (M + 1),
            (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) := by
              rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (M + 1),
          (C * ∑ p ∈ I, A j p) ^ 2) := by
            exact Real.sqrt_le_sqrt hsq_bound
    _ = C * Real.sqrt (∑ j ∈ Finset.range (M + 1),
          (∑ p ∈ I, A j p) ^ 2) := by
            exact sqrt_sum_sq_const_mul_eq (Finset.range (M + 1)) C
              (fun j => ∑ p ∈ I, A j p) hC
    _ ≤ C * ∑ p ∈ I,
          Real.sqrt (∑ j ∈ Finset.range (M + 1), (A j p) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact sqrt_sum_sq_sum_le_sum_sqrt_sum_sq
              (Finset.range (M + 1)) I A hA_nonneg
    _ ≤ C * ∑ p ∈ I, r ^ p.2 * Bcirc := by
            exact mul_le_mul_of_nonneg_left hcolsum hC
    _ ≤ C * ((Fintype.card (Fin d) : ℝ) * ((1 - r)⁻¹ * Bcirc)) := by
            exact mul_le_mul_of_nonneg_left hpairsum_bound hC
    _ = C * (1 - r)⁻¹ * ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
            ring

theorem CubeLocalMultiscalePoincareVectorEstimate.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs_of_component_bound
    {d : ℕ} {Q : TriadicCube d} {s C Bcirc : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareVectorEstimate Q C (cubeFluctuation Q u) G M)
    (hs : 0 < s) (hC : 0 ≤ C) (hBcirc : 0 ≤ Bcirc)
    (hcirc : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u) ≤
      cubeBesovScaleWeight (-s) Q *
        ((C * (1 - (3 : ℝ) ^ (-s))⁻¹) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
  have hgeneric :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M
          (cubeFluctuation Q u) ≤
        C * (1 - (3 : ℝ) ^ (-s))⁻¹ * ((Fintype.card (Fin d) : ℝ) * Bcirc) :=
    hlocal.partialSeminorm_two_two_le_geometric_mul_card_mul_of_component_bound
      hs hC hBcirc hcirc
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u)
        = cubeBesovScaleWeight (-s) Q *
            cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M
              (cubeFluctuation Q u) := by
              rw [cubeBesovPositiveScalarPartialSeminormTwo_eq_scaleWeight_neg_mul_cubeBesovPartialSeminorm_two_two]
    _ ≤ cubeBesovScaleWeight (-s) Q *
          ((C * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgeneric hscale_nonneg

theorem CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs_of_component_bound
    {d : ℕ} {Q : TriadicCube d} {s C Bcirc : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hproj :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G M)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 < s) (hC : 0 ≤ C) (hBcirc : 0 ≤ Bcirc)
    (hcirc : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u) ≤
      cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
  have hlocal :=
    hproj.to_localEstimate hG hC
  have hK_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hgeneric :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹ * ((Fintype.card (Fin d) : ℝ) * Bcirc) := by
    exact
      hlocal.partialSeminorm_two_two_le_geometric_mul_card_mul_of_component_bound
        hs hK_nonneg hBcirc hcirc
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u)
        = cubeBesovScaleWeight (-s) Q *
            cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
              rw [cubeBesovPositiveScalarPartialSeminormTwo_eq_scaleWeight_neg_mul_cubeBesovPartialSeminorm_two_two]
    _ ≤ cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * ((Fintype.card (Fin d) : ℝ) * Bcirc)) := by
          exact mul_le_mul_of_nonneg_left hgeneric hscale_nonneg

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : 0 < s) (hC : 0 ≤ C) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u) ≤
      cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g) := by
  have hgeneric :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g := by
    exact
      (hproj.to_input hg hC).partialSeminorm_two_two_le_geometric_mul_cubeBesovCircPartialNorm
        hs (by positivity)
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s M (cubeFluctuation Q u)
        = cubeBesovScaleWeight (-s) Q *
            cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
              rw [cubeBesovPositiveScalarPartialSeminormTwo_eq_scaleWeight_neg_mul_cubeBesovPartialSeminorm_two_two]
    _ ≤ cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M g) := by
          exact mul_le_mul_of_nonneg_left hgeneric hscale_nonneg



end

end Homogenization
