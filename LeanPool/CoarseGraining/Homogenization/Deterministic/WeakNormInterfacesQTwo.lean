/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Descendants
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation

/-! # Weak Norm Interfaces QTwo -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

/-!
# `q = 2` deterministic weak-norm recursion lemmas

This file records the first note-facing scale-splitting identities for the
vector-valued negative Besov wrappers used in the deterministic Chapter-3 right-
hand-side argument.
-/

@[simp] theorem cubeBesovNegativeVectorDepthAverage_depth_zero {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorDepthAverage Q u 0 = vecNormSq (cubeAverageVec Q u) := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  simp

theorem sq_cubeBesovNegativeVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 =
      (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
        cubeBesovNegativeVectorDepthAverage Q u j := by
  have hA : 0 ≤ cubeBesovNegativeVectorDepthAverage Q u j :=
    cubeBesovNegativeVectorDepthAverage_nonneg Q u j
  calc
    (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2
        =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)) ^ 2 := by
              rfl
    _ =
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
          (Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j)) ^ 2 := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
          cubeBesovNegativeVectorDepthAverage Q u j := by
            rw [Real.sq_sqrt hA]

/--
Squared depth contribution controlled by a descendant-average upper bound.
This is the weighted `q = 2` analogue of the finite `q = 1` estimate in
`WeakNormInterfaces`.
-/
theorem sq_cubeBesovNegativeVectorDepthSeminorm_le_of_depthAverage_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) {A : ℝ}
    (hA : cubeBesovNegativeVectorDepthAverage Q u j ≤ A) :
    (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 ≤
      (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 * A := by
  rw [sq_cubeBesovNegativeVectorDepthSeminorm]
  exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)

/--
Finite `q = 2` weak-norm control from depthwise descendant-average controls,
kept in squared form to match the Cauchy/energy estimates used in Section 5.3.
-/
theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_depthAverage_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) {A : ℕ → ℝ}
    (hA : ∀ j ∈ Finset.range (N + 1),
      cubeBesovNegativeVectorDepthAverage Q u j ≤ A j) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1),
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 * A j := by
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
  refine Finset.sum_le_sum ?_
  intro j hj
  exact sq_cubeBesovNegativeVectorDepthSeminorm_le_of_depthAverage_le Q s u j (hA j hj)

/--
Squared finite `q = 2` negative weak-norm bound from a four-term decomposition
of the descendant cube averages at every depth.
-/
theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_four_term_depthAverage_decomposition
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (predictor additivity lowScale tail : ℕ → TriadicCube d → Vec d)
    (hdecomp : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeAverageVec R u =
        predictor j R + additivity j R + lowScale j R + tail j R) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1),
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
          (descendantsAverage Q j fun R =>
            4 *
              (vecNormSq (predictor j R) + vecNormSq (additivity j R) +
                vecNormSq (lowScale j R) + vecNormSq (tail j R))) := by
  refine sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_depthAverage_le Q s N u ?_
  intro j hj
  exact
    cubeBesovNegativeVectorDepthAverage_le_four_mul_sum_of_cubeAverageVec_eq
      Q u j (predictor j) (additivity j) (lowScale j) (tail j)
      (hdecomp j hj)

@[simp] theorem sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) :
    (cubeBesovNegativeVectorDepthSeminorm Q s u 0) ^ 2 =
      vecNormSq (cubeAverageVec Q u) := by
  rw [sq_cubeBesovNegativeVectorDepthSeminorm, cubeBesovNegativeVectorDepthAverage_depth_zero]
  simp

theorem cubeBesovNegativeVectorDepthAverage_succ_eq_descendantsAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q u (j + 1) =
      descendantsAverage Q 1
        (fun R => cubeBesovNegativeVectorDepthAverage R u j) := by
  simpa [Nat.add_comm, cubeBesovNegativeVectorDepthAverage] using
    (descendantsAverage_add_eq_descendantsAverage_descendantsAverage
      (Q := Q) (j := 1) (n := j)
      (F := fun R => vecNormSq (cubeAverageVec R u)))

theorem sq_cubeBesovNegativeVectorDepthSeminorm_succ_eq_discount_mul_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    (cubeBesovNegativeVectorDepthSeminorm Q s u (j + 1)) ^ 2 =
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2) := by
  calc
    (cubeBesovNegativeVectorDepthSeminorm Q s u (j + 1)) ^ 2
        =
          (Real.rpow (3 : ℝ) (-s * ((j + 1 : ℕ) : ℝ))) ^ 2 *
            cubeBesovNegativeVectorDepthAverage Q u (j + 1) := by
              exact sq_cubeBesovNegativeVectorDepthSeminorm Q s u (j + 1)
    _ =
        (Real.rpow (3 : ℝ) (-s)) ^ 2 *
          ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            descendantsAverage Q 1
              (fun R => cubeBesovNegativeVectorDepthAverage R u j)) := by
            rw [rpow_neg_mul_nat_succ_eq,
              cubeBesovNegativeVectorDepthAverage_succ_eq_descendantsAverage]
            ring
    _ =
        (Real.rpow (3 : ℝ) (-s)) ^ 2 *
          descendantsAverage Q 1
            (fun R =>
              (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                cubeBesovNegativeVectorDepthAverage R u j) := by
            rw [← descendantsAverage_mul_left Q 1
              ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2)
              (fun R => cubeBesovNegativeVectorDepthAverage R u j)]
    _ =
        (Real.rpow (3 : ℝ) (-s)) ^ 2 *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2) := by
            congr 1
            refine congrArg (descendantsAverage Q 1) ?_
            funext R
            symm
            exact sq_cubeBesovNegativeVectorDepthSeminorm R s u j
    _ =
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2) := by
            congr 1
            calc
              (Real.rpow (3 : ℝ) (-s)) ^ 2
                  = Real.rpow (3 : ℝ) ((-s : ℝ) * 2) := by
                      simpa [Real.rpow_natCast] using
                        (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s) (2 : ℝ)).symm
              _ = Real.rpow (3 : ℝ) (-2 * s) := by ring_nf

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_eq_top_add_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 =
      vecNormSq (cubeAverageVec Q u) +
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
  have hsplit :
      Finset.sum (Finset.range (N + 2))
        (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) =
          vecNormSq (cubeAverageVec Q u) +
            Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u (j + 1)) ^ 2) := by
    convert
      (Finset.sum_range_succ'
        (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2)
        (N + 1)) using 1
    · simp [add_comm, sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero]
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2
        = Finset.sum (Finset.range (N + 2))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) := by
              exact sq_cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u
    _ =
        vecNormSq (cubeAverageVec Q u) +
          Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u (j + 1)) ^ 2) := by
              exact hsplit
    _ =
        vecNormSq (cubeAverageVec Q u) +
          Finset.sum (Finset.range (N + 1))
            (fun j =>
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2)) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact sq_cubeBesovNegativeVectorDepthSeminorm_succ_eq_discount_mul_descendantsAverage
                Q s u j
    _ =
        vecNormSq (cubeAverageVec Q u) +
          Real.rpow (3 : ℝ) (-2 * s) *
            Finset.sum (Finset.range (N + 1))
              (fun j =>
                descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2)) := by
              rw [← Finset.mul_sum]
    _ =
        vecNormSq (cubeAverageVec Q u) +
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => Finset.sum (Finset.range (N + 1))
                (fun j => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2)) := by
              simpa using
                congrArg
                  (fun x =>
                    vecNormSq (cubeAverageVec Q u) +
                      Real.rpow (3 : ℝ) (-2 * s) * x)
                  (descendantsAverage_sum Q 1 (Finset.range (N + 1))
                    (fun R j => (cubeBesovNegativeVectorDepthSeminorm R s u j) ^ 2)).symm
    _ =
        vecNormSq (cubeAverageVec Q u) +
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
              simpa using
                congrArg
                  (fun x =>
                    vecNormSq (cubeAverageVec Q u) +
                      Real.rpow (3 : ℝ) (-2 * s) * x)
                  (congrArg (descendantsAverage Q 1) <|
                    funext fun R =>
                      (sq_cubeBesovNegativeVectorPartialSeminormTwo R s N u).symm)

end

end Homogenization
