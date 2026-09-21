/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PositiveNorm

/-! # Standard Overlap Comparison -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Standard/overlapping positive Besov comparison

The key geometric observation is that every ordinary descendant cube appears
as the overlapping cube of its middle child.  This file starts the comparison
API with the exact middle-child identities.
-/

@[simp] theorem overlapCubeScaleFactor_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    overlapCubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q := by
  have hscale :
      cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
    simpa [middleChildCube] using
      cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  unfold overlapCubeScaleFactor
  rw [hscale]
  ring

@[simp] theorem overlapCubeVolume_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    overlapCubeVolume (middleChildCube Q) = cubeVolume Q := by
  simp [overlapCubeVolume, cubeVolume_eq_scaleFactor_pow]

@[simp] theorem overlapCubeMeasure_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    overlapCubeMeasure (middleChildCube Q) = cubeMeasure Q := by
  rw [overlapCubeMeasure, cubeMeasure, overlapCubeSet_middleChildCube_eq_cubeSet]

@[simp] theorem normalizedOverlapCubeMeasure_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    normalizedOverlapCubeMeasure (middleChildCube Q) =
      normalizedCubeMeasure Q := by
  rw [normalizedOverlapCubeMeasure, normalizedCubeMeasure]
  simp

@[simp] theorem overlapCubeAverage_middleChildCube {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    overlapCubeAverage (middleChildCube Q) f = cubeAverage Q f := by
  rw [overlapCubeAverage_eq_integral_normalizedOverlapCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  simp

@[simp] theorem overlapCubeAverageVec_middleChildCube {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) :
    overlapCubeAverageVec (middleChildCube Q) u = cubeAverageVec Q u := by
  funext i
  simp [overlapCubeAverageVec, cubeAverageVec]

@[simp] theorem overlapCubeFluctuationVec_middleChildCube {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) :
    overlapCubeFluctuationVec (middleChildCube Q) u = cubeFluctuationVec Q u := by
  funext x
  simp [overlapCubeFluctuationVec, cubeFluctuationVec]

@[simp] theorem overlapCubeLpNorm_middleChildCube {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → E) :
    overlapCubeLpNorm (middleChildCube Q) p u = cubeLpNorm Q p u := by
  unfold overlapCubeLpNorm cubeLpNorm
  simp

@[simp] theorem overlapCubeLpNorm_middleChildCube_fluctuation {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) :
    overlapCubeLpNorm (middleChildCube Q) (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec (middleChildCube Q) u) =
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u) := by
  simp

theorem overlapCentersAtDepth_card_le_three_pow_mul_descendantsAtDepth_card
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≤
      3 ^ d * (descendantsAtDepth Q j).card := by
  calc
    (overlapCentersAtDepth Q j).card
        ≤ (descendantsAtDepth Q (j + 1)).card :=
          overlapCentersAtDepth_card_le_descendantsAtDepth_card Q j
    _ = (descendantsAtDepth Q j).card * 3 ^ d :=
          descendantsAtDepth_card_succ Q j
    _ = 3 ^ d * (descendantsAtDepth Q j).card := by
          rw [Nat.mul_comm]

theorem cubeBesovPositiveVectorDepthAverage_le_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q u j ≤
      (3 ^ d : ℝ) * cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let O : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let G : TriadicCube d → ℝ :=
    fun S =>
      (overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u)) ^ 2
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hD_card_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hD_card_ne : (D.card : ℝ) ≠ 0 := ne_of_gt hD_card_pos
  have hO_nonempty : O.Nonempty := by
    simpa [O] using overlapCentersAtDepth_nonempty Q j
  have hO_card_pos : 0 < (O.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hO_nonempty
  have hO_card_ne : (O.card : ℝ) ≠ 0 := ne_of_gt hO_card_pos
  have hG_nonneg : ∀ S ∈ O, 0 ≤ G S := by
    intro S _hS
    exact sq_nonneg _
  have himage_subset : D.image middleChildCube ⊆ O := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    exact middleChildCube_mem_overlapCentersAtDepth_of_mem_descendantsAtDepth
      (by simpa [D] using hR)
  have hsum_image_le : (D.image middleChildCube).sum G ≤ O.sum G := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun S hSO _hSnot => hG_nonneg S hSO)
  have hsum_desc_eq_image :
      D.sum
          (fun R =>
            (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u)) ^ 2) =
        (D.image middleChildCube).sum G := by
    rw [Finset.sum_image]
    · simp
    · intro R _hR S _hS hRS
      exact middleChildCube_injective hRS
  have hsum_nonneg : 0 ≤ O.sum G := by
    exact Finset.sum_nonneg hG_nonneg
  have hcard_nat :
      O.card ≤ 3 ^ d * D.card := by
    simpa [D, O] using
      overlapCentersAtDepth_card_le_three_pow_mul_descendantsAtDepth_card Q j
  have hcard_real :
      (O.card : ℝ) ≤ (3 ^ d : ℝ) * (D.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hdenom :
      (D.card : ℝ)⁻¹ * O.sum G ≤
        (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := by
    calc
      (D.card : ℝ)⁻¹ * O.sum G
          = ((O.card : ℝ) / (D.card : ℝ)) *
              ((O.card : ℝ)⁻¹ * O.sum G) := by
              field_simp [hD_card_ne, hO_card_ne]
      _ ≤ (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := by
          have hratio :
              (O.card : ℝ) / (D.card : ℝ) ≤ (3 ^ d : ℝ) := by
            rw [div_le_iff₀ hD_card_pos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using hcard_real
          have havg_nonneg : 0 ≤ (O.card : ℝ)⁻¹ * O.sum G :=
            mul_nonneg (inv_nonneg.mpr (le_of_lt hO_card_pos)) hsum_nonneg
          exact mul_le_mul_of_nonneg_right hratio havg_nonneg
  calc
    cubeBesovPositiveVectorDepthAverage Q u j
        = (D.card : ℝ)⁻¹ *
            D.sum
              (fun R =>
                (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u)) ^ 2) := by
            rfl
    _ = (D.card : ℝ)⁻¹ * (D.image middleChildCube).sum G := by
          rw [hsum_desc_eq_image]
    _ ≤ (D.card : ℝ)⁻¹ * O.sum G := by
          exact mul_le_mul_of_nonneg_left hsum_image_le
            (inv_nonneg.mpr (le_of_lt hD_card_pos))
    _ ≤ (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := hdenom
    _ = (3 ^ d : ℝ) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
          rfl

theorem sq_cubeBesovPositiveVectorDepthSeminorm_le_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 ≤
      (3 ^ d : ℝ) *
        (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
  have havg :=
    cubeBesovPositiveVectorDepthAverage_le_three_pow_mul_overlapping Q u j
  have hweight_nonneg :
      0 ≤ (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 := sq_nonneg _
  calc
    (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            cubeBesovPositiveVectorDepthAverage Q u j := by
          exact sq_cubeBesovPositiveVectorDepthSeminorm Q s u j
    _ ≤
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            ((3 ^ d : ℝ) *
              cubeBesovOverlappingPositiveVectorDepthAverage Q u j) := by
          exact mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ =
          (3 ^ d : ℝ) *
            ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
              cubeBesovOverlappingPositiveVectorDepthAverage Q u j) := by
          ring
    _ =
          (3 ^ d : ℝ) *
            (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
          rw [sq_cubeBesovOverlappingPositiveVectorDepthSeminorm]

theorem sq_cubeBesovPositiveVectorPartialSeminormTwo_le_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      (3 ^ d : ℝ) *
        (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 := by
  calc
    (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2
        =
          Finset.sum (Finset.range (N + 1)) fun j =>
            (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
          exact sq_cubeBesovPositiveVectorPartialSeminormTwo Q s N u
    _ ≤
          Finset.sum (Finset.range (N + 1)) fun j =>
            (3 ^ d : ℝ) *
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
          exact Finset.sum_le_sum fun j _hj =>
            sq_cubeBesovPositiveVectorDepthSeminorm_le_three_pow_mul_overlapping
              Q s u j
    _ =
          (3 ^ d : ℝ) *
            Finset.sum (Finset.range (N + 1)) fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
          rw [Finset.mul_sum]
    _ =
          (3 ^ d : ℝ) *
            (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 := by
          rw [sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo]

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_sqrt_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u ≤
      Real.sqrt (3 ^ d : ℝ) *
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u := by
  have hsq :=
    sq_cubeBesovPositiveVectorPartialSeminormTwo_le_three_pow_mul_overlapping
      Q s N u
  have hc_nonneg : 0 ≤ (3 ^ d : ℝ) := by positivity
  have hright_sq :
      (Real.sqrt (3 ^ d : ℝ) *
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 =
        (3 ^ d : ℝ) *
          (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc_nonneg]
  have hsq' :
      (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2 ≤
        (Real.sqrt (3 ^ d : ℝ) *
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 := by
    simpa [hright_sq] using hsq
  exact
    (sq_le_sq₀
      (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s N u)
      (mul_nonneg (Real.sqrt_nonneg _)
        (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q s N u))).mp
      hsq'

theorem cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N u) := by
  rcases hBdd with ⟨B, hB⟩
  refine ⟨Real.sqrt (3 ^ d : ℝ) * B, ?_⟩
  rintro x ⟨N, rfl⟩
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u
        ≤ Real.sqrt (3 ^ d : ℝ) *
            cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u :=
          cubeBesovPositiveVectorPartialSeminormTwo_le_sqrt_three_pow_mul_overlapping
            Q s N u
    _ ≤ Real.sqrt (3 ^ d : ℝ) * B := by
          exact mul_le_mul_of_nonneg_left (hB ⟨N, rfl⟩)
            (Real.sqrt_nonneg _)

theorem cubeBesovPositiveVectorSeminormTwo_le_sqrt_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u)) :
    cubeBesovPositiveVectorSeminormTwo Q s u ≤
      Real.sqrt (3 ^ d : ℝ) *
        cubeBesovOverlappingPositiveVectorSeminormTwo Q s u := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s u ?_
  intro N
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u
        ≤ Real.sqrt (3 ^ d : ℝ) *
            cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u :=
          cubeBesovPositiveVectorPartialSeminormTwo_le_sqrt_three_pow_mul_overlapping
            Q s N u
    _ ≤ Real.sqrt (3 ^ d : ℝ) *
          cubeBesovOverlappingPositiveVectorSeminormTwo Q s u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
              Q s u hBdd N)
            (Real.sqrt_nonneg _)

theorem positiveVectorNormTwo_le_sqrt_three_pow_mul_overlappingNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u)) :
    Real.sqrt (vecNormSq (cubeAverageVec Q u)) +
        cubeBesovPositiveVectorSeminormTwo Q s u ≤
      Real.sqrt (3 ^ d : ℝ) *
        cubeBesovOverlappingPositiveVectorNormTwo Q s u := by
  have hsem :=
    cubeBesovPositiveVectorSeminormTwo_le_sqrt_three_pow_mul_overlapping
      Q s u hBdd
  have hconst_one : 1 ≤ Real.sqrt (3 ^ d : ℝ) := by
    have hpow : (1 : ℝ) ≤ (3 ^ d : ℝ) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
    have hsqrt := Real.sqrt_le_sqrt hpow
    simpa using hsqrt
  have hmean_nonneg : 0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q u)) :=
    Real.sqrt_nonneg _
  have hmean :
      Real.sqrt (vecNormSq (cubeAverageVec Q u)) ≤
        Real.sqrt (3 ^ d : ℝ) *
          Real.sqrt (vecNormSq (cubeAverageVec Q u)) := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right hconst_one hmean_nonneg
  calc
    Real.sqrt (vecNormSq (cubeAverageVec Q u)) +
        cubeBesovPositiveVectorSeminormTwo Q s u
        ≤
          Real.sqrt (3 ^ d : ℝ) *
              Real.sqrt (vecNormSq (cubeAverageVec Q u)) +
            Real.sqrt (3 ^ d : ℝ) *
              cubeBesovOverlappingPositiveVectorSeminormTwo Q s u := by
          exact add_le_add hmean hsem
    _ =
      Real.sqrt (3 ^ d : ℝ) *
        cubeBesovOverlappingPositiveVectorNormTwo Q s u := by
          unfold cubeBesovOverlappingPositiveVectorNormTwo
          ring

end

end Homogenization
