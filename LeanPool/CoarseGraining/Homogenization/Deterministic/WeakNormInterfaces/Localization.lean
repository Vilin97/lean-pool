/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import Mathlib.Algebra.Order.Chebyshev

/-! # Localization -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Localization for the concrete vector negative `q = 2` seminorm

This file proves the finite-energy localization estimate for the concrete
negative Besov seminorm used in the Ch3.3 Hodge-projection input.  The full
seminorm is an `sSup` of finite partial seminorms, so the final full-seminorm
statement assumes the local partial seminorms are bounded above; this is the
same `sSup` well-posedness hypothesis used throughout the deterministic Ch3
files when a finite partial norm is compared to the full norm.
-/

theorem descendantsAverage_sq_le_descendantsAverage_sq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    (descendantsAverage Q j F) ^ 2 ≤ descendantsAverage Q j (fun R => (F R) ^ 2) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let c : ℝ := D.card
  let S : ℝ := ∑ R ∈ D, F R
  let T : ℝ := ∑ R ∈ D, (F R) ^ 2
  have hcard_ne : c ≠ 0 := by
    dsimp [c, D]
    exact_mod_cast (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j))
  have hcheb : S ^ 2 ≤ c * T := by
    dsimp [S, T, c]
    simpa [D] using (sq_sum_le_card_mul_sum_sq (s := D) (f := F))
  change (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, F R) ^ 2 ≤
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, (F R) ^ 2
  change (c⁻¹ * S) ^ 2 ≤ c⁻¹ * T
  calc
    (c⁻¹ * S) ^ 2 = (c⁻¹) ^ 2 * S ^ 2 := by ring
    _ ≤ (c⁻¹) ^ 2 * (c * T) :=
        mul_le_mul_of_nonneg_left hcheb (sq_nonneg c⁻¹)
    _ = c⁻¹ * T := by
        field_simp [hcard_ne]

theorem vecNormSq_cubeAverageVec_le_descendantsAverage_vecNormSq_cubeAverageVec_one_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    vecNormSq (cubeAverageVec Q u) ≤
      descendantsAverage Q 1 fun R => vecNormSq (cubeAverageVec R u) := by
  classical
  have hcoord : ∀ i : Fin d,
      (cubeAverage Q (fun x => u x i)) ^ 2 ≤
        descendantsAverage Q 1 (fun R => (cubeAverage R (fun x => u x i)) ^ 2) := by
    intro i
    have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal)
        (normalizedCubeMeasure Q) := by
      simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
    have hui_int : MeasureTheory.IntegrableOn (fun x => u x i)
        (cubeSet Q) MeasureTheory.volume :=
      integrableOn_of_integrable_normalizedCubeMeasure Q (hui.integrable (by norm_num))
    have havg : cubeAverage Q (fun x => u x i) =
        descendantsAverage Q 1 (fun R => cubeAverage R (fun x => u x i)) :=
      cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
        Q 1 (fun x => u x i) hui_int
    rw [havg]
    exact descendantsAverage_sq_le_descendantsAverage_sq Q 1
      (fun R => cubeAverage R (fun x => u x i))
  calc
    vecNormSq (cubeAverageVec Q u)
        = ∑ i : Fin d, (cubeAverage Q (fun x => u x i)) ^ 2 := by
            simp [cubeAverageVec, vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i : Fin d,
          descendantsAverage Q 1 (fun R => (cubeAverage R (fun x => u x i)) ^ 2) := by
            exact Finset.sum_le_sum fun i _hi => hcoord i
    _ = descendantsAverage Q 1 (fun R => ∑ i : Fin d,
          (cubeAverage R (fun x => u x i)) ^ 2) := by
            simpa using (descendantsAverage_sum Q 1 Finset.univ
              (fun R i => (cubeAverage R (fun x => u x i)) ^ 2)).symm
    _ = descendantsAverage Q 1 (fun R => vecNormSq (cubeAverageVec R u)) := by
            congr 1
            funext R
            simp [cubeAverageVec, vecNormSq, vecDot, pow_two]

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_le_descendantsAverage_one_same_depth_of_memLp
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (_hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) (N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      descendantsAverage Q 1 fun R =>
        (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2 := by
  induction N generalizing Q with
  | zero =>
      have htop :=
        vecNormSq_cubeAverageVec_le_descendantsAverage_vecNormSq_cubeAverageVec_one_of_memLp
          Q u hu
      simpa [sq_cubeBesovNegativeVectorPartialSeminormTwo,
        sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero] using htop
  | succ N ih =>
      have htop :=
        vecNormSq_cubeAverageVec_le_descendantsAverage_vecNormSq_cubeAverageVec_one_of_memLp
          Q u hu
      let r : ℝ := Real.rpow (3 : ℝ) (-2 * s)
      have hr_nonneg : 0 ≤ r := by
        dsimp [r]
        exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
      have hchild_step : ∀ R ∈ descendantsAtDepth Q 1,
          (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2 ≤
            descendantsAverage R 1 fun S =>
              (cubeBesovNegativeVectorPartialSeminormTwo S s N u) ^ 2 := by
        intro R hR
        have huR : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure R) :=
          memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
        exact ih R huR
      calc
        (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2
            = vecNormSq (cubeAverageVec Q u) +
                r * descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
                  simpa [r] using
                    sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_eq_top_add_descendantsAverage
                      Q s N u
        _ ≤ descendantsAverage Q 1 (fun R => vecNormSq (cubeAverageVec R u)) +
                r * descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
              exact add_le_add htop le_rfl
        _ ≤ descendantsAverage Q 1 (fun R => vecNormSq (cubeAverageVec R u)) +
                r * descendantsAverage Q 1
                  (fun R => descendantsAverage R 1
                    (fun S => (cubeBesovNegativeVectorPartialSeminormTwo S s N u) ^ 2)) := by
              refine add_le_add le_rfl ?_
              exact mul_le_mul_of_nonneg_left
                (descendantsAverage_le_descendantsAverage Q 1 hchild_step) hr_nonneg
        _ = descendantsAverage Q 1
              (fun R => vecNormSq (cubeAverageVec R u) +
                r * descendantsAverage R 1
                  (fun S => (cubeBesovNegativeVectorPartialSeminormTwo S s N u) ^ 2)) := by
              rw [descendantsAverage_add]
              rw [descendantsAverage_smul]
        _ = descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s (N + 1) u) ^ 2) := by
              congr 1
              funext R
              simpa [r] using
                (sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_eq_top_add_descendantsAverage
                  R s N u).symm

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_le_descendantsAverage_same_depth_of_memLp
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) (j N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      descendantsAverage Q j fun R =>
        (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2 := by
  induction j generalizing Q with
  | zero =>
      simp [descendantsAverage]
  | succ j ih =>
      have hstep :=
        sq_cubeBesovNegativeVectorPartialSeminormTwo_le_descendantsAverage_one_same_depth_of_memLp
          Q hs u hu N
      have hnext :
          descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) ≤
            descendantsAverage Q 1
              (fun R => descendantsAverage R j
                (fun S => (cubeBesovNegativeVectorPartialSeminormTwo S s N u) ^ 2)) := by
        refine descendantsAverage_le_descendantsAverage Q 1 ?_
        intro R hR
        have huR : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure R) :=
          memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
        exact ih R huR
      calc
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2
            ≤ descendantsAverage Q 1
                (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := hstep
        _ ≤ descendantsAverage Q 1
              (fun R => descendantsAverage R j
                (fun S => (cubeBesovNegativeVectorPartialSeminormTwo S s N u) ^ 2)) := hnext
        _ = descendantsAverage Q (j + 1)
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) := by
              rw [Nat.add_comm]
              rw [descendantsAverage_add_eq_descendantsAverage_descendantsAverage]

theorem cubeBesovNegativeVectorSeminormTwo_le_sqrt_descendantsAverage_sq_of_memLp_of_descendant_bddAbove
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) (j : ℕ)
    (hBdd : ∀ R ∈ descendantsAtDepth Q j,
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N u)) :
    cubeBesovNegativeVectorSeminormTwo Q s u ≤
      Real.sqrt (descendantsAverage Q j fun R =>
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s u ?_
  intro N
  have hsq_partial :=
    sq_cubeBesovNegativeVectorPartialSeminormTwo_le_descendantsAverage_same_depth_of_memLp
      Q hs u hu j N
  have havg_partial_full :
      descendantsAverage Q j
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) ≤
        descendantsAverage Q j
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hpartial_le_full :
        cubeBesovNegativeVectorPartialSeminormTwo R s N u ≤
          cubeBesovNegativeVectorSeminormTwo R s u := by
      unfold cubeBesovNegativeVectorSeminormTwo
      exact le_csSup (hBdd R hR) ⟨N, rfl⟩
    have hpartial_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo R s N u :=
      cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s N u
    have hfull_nonneg : 0 ≤ cubeBesovNegativeVectorSeminormTwo R s u := by
      have hzero_le : cubeBesovNegativeVectorPartialSeminormTwo R s 0 u ≤
          cubeBesovNegativeVectorSeminormTwo R s u := by
        unfold cubeBesovNegativeVectorSeminormTwo
        exact le_csSup (hBdd R hR) ⟨0, rfl⟩
      exact (cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s 0 u).trans hzero_le
    nlinarith
  have hsq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
        descendantsAverage Q j
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) :=
    hsq_partial.trans havg_partial_full
  have hpartial_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have havg_nonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) :=
    descendantsAverage_nonneg Q j _ fun _R _hR => sq_nonneg _
  exact (Real.le_sqrt hpartial_nonneg havg_nonneg).2 hsq

end

end Homogenization
