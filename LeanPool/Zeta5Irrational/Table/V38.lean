/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Energy
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.PotentialV
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V38: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_457 :
    ((1972960046410281505363 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7145675682770966266981 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6955420184827081 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3038638800749049350961 / 10000000000000000000000 : ℝ))) -
              6 * (16783522952507147781 / 156250000000000000000 : ℝ)))) ≤
      Vfield (19351147979 / 40000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19351147979 / 40000000000 : ℝ)) = Real.log (59351147979 / 40000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19351147979 / 40000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19576147979 / 40000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1972960046410281505363 / 5000000000000000000000 : ℝ) ≤
      Real.log (59351147979 / 40000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19576147979 / 40000000000 : ℝ) ≤
      (-(7145675682770966266981 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (19576147979 / 40000000000 : ℝ) = (19576147979 / 10000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19576147979 / 10000000000 : ℝ) ≤
            (6717267923229033733019 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6955420184827081 / 10000000000000000 : ℝ) ≤ Real.sqrt (19351147979 / 40000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19351147979 / 40000000000 : ℝ) ≤ (1738855046206771 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19351147979 / 40000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau686 :
    Real.arctan (3477710092413542 / 11090522759737049 : ℝ) ≤
      (3038638800749049350961 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau685 :
    Real.arctan (1738855046206771 / 2500000000000000 : ℝ) ≤
      (2 * (3038638800749049350961 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6090522759737049 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1738855046206771 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1738855046206771 / 2500000000000000 : ℝ) /
                (1 + (6090522759737049 / 5000000000000000 : ℝ)) =
              (3477710092413542 / 11090522759737049 : ℝ)
            by
        norm_num];
        exact hau686)
  have hat1 :
    (Real.pi / 2 - (2 * (3038638800749049350961 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1738855046206771 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1738855046206771 : ℝ) =
              (1738855046206771 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau685)
  have hz1 :
    (2500000000000000 / 1738855046206771 : ℝ) ≤ 1 / Real.sqrt (19351147979 / 40000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1738855046206771 : ℝ) = 1 / (1738855046206771 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6955420184827081 : ℝ) ≤
      (16783522952507147781 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19351147979 / 40000000000 : ℝ) ≤
      (750000000000000 / 6955420184827081 : ℝ) := by
    rw [show
        (750000000000000 / 6955420184827081 : ℝ) =
          (3 / 40) / (6955420184827081 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3038638800749049350961 / 10000000000000000000000 : ℝ))) -
        6 * (16783522952507147781 / 156250000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19351147979 / 40000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19351147979 / 40000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6955420184827081 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3038638800749049350961 / 10000000000000000000000 : ℝ))) -
          6 * (16783522952507147781 / 156250000000000000000 : ℝ))) ≤
      Real.sqrt (19351147979 / 40000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19351147979 / 40000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19351147979 / 40000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_458 :
    ((3963754549125513984239 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(709170268375400157447 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6974434021682331 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (304504032630575797579 / 1000000000000000000000 : ℝ))) -
              6 * (21424789892291219471 / 200000000000000000000 : ℝ)))) ≤
      Vfield (121606824807 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (121606824807 / 250000000000 : ℝ)) =
      Real.log (371606824807 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((121606824807 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (123013074807 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3963754549125513984239 / 10000000000000000000000 : ℝ) ≤
      Real.log (371606824807 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (123013074807 / 250000000000 : ℝ) ≤
      (-(709170268375400157447 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (123013074807 / 250000000000 : ℝ) = (123013074807 / 62500000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (123013074807 / 62500000000 : ℝ) ≤
            (677124092224599842553 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6974434021682331 / 10000000000000000 : ℝ) ≤ Real.sqrt (121606824807 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (121606824807 / 250000000000 : ℝ) ≤ (3487217010841167 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (121606824807 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau688 :
    Real.arctan (112490871317457 / 357934072259930 : ℝ) ≤
      (304504032630575797579 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau687 :
    Real.arctan (3487217010841167 / 5000000000000000 : ℝ) ≤
      (2 * (304504032630575797579 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (609595624005783 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3487217010841167 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3487217010841167 / 5000000000000000 : ℝ) /
                (1 + (609595624005783 / 500000000000000 : ℝ)) =
              (112490871317457 / 357934072259930 : ℝ)
            by
        norm_num];
        exact hau688)
  have hat1 :
    (Real.pi / 2 - (2 * (304504032630575797579 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3487217010841167 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3487217010841167 : ℝ) =
              (3487217010841167 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau687)
  have hz1 :
    (5000000000000000 / 3487217010841167 : ℝ) ≤ 1 / Real.sqrt (121606824807 / 250000000000 : ℝ) :=
  by
    rw [show
        (5000000000000000 / 3487217010841167 : ℝ) = 1 / (3487217010841167 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2324811340560777 : ℝ) ≤
      (21424789892291219471 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (121606824807 / 250000000000 : ℝ) ≤
      (250000000000000 / 2324811340560777 : ℝ) := by
    rw [show
        (250000000000000 / 2324811340560777 : ℝ) =
          (3 / 40) / (6974434021682331 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (304504032630575797579 / 1000000000000000000000 : ℝ))) -
        6 * (21424789892291219471 / 200000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (121606824807 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (121606824807 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6974434021682331 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (304504032630575797579 / 1000000000000000000000 : ℝ))) -
          6 * (21424789892291219471 / 200000000000000000000 : ℝ))) ≤
      Real.sqrt (121606824807 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (121606824807 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (121606824807 / 250000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_459 :
    ((995389313815897849753 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(703801943005654114471 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3496698081694357 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3051413081799342518727 / 10000000000000000000000 : ℝ))) -
              6 * (534178489479691317771 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (489075898981 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (489075898981 / 1000000000000 : ℝ)) =
      Real.log (1489075898981 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((489075898981 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (494700898981 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (995389313815897849753 / 2500000000000000000000 : ℝ) ≤
      Real.log (1489075898981 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (494700898981 / 1000000000000 : ℝ) ≤
      (-(703801943005654114471 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (494700898981 / 1000000000000 : ℝ) = (494700898981 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (494700898981 / 250000000000 : ℝ) ≤
            (682492417594345885529 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3496698081694357 / 5000000000000000 : ℝ) ≤ Real.sqrt (489075898981 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (489075898981 / 1000000000000 : ℝ) ≤ (6993396163388717 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (489075898981 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau690 :
    Real.arctan (6993396163388717 / 22202769763381590 : ℝ) ≤
      (3051413081799342518727 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau689 :
    Real.arctan (6993396163388717 / 10000000000000000 : ℝ) ≤
      (2 * (3051413081799342518727 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1220276976338159 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6993396163388717 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6993396163388717 / 10000000000000000 : ℝ) /
                (1 + (1220276976338159 / 1000000000000000 : ℝ)) =
              (6993396163388717 / 22202769763381590 : ℝ)
            by
        norm_num];
        exact hau690)
  have hat1 :
    (Real.pi / 2 - (2 * (3051413081799342518727 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6993396163388717 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6993396163388717 : ℝ) =
              (6993396163388717 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau689)
  have hz1 :
    (10000000000000000 / 6993396163388717 : ℝ) ≤
      1 / Real.sqrt (489075898981 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6993396163388717 : ℝ) =
          1 / (6993396163388717 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3496698081694357 : ℝ) ≤
      (534178489479691317771 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (489075898981 / 1000000000000 : ℝ) ≤
      (375000000000000 / 3496698081694357 : ℝ) := by
    rw [show
        (375000000000000 / 3496698081694357 : ℝ) =
          (3 / 40) / (3496698081694357 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3051413081799342518727 / 10000000000000000000000 : ℝ))) -
        6 * (534178489479691317771 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (489075898981 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (489075898981 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3496698081694357 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3051413081799342518727 / 10000000000000000000000 : ℝ))) -
          6 * (534178489479691317771 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (489075898981 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (489075898981 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (489075898981 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_460 :
    ((499916040510216863701 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(873077853422577693929 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1402461405863277 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3057757310175657760821 / 10000000000000000000000 : ℝ))) -
              6 * (213099521612080179629 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (245862249367 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (245862249367 / 500000000000 : ℝ)) =
      Real.log (745862249367 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((245862249367 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (248674749367 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (499916040510216863701 / 1250000000000000000000 : ℝ) ≤
      Real.log (745862249367 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (248674749367 / 500000000000 : ℝ) ≤
      (-(873077853422577693929 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (248674749367 / 500000000000 : ℝ) = (248674749367 / 125000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (248674749367 / 125000000000 : ℝ) ≤
            (859790097327422306071 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1402461405863277 / 2000000000000000 : ℝ) ≤ Real.sqrt (245862249367 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (245862249367 / 500000000000 : ℝ) ≤ (1753076757329097 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (245862249367 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau692 :
    Real.arctan (1753076757329097 / 5553404348769992 : ℝ) ≤
      (3057757310175657760821 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau691 :
    Real.arctan (1753076757329097 / 2500000000000000 : ℝ) ≤
      (2 * (3057757310175657760821 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (381675543596249 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (1753076757329097 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1753076757329097 / 2500000000000000 : ℝ) /
                (1 + (381675543596249 / 312500000000000 : ℝ)) =
              (1753076757329097 / 5553404348769992 : ℝ)
            by
        norm_num];
        exact hau692)
  have hat1 :
    (Real.pi / 2 - (2 * (3057757310175657760821 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1753076757329097 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1753076757329097 : ℝ) =
              (1753076757329097 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau691)
  have hz1 :
    (2500000000000000 / 1753076757329097 : ℝ) ≤ 1 / Real.sqrt (245862249367 / 500000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 1753076757329097 : ℝ) = 1 / (1753076757329097 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 467487135287759 : ℝ) ≤
      (213099521612080179629 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (245862249367 / 500000000000 : ℝ) ≤
      (50000000000000 / 467487135287759 : ℝ) := by
    rw [show
        (50000000000000 / 467487135287759 : ℝ) =
          (3 / 40) / (1402461405863277 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3057757310175657760821 / 10000000000000000000000 : ℝ))) -
        6 * (213099521612080179629 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (245862249367 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (245862249367 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1402461405863277 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3057757310175657760821 / 10000000000000000000000 : ℝ))) -
          6 * (213099521612080179629 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (245862249367 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (245862249367 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (245862249367 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_461 :
    ((4017067867826327729629 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6931509830732862114179 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7031167033195839 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1532036625599493404347 / 5000000000000000000000 : ℝ))) -
              6 * (132832634229193100987 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (494373098487 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (494373098487 / 1000000000000 : ℝ)) =
      Real.log (1494373098487 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((494373098487 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (499998098487 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4017067867826327729629 / 10000000000000000000000 : ℝ) ≤
      Real.log (1494373098487 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (499998098487 / 1000000000000 : ℝ) ≤
      (-(6931509830732862114179 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (499998098487 / 1000000000000 : ℝ) = (499998098487 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (499998098487 / 250000000000 : ℝ) ≤
            (6931433775267137885821 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7031167033195839 / 10000000000000000 : ℝ) ≤ Real.sqrt (494373098487 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (494373098487 / 1000000000000 : ℝ) ≤ (3515583516597921 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (494373098487 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau694 :
    Real.arctan (1171861172199307 / 3704075900150728 : ℝ) ≤
      (1532036625599493404347 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau693 :
    Real.arctan (3515583516597921 / 5000000000000000 : ℝ) ≤
      (2 * (1532036625599493404347 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (764028462556523 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (3515583516597921 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3515583516597921 / 5000000000000000 : ℝ) /
                (1 + (764028462556523 / 625000000000000 : ℝ)) =
              (1171861172199307 / 3704075900150728 : ℝ)
            by
        norm_num];
        exact hau694)
  have hat1 :
    (Real.pi / 2 - (2 * (1532036625599493404347 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3515583516597921 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3515583516597921 : ℝ) =
              (3515583516597921 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau693)
  have hz1 :
    (5000000000000000 / 3515583516597921 : ℝ) ≤
      1 / Real.sqrt (494373098487 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3515583516597921 : ℝ) = 1 / (3515583516597921 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2343722344398613 : ℝ) ≤
      (132832634229193100987 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (494373098487 / 1000000000000 : ℝ) ≤
      (250000000000000 / 2343722344398613 : ℝ) := by
    rw [show
        (250000000000000 / 2343722344398613 : ℝ) =
          (3 / 40) / (7031167033195839 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1532036625599493404347 / 5000000000000000000000 : ℝ))) -
        6 * (132832634229193100987 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (494373098487 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (494373098487 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7031167033195839 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1532036625599493404347 / 5000000000000000000000 : ℝ))) -
          6 * (132832634229193100987 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (494373098487 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (494373098487 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (494373098487 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_462 :
    ((4034775998147450528869 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1719669361495489087719 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((44062353645147 / 62500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (383795142688735162467 / 1250000000000000000000 : ℝ))) -
              6 * (1059847073905755610613 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1553192807 / 3125000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1553192807 / 3125000000 : ℝ)) = Real.log (4678192807 / 3125000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((1553192807 / 3125000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (392692733 / 781250000 : ℝ) :=
    by norm_num
  have hL1 :
    (4034775998147450528869 / 10000000000000000000000 : ℝ) ≤
      Real.log (4678192807 / 3125000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (392692733 / 781250000 : ℝ) ≤
      (-(1719669361495489087719 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (392692733 / 781250000 : ℝ) = (392692733 / 390625000 : ℝ) / 2 ^ 1 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (392692733 / 390625000 : ℝ) ≤
            (13198589254510912281 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo : (44062353645147 / 62500000000000 : ℝ) ≤ Real.sqrt (1553192807 / 3125000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1553192807 / 3125000000 : ℝ) ≤ (7049976583223523 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1553192807 / 3125000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau696 :
    Real.arctan (7049976583223523 / 22235283806434568 : ℝ) ≤
      (383795142688735162467 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau695 :
    Real.arctan (7049976583223523 / 10000000000000000 : ℝ) ≤
      (2 * (383795142688735162467 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1529410475804321 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (7049976583223523 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7049976583223523 / 10000000000000000 : ℝ) /
                (1 + (1529410475804321 / 1250000000000000 : ℝ)) =
              (7049976583223523 / 22235283806434568 : ℝ)
            by
        norm_num];
        exact hau696)
  have hat1 :
    (Real.pi / 2 - (2 * (383795142688735162467 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7049976583223523 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7049976583223523 : ℝ) =
              (7049976583223523 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau695)
  have hz1 :
    (10000000000000000 / 7049976583223523 : ℝ) ≤ 1 / Real.sqrt (1553192807 / 3125000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7049976583223523 : ℝ) =
          1 / (7049976583223523 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (1562500000000 / 14687451215049 : ℝ) ≤
      (1059847073905755610613 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1553192807 / 3125000000 : ℝ) ≤ (1562500000000 / 14687451215049 : ℝ) := by
    rw [show
        (1562500000000 / 14687451215049 : ℝ) = (3 / 40) / (44062353645147 / 62500000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (383795142688735162467 / 1250000000000000000000 : ℝ))) -
        6 * (1059847073905755610613 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1553192807 / 3125000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1553192807 / 3125000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((44062353645147 / 62500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (383795142688735162467 / 1250000000000000000000 : ℝ))) -
          6 * (1059847073905755610613 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1553192807 / 3125000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1553192807 / 3125000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1553192807 / 3125000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_463 :
    ((4052452826103097732711 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6826122718446278959801 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((70687360821649 / 100000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (769155303670411559609 / 2500000000000000000000 : ℝ))) -
              6 * (105705531147958899277 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (499670297993 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (499670297993 / 1000000000000 : ℝ)) =
      Real.log (1499670297993 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((499670297993 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (505295297993 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4052452826103097732711 / 10000000000000000000000 : ℝ) ≤
      Real.log (1499670297993 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (505295297993 / 1000000000000 : ℝ) ≤
      (-(6826122718446278959801 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (505295297993 / 1000000000000 : ℝ) = (505295297993 / 500000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (505295297993 / 500000000000 : ℝ) ≤
            (105349084553721040199 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (70687360821649 / 100000000000000 : ℝ) ≤ Real.sqrt (499670297993 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (499670297993 / 1000000000000 : ℝ) ≤ (7068736082164903 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (499670297993 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau698 :
    Real.arctan (7068736082164903 / 22246102637137253 : ℝ) ≤
      (769155303670411559609 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau697 :
    Real.arctan (7068736082164903 / 10000000000000000 : ℝ) ≤
      (2 * (769155303670411559609 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12246102637137253 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7068736082164903 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7068736082164903 / 10000000000000000 : ℝ) /
                (1 + (12246102637137253 / 10000000000000000 : ℝ)) =
              (7068736082164903 / 22246102637137253 : ℝ)
            by
        norm_num];
        exact hau698)
  have hat1 :
    (Real.pi / 2 - (2 * (769155303670411559609 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7068736082164903 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7068736082164903 : ℝ) =
              (7068736082164903 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau697)
  have hz1 :
    (10000000000000000 / 7068736082164903 : ℝ) ≤
      1 / Real.sqrt (499670297993 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7068736082164903 : ℝ) =
          1 / (7068736082164903 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (7500000000000 / 70687360821649 : ℝ) ≤
      (105705531147958899277 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (499670297993 / 1000000000000 : ℝ) ≤
      (7500000000000 / 70687360821649 : ℝ) := by
    rw [show
        (7500000000000 / 70687360821649 : ℝ) = (3 / 40) / (70687360821649 / 100000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (769155303670411559609 / 2500000000000000000000 : ℝ))) -
        6 * (105705531147958899277 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (499670297993 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (499670297993 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((70687360821649 / 100000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (769155303670411559609 / 2500000000000000000000 : ℝ))) -
          6 * (105705531147958899277 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (499670297993 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (499670297993 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (499670297993 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_464 :
    ((4087713016214549625359 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3360917337612814841707 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3553053255648583 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1544529414447257797889 / 5000000000000000000000 : ℝ))) -
              6 * (210307467807043208833 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (504967497499 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (504967497499 / 1000000000000 : ℝ)) =
      Real.log (1504967497499 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((504967497499 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (510592497499 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4087713016214549625359 / 10000000000000000000000 : ℝ) ≤
      Real.log (1504967497499 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (510592497499 / 1000000000000 : ℝ) ≤
      (-(3360917337612814841707 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (510592497499 / 1000000000000 : ℝ) = (510592497499 / 500000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (510592497499 / 500000000000 : ℝ) ≤
            (104818563887185158293 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3553053255648583 / 5000000000000000 : ℝ) ≤ Real.sqrt (504967497499 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (504967497499 / 1000000000000 : ℝ) ≤ (7106106511297169 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (504967497499 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau700 :
    Real.arctan (7106106511297169 / 22267711675365540 : ℝ) ≤
      (1544529414447257797889 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau699 :
    Real.arctan (7106106511297169 / 10000000000000000 : ℝ) ≤
      (2 * (1544529414447257797889 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (613385583768277 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (7106106511297169 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7106106511297169 / 10000000000000000 : ℝ) /
                (1 + (613385583768277 / 500000000000000 : ℝ)) =
              (7106106511297169 / 22267711675365540 : ℝ)
            by
        norm_num];
        exact hau700)
  have hat1 :
    (Real.pi / 2 - (2 * (1544529414447257797889 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7106106511297169 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7106106511297169 : ℝ) =
              (7106106511297169 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau699)
  have hz1 :
    (10000000000000000 / 7106106511297169 : ℝ) ≤
      1 / Real.sqrt (504967497499 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7106106511297169 : ℝ) =
          1 / (7106106511297169 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3553053255648583 : ℝ) ≤
      (210307467807043208833 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (504967497499 / 1000000000000 : ℝ) ≤
      (375000000000000 / 3553053255648583 : ℝ) := by
    rw [show
        (375000000000000 / 3553053255648583 : ℝ) =
          (3 / 40) / (3553053255648583 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1544529414447257797889 / 5000000000000000000000 : ℝ))) -
        6 * (210307467807043208833 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (504967497499 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (504967497499 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3553053255648583 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1544529414447257797889 / 5000000000000000000000 : ℝ))) -
          6 * (210307467807043208833 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (504967497499 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (504967497499 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (504967497499 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_465 :
    ((4122849314940802649517 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6618623015859148835301 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1785820359465433 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1550693951571935343901 / 5000000000000000000000 : ℝ))) -
              6 * (209220977745917649767 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (102052939401 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (102052939401 / 200000000000 : ℝ)) =
      Real.log (302052939401 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((102052939401 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (103177939401 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4122849314940802649517 / 10000000000000000000000 : ℝ) ≤
      Real.log (302052939401 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (103177939401 / 200000000000 : ℝ) ≤
      (-(6618623015859148835301 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (103177939401 / 200000000000 : ℝ) = (103177939401 / 100000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (103177939401 / 100000000000 : ℝ) ≤
            (312848787140851164699 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1785820359465433 / 2500000000000000 : ℝ) ≤ Real.sqrt (102052939401 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (102052939401 / 200000000000 : ℝ) ≤ (1428656287572347 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (102052939401 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau702 :
    Real.arctan (7143281437861735 / 22289282717087274 : ℝ) ≤
      (1550693951571935343901 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau701 :
    Real.arctan (1428656287572347 / 2000000000000000 : ℝ) ≤
      (2 * (1550693951571935343901 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6144641358543637 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1428656287572347 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1428656287572347 / 2000000000000000 : ℝ) /
                (1 + (6144641358543637 / 5000000000000000 : ℝ)) =
              (7143281437861735 / 22289282717087274 : ℝ)
            by
        norm_num];
        exact hau702)
  have hat1 :
    (Real.pi / 2 - (2 * (1550693951571935343901 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1428656287572347 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1428656287572347 : ℝ) =
              (1428656287572347 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau701)
  have hz1 :
    (2000000000000000 / 1428656287572347 : ℝ) ≤ 1 / Real.sqrt (102052939401 / 200000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 1428656287572347 : ℝ) = 1 / (1428656287572347 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1785820359465433 : ℝ) ≤
      (209220977745917649767 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (102052939401 / 200000000000 : ℝ) ≤
      (187500000000000 / 1785820359465433 : ℝ) := by
    rw [show
        (187500000000000 / 1785820359465433 : ℝ) =
          (3 / 40) / (1785820359465433 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1550693951571935343901 / 5000000000000000000000 : ℝ))) -
        6 * (209220977745917649767 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (102052939401 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (102052939401 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1785820359465433 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1550693951571935343901 / 5000000000000000000000 : ℝ))) -
          6 * (209220977745917649767 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (102052939401 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (102052939401 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (102052939401 / 200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_466 :
    ((4157862589852264614611 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1629116436967895470151 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1436052779686039 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3113610201061039069011 / 10000000000000000000000 : ℝ))) -
              6 * (520377886983577812947 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (515561896511 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (515561896511 / 1000000000000 : ℝ)) =
      Real.log (1515561896511 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((515561896511 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (521186896511 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4157862589852264614611 / 10000000000000000000000 : ℝ) ≤
      Real.log (1515561896511 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (521186896511 / 1000000000000 : ℝ) ≤
      (-(1629116436967895470151 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (521186896511 / 1000000000000 : ℝ) = (521186896511 / 500000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (521186896511 / 500000000000 : ℝ) ≤
            (103751513782104529849 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1436052779686039 / 2000000000000000 : ℝ) ≤ Real.sqrt (515561896511 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (515561896511 / 1000000000000 : ℝ) ≤ (3590131949215099 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (515561896511 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau704 :
    Real.arctan (3590131949215099 / 11155407981017586 : ℝ) ≤
      (3113610201061039069011 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau703 :
    Real.arctan (3590131949215099 / 5000000000000000 : ℝ) ≤
      (2 * (3113610201061039069011 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3077703990508793 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3590131949215099 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3590131949215099 / 5000000000000000 : ℝ) /
                (1 + (3077703990508793 / 2500000000000000 : ℝ)) =
              (3590131949215099 / 11155407981017586 : ℝ)
            by
        norm_num];
        exact hau704)
  have hat1 :
    (Real.pi / 2 - (2 * (3113610201061039069011 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3590131949215099 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3590131949215099 : ℝ) =
              (3590131949215099 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau703)
  have hz1 :
    (5000000000000000 / 3590131949215099 : ℝ) ≤
      1 / Real.sqrt (515561896511 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3590131949215099 : ℝ) = 1 / (3590131949215099 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1436052779686039 : ℝ) ≤
      (520377886983577812947 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (515561896511 / 1000000000000 : ℝ) ≤
      (150000000000000 / 1436052779686039 : ℝ) := by
    rw [show
        (150000000000000 / 1436052779686039 : ℝ) =
          (3 / 40) / (1436052779686039 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3113610201061039069011 / 10000000000000000000000 : ℝ))) -
        6 * (520377886983577812947 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (515561896511 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (515561896511 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1436052779686039 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3113610201061039069011 / 10000000000000000000000 : ℝ))) -
          6 * (520377886983577812947 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (515561896511 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (515561896511 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (515561896511 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_467 :
    ((834864249188940764473 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6468680488511488354407 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((899703389990447 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (623866760360916799687 / 2000000000000000000000 : ℝ))) -
              6 * (1038263128909289262889 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (16577867570387 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (16577867570387 / 32000000000000 : ℝ)) =
      Real.log (48577867570387 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((16577867570387 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (16757867570387 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (834864249188940764473 / 2000000000000000000000 : ℝ) ≤
      Real.log (48577867570387 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (16757867570387 / 32000000000000 : ℝ) ≤
      (-(6468680488511488354407 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16757867570387 / 32000000000000 : ℝ) = (16757867570387 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16757867570387 / 16000000000000 : ℝ) ≤
            (462791314488511645593 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (899703389990447 / 1250000000000000 : ℝ) ≤ Real.sqrt (16577867570387 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (16577867570387 / 32000000000000 : ℝ) ≤
      (7197627119923579 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (16577867570387 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau706 :
    Real.arctan (7197627119923579 / 22320951106041260 : ℝ) ≤
      (623866760360916799687 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau705 :
    Real.arctan (7197627119923579 / 10000000000000000 : ℝ) ≤
      (2 * (623866760360916799687 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (616047555302063 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (7197627119923579 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7197627119923579 / 10000000000000000 : ℝ) /
                (1 + (616047555302063 / 500000000000000 : ℝ)) =
              (7197627119923579 / 22320951106041260 : ℝ)
            by
        norm_num];
        exact hau706)
  have hat1 :
    (Real.pi / 2 - (2 * (623866760360916799687 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7197627119923579 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7197627119923579 : ℝ) =
              (7197627119923579 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau705)
  have hz1 :
    (10000000000000000 / 7197627119923579 : ℝ) ≤
      1 / Real.sqrt (16577867570387 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7197627119923579 : ℝ) =
          1 / (7197627119923579 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 899703389990447 : ℝ) ≤
      (1038263128909289262889 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (16577867570387 / 32000000000000 : ℝ) ≤
      (93750000000000 / 899703389990447 : ℝ) := by
    rw [show
        (93750000000000 / 899703389990447 : ℝ) =
          (3 / 40) / (899703389990447 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (623866760360916799687 / 2000000000000000000000 : ℝ))) -
        6 * (1038263128909289262889 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (16577867570387 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (16577867570387 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((899703389990447 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (623866760360916799687 / 2000000000000000000000 : ℝ))) -
          6 * (1038263128909289262889 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (16577867570387 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (16577867570387 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (16577867570387 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_468 :
    ((1047688214451545209707 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3210561243363384980221 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7214948555867791 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3125034246207891380201 / 10000000000000000000000 : ℝ))) -
              6 * (103578830857744472109 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (8328877226211 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8328877226211 / 16000000000000 : ℝ)) =
      Real.log (24328877226211 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8328877226211 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8418877226211 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1047688214451545209707 / 2500000000000000000000 : ℝ) ≤
      Real.log (24328877226211 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8418877226211 / 16000000000000 : ℝ) ≤
      (-(3210561243363384980221 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8418877226211 / 16000000000000 : ℝ) = (8418877226211 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8418877226211 / 8000000000000 : ℝ) ≤
            (255174658136615019779 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7214948555867791 / 10000000000000000 : ℝ) ≤ Real.sqrt (8328877226211 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8328877226211 / 16000000000000 : ℝ) ≤ (3607474277933897 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8328877226211 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau708 :
    Real.arctan (3607474277933897 / 11165538959892694 : ℝ) ≤
      (3125034246207891380201 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau707 :
    Real.arctan (3607474277933897 / 5000000000000000 : ℝ) ≤
      (2 * (3125034246207891380201 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3082769479946347 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3607474277933897 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3607474277933897 / 5000000000000000 : ℝ) /
                (1 + (3082769479946347 / 2500000000000000 : ℝ)) =
              (3607474277933897 / 11165538959892694 : ℝ)
            by
        norm_num];
        exact hau708)
  have hat1 :
    (Real.pi / 2 - (2 * (3125034246207891380201 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3607474277933897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3607474277933897 : ℝ) =
              (3607474277933897 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau707)
  have hz1 :
    (5000000000000000 / 3607474277933897 : ℝ) ≤
      1 / Real.sqrt (8328877226211 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3607474277933897 : ℝ) = 1 / (3607474277933897 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7214948555867791 : ℝ) ≤
      (103578830857744472109 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8328877226211 / 16000000000000 : ℝ) ≤
      (750000000000000 / 7214948555867791 : ℝ) := by
    rw [show
        (750000000000000 / 7214948555867791 : ℝ) =
          (3 / 40) / (7214948555867791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3125034246207891380201 / 10000000000000000000000 : ℝ))) -
        6 * (103578830857744472109 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8328877226211 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8328877226211 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7214948555867791 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3125034246207891380201 / 10000000000000000000000 : ℝ))) -
          6 * (103578830857744472109 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (8328877226211 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8328877226211 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8328877226211 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
