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

/-! # V20: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_241 :
    ((916213007214556584881 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15763379946783387163977 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((280280107331961 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (526953344135841385621 / 1250000000000000000000 : ℝ)) -
              6 * (828548887056965813683 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (201105762729 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (201105762729 / 1000000000000 : ℝ)) =
      Real.log (1201105762729 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((201105762729 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (206730762729 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (916213007214556584881 / 5000000000000000000000 : ℝ) ≤
      Real.log (1201105762729 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (206730762729 / 1000000000000 : ℝ) ≤
      (-(15763379946783387163977 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (206730762729 / 1000000000000 : ℝ) = (206730762729 / 125000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (206730762729 / 125000000000 : ℝ) ≤
            (5031035462216612836023 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (280280107331961 / 625000000000000 : ℝ) ≤ Real.sqrt (201105762729 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (201105762729 / 1000000000000 : ℝ) ≤ (4484481717311379 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (201105762729 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau303 :
    Real.arctan (4484481717311379 / 10000000000000000 : ℝ) ≤
      (526953344135841385621 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (526953344135841385621 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4484481717311379 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4484481717311379 : ℝ) =
              (4484481717311379 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau303)
  have hz1 :
    (10000000000000000 / 4484481717311379 : ℝ) ≤
      1 / Real.sqrt (201105762729 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4484481717311379 : ℝ) =
          1 / (4484481717311379 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (15625000000000 / 93426702443987 : ℝ) ≤
      (828548887056965813683 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (201105762729 / 1000000000000 : ℝ) ≤
      (15625000000000 / 93426702443987 : ℝ) := by
    rw [show
        (15625000000000 / 93426702443987 : ℝ) = (3 / 40) / (280280107331961 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (526953344135841385621 / 1250000000000000000000 : ℝ)) -
        6 * (828548887056965813683 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (201105762729 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (201105762729 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((280280107331961 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (526953344135841385621 / 1250000000000000000000 : ℝ)) -
          6 * (828548887056965813683 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (201105762729 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (201105762729 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (201105762729 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_242 :
    ((925082402975123894543 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(978797156642601188271 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4508195537539797 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
              6 * (1648538651467957972391 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3251812320751 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3251812320751 / 16000000000000 : ℝ)) =
      Real.log (19251812320751 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3251812320751 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3341812320751 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (925082402975123894543 / 5000000000000000000000 : ℝ) ≤
      Real.log (19251812320751 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3341812320751 / 16000000000000 : ℝ) ≤
      (-(978797156642601188271 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3341812320751 / 16000000000000 : ℝ) = (3341812320751 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3341812320751 / 2000000000000 : ℝ) ≤
            (320853806419898811729 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4508195537539797 / 10000000000000000 : ℝ) ≤ Real.sqrt (3251812320751 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3251812320751 / 16000000000000 : ℝ) ≤ (22540977687699 / 50000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3251812320751 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau304 :
    Real.arctan (22540977687699 / 50000000000000 : ℝ) ≤
      (132354768328260144823 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (50000000000000 / 22540977687699 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 22540977687699 : ℝ) =
              (22540977687699 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hau304)
  have hz1 :
    (50000000000000 / 22540977687699 : ℝ) ≤ 1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ) := by
    rw [show (50000000000000 / 22540977687699 : ℝ) = 1 / (22540977687699 / 50000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1502731845846599 : ℝ) ≤
      (1648538651467957972391 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ) ≤
      (250000000000000 / 1502731845846599 : ℝ) := by
    rw [show
        (250000000000000 / 1502731845846599 : ℝ) =
          (3 / 40) / (4508195537539797 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
        6 * (1648538651467957972391 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4508195537539797 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (132354768328260144823 / 312500000000000000000 : ℝ)) -
          6 * (1648538651467957972391 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3251812320751 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3251812320751 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3251812320751 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_243 :
    ((233484023338699112559 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15559171574152312277573 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((906357054068373 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2127470226874638958149 / 5000000000000000000000 : ℝ)) -
              6 * (205013851103837126691 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (1642966218919 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1642966218919 / 8000000000000 : ℝ)) =
      Real.log (9642966218919 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1642966218919 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1687966218919 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (233484023338699112559 / 1250000000000000000000 : ℝ) ≤
      Real.log (9642966218919 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1687966218919 / 8000000000000 : ℝ) ≤
      (-(15559171574152312277573 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1687966218919 / 8000000000000 : ℝ) = (1687966218919 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1687966218919 / 1000000000000 : ℝ) ≤
            (5235243834847687722427 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (906357054068373 / 2000000000000000 : ℝ) ≤ Real.sqrt (1642966218919 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1642966218919 / 8000000000000 : ℝ) ≤ (1132946317585467 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1642966218919 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau305 :
    Real.arctan (1132946317585467 / 2500000000000000 : ℝ) ≤
      (2127470226874638958149 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2127470226874638958149 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1132946317585467 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1132946317585467 : ℝ) =
              (1132946317585467 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau305)
  have hz1 :
    (2500000000000000 / 1132946317585467 : ℝ) ≤
      1 / Real.sqrt (1642966218919 / 8000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1132946317585467 : ℝ) = 1 / (1132946317585467 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 302119018022791 : ℝ) ≤
      (205013851103837126691 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1642966218919 / 8000000000000 : ℝ) ≤
      (50000000000000 / 302119018022791 : ℝ) := by
    rw [show
        (50000000000000 / 302119018022791 : ℝ) =
          (3 / 40) / (906357054068373 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2127470226874638958149 / 5000000000000000000000 : ℝ)) -
        6 * (205013851103837126691 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1642966218919 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1642966218919 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((906357054068373 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2127470226874638958149 / 5000000000000000000000 : ℝ)) -
          6 * (205013851103837126691 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (1642966218919 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1642966218919 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1642966218919 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_244 :
    ((942774133875520337323 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15458610182818172849901 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((569406605438411 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (427439244048937257737 / 1000000000000000000000 : ℝ)) -
              6 * (326362184796567935759 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (132802102197 / 640000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (132802102197 / 640000000000 : ℝ)) =
      Real.log (772802102197 / 640000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((132802102197 / 640000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (136402102197 / 640000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (942774133875520337323 / 5000000000000000000000 : ℝ) ≤
      Real.log (772802102197 / 640000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (136402102197 / 640000000000 : ℝ) ≤
      (-(15458610182818172849901 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (136402102197 / 640000000000 : ℝ) = (136402102197 / 80000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (136402102197 / 80000000000 : ℝ) ≤
            (5335805226181827150099 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (569406605438411 / 1250000000000000 : ℝ) ≤ Real.sqrt (132802102197 / 640000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (132802102197 / 640000000000 : ℝ) ≤ (4555252843507291 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (132802102197 / 640000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau306 :
    Real.arctan (4555252843507291 / 10000000000000000 : ℝ) ≤
      (427439244048937257737 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (427439244048937257737 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4555252843507291 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4555252843507291 : ℝ) =
              (4555252843507291 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau306)
  have hz1 :
    (10000000000000000 / 4555252843507291 : ℝ) ≤
      1 / Real.sqrt (132802102197 / 640000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4555252843507291 : ℝ) =
          1 / (4555252843507291 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 569406605438411 : ℝ) ≤
      (326362184796567935759 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (132802102197 / 640000000000 : ℝ) ≤
      (93750000000000 / 569406605438411 : ℝ) := by
    rw [show
        (93750000000000 / 569406605438411 : ℝ) =
          (3 / 40) / (569406605438411 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (427439244048937257737 / 1000000000000000000000 : ℝ)) -
        6 * (326362184796567935759 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (132802102197 / 640000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (132802102197 / 640000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((569406605438411 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (427439244048937257737 / 1000000000000000000000 : ℝ)) -
          6 * (326362184796567935759 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (132802102197 / 640000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (132802102197 / 640000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (132802102197 / 640000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_245 :
    ((473593651354481801167 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15408706184512598421353 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4566941409102827 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1071017029048578874257 / 2500000000000000000000 : ℝ)) -
              6 * (325541591908918348673 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (6674225226937 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6674225226937 / 32000000000000 : ℝ)) =
      Real.log (38674225226937 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6674225226937 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6854225226937 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (473593651354481801167 / 2500000000000000000000 : ℝ) ≤
      Real.log (38674225226937 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6854225226937 / 32000000000000 : ℝ) ≤
      (-(15408706184512598421353 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (6854225226937 / 32000000000000 : ℝ) = (6854225226937 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6854225226937 / 4000000000000 : ℝ) ≤
            (5385709224487401578647 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4566941409102827 / 10000000000000000 : ℝ) ≤ Real.sqrt (6674225226937 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6674225226937 / 32000000000000 : ℝ) ≤ (456694140910283 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6674225226937 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau307 :
    Real.arctan (456694140910283 / 1000000000000000 : ℝ) ≤
      (1071017029048578874257 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1071017029048578874257 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 456694140910283 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 456694140910283 : ℝ) =
              (456694140910283 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau307)
  have hz1 :
    (1000000000000000 / 456694140910283 : ℝ) ≤
      1 / Real.sqrt (6674225226937 / 32000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 456694140910283 : ℝ) = 1 / (456694140910283 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4566941409102827 : ℝ) ≤
      (325541591908918348673 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6674225226937 / 32000000000000 : ℝ) ≤
      (750000000000000 / 4566941409102827 : ℝ) := by
    rw [show
        (750000000000000 / 4566941409102827 : ℝ) =
          (3 / 40) / (4566941409102827 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1071017029048578874257 / 2500000000000000000000 : ℝ)) -
        6 * (325541591908918348673 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6674225226937 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6674225226937 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4566941409102827 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1071017029048578874257 / 2500000000000000000000 : ℝ)) -
          6 * (325541591908918348673 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (6674225226937 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6674225226937 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6674225226937 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_246 :
    ((380638631906135117007 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3071809998195709492653 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2289300067710379 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (268356911279549160589 / 625000000000000000000 : ℝ)) -
              6 * (1623635791236049692747 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (838543168003 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (838543168003 / 4000000000000 : ℝ)) =
      Real.log (4838543168003 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((838543168003 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (861043168003 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (380638631906135117007 / 2000000000000000000000 : ℝ) ≤
      Real.log (4838543168003 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (861043168003 / 4000000000000 : ℝ) ≤
      (-(3071809998195709492653 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (861043168003 / 4000000000000 : ℝ) = (861043168003 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (861043168003 / 500000000000 : ℝ) ≤
            (1087073083604290507347 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2289300067710379 / 5000000000000000 : ℝ) ≤ Real.sqrt (838543168003 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (838543168003 / 4000000000000 : ℝ) ≤ (4578600135420761 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (838543168003 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau308 :
    Real.arctan (4578600135420761 / 10000000000000000 : ℝ) ≤
      (268356911279549160589 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (268356911279549160589 / 625000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4578600135420761 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4578600135420761 : ℝ) =
              (4578600135420761 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau308)
  have hz1 :
    (10000000000000000 / 4578600135420761 : ℝ) ≤
      1 / Real.sqrt (838543168003 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4578600135420761 : ℝ) =
          1 / (4578600135420761 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2289300067710379 : ℝ) ≤
      (1623635791236049692747 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (838543168003 / 4000000000000 : ℝ) ≤
      (375000000000000 / 2289300067710379 : ℝ) := by
    rw [show
        (375000000000000 / 2289300067710379 : ℝ) =
          (3 / 40) / (2289300067710379 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (268356911279549160589 / 625000000000000000000 : ℝ)) -
        6 * (1623635791236049692747 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (838543168003 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (838543168003 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2289300067710379 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (268356911279549160589 / 625000000000000000000 : ℝ)) -
          6 * (1623635791236049692747 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (838543168003 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (838543168003 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (838543168003 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_247 :
    ((956001971902565436247 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3061927830671543104789 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1147557312456873 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1075830019932161256039 / 2500000000000000000000 : ℝ)) -
              6 * (1619594035700487665621 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (6742465461111 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6742465461111 / 32000000000000 : ℝ)) =
      Real.log (38742465461111 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6742465461111 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6922465461111 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (956001971902565436247 / 5000000000000000000000 : ℝ) ≤
      Real.log (38742465461111 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6922465461111 / 32000000000000 : ℝ) ≤
      (-(3061927830671543104789 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (6922465461111 / 32000000000000 : ℝ) = (6922465461111 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6922465461111 / 4000000000000 : ℝ) ≤
            (1096955251128456895211 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1147557312456873 / 2500000000000000 : ℝ) ≤ Real.sqrt (6742465461111 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6742465461111 / 32000000000000 : ℝ) ≤ (918045849965499 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6742465461111 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau309 :
    Real.arctan (918045849965499 / 2000000000000000 : ℝ) ≤
      (1075830019932161256039 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1075830019932161256039 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 918045849965499 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 918045849965499 : ℝ) =
              (918045849965499 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau309)
  have hz1 :
    (2000000000000000 / 918045849965499 : ℝ) ≤
      1 / Real.sqrt (6742465461111 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 918045849965499 : ℝ) = 1 / (918045849965499 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 382519104152291 : ℝ) ≤
      (1619594035700487665621 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6742465461111 / 32000000000000 : ℝ) ≤
      (62500000000000 / 382519104152291 : ℝ) := by
    rw [show
        (62500000000000 / 382519104152291 : ℝ) =
          (3 / 40) / (1147557312456873 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1075830019932161256039 / 2500000000000000000000 : ℝ)) -
        6 * (1619594035700487665621 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6742465461111 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6742465461111 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1147557312456873 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1075830019932161256039 / 2500000000000000000000 : ℝ)) -
          6 * (1619594035700487665621 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (6742465461111 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6742465461111 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6742465461111 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_248 :
    ((30012608936264309779 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15260471258913580618157 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4601828976816581 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (215644842867158688389 / 500000000000000000000 : ℝ)) -
              6 * (64623292649177857249 / 400000000000000000000 : ℝ)))) ≤
      Vfield (3388292789099 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3388292789099 / 16000000000000 : ℝ)) =
      Real.log (19388292789099 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3388292789099 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3478292789099 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (30012608936264309779 / 156250000000000000000 : ℝ) ≤
      Real.log (19388292789099 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3478292789099 / 16000000000000 : ℝ) ≤
      (-(15260471258913580618157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3478292789099 / 16000000000000 : ℝ) = (3478292789099 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3478292789099 / 2000000000000 : ℝ) ≤
            (5533944150086419381843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4601828976816581 / 10000000000000000 : ℝ) ≤ Real.sqrt (3388292789099 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3388292789099 / 16000000000000 : ℝ) ≤ (575228622102073 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3388292789099 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau310 :
    Real.arctan (575228622102073 / 1250000000000000 : ℝ) ≤
      (215644842867158688389 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (215644842867158688389 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 575228622102073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 575228622102073 : ℝ) =
              (575228622102073 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau310)
  have hz1 :
    (1250000000000000 / 575228622102073 : ℝ) ≤
      1 / Real.sqrt (3388292789099 / 16000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 575228622102073 : ℝ) = 1 / (575228622102073 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4601828976816581 : ℝ) ≤
      (64623292649177857249 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3388292789099 / 16000000000000 : ℝ) ≤
      (750000000000000 / 4601828976816581 : ℝ) := by
    rw [show
        (750000000000000 / 4601828976816581 : ℝ) =
          (3 / 40) / (4601828976816581 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (215644842867158688389 / 500000000000000000000 : ℝ)) -
        6 * (64623292649177857249 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3388292789099 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3388292789099 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4601828976816581 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (215644842867158688389 / 500000000000000000000 : ℝ)) -
          6 * (64623292649177857249 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (3388292789099 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3388292789099 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3388292789099 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_249 :
    ((1929602257521558340209 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1901442991290557573503 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1153349884514821 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (86448823074548479773 / 200000000000000000000 : ℝ)) -
              6 * (805800131307608396503 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1362141139057 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1362141139057 / 6400000000000 : ℝ)) =
      Real.log (7762141139057 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1362141139057 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1398141139057 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1929602257521558340209 / 10000000000000000000000 : ℝ) ≤
      Real.log (7762141139057 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1398141139057 / 6400000000000 : ℝ) ≤
      (-(1901442991290557573503 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1398141139057 / 6400000000000 : ℝ) = (1398141139057 / 800000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1398141139057 / 800000000000 : ℝ) ≤
            (697858934834442426497 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1153349884514821 / 2500000000000000 : ℝ) ≤ Real.sqrt (1362141139057 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1362141139057 / 6400000000000 : ℝ) ≤ (4613399538059287 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1362141139057 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau311 :
    Real.arctan (4613399538059287 / 10000000000000000 : ℝ) ≤
      (86448823074548479773 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (86448823074548479773 / 200000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4613399538059287 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4613399538059287 : ℝ) =
              (4613399538059287 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau311)
  have hz1 :
    (10000000000000000 / 4613399538059287 : ℝ) ≤
      1 / Real.sqrt (1362141139057 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4613399538059287 : ℝ) =
          1 / (4613399538059287 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1153349884514821 : ℝ) ≤
      (805800131307608396503 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1362141139057 / 6400000000000 : ℝ) ≤
      (187500000000000 / 1153349884514821 : ℝ) := by
    rw [show
        (187500000000000 / 1153349884514821 : ℝ) =
          (3 / 40) / (1153349884514821 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (86448823074548479773 / 200000000000000000000 : ℝ)) -
        6 * (805800131307608396503 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1362141139057 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1362141139057 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1153349884514821 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (86448823074548479773 / 200000000000000000000 : ℝ)) -
          6 * (805800131307608396503 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1362141139057 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1362141139057 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1362141139057 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_250 :
    ((484597453553654580303 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3790713706248445209689 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((924988230490799 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4331953206373391881623 / 10000000000000000000000 : ℝ)) -
              6 * (1607647511007304005851 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1711206453093 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1711206453093 / 8000000000000 : ℝ)) =
      Real.log (9711206453093 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1711206453093 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1756206453093 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (484597453553654580303 / 2500000000000000000000 : ℝ) ≤
      Real.log (9711206453093 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1756206453093 / 8000000000000 : ℝ) ≤
      (-(3790713706248445209689 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1756206453093 / 8000000000000 : ℝ) = (1756206453093 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1756206453093 / 1000000000000 : ℝ) ≤
            (1407890146001554790311 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (924988230490799 / 2000000000000000 : ℝ) ≤ Real.sqrt (1711206453093 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1711206453093 / 8000000000000 : ℝ) ≤ (2312470576226999 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1711206453093 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau312 :
    Real.arctan (2312470576226999 / 5000000000000000 : ℝ) ≤
      (4331953206373391881623 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4331953206373391881623 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2312470576226999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2312470576226999 : ℝ) =
              (2312470576226999 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau312)
  have hz1 :
    (5000000000000000 / 2312470576226999 : ℝ) ≤
      1 / Real.sqrt (1711206453093 / 8000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2312470576226999 : ℝ) = 1 / (2312470576226999 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 924988230490799 : ℝ) ≤
      (1607647511007304005851 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1711206453093 / 8000000000000 : ℝ) ≤
      (150000000000000 / 924988230490799 : ℝ) := by
    rw [show
        (150000000000000 / 924988230490799 : ℝ) =
          (3 / 40) / (924988230490799 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4331953206373391881623 / 10000000000000000000000 : ℝ)) -
        6 * (1607647511007304005851 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1711206453093 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1711206453093 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((924988230490799 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4331953206373391881623 / 10000000000000000000000 : ℝ)) -
          6 * (1607647511007304005851 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1711206453093 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1711206453093 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1711206453093 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_251 :
    ((971390349231681716199 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(15138598883318111695953 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4630701172242809 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4336697214724926254481 / 10000000000000000000000 : ℝ)) -
              6 * (321136402291257269187 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (13723771741831 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (13723771741831 / 64000000000000 : ℝ)) =
      Real.log (77723771741831 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((13723771741831 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14083771741831 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (971390349231681716199 / 5000000000000000000000 : ℝ) ≤
      Real.log (77723771741831 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14083771741831 / 64000000000000 : ℝ) ≤
      (-(15138598883318111695953 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (14083771741831 / 64000000000000 : ℝ) = (14083771741831 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14083771741831 / 8000000000000 : ℝ) ≤
            (5655816525681888304047 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4630701172242809 / 10000000000000000 : ℝ) ≤
      Real.sqrt (13723771741831 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (13723771741831 / 64000000000000 : ℝ) ≤ (1157675293060703 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (13723771741831 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau313 :
    Real.arctan (1157675293060703 / 2500000000000000 : ℝ) ≤
      (4336697214724926254481 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4336697214724926254481 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1157675293060703 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1157675293060703 : ℝ) =
              (1157675293060703 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau313)
  have hz1 :
    (2500000000000000 / 1157675293060703 : ℝ) ≤
      1 / Real.sqrt (13723771741831 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1157675293060703 : ℝ) = 1 / (1157675293060703 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4630701172242809 : ℝ) ≤
      (321136402291257269187 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (13723771741831 / 64000000000000 : ℝ) ≤
      (750000000000000 / 4630701172242809 : ℝ) := by
    rw [show
        (750000000000000 / 4630701172242809 : ℝ) =
          (3 / 40) / (4630701172242809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4336697214724926254481 / 10000000000000000000000 : ℝ)) -
        6 * (321136402291257269187 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (13723771741831 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (13723771741831 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4630701172242809 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4336697214724926254481 / 10000000000000000000000 : ℝ)) -
          6 * (321136402291257269187 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (13723771741831 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (13723771741831 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (13723771741831 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_252 :
    ((486792413892953500607 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(944650102148565756543 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4636454036174559 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4341433249904055055669 / 10000000000000000000000 : ℝ)) -
              6 * (400930925943187151183 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (6878945929459 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6878945929459 / 32000000000000 : ℝ)) =
      Real.log (38878945929459 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6878945929459 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7058945929459 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (486792413892953500607 / 2500000000000000000000 : ℝ) ≤
      Real.log (38878945929459 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7058945929459 / 32000000000000 : ℝ) ≤
      (-(944650102148565756543 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7058945929459 / 32000000000000 : ℝ) = (7058945929459 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7058945929459 / 4000000000000 : ℝ) ≤
            (355000860913934243457 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4636454036174559 / 10000000000000000 : ℝ) ≤ Real.sqrt (6878945929459 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6878945929459 / 32000000000000 : ℝ) ≤ (2318227018087281 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6878945929459 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau314 :
    Real.arctan (2318227018087281 / 5000000000000000 : ℝ) ≤
      (4341433249904055055669 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4341433249904055055669 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2318227018087281 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2318227018087281 : ℝ) =
              (2318227018087281 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau314)
  have hz1 :
    (5000000000000000 / 2318227018087281 : ℝ) ≤
      1 / Real.sqrt (6878945929459 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2318227018087281 : ℝ) = 1 / (2318227018087281 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1545484678724853 : ℝ) ≤
      (400930925943187151183 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6878945929459 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1545484678724853 : ℝ) := by
    rw [show
        (250000000000000 / 1545484678724853 : ℝ) =
          (3 / 40) / (4636454036174559 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4341433249904055055669 / 10000000000000000000000 : ℝ)) -
        6 * (400930925943187151183 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6878945929459 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6878945929459 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4636454036174559 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4341433249904055055669 / 10000000000000000000000 : ℝ)) -
          6 * (400930925943187151183 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (6878945929459 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6878945929459 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6878945929459 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
