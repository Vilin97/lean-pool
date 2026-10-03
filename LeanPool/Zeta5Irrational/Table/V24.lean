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

/-! # V24: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_289 :
    ((2198488629086328392477 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1725323680994778098129 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4958713708268379 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (184135701649771270463 / 400000000000000000000 : ℝ)) -
              6 * (750555712906224550967 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3934214662491 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3934214662491 / 16000000000000 : ℝ)) =
      Real.log (19934214662491 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3934214662491 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4024214662491 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2198488629086328392477 / 10000000000000000000000 : ℝ) ≤
      Real.log (19934214662491 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4024214662491 / 16000000000000 : ℝ) ≤
      (-(1725323680994778098129 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4024214662491 / 16000000000000 : ℝ) = (4024214662491 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4024214662491 / 4000000000000 : ℝ) ≤
            (7544269755221901871 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4958713708268379 / 10000000000000000 : ℝ) ≤ Real.sqrt (3934214662491 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3934214662491 / 16000000000000 : ℝ) ≤ (2479356854134191 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3934214662491 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau351 :
    Real.arctan (2479356854134191 / 5000000000000000 : ℝ) ≤
      (184135701649771270463 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (184135701649771270463 / 400000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2479356854134191 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2479356854134191 : ℝ) =
              (2479356854134191 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau351)
  have hz1 :
    (5000000000000000 / 2479356854134191 : ℝ) ≤
      1 / Real.sqrt (3934214662491 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2479356854134191 : ℝ) = 1 / (2479356854134191 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1652904569422793 : ℝ) ≤
      (750555712906224550967 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3934214662491 / 16000000000000 : ℝ) ≤
      (250000000000000 / 1652904569422793 : ℝ) := by
    rw [show
        (250000000000000 / 1652904569422793 : ℝ) =
          (3 / 40) / (4958713708268379 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (184135701649771270463 / 400000000000000000000 : ℝ)) -
        6 * (750555712906224550967 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3934214662491 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3934214662491 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4958713708268379 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (184135701649771270463 / 400000000000000000000 : ℝ)) -
          6 * (750555712906224550967 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3934214662491 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3934214662491 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3934214662491 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_290 :
    ((1107795178054387541519 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13718159850552214083469 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((622521239250649 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2310299720564564919953 / 5000000000000000000000 : ℝ)) -
              6 * (1494740248442681908947 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1984167389789 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1984167389789 / 8000000000000 : ℝ)) =
      Real.log (9984167389789 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1984167389789 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2029167389789 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1107795178054387541519 / 5000000000000000000000 : ℝ) ≤
      Real.log (9984167389789 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2029167389789 / 8000000000000 : ℝ) ≤
      (-(13718159850552214083469 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2029167389789 / 8000000000000 : ℝ) = (2029167389789 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2029167389789 / 2000000000000 : ℝ) ≤
            (144783755447785916531 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (622521239250649 / 1250000000000000 : ℝ) ≤ Real.sqrt (1984167389789 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1984167389789 / 8000000000000 : ℝ) ≤ (996033982801039 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1984167389789 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau352 :
    Real.arctan (996033982801039 / 2000000000000000 : ℝ) ≤
      (2310299720564564919953 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2310299720564564919953 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 996033982801039 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 996033982801039 : ℝ) =
              (996033982801039 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau352)
  have hz1 :
    (2000000000000000 / 996033982801039 : ℝ) ≤
      1 / Real.sqrt (1984167389789 / 8000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 996033982801039 : ℝ) = 1 / (996033982801039 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 622521239250649 : ℝ) ≤
      (1494740248442681908947 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1984167389789 / 8000000000000 : ℝ) ≤
      (93750000000000 / 622521239250649 : ℝ) := by
    rw [show
        (93750000000000 / 622521239250649 : ℝ) =
          (3 / 40) / (622521239250649 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2310299720564564919953 / 5000000000000000000000 : ℝ)) -
        6 * (1494740248442681908947 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1984167389789 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1984167389789 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((622521239250649 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2310299720564564919953 / 5000000000000000000000 : ℝ)) -
          6 * (1494740248442681908947 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1984167389789 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1984167389789 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1984167389789 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_291 :
    ((281213289841407876621 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3387852383232238012393 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((502280736600061 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (581838166519744333303 / 2500000000000000000000 : ℝ))) -
              6 * (1482237548872014842613 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (504571876719 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (504571876719 / 2000000000000 : ℝ)) =
      Real.log (2504571876719 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((504571876719 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (515821876719 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (281213289841407876621 / 1250000000000000000000 : ℝ) ≤
      Real.log (2504571876719 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (515821876719 / 2000000000000 : ℝ) ≤
      (-(3387852383232238012393 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (515821876719 / 2000000000000 : ℝ) = (515821876719 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (515821876719 / 500000000000 : ℝ) ≤
            (77883518267761987607 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (502280736600061 / 1000000000000000 : ℝ) ≤ Real.sqrt (504571876719 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (504571876719 / 2000000000000 : ℝ) ≤ (5022807366000613 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (504571876719 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau354 :
    Real.arctan (5022807366000613 / 21190558245054175 : ℝ) ≤
      (581838166519744333303 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau353 :
    Real.arctan (5022807366000613 / 10000000000000000 : ℝ) ≤
      (2 * (581838166519744333303 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (447622329802167 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (5022807366000613 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5022807366000613 / 10000000000000000 : ℝ) /
                (1 + (447622329802167 / 400000000000000 : ℝ)) =
              (5022807366000613 / 21190558245054175 : ℝ)
            by
        norm_num];
        exact hau354)
  have hat1 :
    (Real.pi / 2 - (2 * (581838166519744333303 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5022807366000613 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5022807366000613 : ℝ) =
              (5022807366000613 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau353)
  have hz1 :
    (10000000000000000 / 5022807366000613 : ℝ) ≤
      1 / Real.sqrt (504571876719 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5022807366000613 : ℝ) =
          1 / (5022807366000613 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 502280736600061 : ℝ) ≤
      (1482237548872014842613 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (504571876719 / 2000000000000 : ℝ) ≤
      (75000000000000 / 502280736600061 : ℝ) := by
    rw [show
        (75000000000000 / 502280736600061 : ℝ) =
          (3 / 40) / (502280736600061 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (581838166519744333303 / 2500000000000000000000 : ℝ))) -
        6 * (1482237548872014842613 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (504571876719 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (504571876719 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((502280736600061 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (581838166519744333303 / 2500000000000000000000 : ℝ))) -
          6 * (1482237548872014842613 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (504571876719 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (504571876719 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (504571876719 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_292 :
    ((1141853143538352302107 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13387394237893872067869 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((31656786952219 / 62500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2344204573684607949139 / 10000000000000000000000 : ℝ))) -
              6 * (36751085971136076113 / 250000000000000000000 : ℝ)))) ≤
      Vfield (2052407623963 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2052407623963 / 8000000000000 : ℝ)) =
      Real.log (10052407623963 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2052407623963 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2097407623963 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1141853143538352302107 / 5000000000000000000000 : ℝ) ≤
      Real.log (10052407623963 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2097407623963 / 8000000000000 : ℝ) ≤
      (-(13387394237893872067869 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2097407623963 / 8000000000000 : ℝ) = (2097407623963 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2097407623963 / 2000000000000 : ℝ) ≤
            (475549368106127932131 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (31656786952219 / 62500000000000 : ℝ) ≤ Real.sqrt (2052407623963 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2052407623963 / 8000000000000 : ℝ) ≤ (5065085912355043 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2052407623963 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau356 :
    Real.arctan (5065085912355043 / 21209598355852786 : ℝ) ≤
      (2344204573684607949139 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau355 :
    Real.arctan (5065085912355043 / 10000000000000000 : ℝ) ≤
      (2 * (2344204573684607949139 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5604799177926393 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5065085912355043 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5065085912355043 / 10000000000000000 : ℝ) /
                (1 + (5604799177926393 / 5000000000000000 : ℝ)) =
              (5065085912355043 / 21209598355852786 : ℝ)
            by
        norm_num];
        exact hau356)
  have hat1 :
    (Real.pi / 2 - (2 * (2344204573684607949139 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5065085912355043 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5065085912355043 : ℝ) =
              (5065085912355043 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau355)
  have hz1 :
    (10000000000000000 / 5065085912355043 : ℝ) ≤
      1 / Real.sqrt (2052407623963 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5065085912355043 : ℝ) =
          1 / (5065085912355043 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (4687500000000 / 31656786952219 : ℝ) ≤
      (36751085971136076113 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2052407623963 / 8000000000000 : ℝ) ≤
      (4687500000000 / 31656786952219 : ℝ) := by
    rw [show
        (4687500000000 / 31656786952219 : ℝ) = (3 / 40) / (31656786952219 / 62500000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2344204573684607949139 / 10000000000000000000000 : ℝ))) -
        6 * (36751085971136076113 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2052407623963 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2052407623963 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((31656786952219 / 62500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2344204573684607949139 / 10000000000000000000000 : ℝ))) -
          6 * (36751085971136076113 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (2052407623963 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2052407623963 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2052407623963 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_293 :
    ((1158795523617137301057 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13226025692197263579119 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2553507233352051 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (147553771669833188447 / 625000000000000000000 : ℝ))) -
              6 * (72907271447543795003 / 500000000000000000000 : ℝ)))) ≤
      Vfield (41730554821 / 160000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (41730554821 / 160000000000 : ℝ)) =
      Real.log (201730554821 / 160000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((41730554821 / 160000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (42630554821 / 160000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1158795523617137301057 / 5000000000000000000000 : ℝ) ≤
      Real.log (201730554821 / 160000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (42630554821 / 160000000000 : ℝ) ≤
      (-(13226025692197263579119 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (42630554821 / 160000000000 : ℝ) = (42630554821 / 40000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (42630554821 / 40000000000 : ℝ) ≤
            (636917913802736420881 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2553507233352051 / 5000000000000000 : ℝ) ≤ Real.sqrt (41730554821 / 160000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (41730554821 / 160000000000 : ℝ) ≤ (1021402893340821 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (41730554821 / 160000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau358 :
    Real.arctan (5107014466704105 / 21228606180783302 : ℝ) ≤
      (147553771669833188447 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau357 :
    Real.arctan (1021402893340821 / 2000000000000000 : ℝ) ≤
      (2 * (147553771669833188447 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5614303090391651 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1021402893340821 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1021402893340821 / 2000000000000000 : ℝ) /
                (1 + (5614303090391651 / 5000000000000000 : ℝ)) =
              (5107014466704105 / 21228606180783302 : ℝ)
            by
        norm_num];
        exact hau358)
  have hat1 :
    (Real.pi / 2 - (2 * (147553771669833188447 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1021402893340821 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1021402893340821 : ℝ) =
              (1021402893340821 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau357)
  have hz1 :
    (2000000000000000 / 1021402893340821 : ℝ) ≤ 1 / Real.sqrt (41730554821 / 160000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1021402893340821 : ℝ) = 1 / (1021402893340821 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 851169077784017 : ℝ) ≤
      (72907271447543795003 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (41730554821 / 160000000000 : ℝ) ≤
      (125000000000000 / 851169077784017 : ℝ) := by
    rw [show
        (125000000000000 / 851169077784017 : ℝ) =
          (3 / 40) / (2553507233352051 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (147553771669833188447 / 625000000000000000000 : ℝ))) -
        6 * (72907271447543795003 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (41730554821 / 160000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (41730554821 / 160000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2553507233352051 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (147553771669833188447 / 625000000000000000000 : ℝ))) -
          6 * (72907271447543795003 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (41730554821 / 160000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (41730554821 / 160000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (41730554821 / 160000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_294 :
    ((2385018047629768990871 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20173275815075893487 / 15625000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2594927729740271 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1196801073083827964937 / 5000000000000000000000 : ℝ))) -
              6 * (1435191184916654243353 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (269345996903 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (269345996903 / 1000000000000 : ℝ)) =
      Real.log (1269345996903 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((269345996903 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (274970996903 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2385018047629768990871 / 10000000000000000000000 : ℝ) ≤
      Real.log (1269345996903 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (274970996903 / 1000000000000 : ℝ) ≤
      (-(20173275815075893487 / 15625000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (274970996903 / 1000000000000 : ℝ) = (274970996903 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (274970996903 / 250000000000 : ℝ) ≤
            (1487573569299106513 / 15625000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2594927729740271 / 5000000000000000 : ℝ) ≤ Real.sqrt (269345996903 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (269345996903 / 1000000000000 : ℝ) ≤ (1037971091896109 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (269345996903 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau360 :
    Real.arctan (5189855459480545 / 21266525626398761 : ℝ) ≤
      (1196801073083827964937 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau359 :
    Real.arctan (1037971091896109 / 2000000000000000 : ℝ) ≤
      (2 * (1196801073083827964937 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11266525626398761 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1037971091896109 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1037971091896109 / 2000000000000000 : ℝ) /
                (1 + (11266525626398761 / 10000000000000000 : ℝ)) =
              (5189855459480545 / 21266525626398761 : ℝ)
            by
        norm_num];
        exact hau360)
  have hat1 :
    (Real.pi / 2 - (2 * (1196801073083827964937 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1037971091896109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1037971091896109 : ℝ) =
              (1037971091896109 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau359)
  have hz1 :
    (2000000000000000 / 1037971091896109 : ℝ) ≤
      1 / Real.sqrt (269345996903 / 1000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1037971091896109 : ℝ) = 1 / (1037971091896109 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2594927729740271 : ℝ) ≤
      (1435191184916654243353 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (269345996903 / 1000000000000 : ℝ) ≤
      (375000000000000 / 2594927729740271 : ℝ) := by
    rw [show
        (375000000000000 / 2594927729740271 : ℝ) =
          (3 / 40) / (2594927729740271 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1196801073083827964937 / 5000000000000000000000 : ℝ))) -
        6 * (1435191184916654243353 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (269345996903 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (269345996903 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2594927729740271 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1196801073083827964937 / 5000000000000000000000 : ℝ))) -
          6 * (1435191184916654243353 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (269345996903 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (269345996903 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (269345996903 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_295 :
    ((300517427895070866779 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12822930291729512624071 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5213209021966759 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (96111696549200328527 / 400000000000000000000 : ℝ))) -
              6 * (714424657120258015799 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (8696815458149 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8696815458149 / 32000000000000 : ℝ)) =
      Real.log (40696815458149 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8696815458149 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8876815458149 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (300517427895070866779 / 1250000000000000000000 : ℝ) ≤
      Real.log (40696815458149 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8876815458149 / 32000000000000 : ℝ) ≤
      (-(12822930291729512624071 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (8876815458149 / 32000000000000 : ℝ) = (8876815458149 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8876815458149 / 8000000000000 : ℝ) ≤
            (1040013314270487375929 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5213209021966759 / 10000000000000000 : ℝ) ≤ Real.sqrt (8696815458149 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8696815458149 / 32000000000000 : ℝ) ≤ (2606604510983381 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8696815458149 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau362 :
    Real.arctan (2606604510983381 / 10638651175297059 : ℝ) ≤
      (96111696549200328527 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau361 :
    Real.arctan (2606604510983381 / 5000000000000000 : ℝ) ≤
      (2 * (96111696549200328527 / 400000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5638651175297059 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2606604510983381 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2606604510983381 / 5000000000000000 : ℝ) /
                (1 + (5638651175297059 / 5000000000000000 : ℝ)) =
              (2606604510983381 / 10638651175297059 : ℝ)
            by
        norm_num];
        exact hau362)
  have hat1 :
    (Real.pi / 2 - (2 * (96111696549200328527 / 400000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2606604510983381 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2606604510983381 : ℝ) =
              (2606604510983381 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau361)
  have hz1 :
    (5000000000000000 / 2606604510983381 : ℝ) ≤
      1 / Real.sqrt (8696815458149 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2606604510983381 : ℝ) = 1 / (2606604510983381 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5213209021966759 : ℝ) ≤
      (714424657120258015799 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8696815458149 / 32000000000000 : ℝ) ≤
      (750000000000000 / 5213209021966759 : ℝ) := by
    rw [show
        (750000000000000 / 5213209021966759 : ℝ) =
          (3 / 40) / (5213209021966759 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (96111696549200328527 / 400000000000000000000 : ℝ))) -
        6 * (714424657120258015799 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8696815458149 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8696815458149 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5213209021966759 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (96111696549200328527 / 400000000000000000000 : ℝ))) -
          6 * (714424657120258015799 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (8696815458149 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8696815458149 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8696815458149 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_296 :
    ((1211612152879776726763 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12735731124909343586647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2618229216623863 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2411924233564044653293 / 10000000000000000000000 : ℝ))) -
              6 * (56903631257368425313 / 400000000000000000000 : ℝ)))) ≤
      Vfield (4387279507701 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4387279507701 / 16000000000000 : ℝ)) =
      Real.log (20387279507701 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4387279507701 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4477279507701 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1211612152879776726763 / 5000000000000000000000 : ℝ) ≤
      Real.log (20387279507701 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4477279507701 / 16000000000000 : ℝ) ≤
      (-(12735731124909343586647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4477279507701 / 16000000000000 : ℝ) = (4477279507701 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4477279507701 / 4000000000000 : ℝ) ≤
            (1127212481090656413353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2618229216623863 / 5000000000000000 : ℝ) ≤ Real.sqrt (4387279507701 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4387279507701 / 16000000000000 : ℝ) ≤ (5236458433247729 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4387279507701 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau364 :
    Real.arctan (5236458433247729 / 21288068786250872 : ℝ) ≤
      (2411924233564044653293 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau363 :
    Real.arctan (5236458433247729 / 10000000000000000 : ℝ) ≤
      (2 * (2411924233564044653293 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1411008598281359 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5236458433247729 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5236458433247729 / 10000000000000000 : ℝ) /
                (1 + (1411008598281359 / 1250000000000000 : ℝ)) =
              (5236458433247729 / 21288068786250872 : ℝ)
            by
        norm_num];
        exact hau364)
  have hat1 :
    (Real.pi / 2 - (2 * (2411924233564044653293 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5236458433247729 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5236458433247729 : ℝ) =
              (5236458433247729 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau363)
  have hz1 :
    (10000000000000000 / 5236458433247729 : ℝ) ≤
      1 / Real.sqrt (4387279507701 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5236458433247729 : ℝ) =
          1 / (5236458433247729 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2618229216623863 : ℝ) ≤
      (56903631257368425313 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4387279507701 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2618229216623863 : ℝ) := by
    rw [show
        (375000000000000 / 2618229216623863 : ℝ) =
          (3 / 40) / (2618229216623863 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2411924233564044653293 / 10000000000000000000000 : ℝ))) -
        6 * (56903631257368425313 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4387279507701 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4387279507701 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2618229216623863 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2411924233564044653293 / 10000000000000000000000 : ℝ))) -
          6 * (56903631257368425313 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (4387279507701 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4387279507701 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4387279507701 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_297 :
    ((152642052153384038571 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2529857151842140007031 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5259605074484857 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1210499184897321206457 / 5000000000000000000000 : ℝ))) -
              6 * (708206888526691726481 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1770460514531 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1770460514531 / 6400000000000 : ℝ)) =
      Real.log (8170460514531 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1770460514531 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1806460514531 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (152642052153384038571 / 625000000000000000000 : ℝ) ≤
      Real.log (8170460514531 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1806460514531 / 6400000000000 : ℝ) ≤
      (-(2529857151842140007031 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1806460514531 / 6400000000000 : ℝ) = (1806460514531 / 1600000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1806460514531 / 1600000000000 : ℝ) ≤
            (242731569357859992969 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5259605074484857 / 10000000000000000 : ℝ) ≤ Real.sqrt (1770460514531 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1770460514531 / 6400000000000 : ℝ) ≤ (262980253724243 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1770460514531 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau366 :
    Real.arctan (5259605074484860 / 21298824962780283 : ℝ) ≤
      (1210499184897321206457 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau365 :
    Real.arctan (262980253724243 / 500000000000000 : ℝ) ≤
      (2 * (1210499184897321206457 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11298824962780283 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (262980253724243 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (262980253724243 / 500000000000000 : ℝ) /
                (1 + (11298824962780283 / 10000000000000000 : ℝ)) =
              (5259605074484860 / 21298824962780283 : ℝ)
            by
        norm_num];
        exact hau366)
  have hat1 :
    (Real.pi / 2 - (2 * (1210499184897321206457 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 262980253724243 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 262980253724243 : ℝ) =
              (262980253724243 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau365)
  have hz1 :
    (500000000000000 / 262980253724243 : ℝ) ≤ 1 / Real.sqrt (1770460514531 / 6400000000000 : ℝ) :=
  by
    rw [show (500000000000000 / 262980253724243 : ℝ) = 1 / (262980253724243 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5259605074484857 : ℝ) ≤
      (708206888526691726481 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1770460514531 / 6400000000000 : ℝ) ≤
      (750000000000000 / 5259605074484857 : ℝ) := by
    rw [show
        (750000000000000 / 5259605074484857 : ℝ) =
          (3 / 40) / (5259605074484857 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1210499184897321206457 / 5000000000000000000000 : ℝ))) -
        6 * (708206888526691726481 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1770460514531 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1770460514531 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5259605074484857 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1210499184897321206457 / 5000000000000000000000 : ℝ))) -
          6 * (708206888526691726481 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1770460514531 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1770460514531 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1770460514531 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_298 :
    ((1225891754658183301957 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6303170850486857560717 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((658892534956321 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (303189255113144357391 / 1250000000000000000000 : ℝ))) -
              6 * (353338824384936034991 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (17782348702563 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17782348702563 / 64000000000000 : ℝ)) =
      Real.log (81782348702563 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17782348702563 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18142348702563 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1225891754658183301957 / 5000000000000000000000 : ℝ) ≤
      Real.log (81782348702563 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18142348702563 / 64000000000000 : ℝ) ≤
      (-(6303170850486857560717 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (18142348702563 / 64000000000000 : ℝ) = (18142348702563 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18142348702563 / 16000000000000 : ℝ) ≤
            (628300952513142439283 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (658892534956321 / 1250000000000000 : ℝ) ≤ Real.sqrt (17782348702563 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17782348702563 / 64000000000000 : ℝ) ≤
      (5271140279650571 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17782348702563 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau368 :
    Real.arctan (5271140279650571 / 21304199213024984 : ℝ) ≤
      (303189255113144357391 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau367 :
    Real.arctan (5271140279650571 / 10000000000000000 : ℝ) ≤
      (2 * (303189255113144357391 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1413024901628123 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5271140279650571 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5271140279650571 / 10000000000000000 : ℝ) /
                (1 + (1413024901628123 / 1250000000000000 : ℝ)) =
              (5271140279650571 / 21304199213024984 : ℝ)
            by
        norm_num];
        exact hau368)
  have hat1 :
    (Real.pi / 2 - (2 * (303189255113144357391 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5271140279650571 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5271140279650571 : ℝ) =
              (5271140279650571 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau367)
  have hz1 :
    (10000000000000000 / 5271140279650571 : ℝ) ≤
      1 / Real.sqrt (17782348702563 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5271140279650571 : ℝ) =
          1 / (5271140279650571 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 658892534956321 : ℝ) ≤
      (353338824384936034991 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17782348702563 / 64000000000000 : ℝ) ≤
      (93750000000000 / 658892534956321 : ℝ) := by
    rw [show
        (93750000000000 / 658892534956321 : ℝ) =
          (3 / 40) / (658892534956321 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (303189255113144357391 / 1250000000000000000000 : ℝ))) -
        6 * (353338824384936034991 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17782348702563 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17782348702563 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((658892534956321 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (303189255113144357391 / 1250000000000000000000 : ℝ))) -
          6 * (353338824384936034991 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (17782348702563 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17782348702563 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17782348702563 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_299 :
    ((1230642573739392974039 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6281790636822936316249 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2641325148290271 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2430015570348441889311 / 10000000000000000000000 : ℝ))) -
              6 * (282063309236787619361 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (2232511532477 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2232511532477 / 8000000000000 : ℝ)) =
      Real.log (10232511532477 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2232511532477 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2277511532477 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1230642573739392974039 / 5000000000000000000000 : ℝ) ≤
      Real.log (10232511532477 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2277511532477 / 8000000000000 : ℝ) ≤
      (-(6281790636822936316249 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2277511532477 / 8000000000000 : ℝ) = (2277511532477 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2277511532477 / 2000000000000 : ℝ) ≤
            (649681166177063683751 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2641325148290271 / 5000000000000000 : ℝ) ≤ Real.sqrt (2232511532477 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2232511532477 / 8000000000000 : ℝ) ≤ (1056530059316109 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2232511532477 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau370 :
    Real.arctan (5282650296580545 / 21309570909453748 : ℝ) ≤
      (2430015570348441889311 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau369 :
    Real.arctan (1056530059316109 / 2000000000000000 : ℝ) ≤
      (2 * (2430015570348441889311 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2827392727363437 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1056530059316109 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1056530059316109 / 2000000000000000 : ℝ) /
                (1 + (2827392727363437 / 2500000000000000 : ℝ)) =
              (5282650296580545 / 21309570909453748 : ℝ)
            by
        norm_num];
        exact hau370)
  have hat1 :
    (Real.pi / 2 - (2 * (2430015570348441889311 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1056530059316109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1056530059316109 : ℝ) =
              (1056530059316109 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau369)
  have hz1 :
    (2000000000000000 / 1056530059316109 : ℝ) ≤
      1 / Real.sqrt (2232511532477 / 8000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1056530059316109 : ℝ) = 1 / (1056530059316109 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 880441716096757 : ℝ) ≤
      (282063309236787619361 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2232511532477 / 8000000000000 : ℝ) ≤
      (125000000000000 / 880441716096757 : ℝ) := by
    rw [show
        (125000000000000 / 880441716096757 : ℝ) =
          (3 / 40) / (2641325148290271 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2430015570348441889311 / 10000000000000000000000 : ℝ))) -
        6 * (282063309236787619361 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2232511532477 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2232511532477 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2641325148290271 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2430015570348441889311 / 10000000000000000000000 : ℝ))) -
          6 * (282063309236787619361 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (2232511532477 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2232511532477 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2232511532477 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_300 :
    ((2470777766097794190011 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6260501456740909970931 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5294135289560543 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2434503049163477909489 / 10000000000000000000000 : ℝ))) -
              6 * (1407297311798374862231 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (17937835817069 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17937835817069 / 64000000000000 : ℝ)) =
      Real.log (81937835817069 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17937835817069 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18297835817069 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2470777766097794190011 / 10000000000000000000000 : ℝ) ≤
      Real.log (81937835817069 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18297835817069 / 64000000000000 : ℝ) ≤
      (-(6260501456740909970931 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (18297835817069 / 64000000000000 : ℝ) = (18297835817069 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18297835817069 / 16000000000000 : ℝ) ≤
            (670970346259090029069 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5294135289560543 / 10000000000000000 : ℝ) ≤
      Real.sqrt (17937835817069 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17937835817069 / 64000000000000 : ℝ) ≤ (2647067644780273 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17937835817069 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau372 :
    Real.arctan (5294135289560546 / 21314940055703799 : ℝ) ≤
      (2434503049163477909489 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau371 :
    Real.arctan (2647067644780273 / 5000000000000000 : ℝ) ≤
      (2 * (2434503049163477909489 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11314940055703799 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2647067644780273 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2647067644780273 / 5000000000000000 : ℝ) /
                (1 + (11314940055703799 / 10000000000000000 : ℝ)) =
              (5294135289560546 / 21314940055703799 : ℝ)
            by
        norm_num];
        exact hau372)
  have hat1 :
    (Real.pi / 2 - (2 * (2434503049163477909489 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2647067644780273 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2647067644780273 : ℝ) =
              (2647067644780273 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau371)
  have hz1 :
    (5000000000000000 / 2647067644780273 : ℝ) ≤
      1 / Real.sqrt (17937835817069 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2647067644780273 : ℝ) = 1 / (2647067644780273 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5294135289560543 : ℝ) ≤
      (1407297311798374862231 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17937835817069 / 64000000000000 : ℝ) ≤
      (750000000000000 / 5294135289560543 : ℝ) := by
    rw [show
        (750000000000000 / 5294135289560543 : ℝ) =
          (3 / 40) / (5294135289560543 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2434503049163477909489 / 10000000000000000000000 : ℝ))) -
        6 * (1407297311798374862231 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17937835817069 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17937835817069 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5294135289560543 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2434503049163477909489 / 10000000000000000000000 : ℝ))) -
          6 * (1407297311798374862231 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (17937835817069 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17937835817069 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17937835817069 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
