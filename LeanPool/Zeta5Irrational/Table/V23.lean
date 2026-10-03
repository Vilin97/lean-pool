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

/-! # V23: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_277 :
    ((64394112760097439463 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(226640407886521376383 / 156250000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2391800356751099 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4461862808171570115379 / 10000000000000000000000 : ℝ)) -
              6 * (1555195942020142671139 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (732250745159 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (732250745159 / 3200000000000 : ℝ)) =
      Real.log (3932250745159 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((732250745159 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (750250745159 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (64394112760097439463 / 312500000000000000000 : ℝ) ≤
      Real.log (3932250745159 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (750250745159 / 3200000000000 : ℝ) ≤
      (-(226640407886521376383 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (750250745159 / 3200000000000 : ℝ) = (750250745159 / 400000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (750250745159 / 400000000000 : ℝ) ≤
            (98272332879103623617 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2391800356751099 / 5000000000000000 : ℝ) ≤ Real.sqrt (732250745159 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (732250745159 / 3200000000000 : ℝ) ≤ (4783600713502201 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (732250745159 / 3200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau339 :
    Real.arctan (4783600713502201 / 10000000000000000 : ℝ) ≤
      (4461862808171570115379 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4461862808171570115379 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4783600713502201 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4783600713502201 : ℝ) =
              (4783600713502201 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau339)
  have hz1 :
    (10000000000000000 / 4783600713502201 : ℝ) ≤
      1 / Real.sqrt (732250745159 / 3200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4783600713502201 : ℝ) =
          1 / (4783600713502201 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2391800356751099 : ℝ) ≤
      (1555195942020142671139 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (732250745159 / 3200000000000 : ℝ) ≤
      (375000000000000 / 2391800356751099 : ℝ) := by
    rw [show
        (375000000000000 / 2391800356751099 : ℝ) =
          (3 / 40) / (2391800356751099 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4461862808171570115379 / 10000000000000000000000 : ℝ)) -
        6 * (1555195942020142671139 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (732250745159 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (732250745159 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2391800356751099 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4461862808171570115379 / 10000000000000000000000 : ℝ)) -
          6 * (1555195942020142671139 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (732250745159 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (732250745159 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (732250745159 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_278 :
    ((2069284840233233473751 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2891922184229524885251 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((29967079041083 / 62500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2235458931496437735461 / 5000000000000000000000 : ℝ)) -
              6 * (310328596773444075099 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (7356627568677 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7356627568677 / 32000000000000 : ℝ)) =
      Real.log (39356627568677 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7356627568677 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7536627568677 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2069284840233233473751 / 10000000000000000000000 : ℝ) ≤
      Real.log (39356627568677 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7536627568677 / 32000000000000 : ℝ) ≤
      (-(2891922184229524885251 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7536627568677 / 32000000000000 : ℝ) = (7536627568677 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7536627568677 / 4000000000000 : ℝ) ≤
            (1266960897570475114749 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (29967079041083 / 62500000000000 : ℝ) ≤ Real.sqrt (7356627568677 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7356627568677 / 32000000000000 : ℝ) ≤ (4794732646573283 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7356627568677 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau340 :
    Real.arctan (4794732646573283 / 10000000000000000 : ℝ) ≤
      (2235458931496437735461 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2235458931496437735461 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4794732646573283 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4794732646573283 : ℝ) =
              (4794732646573283 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau340)
  have hz1 :
    (10000000000000000 / 4794732646573283 : ℝ) ≤
      1 / Real.sqrt (7356627568677 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4794732646573283 : ℝ) =
          1 / (4794732646573283 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (4687500000000 / 29967079041083 : ℝ) ≤
      (310328596773444075099 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7356627568677 / 32000000000000 : ℝ) ≤
      (4687500000000 / 29967079041083 : ℝ) := by
    rw [show
        (4687500000000 / 29967079041083 : ℝ) = (3 / 40) / (29967079041083 / 62500000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2235458931496437735461 / 5000000000000000000000 : ℝ)) -
        6 * (310328596773444075099 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7356627568677 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7356627568677 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((29967079041083 / 62500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2235458931496437735461 / 5000000000000000000000 : ℝ)) -
          6 * (310328596773444075099 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (7356627568677 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7356627568677 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7356627568677 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_279 :
    ((2077950556166482502539 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7207220349310972146853 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((600729849303283 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2239972057321476567427 / 5000000000000000000000 : ℝ)) -
              6 * (774057133603146563687 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1847686921441 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1847686921441 / 8000000000000 : ℝ)) =
      Real.log (9847686921441 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1847686921441 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1892686921441 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2077950556166482502539 / 10000000000000000000000 : ℝ) ≤
      Real.log (9847686921441 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1892686921441 / 8000000000000 : ℝ) ≤
      (-(7207220349310972146853 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1892686921441 / 8000000000000 : ℝ) = (1892686921441 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1892686921441 / 1000000000000 : ℝ) ≤
            (3189987355189027853147 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (600729849303283 / 1250000000000000 : ℝ) ≤ Real.sqrt (1847686921441 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1847686921441 / 8000000000000 : ℝ) ≤ (4805838794426267 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1847686921441 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau341 :
    Real.arctan (4805838794426267 / 10000000000000000 : ℝ) ≤
      (2239972057321476567427 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2239972057321476567427 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4805838794426267 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4805838794426267 : ℝ) =
              (4805838794426267 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau341)
  have hz1 :
    (10000000000000000 / 4805838794426267 : ℝ) ≤
      1 / Real.sqrt (1847686921441 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4805838794426267 : ℝ) =
          1 / (4805838794426267 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 600729849303283 : ℝ) ≤
      (774057133603146563687 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1847686921441 / 8000000000000 : ℝ) ≤
      (93750000000000 / 600729849303283 : ℝ) := by
    rw [show
        (93750000000000 / 600729849303283 : ℝ) =
          (3 / 40) / (600729849303283 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2239972057321476567427 / 5000000000000000000000 : ℝ)) -
        6 * (774057133603146563687 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1847686921441 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1847686921441 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((600729849303283 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2239972057321476567427 / 5000000000000000000000 : ℝ)) -
          6 * (774057133603146563687 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1847686921441 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1847686921441 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1847686921441 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_280 :
    ((2086608769137852456389 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14369473593852945214773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4816919335416503 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (280558859864199691039 / 625000000000000000000 : ℝ)) -
              6 * (308921903521780670773 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (7424867802851 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7424867802851 / 32000000000000 : ℝ)) =
      Real.log (39424867802851 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7424867802851 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7604867802851 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2086608769137852456389 / 10000000000000000000000 : ℝ) ≤
      Real.log (39424867802851 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7604867802851 / 32000000000000 : ℝ) ≤
      (-(14369473593852945214773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7604867802851 / 32000000000000 : ℝ) = (7604867802851 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7604867802851 / 4000000000000 : ℝ) ≤
            (6424941815147054785227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4816919335416503 / 10000000000000000 : ℝ) ≤ Real.sqrt (7424867802851 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7424867802851 / 32000000000000 : ℝ) ≤ (2408459667708253 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7424867802851 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau342 :
    Real.arctan (2408459667708253 / 5000000000000000 : ℝ) ≤
      (280558859864199691039 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (280558859864199691039 / 625000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2408459667708253 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2408459667708253 : ℝ) =
              (2408459667708253 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau342)
  have hz1 :
    (5000000000000000 / 2408459667708253 : ℝ) ≤
      1 / Real.sqrt (7424867802851 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2408459667708253 : ℝ) = 1 / (2408459667708253 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4816919335416503 : ℝ) ≤
      (308921903521780670773 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7424867802851 / 32000000000000 : ℝ) ≤
      (750000000000000 / 4816919335416503 : ℝ) := by
    rw [show
        (750000000000000 / 4816919335416503 : ℝ) =
          (3 / 40) / (4816919335416503 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (280558859864199691039 / 625000000000000000000 : ℝ)) -
        6 * (308921903521780670773 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7424867802851 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7424867802851 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4816919335416503 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (280558859864199691039 / 625000000000000000000 : ℝ)) -
          6 * (308921903521780670773 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (7424867802851 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7424867802851 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7424867802851 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_281 :
    ((2095259492128553921179 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14324707788288511762533 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4827974445852653 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4497910985085163099573 / 10000000000000000000000 : ℝ)) -
              6 * (1541128464976589575851 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3729493959969 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3729493959969 / 16000000000000 : ℝ)) =
      Real.log (19729493959969 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3729493959969 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3819493959969 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2095259492128553921179 / 10000000000000000000000 : ℝ) ≤
      Real.log (19729493959969 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3819493959969 / 16000000000000 : ℝ) ≤
      (-(14324707788288511762533 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3819493959969 / 16000000000000 : ℝ) = (3819493959969 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3819493959969 / 2000000000000 : ℝ) ≤
            (6469707620711488237467 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4827974445852653 / 10000000000000000 : ℝ) ≤ Real.sqrt (3729493959969 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3729493959969 / 16000000000000 : ℝ) ≤ (301748402865791 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3729493959969 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau343 :
    Real.arctan (301748402865791 / 625000000000000 : ℝ) ≤
      (4497910985085163099573 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4497910985085163099573 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 301748402865791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 301748402865791 : ℝ) =
              (301748402865791 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau343)
  have hz1 :
    (625000000000000 / 301748402865791 : ℝ) ≤
      1 / Real.sqrt (3729493959969 / 16000000000000 : ℝ) := by
    rw [show (625000000000000 / 301748402865791 : ℝ) = 1 / (301748402865791 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4827974445852653 : ℝ) ≤
      (1541128464976589575851 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3729493959969 / 16000000000000 : ℝ) ≤
      (750000000000000 / 4827974445852653 : ℝ) := by
    rw [show
        (750000000000000 / 4827974445852653 : ℝ) =
          (3 / 40) / (4827974445852653 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4497910985085163099573 / 10000000000000000000000 : ℝ)) -
        6 * (1541128464976589575851 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3729493959969 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3729493959969 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4827974445852653 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4497910985085163099573 / 10000000000000000000000 : ℝ)) -
          6 * (1541128464976589575851 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (3729493959969 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3729493959969 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3729493959969 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_282 :
    ((2103902738086137537693 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14280141487690492393971 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4839004300029409 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1126712996706153351403 / 2500000000000000000000 : ℝ)) -
              6 * (1537670843453434960069 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (299724321481 / 1280000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (299724321481 / 1280000000000 : ℝ)) =
      Real.log (1579724321481 / 1280000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((299724321481 / 1280000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (306924321481 / 1280000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2103902738086137537693 / 10000000000000000000000 : ℝ) ≤
      Real.log (1579724321481 / 1280000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (306924321481 / 1280000000000 : ℝ) ≤
      (-(14280141487690492393971 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (306924321481 / 1280000000000 : ℝ) = (306924321481 / 160000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (306924321481 / 160000000000 : ℝ) ≤
            (6514273921309507606029 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4839004300029409 / 10000000000000000 : ℝ) ≤ Real.sqrt (299724321481 / 1280000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (299724321481 / 1280000000000 : ℝ) ≤ (1209751075007353 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (299724321481 / 1280000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau344 :
    Real.arctan (1209751075007353 / 2500000000000000 : ℝ) ≤
      (1126712996706153351403 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1126712996706153351403 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1209751075007353 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1209751075007353 : ℝ) =
              (1209751075007353 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau344)
  have hz1 :
    (2500000000000000 / 1209751075007353 : ℝ) ≤
      1 / Real.sqrt (299724321481 / 1280000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1209751075007353 : ℝ) = 1 / (1209751075007353 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4839004300029409 : ℝ) ≤
      (1537670843453434960069 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (299724321481 / 1280000000000 : ℝ) ≤
      (750000000000000 / 4839004300029409 : ℝ) := by
    rw [show
        (750000000000000 / 4839004300029409 : ℝ) =
          (3 / 40) / (4839004300029409 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1126712996706153351403 / 2500000000000000000000 : ℝ)) -
        6 * (1537670843453434960069 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (299724321481 / 1280000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (299724321481 / 1280000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4839004300029409 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1126712996706153351403 / 2500000000000000000000 : ℝ)) -
          6 * (1537670843453434960069 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (299724321481 / 1280000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (299724321481 / 1280000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (299724321481 / 1280000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_283 :
    ((264067314990576284203 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7117886460851593151109 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2425004535129779 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4515764951354820672259 / 10000000000000000000000 : ℝ)) -
              6 * (383559097835192323907 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (29403234977 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (29403234977 / 125000000000 : ℝ)) =
      Real.log (154403234977 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((29403234977 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (30106359977 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (264067314990576284203 / 1250000000000000000000 : ℝ) ≤
      Real.log (154403234977 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (30106359977 / 125000000000 : ℝ) ≤
      (-(7117886460851593151109 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (30106359977 / 125000000000 : ℝ) = (30106359977 / 15625000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30106359977 / 15625000000 : ℝ) ≤
            (3279321243648406848891 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2425004535129779 / 5000000000000000 : ℝ) ≤ Real.sqrt (29403234977 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (29403234977 / 125000000000 : ℝ) ≤ (4850009070259561 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (29403234977 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau345 :
    Real.arctan (4850009070259561 / 10000000000000000 : ℝ) ≤
      (4515764951354820672259 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (4515764951354820672259 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4850009070259561 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4850009070259561 : ℝ) =
              (4850009070259561 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau345)
  have hz1 :
    (10000000000000000 / 4850009070259561 : ℝ) ≤ 1 / Real.sqrt (29403234977 / 125000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 4850009070259561 : ℝ) =
          1 / (4850009070259561 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2425004535129779 : ℝ) ≤
      (383559097835192323907 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (29403234977 / 125000000000 : ℝ) ≤
      (375000000000000 / 2425004535129779 : ℝ) := by
    rw [show
        (375000000000000 / 2425004535129779 : ℝ) =
          (3 / 40) / (2425004535129779 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (4515764951354820672259 / 10000000000000000000000 : ℝ)) -
        6 * (383559097835192323907 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (29403234977 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (29403234977 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2425004535129779 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (4515764951354820672259 / 10000000000000000000000 : ℝ)) -
          6 * (383559097835192323907 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (29403234977 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (29403234977 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (29403234977 / 125000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_284 :
    ((2121166850524551193967 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1419160034343136087147 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((972197785381079 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2262325032459621594699 / 5000000000000000000000 : ℝ)) -
              6 * (61232994040558072229 / 400000000000000000000 : ℝ)))) ≤
      Vfield (7561348271199 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7561348271199 / 32000000000000 : ℝ)) =
      Real.log (39561348271199 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7561348271199 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7741348271199 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2121166850524551193967 / 10000000000000000000000 : ℝ) ≤
      Real.log (39561348271199 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7741348271199 / 32000000000000 : ℝ) ≤
      (-(1419160034343136087147 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (7741348271199 / 32000000000000 : ℝ) = (7741348271199 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7741348271199 / 4000000000000 : ℝ) ≤
            (660281506556863912853 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (972197785381079 / 2000000000000000 : ℝ) ≤ Real.sqrt (7561348271199 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7561348271199 / 32000000000000 : ℝ) ≤ (2430494463452699 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7561348271199 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau346 :
    Real.arctan (2430494463452699 / 5000000000000000 : ℝ) ≤
      (2262325032459621594699 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2262325032459621594699 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 2430494463452699 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2430494463452699 : ℝ) =
              (2430494463452699 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau346)
  have hz1 :
    (5000000000000000 / 2430494463452699 : ℝ) ≤
      1 / Real.sqrt (7561348271199 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2430494463452699 : ℝ) = 1 / (2430494463452699 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 972197785381079 : ℝ) ≤
      (61232994040558072229 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7561348271199 / 32000000000000 : ℝ) ≤
      (150000000000000 / 972197785381079 : ℝ) := by
    rw [show
        (150000000000000 / 972197785381079 : ℝ) =
          (3 / 40) / (972197785381079 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2262325032459621594699 / 5000000000000000000000 : ℝ)) -
        6 * (61232994040558072229 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7561348271199 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7561348271199 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((972197785381079 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2262325032459621594699 / 5000000000000000000000 : ℝ)) -
          6 * (61232994040558072229 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (7561348271199 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7561348271199 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7561348271199 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_285 :
    ((266223467841653341547 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14147622029027548248203 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2435972019204743 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1133376877931879777319 / 2500000000000000000000 : ℝ)) -
              6 * (95464748052574244179 / 625000000000000000000 : ℝ)))) ≤
      Vfield (3797734194143 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3797734194143 / 16000000000000 : ℝ)) =
      Real.log (19797734194143 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3797734194143 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3887734194143 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (266223467841653341547 / 1250000000000000000000 : ℝ) ≤
      Real.log (19797734194143 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3887734194143 / 16000000000000 : ℝ) ≤
      (-(14147622029027548248203 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3887734194143 / 16000000000000 : ℝ) = (3887734194143 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3887734194143 / 2000000000000 : ℝ) ≤
            (6646793379972451751797 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2435972019204743 / 5000000000000000 : ℝ) ≤ Real.sqrt (3797734194143 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3797734194143 / 16000000000000 : ℝ) ≤ (4871944038409489 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3797734194143 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau347 :
    Real.arctan (4871944038409489 / 10000000000000000 : ℝ) ≤
      (1133376877931879777319 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1133376877931879777319 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4871944038409489 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4871944038409489 : ℝ) =
              (4871944038409489 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau347)
  have hz1 :
    (10000000000000000 / 4871944038409489 : ℝ) ≤
      1 / Real.sqrt (3797734194143 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 4871944038409489 : ℝ) =
          1 / (4871944038409489 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2435972019204743 : ℝ) ≤
      (95464748052574244179 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3797734194143 / 16000000000000 : ℝ) ≤
      (375000000000000 / 2435972019204743 : ℝ) := by
    rw [show
        (375000000000000 / 2435972019204743 : ℝ) =
          (3 / 40) / (2435972019204743 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1133376877931879777319 / 2500000000000000000000 : ℝ)) -
        6 * (95464748052574244179 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3797734194143 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3797734194143 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2435972019204743 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1133376877931879777319 / 2500000000000000000000 : ℝ)) -
          6 * (95464748052574244179 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (3797734194143 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3797734194143 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3797734194143 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_286 :
    ((2147007263199972397 / 10000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1757530176157463034543 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4893780690344377 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (568892516491583260051 / 1250000000000000000000 : ℝ)) -
              6 * (760362591960730908383 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (383185431123 / 1600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (383185431123 / 1600000000000 : ℝ)) =
      Real.log (1983185431123 / 1600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((383185431123 / 1600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (392185431123 / 1600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2147007263199972397 / 10000000000000000000 : ℝ) ≤
      Real.log (1983185431123 / 1600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (392185431123 / 1600000000000 : ℝ) ≤
      (-(1757530176157463034543 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (392185431123 / 1600000000000 : ℝ) = (392185431123 / 200000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (392185431123 / 200000000000 : ℝ) ≤
            (841771749967536965457 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4893780690344377 / 10000000000000000 : ℝ) ≤ Real.sqrt (383185431123 / 1600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (383185431123 / 1600000000000 : ℝ) ≤ (244689034517219 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (383185431123 / 1600000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau348 :
    Real.arctan (244689034517219 / 500000000000000 : ℝ) ≤
      (568892516491583260051 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (568892516491583260051 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 244689034517219 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 244689034517219 : ℝ) =
              (244689034517219 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau348)
  have hz1 :
    (500000000000000 / 244689034517219 : ℝ) ≤ 1 / Real.sqrt (383185431123 / 1600000000000 : ℝ) := by
    rw [show (500000000000000 / 244689034517219 : ℝ) = 1 / (244689034517219 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4893780690344377 : ℝ) ≤
      (760362591960730908383 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (383185431123 / 1600000000000 : ℝ) ≤
      (750000000000000 / 4893780690344377 : ℝ) := by
    rw [show
        (750000000000000 / 4893780690344377 : ℝ) =
          (3 / 40) / (4893780690344377 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (568892516491583260051 / 1250000000000000000000 : ℝ)) -
        6 * (760362591960730908383 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (383185431123 / 1600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (383185431123 / 1600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4893780690344377 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (568892516491583260051 / 1250000000000000000000 : ℝ)) -
          6 * (760362591960730908383 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (383185431123 / 1600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (383185431123 / 1600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (383185431123 / 1600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_287 :
    ((541049295860268807619 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(13973617717453968005883 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4915520336340929 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (228433212307367662667 / 500000000000000000000 : ℝ)) -
              6 * (75705104221060272141 / 500000000000000000000 : ℝ)))) ≤
      Vfield (3865974428317 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3865974428317 / 16000000000000 : ℝ)) =
      Real.log (19865974428317 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3865974428317 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3955974428317 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (541049295860268807619 / 2500000000000000000000 : ℝ) ≤
      Real.log (19865974428317 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3955974428317 / 16000000000000 : ℝ) ≤
      (-(13973617717453968005883 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3955974428317 / 16000000000000 : ℝ) = (3955974428317 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3955974428317 / 2000000000000 : ℝ) ≤
            (6820797691546031994117 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4915520336340929 / 10000000000000000 : ℝ) ≤ Real.sqrt (3865974428317 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3865974428317 / 16000000000000 : ℝ) ≤ (1228880084085233 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3865974428317 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau349 :
    Real.arctan (1228880084085233 / 2500000000000000 : ℝ) ≤
      (228433212307367662667 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (228433212307367662667 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1228880084085233 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1228880084085233 : ℝ) =
              (1228880084085233 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau349)
  have hz1 :
    (2500000000000000 / 1228880084085233 : ℝ) ≤
      1 / Real.sqrt (3865974428317 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1228880084085233 : ℝ) = 1 / (1228880084085233 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 4915520336340929 : ℝ) ≤
      (75705104221060272141 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3865974428317 / 16000000000000 : ℝ) ≤
      (750000000000000 / 4915520336340929 : ℝ) := by
    rw [show
        (750000000000000 / 4915520336340929 : ℝ) =
          (3 / 40) / (4915520336340929 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (228433212307367662667 / 500000000000000000000 : ℝ)) -
        6 * (75705104221060272141 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3865974428317 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3865974428317 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4915520336340929 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (228433212307367662667 / 500000000000000000000 : ℝ)) -
          6 * (75705104221060272141 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (3865974428317 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3865974428317 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3865974428317 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_288 :
    ((545339401261763887393 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3471934488122335850373 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4937164257828069 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (36688650063609893199 / 80000000000000000000 : ℝ)) -
              6 * (12060518217518261529 / 80000000000000000000 : ℝ)))) ≤
      Vfield (975023636351 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (975023636351 / 4000000000000 : ℝ)) =
      Real.log (4975023636351 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((975023636351 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (997523636351 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (545339401261763887393 / 2500000000000000000000 : ℝ) ≤
      Real.log (4975023636351 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (997523636351 / 4000000000000 : ℝ) ≤
      (-(3471934488122335850373 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (997523636351 / 4000000000000 : ℝ) = (997523636351 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (997523636351 / 500000000000 : ℝ) ≤
            (1726669364127664149627 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4937164257828069 / 10000000000000000 : ℝ) ≤ Real.sqrt (975023636351 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (975023636351 / 4000000000000 : ℝ) ≤ (617145532228509 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (975023636351 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau350 :
    Real.arctan (617145532228509 / 1250000000000000 : ℝ) ≤
      (36688650063609893199 / 80000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (36688650063609893199 / 80000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 617145532228509 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 617145532228509 : ℝ) =
              (617145532228509 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau350)
  have hz1 :
    (1250000000000000 / 617145532228509 : ℝ) ≤ 1 / Real.sqrt (975023636351 / 4000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 617145532228509 : ℝ) = 1 / (617145532228509 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1645721419276023 : ℝ) ≤
      (12060518217518261529 / 80000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (975023636351 / 4000000000000 : ℝ) ≤
      (250000000000000 / 1645721419276023 : ℝ) := by
    rw [show
        (250000000000000 / 1645721419276023 : ℝ) =
          (3 / 40) / (4937164257828069 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (36688650063609893199 / 80000000000000000000 : ℝ)) -
        6 * (12060518217518261529 / 80000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (975023636351 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (975023636351 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4937164257828069 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (36688650063609893199 / 80000000000000000000 : ℝ)) -
          6 * (12060518217518261529 / 80000000000000000000 : ℝ))) ≤
      Real.sqrt (975023636351 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (975023636351 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (975023636351 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
