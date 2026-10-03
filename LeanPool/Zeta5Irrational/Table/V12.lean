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

/-! # V12: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_145 :
    ((474191423687705405539 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11263927763828573808227 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3154061475050857 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (95478208413835360219 / 312500000000000000000 : ℝ)) -
              6 * (1167265072719666656229 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (24870259471 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (24870259471 / 250000000000 : ℝ)) =
      Real.log (274870259471 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((24870259471 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (26276509471 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (474191423687705405539 / 5000000000000000000000 : ℝ) ≤
      Real.log (274870259471 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (26276509471 / 250000000000 : ℝ) ≤
      (-(11263927763828573808227 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (26276509471 / 250000000000 : ℝ) = (26276509471 / 15625000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26276509471 / 15625000000 : ℝ) ≤
            (2599015842171426191773 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3154061475050857 / 10000000000000000 : ℝ) ≤ Real.sqrt (24870259471 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (24870259471 / 250000000000 : ℝ) ≤ (157703073752543 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (24870259471 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau207 :
    Real.arctan (157703073752543 / 500000000000000 : ℝ) ≤
      (95478208413835360219 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (95478208413835360219 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 157703073752543 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 157703073752543 : ℝ) =
              (157703073752543 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau207)
  have hz1 :
    (500000000000000 / 157703073752543 : ℝ) ≤ 1 / Real.sqrt (24870259471 / 250000000000 : ℝ) := by
    rw [show (500000000000000 / 157703073752543 : ℝ) = 1 / (157703073752543 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3154061475050857 : ℝ) ≤
      (1167265072719666656229 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (24870259471 / 250000000000 : ℝ) ≤
      (750000000000000 / 3154061475050857 : ℝ) := by
    rw [show
        (750000000000000 / 3154061475050857 : ℝ) =
          (3 / 40) / (3154061475050857 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (95478208413835360219 / 312500000000000000000 : ℝ)) -
        6 * (1167265072719666656229 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (24870259471 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (24870259471 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3154061475050857 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (95478208413835360219 / 312500000000000000000 : ℝ)) -
          6 * (1167265072719666656229 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (24870259471 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (24870259471 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (24870259471 / 250000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_146 :
    ((120140089155551917327 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(22395404883448735089487 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((198512470516247 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3075424865340954955163 / 10000000000000000000000 : ℝ)) -
              6 * (2318837467048294312633 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1614118950931 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1614118950931 / 16000000000000 : ℝ)) =
      Real.log (17614118950931 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1614118950931 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1704118950931 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (120140089155551917327 / 1250000000000000000000 : ℝ) ≤
      Real.log (17614118950931 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1704118950931 / 16000000000000 : ℝ) ≤
      (-(22395404883448735089487 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1704118950931 / 16000000000000 : ℝ) = (1704118950931 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1704118950931 / 1000000000000 : ℝ) ≤
            (5330482328551264910513 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (198512470516247 / 625000000000000 : ℝ) ≤ Real.sqrt (1614118950931 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1614118950931 / 16000000000000 : ℝ) ≤ (635239905651991 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1614118950931 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau208 :
    Real.arctan (635239905651991 / 2000000000000000 : ℝ) ≤
      (3075424865340954955163 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3075424865340954955163 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 635239905651991 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 635239905651991 : ℝ) =
              (635239905651991 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau208)
  have hz1 :
    (2000000000000000 / 635239905651991 : ℝ) ≤
      1 / Real.sqrt (1614118950931 / 16000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 635239905651991 : ℝ) = 1 / (635239905651991 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 198512470516247 : ℝ) ≤
      (2318837467048294312633 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1614118950931 / 16000000000000 : ℝ) ≤
      (46875000000000 / 198512470516247 : ℝ) := by
    rw [show
        (46875000000000 / 198512470516247 : ℝ) =
          (3 / 40) / (198512470516247 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3075424865340954955163 / 10000000000000000000000 : ℝ)) -
        6 * (2318837467048294312633 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1614118950931 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1614118950931 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((198512470516247 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3075424865340954955163 / 10000000000000000000000 : ℝ)) -
          6 * (2318837467048294312633 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1614118950931 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1614118950931 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1614118950931 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_147 :
    ((194768474885970078339 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(22264685648903831350143 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((799546086001203 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1547691177866349120623 / 5000000000000000000000 : ℝ)) -
              6 * (575864282886168339093 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (818270647859 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (818270647859 / 8000000000000 : ℝ)) =
      Real.log (8818270647859 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((818270647859 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (863270647859 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (194768474885970078339 / 2000000000000000000000 : ℝ) ≤
      Real.log (8818270647859 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (863270647859 / 8000000000000 : ℝ) ≤
      (-(22264685648903831350143 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (863270647859 / 8000000000000 : ℝ) = (863270647859 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (863270647859 / 500000000000 : ℝ) ≤
            (5461201563096168649857 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (799546086001203 / 2500000000000000 : ℝ) ≤ Real.sqrt (818270647859 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (818270647859 / 8000000000000 : ℝ) ≤ (639636868800963 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (818270647859 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau209 :
    Real.arctan (639636868800963 / 2000000000000000 : ℝ) ≤
      (1547691177866349120623 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1547691177866349120623 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 639636868800963 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 639636868800963 : ℝ) =
              (639636868800963 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau209)
  have hz1 :
    (2000000000000000 / 639636868800963 : ℝ) ≤ 1 / Real.sqrt (818270647859 / 8000000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 639636868800963 : ℝ) = 1 / (639636868800963 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 266515362000401 : ℝ) ≤
      (575864282886168339093 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (818270647859 / 8000000000000 : ℝ) ≤
      (62500000000000 / 266515362000401 : ℝ) := by
    rw [show
        (62500000000000 / 266515362000401 : ℝ) =
          (3 / 40) / (799546086001203 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1547691177866349120623 / 5000000000000000000000 : ℝ)) -
        6 * (575864282886168339093 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (818270647859 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (818270647859 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((799546086001203 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1547691177866349120623 / 5000000000000000000000 : ℝ)) -
          6 * (575864282886168339093 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (818270647859 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (818270647859 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (818270647859 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_148 :
    ((98654787210944095483 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(22135653141131857303987 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3220019060992689 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (124607136184504540319 / 400000000000000000000 : ℝ)) -
              6 * (457675782124995330019 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (331792728101 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (331792728101 / 3200000000000 : ℝ)) =
      Real.log (3531792728101 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((331792728101 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (349792728101 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (98654787210944095483 / 1000000000000000000000 : ℝ) ≤
      Real.log (3531792728101 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (349792728101 / 3200000000000 : ℝ) ≤
      (-(22135653141131857303987 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (349792728101 / 3200000000000 : ℝ) = (349792728101 / 200000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (349792728101 / 200000000000 : ℝ) ≤
            (5590234070868142696013 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3220019060992689 / 10000000000000000 : ℝ) ≤ Real.sqrt (331792728101 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (331792728101 / 3200000000000 : ℝ) ≤ (805004765248173 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (331792728101 / 3200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau210 :
    Real.arctan (805004765248173 / 2500000000000000 : ℝ) ≤
      (124607136184504540319 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (124607136184504540319 / 400000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 805004765248173 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 805004765248173 : ℝ) =
              (805004765248173 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau210)
  have hz1 :
    (2500000000000000 / 805004765248173 : ℝ) ≤ 1 / Real.sqrt (331792728101 / 3200000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 805004765248173 : ℝ) = 1 / (805004765248173 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1073339686997563 : ℝ) ≤
      (457675782124995330019 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (331792728101 / 3200000000000 : ℝ) ≤
      (250000000000000 / 1073339686997563 : ℝ) := by
    rw [show
        (250000000000000 / 1073339686997563 : ℝ) =
          (3 / 40) / (3220019060992689 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (124607136184504540319 / 400000000000000000000 : ℝ)) -
        6 * (457675782124995330019 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (331792728101 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (331792728101 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3220019060992689 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (124607136184504540319 / 400000000000000000000 : ℝ)) -
          6 * (457675782124995330019 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (331792728101 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (331792728101 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (331792728101 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_149 :
    ((496447286229849446731 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4414351183143760254287 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3230881084257917 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (781254219709386649659 / 2500000000000000000000 : ℝ)) -
              6 * (1140475012063116264297 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3340349625797 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3340349625797 / 32000000000000 : ℝ)) =
      Real.log (35340349625797 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3340349625797 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3520349625797 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (496447286229849446731 / 5000000000000000000000 : ℝ) ≤
      Real.log (35340349625797 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3520349625797 / 32000000000000 : ℝ) ≤
      (-(4414351183143760254287 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3520349625797 / 32000000000000 : ℝ) = (3520349625797 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3520349625797 / 2000000000000 : ℝ) ≤
            (1130826259256239745713 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3230881084257917 / 10000000000000000 : ℝ) ≤ Real.sqrt (3340349625797 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3340349625797 / 32000000000000 : ℝ) ≤ (5048251694153 / 15625000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3340349625797 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau211 :
    Real.arctan (5048251694153 / 15625000000000 : ℝ) ≤
      (781254219709386649659 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (781254219709386649659 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (15625000000000 / 5048251694153 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (15625000000000 / 5048251694153 : ℝ) = (5048251694153 / 15625000000000 : ℝ)
            by
        norm_num];
        exact hau211)
  have hz1 :
    (15625000000000 / 5048251694153 : ℝ) ≤ 1 / Real.sqrt (3340349625797 / 32000000000000 : ℝ) := by
    rw [show (15625000000000 / 5048251694153 : ℝ) = 1 / (5048251694153 / 15625000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3230881084257917 : ℝ) ≤
      (1140475012063116264297 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3340349625797 / 32000000000000 : ℝ) ≤
      (750000000000000 / 3230881084257917 : ℝ) := by
    rw [show
        (750000000000000 / 3230881084257917 : ℝ) =
          (3 / 40) / (3230881084257917 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (781254219709386649659 / 2500000000000000000000 : ℝ)) -
        6 * (1140475012063116264297 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3340349625797 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3340349625797 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3230881084257917 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (781254219709386649659 / 2500000000000000000000 : ℝ)) -
          6 * (1140475012063116264297 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3340349625797 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3340349625797 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3340349625797 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_150 :
    ((499618623652078033613 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(22008264384942687831393 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((648341342444703 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (313481616803270820263 / 1000000000000000000000 : ℝ)) -
              6 * (2273593038966975577993 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (420346496323 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (420346496323 / 4000000000000 : ℝ)) =
      Real.log (4420346496323 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((420346496323 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (442846496323 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (499618623652078033613 / 5000000000000000000000 : ℝ) ≤
      Real.log (4420346496323 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (442846496323 / 4000000000000 : ℝ) ≤
      (-(22008264384942687831393 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (442846496323 / 4000000000000 : ℝ) = (442846496323 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (442846496323 / 250000000000 : ℝ) ≤
            (5717622827057312168607 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (648341342444703 / 2000000000000000 : ℝ) ≤ Real.sqrt (420346496323 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (420346496323 / 4000000000000 : ℝ) ≤ (1620853356111759 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (420346496323 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau212 :
    Real.arctan (1620853356111759 / 5000000000000000 : ℝ) ≤
      (313481616803270820263 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (313481616803270820263 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1620853356111759 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1620853356111759 : ℝ) =
              (1620853356111759 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau212)
  have hz1 :
    (5000000000000000 / 1620853356111759 : ℝ) ≤
      1 / Real.sqrt (420346496323 / 4000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1620853356111759 : ℝ) = 1 / (1620853356111759 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 216113780814901 : ℝ) ≤
      (2273593038966975577993 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (420346496323 / 4000000000000 : ℝ) ≤
      (50000000000000 / 216113780814901 : ℝ) := by
    rw [show
        (50000000000000 / 216113780814901 : ℝ) =
          (3 / 40) / (648341342444703 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (313481616803270820263 / 1000000000000000000000 : ℝ)) -
        6 * (2273593038966975577993 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (420346496323 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (420346496323 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((648341342444703 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (313481616803270820263 / 1000000000000000000000 : ℝ)) -
          6 * (2273593038966975577993 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (420346496323 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (420346496323 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (420346496323 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_151 :
    ((201115180349214172211 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2194517342963678964519 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1626248154152247 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3144576650626855419069 / 10000000000000000000000 : ℝ)) -
              6 * (18130454419663968323 / 80000000000000000000 : ℝ)))) ≤
      Vfield (3385194315371 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3385194315371 / 32000000000000 : ℝ)) =
      Real.log (35385194315371 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3385194315371 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3565194315371 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (201115180349214172211 / 2000000000000000000000 : ℝ) ≤
      Real.log (35385194315371 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3565194315371 / 32000000000000 : ℝ) ≤
      (-(2194517342963678964519 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3565194315371 / 32000000000000 : ℝ) = (3565194315371 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3565194315371 / 2000000000000 : ℝ) ≤
            (578071378236321035481 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1626248154152247 / 5000000000000000 : ℝ) ≤ Real.sqrt (3385194315371 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3385194315371 / 32000000000000 : ℝ) ≤ (3252496308304497 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3385194315371 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau213 :
    Real.arctan (3252496308304497 / 10000000000000000 : ℝ) ≤
      (3144576650626855419069 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3144576650626855419069 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3252496308304497 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3252496308304497 : ℝ) =
              (3252496308304497 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau213)
  have hz1 :
    (10000000000000000 / 3252496308304497 : ℝ) ≤
      1 / Real.sqrt (3385194315371 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3252496308304497 : ℝ) =
          1 / (3252496308304497 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 542082718050749 : ℝ) ≤
      (18130454419663968323 / 80000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3385194315371 / 32000000000000 : ℝ) ≤
      (125000000000000 / 542082718050749 : ℝ) := by
    rw [show
        (125000000000000 / 542082718050749 : ℝ) =
          (3 / 40) / (1626248154152247 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3144576650626855419069 / 10000000000000000000000 : ℝ)) -
        6 * (18130454419663968323 / 80000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3385194315371 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3385194315371 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1626248154152247 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3144576650626855419069 / 10000000000000000000000 : ℝ)) -
          6 * (18130454419663968323 / 80000000000000000000 : ℝ))) ≤
      Real.sqrt (3385194315371 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3385194315371 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3385194315371 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_152 :
    ((1011910540879013487081 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21882478026919803602261 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1631625114953933 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (630859739779612780437 / 2000000000000000000000 : ℝ)) -
              6 * (2259090187622654074271 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1703808330079 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1703808330079 / 16000000000000 : ℝ)) =
      Real.log (17703808330079 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1703808330079 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1793808330079 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1011910540879013487081 / 10000000000000000000000 : ℝ) ≤
      Real.log (17703808330079 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1793808330079 / 16000000000000 : ℝ) ≤
      (-(21882478026919803602261 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1793808330079 / 16000000000000 : ℝ) = (1793808330079 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1793808330079 / 1000000000000 : ℝ) ≤
            (5843409185080196397739 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1631625114953933 / 5000000000000000 : ℝ) ≤ Real.sqrt (1703808330079 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1703808330079 / 16000000000000 : ℝ) ≤ (3263250229907869 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1703808330079 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau214 :
    Real.arctan (3263250229907869 / 10000000000000000 : ℝ) ≤
      (630859739779612780437 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (630859739779612780437 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3263250229907869 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3263250229907869 : ℝ) =
              (3263250229907869 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau214)
  have hz1 :
    (10000000000000000 / 3263250229907869 : ℝ) ≤
      1 / Real.sqrt (1703808330079 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3263250229907869 : ℝ) =
          1 / (3263250229907869 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1631625114953933 : ℝ) ≤
      (2259090187622654074271 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1703808330079 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1631625114953933 : ℝ) := by
    rw [show
        (375000000000000 / 1631625114953933 : ℝ) =
          (3 / 40) / (1631625114953933 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (630859739779612780437 / 2000000000000000000000 : ℝ)) -
        6 * (2259090187622654074271 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1703808330079 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1703808330079 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1631625114953933 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (630859739779612780437 / 2000000000000000000000 : ℝ)) -
          6 * (2259090187622654074271 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1703808330079 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1703808330079 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1703808330079 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_153 :
    ((2545602924467127949 / 25000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21820173247796202238733 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1636984414285389 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3163982679114103670613 / 10000000000000000000000 : ℝ)) -
              6 * (225194209246394264897 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (686007800989 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (686007800989 / 6400000000000 : ℝ)) =
      Real.log (7086007800989 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((686007800989 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (722007800989 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2545602924467127949 / 25000000000000000000 : ℝ) ≤
      Real.log (7086007800989 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (722007800989 / 6400000000000 : ℝ) ≤
      (-(21820173247796202238733 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (722007800989 / 6400000000000 : ℝ) = (722007800989 / 400000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (722007800989 / 400000000000 : ℝ) ≤
            (5905713964203797761267 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1636984414285389 / 5000000000000000 : ℝ) ≤ Real.sqrt (686007800989 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (686007800989 / 6400000000000 : ℝ) ≤ (3273968828570781 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (686007800989 / 6400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau215 :
    Real.arctan (3273968828570781 / 10000000000000000 : ℝ) ≤
      (3163982679114103670613 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3163982679114103670613 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3273968828570781 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3273968828570781 : ℝ) =
              (3273968828570781 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau215)
  have hz1 :
    (10000000000000000 / 3273968828570781 : ℝ) ≤
      1 / Real.sqrt (686007800989 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3273968828570781 : ℝ) =
          1 / (3273968828570781 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 545661471428463 : ℝ) ≤
      (225194209246394264897 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (686007800989 / 6400000000000 : ℝ) ≤
      (125000000000000 / 545661471428463 : ℝ) := by
    rw [show
        (125000000000000 / 545661471428463 : ℝ) =
          (3 / 40) / (1636984414285389 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3163982679114103670613 / 10000000000000000000000 : ℝ)) -
        6 * (225194209246394264897 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (686007800989 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (686007800989 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1636984414285389 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3163982679114103670613 / 10000000000000000000000 : ℝ)) -
          6 * (225194209246394264897 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (686007800989 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (686007800989 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (686007800989 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_154 :
    ((1024567793543830700313 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21758254254830878525977 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((656930490018921 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3173628951668722226459 / 10000000000000000000000 : ℝ)) -
              6 * (89794457570276818707 / 400000000000000000000 : ℝ)))) ≤
      Vfield (863115337433 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (863115337433 / 8000000000000 : ℝ)) =
      Real.log (8863115337433 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((863115337433 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (908115337433 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1024567793543830700313 / 10000000000000000000000 : ℝ) ≤
      Real.log (8863115337433 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (908115337433 / 8000000000000 : ℝ) ≤
      (-(21758254254830878525977 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (908115337433 / 8000000000000 : ℝ) = (908115337433 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (908115337433 / 500000000000 : ℝ) ≤
            (5967632957169121474023 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (656930490018921 / 2000000000000000 : ℝ) ≤ Real.sqrt (863115337433 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (863115337433 / 8000000000000 : ℝ) ≤ (205290778130913 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (863115337433 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau216 :
    Real.arctan (205290778130913 / 625000000000000 : ℝ) ≤
      (3173628951668722226459 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3173628951668722226459 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 205290778130913 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 205290778130913 : ℝ) =
              (205290778130913 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau216)
  have hz1 :
    (625000000000000 / 205290778130913 : ℝ) ≤ 1 / Real.sqrt (863115337433 / 8000000000000 : ℝ) := by
    rw [show (625000000000000 / 205290778130913 : ℝ) = 1 / (205290778130913 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 218976830006307 : ℝ) ≤
      (89794457570276818707 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (863115337433 / 8000000000000 : ℝ) ≤
      (50000000000000 / 218976830006307 : ℝ) := by
    rw [show
        (50000000000000 / 218976830006307 : ℝ) =
          (3 / 40) / (656930490018921 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3173628951668722226459 / 10000000000000000000000 : ℝ)) -
        6 * (89794457570276818707 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (863115337433 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (863115337433 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((656930490018921 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3173628951668722226459 / 10000000000000000000000 : ℝ)) -
          6 * (89794457570276818707 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (863115337433 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (863115337433 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (863115337433 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_155 :
    ((20554592101476308083 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21727437940939080223441 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1644990625478013 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1589219029311252440703 / 5000000000000000000000 : ℝ)) -
              6 * (448269214612905134469 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (6927345044251 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6927345044251 / 64000000000000 : ℝ)) =
      Real.log (70927345044251 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6927345044251 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7287345044251 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (20554592101476308083 / 200000000000000000000 : ℝ) ≤
      Real.log (70927345044251 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7287345044251 / 64000000000000 : ℝ) ≤
      (-(21727437940939080223441 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7287345044251 / 64000000000000 : ℝ) = (7287345044251 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7287345044251 / 4000000000000 : ℝ) ≤
            (5998449271060919776559 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1644990625478013 / 5000000000000000 : ℝ) ≤ Real.sqrt (6927345044251 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6927345044251 / 64000000000000 : ℝ) ≤ (3289981250956029 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6927345044251 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau217 :
    Real.arctan (3289981250956029 / 10000000000000000 : ℝ) ≤
      (1589219029311252440703 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1589219029311252440703 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3289981250956029 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3289981250956029 : ℝ) =
              (3289981250956029 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau217)
  have hz1 :
    (10000000000000000 / 3289981250956029 : ℝ) ≤
      1 / Real.sqrt (6927345044251 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3289981250956029 : ℝ) =
          1 / (3289981250956029 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 548330208492671 : ℝ) ≤
      (448269214612905134469 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6927345044251 / 64000000000000 : ℝ) ≤
      (125000000000000 / 548330208492671 : ℝ) := by
    rw [show
        (125000000000000 / 548330208492671 : ℝ) =
          (3 / 40) / (1644990625478013 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1589219029311252440703 / 5000000000000000000000 : ℝ)) -
        6 * (448269214612905134469 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6927345044251 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6927345044251 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1644990625478013 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1589219029311252440703 / 5000000000000000000000 : ℝ)) -
          6 * (448269214612905134469 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (6927345044251 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6927345044251 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6927345044251 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_156 :
    ((1030890417214564711111 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10848358149947670282237 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1647650717337557 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (795809467803487892921 / 2500000000000000000000 : ℝ)) -
              6 * (279730896733188049123 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (3474883694519 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3474883694519 / 32000000000000 : ℝ)) =
      Real.log (35474883694519 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3474883694519 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3654883694519 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1030890417214564711111 / 10000000000000000000000 : ℝ) ≤
      Real.log (35474883694519 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3654883694519 / 32000000000000 : ℝ) ≤
      (-(10848358149947670282237 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3654883694519 / 32000000000000 : ℝ) = (3654883694519 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3654883694519 / 2000000000000 : ℝ) ≤
            (3014585456052329717763 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1647650717337557 / 5000000000000000 : ℝ) ≤ Real.sqrt (3474883694519 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3474883694519 / 32000000000000 : ℝ) ≤ (3295301434675117 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3474883694519 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau218 :
    Real.arctan (3295301434675117 / 10000000000000000 : ℝ) ≤
      (795809467803487892921 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (795809467803487892921 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3295301434675117 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3295301434675117 : ℝ) =
              (3295301434675117 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau218)
  have hz1 :
    (10000000000000000 / 3295301434675117 : ℝ) ≤
      1 / Real.sqrt (3474883694519 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3295301434675117 : ℝ) =
          1 / (3295301434675117 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1647650717337557 : ℝ) ≤
      (279730896733188049123 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3474883694519 / 32000000000000 : ℝ) ≤
      (375000000000000 / 1647650717337557 : ℝ) := by
    rw [show
        (375000000000000 / 1647650717337557 : ℝ) =
          (3 / 40) / (1647650717337557 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (795809467803487892921 / 2500000000000000000000 : ℝ)) -
        6 * (279730896733188049123 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3474883694519 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3474883694519 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1647650717337557 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (795809467803487892921 / 2500000000000000000000 : ℝ)) -
          6 * (279730896733188049123 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (3474883694519 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3474883694519 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3474883694519 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
