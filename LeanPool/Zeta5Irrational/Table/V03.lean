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

/-! # V03: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_37 :
    ((21048393928938516659 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(41224495654581728135701 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((20571602866087 / 200000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1024975616002557514417 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (630029876112921474829 / 2000000000000000000000 : ℝ))))) ≤
      Vfield (1322471389 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1322471389 / 125000000000 : ℝ)) = Real.log (126322471389 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1322471389 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2025596389 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (21048393928938516659 / 2000000000000000000000 : ℝ) ≤
      Real.log (126322471389 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2025596389 / 125000000000 : ℝ) ≤
      (-(41224495654581728135701 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (2025596389 / 125000000000 : ℝ) = (2025596389 / 1953125000 : ℝ) / 2 ^ 6 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2025596389 / 1953125000 : ℝ) ≤
            (364335163418271864299 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (20571602866087 / 200000000000000 : ℝ) ≤ Real.sqrt (1322471389 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1322471389 / 125000000000 : ℝ) ≤ (1028580143304353 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1322471389 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau82 :
    Real.arctan (1028580143304353 / 10000000000000000 : ℝ) ≤
      (1024975616002557514417 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1024975616002557514417 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1028580143304353 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1028580143304353 : ℝ) =
              (1028580143304353 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau82)
  have hz1 :
    (10000000000000000 / 1028580143304353 : ℝ) ≤ 1 / Real.sqrt (1322471389 / 125000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1028580143304353 : ℝ) =
          1 / (1028580143304353 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau83 :
    Real.arctan (75000000000000000000000000000 / 230155976262274147498241660923 : ℝ) ≤
      (630029876112921474829 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (15000000000000 / 20571602866087 : ℝ) ≤
      (2 * (630029876112921474829 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6188042942521229 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (15000000000000 / 20571602866087 : ℝ) ^ 2))
      (by
        rw [show
            (15000000000000 / 20571602866087 : ℝ) /
                (1 + (6188042942521229 / 5000000000000000 : ℝ)) =
              (75000000000000000000000000000 / 230155976262274147498241660923 : ℝ)
            by
        norm_num];
        exact hau83)
  have hz2 :
    (3 / 40) / Real.sqrt (1322471389 / 125000000000 : ℝ) ≤
      (15000000000000 / 20571602866087 : ℝ) := by
    rw [show
        (15000000000000 / 20571602866087 : ℝ) = (3 / 40) / (20571602866087 / 200000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1024975616002557514417 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (630029876112921474829 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1322471389 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1322471389 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((20571602866087 / 200000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1024975616002557514417 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (630029876112921474829 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt (1322471389 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1322471389 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1322471389 / 125000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_38 :
    ((113091190668515940261 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(40746414146378761469201 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1066457167564641 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1062441486169975621307 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (3064563126433209565083 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (4549323561 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4549323561 / 400000000000 : ℝ)) = Real.log (404549323561 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4549323561 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6799323561 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (113091190668515940261 / 10000000000000000000000 : ℝ) ≤
      Real.log (404549323561 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6799323561 / 400000000000 : ℝ) ≤
      (-(40746414146378761469201 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (6799323561 / 400000000000 : ℝ) = (6799323561 / 6250000000 : ℝ) / 2 ^ 6 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6799323561 / 6250000000 : ℝ) ≤
            (842416671621238530799 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1066457167564641 / 10000000000000000 : ℝ) ≤ Real.sqrt (4549323561 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4549323561 / 400000000000 : ℝ) ≤ (266614291891161 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4549323561 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau84 :
    Real.arctan (266614291891161 / 2500000000000000 : ℝ) ≤
      (1062441486169975621307 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1062441486169975621307 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 266614291891161 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 266614291891161 : ℝ) =
              (266614291891161 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau84)
  have hz1 :
    (2500000000000000 / 266614291891161 : ℝ) ≤ 1 / Real.sqrt (4549323561 / 400000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 266614291891161 : ℝ) = 1 / (266614291891161 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau85 :
    Real.arctan (2500000000000000000000000000000 / 7900775987878507578486688127791 : ℝ) ≤
      (3064563126433209565083 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 355485722521547 : ℝ) ≤
      (2 * (3064563126433209565083 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12225297634561453 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (250000000000000 / 355485722521547 : ℝ) ^ 2))
      (by
        rw [show
            (250000000000000 / 355485722521547 : ℝ) /
                (1 + (12225297634561453 / 10000000000000000 : ℝ)) =
              (2500000000000000000000000000000 / 7900775987878507578486688127791 : ℝ)
            by
        norm_num];
        exact hau85)
  have hz2 :
    (3 / 40) / Real.sqrt (4549323561 / 400000000000 : ℝ) ≤
      (250000000000000 / 355485722521547 : ℝ) := by
    rw [show
        (250000000000000 / 355485722521547 : ℝ) =
          (3 / 40) / (1066457167564641 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1062441486169975621307 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (3064563126433209565083 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4549323561 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4549323561 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1066457167564641 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1062441486169975621307 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (3064563126433209565083 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (4549323561 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4549323561 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4549323561 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_39 :
    ((120934255497089002089 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8058029952033732590147 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((551517150526617 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (549296596867263340437 / 5000000000000000000000 : ℝ)) -
              6 * (2 * (1492843499897578576763 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (12166846693 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (12166846693 / 1000000000000 : ℝ)) =
      Real.log (1012166846693 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((12166846693 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (17791846693 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (120934255497089002089 / 10000000000000000000000 : ℝ) ≤
      Real.log (1012166846693 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (17791846693 / 1000000000000 : ℝ) ≤
      (-(8058029952033732590147 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (17791846693 / 1000000000000 : ℝ) = (17791846693 / 15625000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17791846693 / 15625000000 : ℝ) ≤
            (259736211566267409853 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (551517150526617 / 5000000000000000 : ℝ) ≤ Real.sqrt (12166846693 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (12166846693 / 1000000000000 : ℝ) ≤ (1103034301053237 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (12166846693 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau86 :
    Real.arctan (1103034301053237 / 10000000000000000 : ℝ) ≤
      (549296596867263340437 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (549296596867263340437 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1103034301053237 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1103034301053237 : ℝ) =
              (1103034301053237 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau86)
  have hz1 :
    (10000000000000000 / 1103034301053237 : ℝ) ≤
      1 / Real.sqrt (12166846693 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1103034301053237 : ℝ) =
          1 / (1103034301053237 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau87 :
    Real.arctan (50000000000000000000000000000 / 162459674291281643418659719961 : ℝ) ≤
      (1492843499897578576763 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (125000000000000 / 183839050175539 : ℝ) ≤
      (2 * (1492843499897578576763 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (483706014234499 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (125000000000000 / 183839050175539 : ℝ) ^ 2))
      (by
        rw [show
            (125000000000000 / 183839050175539 : ℝ) /
                (1 + (483706014234499 / 400000000000000 : ℝ)) =
              (50000000000000000000000000000 / 162459674291281643418659719961 : ℝ)
            by
        norm_num];
        exact hau87)
  have hz2 :
    (3 / 40) / Real.sqrt (12166846693 / 1000000000000 : ℝ) ≤
      (125000000000000 / 183839050175539 : ℝ) := by
    rw [show
        (125000000000000 / 183839050175539 : ℝ) =
          (3 / 40) / (551517150526617 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (549296596867263340437 / 5000000000000000000000 : ℝ)) -
        6 * (2 * (1492843499897578576763 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (12166846693 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (12166846693 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((551517150526617 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (549296596867263340437 / 5000000000000000000000 : ℝ)) -
          6 * (2 * (1492843499897578576763 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (12166846693 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (12166846693 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (12166846693 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_40 :
    ((152245145501698111849 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(38648533017005889889951 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((309646954762597 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (154038970346850627713 / 1250000000000000000000 : ℝ)) -
              6 * (2 * (2722372641804015738093 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (3068199571 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3068199571 / 200000000000 : ℝ)) = Real.log (203068199571 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3068199571 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4193199571 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (152245145501698111849 / 10000000000000000000000 : ℝ) ≤
      Real.log (203068199571 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4193199571 / 200000000000 : ℝ) ≤
      (-(38648533017005889889951 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (4193199571 / 200000000000 : ℝ) = (4193199571 / 3125000000 : ℝ) / 2 ^ 6 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4193199571 / 3125000000 : ℝ) ≤
            (2940297800994110110049 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (309646954762597 / 2500000000000000 : ℝ) ≤ Real.sqrt (3068199571 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3068199571 / 200000000000 : ℝ) ≤ (1238587819050391 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3068199571 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau88 :
    Real.arctan (1238587819050391 / 10000000000000000 : ℝ) ≤
      (154038970346850627713 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (154038970346850627713 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1238587819050391 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1238587819050391 : ℝ) =
              (1238587819050391 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau88)
  have hz1 :
    (10000000000000000 / 1238587819050391 : ℝ) ≤ 1 / Real.sqrt (3068199571 / 200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1238587819050391 : ℝ) =
          1 / (1238587819050391 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau89 :
    Real.arctan (1875000000000000000000000000000 / 6716379582333321103149502846301 : ℝ) ≤
      (2722372641804015738093 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (187500000000000 / 309646954762597 : ℝ) ≤
      (2 * (2722372641804015738093 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11690442870599833 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (187500000000000 / 309646954762597 : ℝ) ^ 2))
      (by
        rw [show
            (187500000000000 / 309646954762597 : ℝ) /
                (1 + (11690442870599833 / 10000000000000000 : ℝ)) =
              (1875000000000000000000000000000 / 6716379582333321103149502846301 : ℝ)
            by
        norm_num];
        exact hau89)
  have hz2 :
    (3 / 40) / Real.sqrt (3068199571 / 200000000000 : ℝ) ≤
      (187500000000000 / 309646954762597 : ℝ) := by
    rw [show
        (187500000000000 / 309646954762597 : ℝ) =
          (3 / 40) / (309646954762597 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (154038970346850627713 / 1250000000000000000000 : ℝ)) -
        6 * (2 * (2722372641804015738093 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3068199571 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3068199571 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((309646954762597 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (154038970346850627713 / 1250000000000000000000 : ℝ)) -
          6 * (2 * (2722372641804015738093 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (3068199571 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3068199571 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3068199571 / 200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_41 :
    ((158638233080768093329 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(38343528723300591384029 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((126452844113181 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (251570460987800448443 / 2000000000000000000000 : ℝ)) -
              6 * (2 * (1338338273905248023557 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (255845148549 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (255845148549 / 16000000000000 : ℝ)) =
      Real.log (16255845148549 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((255845148549 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (345845148549 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (158638233080768093329 / 10000000000000000000000 : ℝ) ≤
      Real.log (16255845148549 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (345845148549 / 16000000000000 : ℝ) ≤
      (-(38343528723300591384029 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (345845148549 / 16000000000000 : ℝ) = (345845148549 / 250000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (345845148549 / 250000000000 : ℝ) ≤
            (3245302094699408615971 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (126452844113181 / 1000000000000000 : ℝ) ≤ Real.sqrt (255845148549 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (255845148549 / 16000000000000 : ℝ) ≤ (1264528441131813 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (255845148549 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau90 :
    Real.arctan (1264528441131813 / 10000000000000000 : ℝ) ≤
      (251570460987800448443 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (251570460987800448443 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1264528441131813 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1264528441131813 : ℝ) =
              (1264528441131813 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau90)
  have hz1 :
    (10000000000000000 / 1264528441131813 : ℝ) ≤
      1 / Real.sqrt (255845148549 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1264528441131813 : ℝ) =
          1 / (1264528441131813 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau91 :
    Real.arctan (25000000000000000000000000000 / 91158115069490436044377004569 : ℝ) ≤
      (1338338273905248023557 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (25000000000000 / 42150948037727 : ℝ) ≤
      (2 * (1338338273905248023557 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1162658713818247 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (25000000000000 / 42150948037727 : ℝ) ^ 2))
      (by
        rw [show
            (25000000000000 / 42150948037727 : ℝ) /
                (1 + (1162658713818247 / 1000000000000000 : ℝ)) =
              (25000000000000000000000000000 / 91158115069490436044377004569 : ℝ)
            by
        norm_num];
        exact hau91)
  have hz2 :
    (3 / 40) / Real.sqrt (255845148549 / 16000000000000 : ℝ) ≤
      (25000000000000 / 42150948037727 : ℝ) := by
    rw [show
        (25000000000000 / 42150948037727 : ℝ) =
          (3 / 40) / (126452844113181 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (251570460987800448443 / 2000000000000000000000 : ℝ)) -
        6 * (2 * (1338338273905248023557 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (255845148549 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (255845148549 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((126452844113181 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (251570460987800448443 / 2000000000000000000000 : ℝ)) -
          6 * (2 * (1338338273905248023557 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (255845148549 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (255845148549 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (255845148549 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_42 :
    ((165027236114105152063 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4755944063788979246611 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1289947507212017 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (160357918015002146829 / 1250000000000000000000 : ℝ)) -
              6 * (2 * (2633224767274595554807 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (133117165709 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (133117165709 / 8000000000000 : ℝ)) =
      Real.log (8133117165709 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((133117165709 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (178117165709 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (165027236114105152063 / 10000000000000000000000 : ℝ) ≤
      Real.log (8133117165709 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (178117165709 / 8000000000000 : ℝ) ≤
      (-(4755944063788979246611 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (178117165709 / 8000000000000 : ℝ) = (178117165709 / 125000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (178117165709 / 125000000000 : ℝ) ≤
            (442659788461020753389 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1289947507212017 / 10000000000000000 : ℝ) ≤ Real.sqrt (133117165709 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (133117165709 / 8000000000000 : ℝ) ≤ (64497375360601 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (133117165709 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau92 :
    Real.arctan (64497375360601 / 500000000000000 : ℝ) ≤
      (160357918015002146829 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (160357918015002146829 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 64497375360601 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 64497375360601 : ℝ) =
              (64497375360601 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau92)
  have hz1 :
    (500000000000000 / 64497375360601 : ℝ) ≤ 1 / Real.sqrt (133117165709 / 8000000000000 : ℝ) := by
    rw [show (500000000000000 / 64497375360601 : ℝ) = 1 / (64497375360601 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau93 :
    Real.arctan (7500000000000000000000000000000 / 27820817409063237865736181214393 : ℝ) ≤
      (2633224767274595554807 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1289947507212017 : ℝ) ≤
      (2 * (2633224767274595554807 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11567402745862729 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1289947507212017 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1289947507212017 : ℝ) /
                (1 + (11567402745862729 / 10000000000000000 : ℝ)) =
              (7500000000000000000000000000000 / 27820817409063237865736181214393 : ℝ)
            by
        norm_num];
        exact hau93)
  have hz2 :
    (3 / 40) / Real.sqrt (133117165709 / 8000000000000 : ℝ) ≤
      (750000000000000 / 1289947507212017 : ℝ) := by
    rw [show
        (750000000000000 / 1289947507212017 : ℝ) =
          (3 / 40) / (1289947507212017 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (160357918015002146829 / 1250000000000000000000 : ℝ)) -
        6 * (2 * (2633224767274595554807 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (133117165709 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (133117165709 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1289947507212017 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (160357918015002146829 / 1250000000000000000000 : ℝ)) -
          6 * (2 * (2633224767274595554807 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (133117165709 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (133117165709 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (133117165709 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_43 :
    ((168220207556483795939 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(37902785946772965577681 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((130247102379597 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (647589960594501769007 / 5000000000000000000000 : ℝ)) -
              6 * (2 * (1306141833947405153479 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (108571569141 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (108571569141 / 6400000000000 : ℝ)) =
      Real.log (6508571569141 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((108571569141 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (144571569141 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (168220207556483795939 / 10000000000000000000000 : ℝ) ≤
      Real.log (6508571569141 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (144571569141 / 6400000000000 : ℝ) ≤
      (-(37902785946772965577681 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (144571569141 / 6400000000000 : ℝ) = (144571569141 / 100000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (144571569141 / 100000000000 : ℝ) ≤
            (3686044871227034422319 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (130247102379597 / 1000000000000000 : ℝ) ≤ Real.sqrt (108571569141 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (108571569141 / 6400000000000 : ℝ) ≤ (1302471023795973 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (108571569141 / 6400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau94 :
    Real.arctan (1302471023795973 / 10000000000000000 : ℝ) ≤
      (647589960594501769007 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (647589960594501769007 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1302471023795973 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1302471023795973 : ℝ) =
              (1302471023795973 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau94)
  have hz1 :
    (10000000000000000 / 1302471023795973 : ℝ) ≤
      1 / Real.sqrt (108571569141 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1302471023795973 : ℝ) =
          1 / (1302471023795973 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau95 :
    Real.arctan (1953125000000000000000000000 / 7305846349559108574878267487 : ℝ) ≤
      (1306141833947405153479 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (25000000000000 / 43415700793199 : ℝ) ≤
      (2 * (1306141833947405153479 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (90151596164113 / 78125000000000 : ℝ) ≤
          Real.sqrt (1 + (25000000000000 / 43415700793199 : ℝ) ^ 2))
      (by
        rw [show
            (25000000000000 / 43415700793199 : ℝ) / (1 + (90151596164113 / 78125000000000 : ℝ)) =
              (1953125000000000000000000000 / 7305846349559108574878267487 : ℝ)
            by
        norm_num];
        exact hau95)
  have hz2 :
    (3 / 40) / Real.sqrt (108571569141 / 6400000000000 : ℝ) ≤
      (25000000000000 / 43415700793199 : ℝ) := by
    rw [show
        (25000000000000 / 43415700793199 : ℝ) =
          (3 / 40) / (130247102379597 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (647589960594501769007 / 5000000000000000000000 : ℝ)) -
        6 * (2 * (1306141833947405153479 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (108571569141 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (108571569141 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((130247102379597 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (647589960594501769007 / 5000000000000000000000 : ℝ)) -
          6 * (2 * (1306141833947405153479 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (108571569141 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (108571569141 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (108571569141 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_44 :
    ((42853039954403033183 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7552017049555776737193 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1314875265678743 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (653687650225280262137 / 5000000000000000000000 : ℝ)) -
              6 * (2 * (1295919005291486724873 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (276623514287 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (276623514287 / 16000000000000 : ℝ)) =
      Real.log (16276623514287 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((276623514287 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (366623514287 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (42853039954403033183 / 2500000000000000000000 : ℝ) ≤
      Real.log (16276623514287 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (366623514287 / 16000000000000 : ℝ) ≤
      (-(7552017049555776737193 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (366623514287 / 16000000000000 : ℝ) = (366623514287 / 250000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (366623514287 / 250000000000 : ℝ) ≤
            (765749114044223262807 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1314875265678743 / 10000000000000000 : ℝ) ≤ Real.sqrt (276623514287 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (276623514287 / 16000000000000 : ℝ) ≤ (657437632839373 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (276623514287 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau96 :
    Real.arctan (657437632839373 / 5000000000000000 : ℝ) ≤
      (653687650225280262137 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (653687650225280262137 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 657437632839373 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 657437632839373 : ℝ) =
              (657437632839373 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau96)
  have hz1 :
    (5000000000000000 / 657437632839373 : ℝ) ≤
      1 / Real.sqrt (276623514287 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 657437632839373 : ℝ) = 1 / (657437632839373 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau97 :
    Real.arctan (7500000000000000000000000000000 / 28286113603444361580753162742349 : ℝ) ≤
      (1295919005291486724873 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1314875265678743 : ℝ) ≤
      (2 * (1295919005291486724873 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11512393108134843 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1314875265678743 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1314875265678743 : ℝ) /
                (1 + (11512393108134843 / 10000000000000000 : ℝ)) =
              (7500000000000000000000000000000 / 28286113603444361580753162742349 : ℝ)
            by
        norm_num];
        exact hau97)
  have hz2 :
    (3 / 40) / Real.sqrt (276623514287 / 16000000000000 : ℝ) ≤
      (750000000000000 / 1314875265678743 : ℝ) := by
    rw [show
        (750000000000000 / 1314875265678743 : ℝ) =
          (3 / 40) / (1314875265678743 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (653687650225280262137 / 5000000000000000000000 : ℝ)) -
        6 * (2 * (1295919005291486724873 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (276623514287 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (276623514287 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1314875265678743 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (653687650225280262137 / 5000000000000000000000 : ℝ)) -
          6 * (2 * (1295919005291486724873 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (276623514287 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (276623514287 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (276623514287 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_45 :
    ((174603093547929167631 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7523878456169585870279 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1327163577242599 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1319452846275249601221 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (514373683695854022843 / 2000000000000000000000 : ℝ))))) ≤
      Vfield (563636211443 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (563636211443 / 32000000000000 : ℝ)) =
      Real.log (32563636211443 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((563636211443 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (743636211443 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (174603093547929167631 / 10000000000000000000000 : ℝ) ≤
      Real.log (32563636211443 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (743636211443 / 32000000000000 : ℝ) ≤
      (-(7523878456169585870279 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (743636211443 / 32000000000000 : ℝ) = (743636211443 / 500000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (743636211443 / 500000000000 : ℝ) ≤
            (793887707430414129721 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1327163577242599 / 10000000000000000 : ℝ) ≤ Real.sqrt (563636211443 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (563636211443 / 32000000000000 : ℝ) ≤ (663581788621301 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (563636211443 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau98 :
    Real.arctan (663581788621301 / 5000000000000000 : ℝ) ≤
      (1319452846275249601221 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1319452846275249601221 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 663581788621301 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 663581788621301 : ℝ) =
              (663581788621301 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau98)
  have hz1 :
    (5000000000000000 / 663581788621301 : ℝ) ≤
      1 / Real.sqrt (563636211443 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 663581788621301 : ℝ) = 1 / (663581788621301 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau99 :
    Real.arctan (156250000000000000000000000000 / 594080378247320218277056913069 : ℝ) ≤
      (514373683695854022843 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1327163577242599 : ℝ) ≤
      (2 * (514373683695854022843 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (717894851322593 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1327163577242599 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1327163577242599 : ℝ) /
                (1 + (717894851322593 / 625000000000000 : ℝ)) =
              (156250000000000000000000000000 / 594080378247320218277056913069 : ℝ)
            by
        norm_num];
        exact hau99)
  have hz2 :
    (3 / 40) / Real.sqrt (563636211443 / 32000000000000 : ℝ) ≤
      (750000000000000 / 1327163577242599 : ℝ) := by
    rw [show
        (750000000000000 / 1327163577242599 : ℝ) =
          (3 / 40) / (1327163577242599 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1319452846275249601221 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (514373683695854022843 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (563636211443 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (563636211443 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1327163577242599 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1319452846275249601221 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (514373683695854022843 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt (563636211443 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (563636211443 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (563636211443 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_46 :
    ((177793009397219830411 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(37480651333224899688083 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1339339149440871 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1331415769064528188357 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (510471313435554669691 / 2000000000000000000000 : ℝ))))) ≤
      Vfield (71753174289 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (71753174289 / 4000000000000 : ℝ)) =
      Real.log (4071753174289 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((71753174289 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (94253174289 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (177793009397219830411 / 10000000000000000000000 : ℝ) ≤
      Real.log (4071753174289 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (94253174289 / 4000000000000 : ℝ) ≤
      (-(37480651333224899688083 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (94253174289 / 4000000000000 : ℝ) = (94253174289 / 62500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (94253174289 / 62500000000 : ℝ) ≤
            (4108179484775100311917 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1339339149440871 / 10000000000000000 : ℝ) ≤ Real.sqrt (71753174289 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (71753174289 / 4000000000000 : ℝ) ≤ (669669574720437 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (71753174289 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau100 :
    Real.arctan (669669574720437 / 5000000000000000 : ℝ) ≤
      (1331415769064528188357 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1331415769064528188357 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 669669574720437 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 669669574720437 : ℝ) =
              (669669574720437 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau100)
  have hz1 :
    (5000000000000000 / 669669574720437 : ℝ) ≤ 1 / Real.sqrt (71753174289 / 4000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 669669574720437 : ℝ) = 1 / (669669574720437 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau101 :
    Real.arctan (312500000000000000000000000000 / 1197655475685803382537060230697 : ℝ) ≤
      (510471313435554669691 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 446446383146957 : ℝ) ≤
      (2 * (510471313435554669691 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1432641232847821 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (250000000000000 / 446446383146957 : ℝ) ^ 2))
      (by
        rw [show
            (250000000000000 / 446446383146957 : ℝ) /
                (1 + (1432641232847821 / 1250000000000000 : ℝ)) =
              (312500000000000000000000000000 / 1197655475685803382537060230697 : ℝ)
            by
        norm_num];
        exact hau101)
  have hz2 :
    (3 / 40) / Real.sqrt (71753174289 / 4000000000000 : ℝ) ≤
      (250000000000000 / 446446383146957 : ℝ) := by
    rw [show
        (250000000000000 / 446446383146957 : ℝ) =
          (3 / 40) / (1339339149440871 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1331415769064528188357 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (510471313435554669691 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (71753174289 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (71753174289 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1339339149440871 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1331415769064528188357 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (510471313435554669691 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt (71753174289 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (71753174289 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (71753174289 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_47 :
    ((180981908014677709171 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3734380897942405989187 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1351405029475109 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (335816783738066689991 / 2500000000000000000000 : ℝ)) -
              6 * (2 * (2533285111816478099343 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (584414577181 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (584414577181 / 32000000000000 : ℝ)) =
      Real.log (32584414577181 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((584414577181 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (764414577181 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (180981908014677709171 / 10000000000000000000000 : ℝ) ≤
      Real.log (32584414577181 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (764414577181 / 32000000000000 : ℝ) ≤
      (-(3734380897942405989187 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (764414577181 / 32000000000000 : ℝ) = (764414577181 / 500000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (764414577181 / 500000000000 : ℝ) ≤
            (424502183857594010813 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1351405029475109 / 10000000000000000 : ℝ) ≤ Real.sqrt (584414577181 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (584414577181 / 32000000000000 : ℝ) ≤ (168925628684389 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (584414577181 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau102 :
    Real.arctan (168925628684389 / 1250000000000000 : ℝ) ≤
      (335816783738066689991 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (335816783738066689991 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 168925628684389 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 168925628684389 : ℝ) =
              (168925628684389 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau102)
  have hz1 :
    (1250000000000000 / 168925628684389 : ℝ) ≤
      1 / Real.sqrt (584414577181 / 32000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 168925628684389 : ℝ) = 1 / (168925628684389 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau103 :
    Real.arctan (2500000000000000000000000000000 / 9656593059943326973085658954717 : ℝ) ≤
      (2533285111816478099343 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1351405029475109 : ℝ) ≤
      (2 * (2533285111816478099343 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11436785085136139 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1351405029475109 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1351405029475109 : ℝ) /
                (1 + (11436785085136139 / 10000000000000000 : ℝ)) =
              (2500000000000000000000000000000 / 9656593059943326973085658954717 : ℝ)
            by
        norm_num];
        exact hau103)
  have hz2 :
    (3 / 40) / Real.sqrt (584414577181 / 32000000000000 : ℝ) ≤
      (750000000000000 / 1351405029475109 : ℝ) := by
    rw [show
        (750000000000000 / 1351405029475109 : ℝ) =
          (3 / 40) / (1351405029475109 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (335816783738066689991 / 2500000000000000000000 : ℝ)) -
        6 * (2 * (2533285111816478099343 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (584414577181 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (584414577181 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1351405029475109 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (335816783738066689991 / 2500000000000000000000 : ℝ)) -
          6 * (2 * (2533285111816478099343 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (584414577181 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (584414577181 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (584414577181 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_48 :
    ((184169790048865831767 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18604406978856690119019 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1363364129701323 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (677504937366921683649 / 5000000000000000000000 : ℝ)) -
              6 * (2 * (1257318810145620304883 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (11896075201 / 640000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11896075201 / 640000000000 : ℝ)) =
      Real.log (651896075201 / 640000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11896075201 / 640000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (15496075201 / 640000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (184169790048865831767 / 10000000000000000000000 : ℝ) ≤
      Real.log (651896075201 / 640000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (15496075201 / 640000000000 : ℝ) ≤
      (-(18604406978856690119019 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (15496075201 / 640000000000 : ℝ) = (15496075201 / 10000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15496075201 / 10000000000 : ℝ) ≤
            (2190008430143309880981 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1363364129701323 / 10000000000000000 : ℝ) ≤ Real.sqrt (11896075201 / 640000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11896075201 / 640000000000 : ℝ) ≤ (681682064850663 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11896075201 / 640000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau104 :
    Real.arctan (681682064850663 / 5000000000000000 : ℝ) ≤
      (677504937366921683649 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (677504937366921683649 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 681682064850663 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 681682064850663 : ℝ) =
              (681682064850663 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau104)
  have hz1 :
    (5000000000000000 / 681682064850663 : ℝ) ≤ 1 / Real.sqrt (11896075201 / 640000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 681682064850663 : ℝ) = 1 / (681682064850663 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau105 :
    Real.arctan (250000000000000000000000000000 / 973134845774848592644041727587 : ℝ) ≤
      (1257318810145620304883 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (250000000000000 / 454454709900441 : ℝ) ≤
      (2 * (1257318810145620304883 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1141324150844507 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (250000000000000 / 454454709900441 : ℝ) ^ 2))
      (by
        rw [show
            (250000000000000 / 454454709900441 : ℝ) /
                (1 + (1141324150844507 / 1000000000000000 : ℝ)) =
              (250000000000000000000000000000 / 973134845774848592644041727587 : ℝ)
            by
        norm_num];
        exact hau105)
  have hz2 :
    (3 / 40) / Real.sqrt (11896075201 / 640000000000 : ℝ) ≤
      (250000000000000 / 454454709900441 : ℝ) := by
    rw [show
        (250000000000000 / 454454709900441 : ℝ) =
          (3 / 40) / (1363364129701323 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (677504937366921683649 / 5000000000000000000000 : ℝ)) -
        6 * (2 * (1257318810145620304883 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11896075201 / 640000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11896075201 / 640000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1363364129701323 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (677504937366921683649 / 5000000000000000000000 : ℝ)) -
          6 * (2 * (1257318810145620304883 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (11896075201 / 640000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11896075201 / 640000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11896075201 / 640000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
