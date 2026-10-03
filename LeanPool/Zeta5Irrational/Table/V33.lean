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

/-! # V33: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_397 :
    ((830766881093553021839 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8952902555955087179 / 9765625000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1255675835837717 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (700796828610549806021 / 2500000000000000000000 : ℝ))) -
              6 * (118894174383393800607 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (6306887218827 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6306887218827 / 16000000000000 : ℝ)) =
      Real.log (22306887218827 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6306887218827 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6396887218827 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (830766881093553021839 / 2500000000000000000000 : ℝ) ≤
      Real.log (22306887218827 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6396887218827 / 16000000000000 : ℝ) ≤
      (-(8952902555955087179 / 9765625000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (6396887218827 / 16000000000000 : ℝ) = (6396887218827 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6396887218827 / 4000000000000 : ℝ) ≤
            (4585128309279287821 / 9765625000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1255675835837717 / 2000000000000000 : ℝ) ≤ Real.sqrt (6306887218827 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6306887218827 / 16000000000000 : ℝ) ≤ (1569594794797147 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6306887218827 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau566 :
    Real.arctan (6278379179188588 / 21807541874482967 : ℝ) ≤
      (700796828610549806021 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau565 :
    Real.arctan (1569594794797147 / 2500000000000000 : ℝ) ≤
      (2 * (700796828610549806021 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11807541874482967 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1569594794797147 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1569594794797147 / 2500000000000000 : ℝ) /
                (1 + (11807541874482967 / 10000000000000000 : ℝ)) =
              (6278379179188588 / 21807541874482967 : ℝ)
            by
        norm_num];
        exact hau566)
  have hat1 :
    (Real.pi / 2 - (2 * (700796828610549806021 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1569594794797147 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1569594794797147 : ℝ) =
              (1569594794797147 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau565)
  have hz1 :
    (2500000000000000 / 1569594794797147 : ℝ) ≤
      1 / Real.sqrt (6306887218827 / 16000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1569594794797147 : ℝ) = 1 / (1569594794797147 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1255675835837717 : ℝ) ≤
      (118894174383393800607 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6306887218827 / 16000000000000 : ℝ) ≤
      (150000000000000 / 1255675835837717 : ℝ) := by
    rw [show
        (150000000000000 / 1255675835837717 : ℝ) =
          (3 / 40) / (1255675835837717 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (700796828610549806021 / 2500000000000000000000 : ℝ))) -
        6 * (118894174383393800607 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6306887218827 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6306887218827 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1255675835837717 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (700796828610549806021 / 2500000000000000000000 : ℝ))) -
          6 * (118894174383393800607 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (6306887218827 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6306887218827 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6306887218827 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_398 :
    ((3341814806437021744403 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4551274765307920417809 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1574794851961441 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1405319994812823534829 / 5000000000000000000000 : ℝ))) -
              6 * (237010501418881799479 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (12697491587913 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (12697491587913 / 32000000000000 : ℝ)) =
      Real.log (44697491587913 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((12697491587913 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12877491587913 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3341814806437021744403 / 10000000000000000000000 : ℝ) ≤
      Real.log (44697491587913 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12877491587913 / 32000000000000 : ℝ) ≤
      (-(4551274765307920417809 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (12877491587913 / 32000000000000 : ℝ) = (12877491587913 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12877491587913 / 8000000000000 : ℝ) ≤
            (2380197037692079582191 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1574794851961441 / 2500000000000000 : ℝ) ≤ Real.sqrt (12697491587913 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (12697491587913 / 32000000000000 : ℝ) ≤
      (6299179407845767 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (12697491587913 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau568 :
    Real.arctan (6299179407845767 / 21818615029360594 : ℝ) ≤
      (1405319994812823534829 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau567 :
    Real.arctan (6299179407845767 / 10000000000000000 : ℝ) ≤
      (2 * (1405319994812823534829 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5909307514680297 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6299179407845767 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6299179407845767 / 10000000000000000 : ℝ) /
                (1 + (5909307514680297 / 5000000000000000 : ℝ)) =
              (6299179407845767 / 21818615029360594 : ℝ)
            by
        norm_num];
        exact hau568)
  have hat1 :
    (Real.pi / 2 - (2 * (1405319994812823534829 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6299179407845767 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6299179407845767 : ℝ) =
              (6299179407845767 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau567)
  have hz1 :
    (10000000000000000 / 6299179407845767 : ℝ) ≤
      1 / Real.sqrt (12697491587913 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6299179407845767 : ℝ) =
          1 / (6299179407845767 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1574794851961441 : ℝ) ≤
      (237010501418881799479 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (12697491587913 / 32000000000000 : ℝ) ≤
      (187500000000000 / 1574794851961441 : ℝ) := by
    rw [show
        (187500000000000 / 1574794851961441 : ℝ) =
          (3 / 40) / (1574794851961441 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1405319994812823534829 / 5000000000000000000000 : ℝ))) -
        6 * (237010501418881799479 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (12697491587913 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (12697491587913 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1574794851961441 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1405319994812823534829 / 5000000000000000000000 : ℝ))) -
          6 * (237010501418881799479 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (12697491587913 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (12697491587913 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (12697491587913 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_399 :
    ((840131752049283713763 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2259437372176322009597 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1263982235742061 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2818054236801107742807 / 10000000000000000000000 : ℝ))) -
              6 * (590600595064456682237 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3195302184543 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3195302184543 / 8000000000000 : ℝ)) =
      Real.log (11195302184543 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3195302184543 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3240302184543 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (840131752049283713763 / 2500000000000000000000 : ℝ) ≤
      Real.log (11195302184543 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3240302184543 / 8000000000000 : ℝ) ≤
      (-(2259437372176322009597 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (3240302184543 / 8000000000000 : ℝ) = (3240302184543 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3240302184543 / 2000000000000 : ℝ) ≤
            (1206298529323677990403 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1263982235742061 / 2000000000000000 : ℝ) ≤ Real.sqrt (3195302184543 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3195302184543 / 8000000000000 : ℝ) ≤ (1579977794677577 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3195302184543 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau570 :
    Real.arctan (6319911178710308 / 21829677819230221 : ℝ) ≤
      (2818054236801107742807 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau569 :
    Real.arctan (1579977794677577 / 2500000000000000 : ℝ) ≤
      (2 * (2818054236801107742807 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11829677819230221 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1579977794677577 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1579977794677577 / 2500000000000000 : ℝ) /
                (1 + (11829677819230221 / 10000000000000000 : ℝ)) =
              (6319911178710308 / 21829677819230221 : ℝ)
            by
        norm_num];
        exact hau570)
  have hat1 :
    (Real.pi / 2 - (2 * (2818054236801107742807 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1579977794677577 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1579977794677577 : ℝ) =
              (1579977794677577 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau569)
  have hz1 :
    (2500000000000000 / 1579977794677577 : ℝ) ≤
      1 / Real.sqrt (3195302184543 / 8000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1579977794677577 : ℝ) = 1 / (1579977794677577 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1263982235742061 : ℝ) ≤
      (590600595064456682237 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3195302184543 / 8000000000000 : ℝ) ≤
      (150000000000000 / 1263982235742061 : ℝ) := by
    rw [show
        (150000000000000 / 1263982235742061 : ℝ) =
          (3 / 40) / (1263982235742061 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2818054236801107742807 / 10000000000000000000000 : ℝ))) -
        6 * (590600595064456682237 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3195302184543 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3195302184543 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1263982235742061 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2818054236801107742807 / 10000000000000000000000 : ℝ))) -
          6 * (590600595064456682237 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (3195302184543 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3195302184543 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3195302184543 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_400 :
    ((3379204260695362054447 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8973366649314295692837 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((99071486926427 / 156250000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2825430439216674767041 / 10000000000000000000000 : ℝ))) -
              6 * (1177387180713437419171 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (12864925888431 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (12864925888431 / 32000000000000 : ℝ)) =
      Real.log (44864925888431 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((12864925888431 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (13044925888431 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3379204260695362054447 / 10000000000000000000000 : ℝ) ≤
      Real.log (44864925888431 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (13044925888431 / 32000000000000 : ℝ) ≤
      (-(8973366649314295692837 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (13044925888431 / 32000000000000 : ℝ) = (13044925888431 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13044925888431 / 8000000000000 : ℝ) ≤
            (4889576956685704307163 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (99071486926427 / 156250000000000 : ℝ) ≤ Real.sqrt (12864925888431 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (12864925888431 / 32000000000000 : ℝ) ≤
      (6340575163291331 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (12864925888431 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau572 :
    Real.arctan (6340575163291331 / 21840730273143918 : ℝ) ≤
      (2825430439216674767041 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau571 :
    Real.arctan (6340575163291331 / 10000000000000000 : ℝ) ≤
      (2 * (2825430439216674767041 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5920365136571959 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6340575163291331 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6340575163291331 / 10000000000000000 : ℝ) /
                (1 + (5920365136571959 / 5000000000000000 : ℝ)) =
              (6340575163291331 / 21840730273143918 : ℝ)
            by
        norm_num];
        exact hau572)
  have hat1 :
    (Real.pi / 2 - (2 * (2825430439216674767041 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6340575163291331 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6340575163291331 : ℝ) =
              (6340575163291331 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau571)
  have hz1 :
    (10000000000000000 / 6340575163291331 : ℝ) ≤
      1 / Real.sqrt (12864925888431 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6340575163291331 : ℝ) =
          1 / (6340575163291331 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (11718750000000 / 99071486926427 : ℝ) ≤
      (1177387180713437419171 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (12864925888431 / 32000000000000 : ℝ) ≤
      (11718750000000 / 99071486926427 : ℝ) := by
    rw [show
        (11718750000000 / 99071486926427 : ℝ) = (3 / 40) / (99071486926427 / 156250000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2825430439216674767041 / 10000000000000000000000 : ℝ))) -
        6 * (1177387180713437419171 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (12864925888431 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (12864925888431 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((99071486926427 / 156250000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2825430439216674767041 / 10000000000000000000000 : ℝ))) -
          6 * (1177387180713437419171 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (12864925888431 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (12864925888431 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (12864925888431 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_401 :
    ((3397846694239637457303 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8909395674635741552251 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1272234404438211 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2832768974090960128569 / 10000000000000000000000 : ℝ))) -
              6 * (293402470093434932507 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1294864303869 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1294864303869 / 3200000000000 : ℝ)) =
      Real.log (4494864303869 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1294864303869 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1312864303869 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3397846694239637457303 / 10000000000000000000000 : ℝ) ≤
      Real.log (4494864303869 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1312864303869 / 3200000000000 : ℝ) ≤
      (-(8909395674635741552251 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1312864303869 / 3200000000000 : ℝ) = (1312864303869 / 800000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1312864303869 / 800000000000 : ℝ) ≤
            (4953547931364258447749 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1272234404438211 / 2000000000000000 : ℝ) ≤ Real.sqrt (1294864303869 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1294864303869 / 3200000000000 : ℝ) ≤ (3180586011095529 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1294864303869 / 3200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau574 :
    Real.arctan (3180586011095529 / 10925886210009146 : ℝ) ≤
      (2832768974090960128569 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau573 :
    Real.arctan (3180586011095529 / 5000000000000000 : ℝ) ≤
      (2 * (2832768974090960128569 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2962943105004573 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3180586011095529 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3180586011095529 / 5000000000000000 : ℝ) /
                (1 + (2962943105004573 / 2500000000000000 : ℝ)) =
              (3180586011095529 / 10925886210009146 : ℝ)
            by
        norm_num];
        exact hau574)
  have hat1 :
    (Real.pi / 2 - (2 * (2832768974090960128569 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3180586011095529 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3180586011095529 : ℝ) =
              (3180586011095529 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau573)
  have hz1 :
    (5000000000000000 / 3180586011095529 : ℝ) ≤
      1 / Real.sqrt (1294864303869 / 3200000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3180586011095529 : ℝ) = 1 / (3180586011095529 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 424078134812737 : ℝ) ≤
      (293402470093434932507 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1294864303869 / 3200000000000 : ℝ) ≤
      (50000000000000 / 424078134812737 : ℝ) := by
    rw [show
        (50000000000000 / 424078134812737 : ℝ) =
          (3 / 40) / (1272234404438211 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2832768974090960128569 / 10000000000000000000000 : ℝ))) -
        6 * (293402470093434932507 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1294864303869 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1294864303869 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1272234404438211 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2832768974090960128569 / 10000000000000000000000 : ℝ))) -
          6 * (293402470093434932507 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1294864303869 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1294864303869 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1294864303869 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_402 :
    ((3416454438410473535733 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8845831328651810423357 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((255268096214049 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (14200351063728030601 / 50000000000000000000 : ℝ))) -
              6 * (584934351995421838111 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (13032360188949 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (13032360188949 / 32000000000000 : ℝ)) =
      Real.log (45032360188949 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((13032360188949 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (13212360188949 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3416454438410473535733 / 10000000000000000000000 : ℝ) ≤
      Real.log (45032360188949 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (13212360188949 / 32000000000000 : ℝ) ≤
      (-(8845831328651810423357 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (13212360188949 / 32000000000000 : ℝ) = (13212360188949 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13212360188949 / 8000000000000 : ℝ) ≤
            (5017112277348189576643 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (255268096214049 / 400000000000000 : ℝ) ≤ Real.sqrt (13032360188949 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (13032360188949 / 32000000000000 : ℝ) ≤ (1595425601337807 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (13032360188949 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau576 :
    Real.arctan (6381702405351228 / 21862804288635365 : ℝ) ≤
      (14200351063728030601 / 50000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau575 :
    Real.arctan (1595425601337807 / 2500000000000000 : ℝ) ≤
      (2 * (14200351063728030601 / 50000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2372560857727073 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1595425601337807 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1595425601337807 / 2500000000000000 : ℝ) /
                (1 + (2372560857727073 / 2000000000000000 : ℝ)) =
              (6381702405351228 / 21862804288635365 : ℝ)
            by
        norm_num];
        exact hau576)
  have hat1 :
    (Real.pi / 2 - (2 * (14200351063728030601 / 50000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1595425601337807 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1595425601337807 : ℝ) =
              (1595425601337807 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau575)
  have hz1 :
    (2500000000000000 / 1595425601337807 : ℝ) ≤
      1 / Real.sqrt (13032360188949 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1595425601337807 : ℝ) = 1 / (1595425601337807 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (10000000000000 / 85089365404683 : ℝ) ≤
      (584934351995421838111 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (13032360188949 / 32000000000000 : ℝ) ≤
      (10000000000000 / 85089365404683 : ℝ) := by
    rw [show
        (10000000000000 / 85089365404683 : ℝ) = (3 / 40) / (255268096214049 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (14200351063728030601 / 50000000000000000000 : ℝ))) -
        6 * (584934351995421838111 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (13032360188949 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (13032360188949 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((255268096214049 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (14200351063728030601 / 50000000000000000000 : ℝ))) -
          6 * (584934351995421838111 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (13032360188949 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (13032360188949 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (13032360188949 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_403 :
    ((1717513811033182669897 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4391334237281119106909 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3201083476146201 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (355916815091755312081 / 1250000000000000000000 : ℝ))) -
              6 * (583081539710138134777 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1639509667401 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1639509667401 / 4000000000000 : ℝ)) =
      Real.log (5639509667401 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1639509667401 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1662009667401 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1717513811033182669897 / 5000000000000000000000 : ℝ) ≤
      Real.log (5639509667401 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1662009667401 / 4000000000000 : ℝ) ≤
      (-(4391334237281119106909 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1662009667401 / 4000000000000 : ℝ) = (1662009667401 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1662009667401 / 1000000000000 : ℝ) ≤
            (2540137565718880893091 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3201083476146201 / 5000000000000000 : ℝ) ≤ Real.sqrt (1639509667401 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1639509667401 / 4000000000000 : ℝ) ≤ (1280433390458481 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1639509667401 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau578 :
    Real.arctan (914595278898915 / 3124832272520494 : ℝ) ≤
      (355916815091755312081 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau577 :
    Real.arctan (1280433390458481 / 2000000000000000 : ℝ) ≤
      (2 * (355916815091755312081 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5936912953821729 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1280433390458481 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1280433390458481 / 2000000000000000 : ℝ) /
                (1 + (5936912953821729 / 5000000000000000 : ℝ)) =
              (914595278898915 / 3124832272520494 : ℝ)
            by
        norm_num];
        exact hau578)
  have hat1 :
    (Real.pi / 2 - (2 * (355916815091755312081 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1280433390458481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1280433390458481 : ℝ) =
              (1280433390458481 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau577)
  have hz1 :
    (2000000000000000 / 1280433390458481 : ℝ) ≤
      1 / Real.sqrt (1639509667401 / 4000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1280433390458481 : ℝ) = 1 / (1280433390458481 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1067027825382067 : ℝ) ≤
      (583081539710138134777 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1639509667401 / 4000000000000 : ℝ) ≤
      (125000000000000 / 1067027825382067 : ℝ) := by
    rw [show
        (125000000000000 / 1067027825382067 : ℝ) =
          (3 / 40) / (3201083476146201 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (355916815091755312081 / 1250000000000000000000 : ℝ))) -
        6 * (583081539710138134777 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1639509667401 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1639509667401 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3201083476146201 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (355916815091755312081 / 1250000000000000000000 : ℝ))) -
          6 * (583081539710138134777 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1639509667401 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1639509667401 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1639509667401 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_404 :
    ((868017704922321109341 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(541095448505268199687 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((805362630610271 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (715438444708057385753 / 2500000000000000000000 : ℝ))) -
              6 * (115885625981794946927 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (6641755819863 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6641755819863 / 16000000000000 : ℝ)) =
      Real.log (22641755819863 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6641755819863 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6731755819863 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (868017704922321109341 / 2500000000000000000000 : ℝ) ≤
      Real.log (22641755819863 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6731755819863 / 16000000000000 : ℝ) ≤
      (-(541095448505268199687 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (6731755819863 / 16000000000000 : ℝ) = (6731755819863 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6731755819863 / 4000000000000 : ℝ) ≤
            (325338526869731800313 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (805362630610271 / 1250000000000000 : ℝ) ≤ Real.sqrt (6641755819863 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6641755819863 / 16000000000000 : ℝ) ≤ (6442901044882171 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6641755819863 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau580 :
    Real.arctan (6442901044882171 / 21895838510762650 : ℝ) ≤
      (715438444708057385753 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau579 :
    Real.arctan (6442901044882171 / 10000000000000000 : ℝ) ≤
      (2 * (715438444708057385753 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (237916770215253 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (6442901044882171 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6442901044882171 / 10000000000000000 : ℝ) /
                (1 + (237916770215253 / 200000000000000 : ℝ)) =
              (6442901044882171 / 21895838510762650 : ℝ)
            by
        norm_num];
        exact hau580)
  have hat1 :
    (Real.pi / 2 - (2 * (715438444708057385753 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6442901044882171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6442901044882171 : ℝ) =
              (6442901044882171 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau579)
  have hz1 :
    (10000000000000000 / 6442901044882171 : ℝ) ≤
      1 / Real.sqrt (6641755819863 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6442901044882171 : ℝ) =
          1 / (6442901044882171 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 805362630610271 : ℝ) ≤
      (115885625981794946927 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6641755819863 / 16000000000000 : ℝ) ≤
      (93750000000000 / 805362630610271 : ℝ) := by
    rw [show
        (93750000000000 / 805362630610271 : ℝ) =
          (3 / 40) / (805362630610271 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (715438444708057385753 / 2500000000000000000000 : ℝ))) -
        6 * (115885625981794946927 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6641755819863 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6641755819863 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((805362630610271 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (715438444708057385753 / 2500000000000000000000 : ℝ))) -
          6 * (115885625981794946927 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (6641755819863 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6641755819863 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6641755819863 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_405 :
    ((175448865186911473401 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8533932576410381810459 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6483379216370309 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2876029562117140236423 / 10000000000000000000000 : ℝ))) -
              6 * (115168509024532050863 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (3362736485061 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3362736485061 / 8000000000000 : ℝ)) =
      Real.log (11362736485061 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3362736485061 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3407736485061 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (175448865186911473401 / 500000000000000000000 : ℝ) ≤
      Real.log (11362736485061 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3407736485061 / 8000000000000 : ℝ) ≤
      (-(8533932576410381810459 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (3407736485061 / 8000000000000 : ℝ) = (3407736485061 / 2000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3407736485061 / 2000000000000 : ℝ) ≤
            (5329011029589618189541 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6483379216370309 / 10000000000000000 : ℝ) ≤ Real.sqrt (3362736485061 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3362736485061 / 8000000000000 : ℝ) ≤ (810422402046289 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3362736485061 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau582 :
    Real.arctan (1620844804092578 / 5479452613980277 : ℝ) ≤
      (2876029562117140236423 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau581 :
    Real.arctan (810422402046289 / 1250000000000000 : ℝ) ≤
      (2 * (2876029562117140236423 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2979452613980277 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (810422402046289 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (810422402046289 / 1250000000000000 : ℝ) /
                (1 + (2979452613980277 / 2500000000000000 : ℝ)) =
              (1620844804092578 / 5479452613980277 : ℝ)
            by
        norm_num];
        exact hau582)
  have hat1 :
    (Real.pi / 2 - (2 * (2876029562117140236423 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 810422402046289 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 810422402046289 : ℝ) =
              (810422402046289 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau581)
  have hz1 :
    (1250000000000000 / 810422402046289 : ℝ) ≤
      1 / Real.sqrt (3362736485061 / 8000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 810422402046289 : ℝ) = 1 / (810422402046289 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6483379216370309 : ℝ) ≤
      (115168509024532050863 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3362736485061 / 8000000000000 : ℝ) ≤
      (750000000000000 / 6483379216370309 : ℝ) := by
    rw [show
        (750000000000000 / 6483379216370309 : ℝ) =
          (3 / 40) / (6483379216370309 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2876029562117140236423 / 10000000000000000000000 : ℝ))) -
        6 * (115168509024532050863 / 1000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3362736485061 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3362736485061 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6483379216370309 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2876029562117140236423 / 10000000000000000000000 : ℝ))) -
          6 * (115168509024532050863 / 1000000000000000000000 : ℝ))) ≤
      Real.sqrt (3362736485061 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3362736485061 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3362736485061 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_406 :
    ((886437019907079153121 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8411846908633533086469 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((652360623063511 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1445082299841854199793 / 5000000000000000000000 : ℝ))) -
              6 * (1144645424719571608529 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (6809190120381 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6809190120381 / 16000000000000 : ℝ)) =
      Real.log (22809190120381 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6809190120381 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (6899190120381 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (886437019907079153121 / 2500000000000000000000 : ℝ) ≤
      Real.log (22809190120381 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (6899190120381 / 16000000000000 : ℝ) ≤
      (-(8411846908633533086469 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (6899190120381 / 16000000000000 : ℝ) = (6899190120381 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6899190120381 / 4000000000000 : ℝ) ≤
            (5451096697366466913531 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (652360623063511 / 1000000000000000 : ℝ) ≤ Real.sqrt (6809190120381 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6809190120381 / 16000000000000 : ℝ) ≤ (6523606230635113 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6809190120381 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau584 :
    Real.arctan (6523606230635113 / 21939741967579585 : ℝ) ≤
      (1445082299841854199793 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau583 :
    Real.arctan (6523606230635113 / 10000000000000000 : ℝ) ≤
      (2 * (1445082299841854199793 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2387948393515917 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6523606230635113 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6523606230635113 / 10000000000000000 : ℝ) /
                (1 + (2387948393515917 / 2000000000000000 : ℝ)) =
              (6523606230635113 / 21939741967579585 : ℝ)
            by
        norm_num];
        exact hau584)
  have hat1 :
    (Real.pi / 2 - (2 * (1445082299841854199793 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6523606230635113 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6523606230635113 : ℝ) =
              (6523606230635113 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau583)
  have hz1 :
    (10000000000000000 / 6523606230635113 : ℝ) ≤
      1 / Real.sqrt (6809190120381 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6523606230635113 : ℝ) =
          1 / (6523606230635113 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 652360623063511 : ℝ) ≤
      (1144645424719571608529 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (6809190120381 / 16000000000000 : ℝ) ≤
      (75000000000000 / 652360623063511 : ℝ) := by
    rw [show
        (75000000000000 / 652360623063511 : ℝ) =
          (3 / 40) / (652360623063511 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1445082299841854199793 / 5000000000000000000000 : ℝ))) -
        6 * (1144645424719571608529 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6809190120381 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6809190120381 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((652360623063511 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1445082299841854199793 / 5000000000000000000000 : ℝ))) -
          6 * (1144645424719571608529 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (6809190120381 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6809190120381 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6809190120381 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_407 :
    ((3582384141724289505683 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8291233772453230333 / 10000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3281793352783657 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (290416153952159878763 / 1000000000000000000000 : ℝ))) -
              6 * (568866646261417588901 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (86161340883 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (86161340883 / 200000000000 : ℝ)) =
      Real.log (286161340883 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((86161340883 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (87286340883 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3582384141724289505683 / 10000000000000000000000 : ℝ) ≤
      Real.log (286161340883 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (87286340883 / 200000000000 : ℝ) ≤
      (-(8291233772453230333 / 10000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (87286340883 / 200000000000 : ℝ) = (87286340883 / 50000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (87286340883 / 50000000000 : ℝ) ≤
            (5571709833546769667 / 10000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3281793352783657 / 5000000000000000 : ℝ) ≤ Real.sqrt (86161340883 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (86161340883 / 200000000000 : ℝ) ≤ (6563586705567317 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (86161340883 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau586 :
    Real.arctan (6563586705567317 / 21961633268141102 : ℝ) ≤
      (290416153952159878763 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau585 :
    Real.arctan (6563586705567317 / 10000000000000000 : ℝ) ≤
      (2 * (290416153952159878763 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5980816634070551 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6563586705567317 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6563586705567317 / 10000000000000000 : ℝ) /
                (1 + (5980816634070551 / 5000000000000000 : ℝ)) =
              (6563586705567317 / 21961633268141102 : ℝ)
            by
        norm_num];
        exact hau586)
  have hat1 :
    (Real.pi / 2 - (2 * (290416153952159878763 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6563586705567317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6563586705567317 : ℝ) =
              (6563586705567317 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau585)
  have hz1 :
    (10000000000000000 / 6563586705567317 : ℝ) ≤ 1 / Real.sqrt (86161340883 / 200000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 6563586705567317 : ℝ) =
          1 / (6563586705567317 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3281793352783657 : ℝ) ≤
      (568866646261417588901 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (86161340883 / 200000000000 : ℝ) ≤
      (375000000000000 / 3281793352783657 : ℝ) := by
    rw [show
        (375000000000000 / 3281793352783657 : ℝ) =
          (3 / 40) / (3281793352783657 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (290416153952159878763 / 1000000000000000000000 : ℝ))) -
        6 * (568866646261417588901 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (86161340883 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (86161340883 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3281793352783657 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (290416153952159878763 / 1000000000000000000000 : ℝ))) -
          6 * (568866646261417588901 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (86161340883 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (86161340883 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (86161340883 / 200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_408 :
    ((3600878263421158486701 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8230729569040064947449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1316746451171219 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2911194962262022984371 / 10000000000000000000000 : ℝ))) -
              6 * (1134281773410074366533 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (54181913021 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (54181913021 / 125000000000 : ℝ)) =
      Real.log (179181913021 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((54181913021 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (54885038021 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3600878263421158486701 / 10000000000000000000000 : ℝ) ≤
      Real.log (179181913021 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (54885038021 / 125000000000 : ℝ) ≤
      (-(8230729569040064947449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (54885038021 / 125000000000 : ℝ) = (54885038021 / 31250000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (54885038021 / 31250000000 : ℝ) ≤
            (5632214036959935052551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1316746451171219 / 2000000000000000 : ℝ) ≤ Real.sqrt (54181913021 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (54181913021 / 125000000000 : ℝ) ≤ (3291866127928049 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (54181913021 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau588 :
    Real.arctan (940533179408014 / 3138957054124321 : ℝ) ≤
      (2911194962262022984371 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau587 :
    Real.arctan (3291866127928049 / 5000000000000000 : ℝ) ≤
      (2 * (2911194962262022984371 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11972699378870247 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3291866127928049 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3291866127928049 / 5000000000000000 : ℝ) /
                (1 + (11972699378870247 / 10000000000000000 : ℝ)) =
              (940533179408014 / 3138957054124321 : ℝ)
            by
        norm_num];
        exact hau588)
  have hat1 :
    (Real.pi / 2 - (2 * (2911194962262022984371 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3291866127928049 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3291866127928049 : ℝ) =
              (3291866127928049 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau587)
  have hz1 :
    (5000000000000000 / 3291866127928049 : ℝ) ≤ 1 / Real.sqrt (54181913021 / 125000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3291866127928049 : ℝ) = 1 / (3291866127928049 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1316746451171219 : ℝ) ≤
      (1134281773410074366533 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (54181913021 / 125000000000 : ℝ) ≤
      (150000000000000 / 1316746451171219 : ℝ) := by
    rw [show
        (150000000000000 / 1316746451171219 : ℝ) =
          (3 / 40) / (1316746451171219 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2911194962262022984371 / 10000000000000000000000 : ℝ))) -
        6 * (1134281773410074366533 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (54181913021 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (54181913021 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1316746451171219 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2911194962262022984371 / 10000000000000000000000 : ℝ))) -
          6 * (1134281773410074366533 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (54181913021 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (54181913021 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (54181913021 / 125000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
