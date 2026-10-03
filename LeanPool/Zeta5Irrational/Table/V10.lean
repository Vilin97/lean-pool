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

/-! # V10: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_121 :
    ((358153637420051856447 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(505436999038738140509 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((681260672591859 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) -
              6 * (2685754224056738553489 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (297034306573 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (297034306573 / 4000000000000 : ℝ)) =
      Real.log (4297034306573 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((297034306573 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (319534306573 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (358153637420051856447 / 5000000000000000000000 : ℝ) ≤
      Real.log (4297034306573 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (319534306573 / 4000000000000 : ℝ) ≤
      (-(505436999038738140509 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (319534306573 / 4000000000000 : ℝ) = (319534306573 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (319534306573 / 250000000000 : ℝ) ≤
            (49080745201261859491 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (681260672591859 / 2500000000000000 : ℝ) ≤ Real.sqrt (297034306573 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (297034306573 / 4000000000000 : ℝ) ≤ (2725042690367439 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (297034306573 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau183 :
    Real.arctan (2725042690367439 / 10000000000000000 : ℝ) ≤
      (2660444724297807303401 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2725042690367439 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2725042690367439 : ℝ) =
              (2725042690367439 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau183)
  have hz1 :
    (10000000000000000 / 2725042690367439 : ℝ) ≤
      1 / Real.sqrt (297034306573 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2725042690367439 : ℝ) =
          1 / (2725042690367439 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 227086890863953 : ℝ) ≤
      (2685754224056738553489 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (297034306573 / 4000000000000 : ℝ) ≤
      (62500000000000 / 227086890863953 : ℝ) := by
    rw [show
        (62500000000000 / 227086890863953 : ℝ) =
          (3 / 40) / (681260672591859 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) -
        6 * (2685754224056738553489 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (297034306573 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (297034306573 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((681260672591859 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) -
          6 * (2685754224056738553489 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (297034306573 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (297034306573 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (297034306573 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_122 :
    ((143750539911760461247 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25239014309567609724181 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2729859165131193 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) -
              6 * (2681239616034587774699 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9538727758657 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9538727758657 / 128000000000000 : ℝ)) =
      Real.log (137538727758657 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9538727758657 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10258727758657 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (143750539911760461247 / 2000000000000000000000 : ℝ) ≤
      Real.log (137538727758657 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10258727758657 / 128000000000000 : ℝ) ≤
      (-(25239014309567609724181 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10258727758657 / 128000000000000 : ℝ) = (10258727758657 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10258727758657 / 8000000000000 : ℝ) ≤
            (2486872902432390275819 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2729859165131193 / 10000000000000000 : ℝ) ≤
      Real.sqrt (9538727758657 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9538727758657 / 128000000000000 : ℝ) ≤ (682464791282799 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9538727758657 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau184 :
    Real.arctan (682464791282799 / 2500000000000000 : ℝ) ≤
      (1332463855095506303277 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 682464791282799 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 682464791282799 : ℝ) =
              (682464791282799 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau184)
  have hz1 :
    (2500000000000000 / 682464791282799 : ℝ) ≤
      1 / Real.sqrt (9538727758657 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 682464791282799 : ℝ) = 1 / (682464791282799 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 909953055043731 : ℝ) ≤
      (2681239616034587774699 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9538727758657 / 128000000000000 : ℝ) ≤
      (250000000000000 / 909953055043731 : ℝ) := by
    rw [show
        (250000000000000 / 909953055043731 : ℝ) =
          (3 / 40) / (2729859165131193 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) -
        6 * (2681239616034587774699 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9538727758657 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9538727758657 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2729859165131193 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) -
          6 * (2681239616034587774699 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9538727758657 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9538727758657 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9538727758657 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_123 :
    ((180299381603373895023 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25206286132366748618349 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((546933431363509 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) -
              6 * (2676747708916748668133 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4786178853489 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4786178853489 / 64000000000000 : ℝ)) =
      Real.log (68786178853489 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4786178853489 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5146178853489 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (180299381603373895023 / 2500000000000000000000 : ℝ) ≤
      Real.log (68786178853489 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5146178853489 / 64000000000000 : ℝ) ≤
      (-(25206286132366748618349 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5146178853489 / 64000000000000 : ℝ) = (5146178853489 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5146178853489 / 4000000000000 : ℝ) ≤
            (2519601079633251381651 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (546933431363509 / 2000000000000000 : ℝ) ≤ Real.sqrt (4786178853489 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4786178853489 / 64000000000000 : ℝ) ≤ (683666789204387 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4786178853489 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau185 :
    Real.arctan (683666789204387 / 2500000000000000 : ℝ) ≤
      (2669401706285649911771 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 683666789204387 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 683666789204387 : ℝ) =
              (683666789204387 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau185)
  have hz1 :
    (2500000000000000 / 683666789204387 : ℝ) ≤
      1 / Real.sqrt (4786178853489 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 683666789204387 : ℝ) = 1 / (683666789204387 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 546933431363509 : ℝ) ≤
      (2676747708916748668133 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4786178853489 / 64000000000000 : ℝ) ≤
      (150000000000000 / 546933431363509 : ℝ) := by
    rw [show
        (150000000000000 / 546933431363509 : ℝ) =
          (3 / 40) / (546933431363509 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) -
        6 * (2676747708916748668133 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4786178853489 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4786178853489 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((546933431363509 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) -
          6 * (2676747708916748668133 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4786178853489 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4786178853489 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4786178853489 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_124 :
    ((180910438924111719793 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6293416179799985485973 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2739466710092009 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) -
              6 * (1336139156501337456721 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9605987655299 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9605987655299 / 128000000000000 : ℝ)) =
      Real.log (137605987655299 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9605987655299 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10325987655299 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (180910438924111719793 / 2500000000000000000000 : ℝ) ≤
      Real.log (137605987655299 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10325987655299 / 128000000000000 : ℝ) ≤
      (-(6293416179799985485973 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10325987655299 / 128000000000000 : ℝ) = (10325987655299 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10325987655299 / 8000000000000 : ℝ) ≤
            (638055623200014514027 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2739466710092009 / 10000000000000000 : ℝ) ≤
      Real.sqrt (9605987655299 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9605987655299 / 128000000000000 : ℝ) ≤ (684866677523003 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9605987655299 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau186 :
    Real.arctan (684866677523003 / 2500000000000000 : ℝ) ≤
      (2673866758528940898129 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 684866677523003 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 684866677523003 : ℝ) =
              (684866677523003 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau186)
  have hz1 :
    (2500000000000000 / 684866677523003 : ℝ) ≤
      1 / Real.sqrt (9605987655299 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 684866677523003 : ℝ) = 1 / (684866677523003 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2739466710092009 : ℝ) ≤
      (1336139156501337456721 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9605987655299 / 128000000000000 : ℝ) ≤
      (750000000000000 / 2739466710092009 : ℝ) := by
    rw [show
        (750000000000000 / 2739466710092009 : ℝ) =
          (3 / 40) / (2739466710092009 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) -
        6 * (1336139156501337456721 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9605987655299 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9605987655299 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2739466710092009 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) -
          6 * (1336139156501337456721 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9605987655299 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9605987655299 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9605987655299 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_125 :
    ((726085387699705292959 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6285287343943028423973 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((548851573845903 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) -
              6 * (1333915620402408418013 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (481980880181 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (481980880181 / 6400000000000 : ℝ)) =
      Real.log (6881980880181 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((481980880181 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (517980880181 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (726085387699705292959 / 10000000000000000000000 : ℝ) ≤
      Real.log (6881980880181 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (517980880181 / 6400000000000 : ℝ) ≤
      (-(6285287343943028423973 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (517980880181 / 6400000000000 : ℝ) = (517980880181 / 400000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (517980880181 / 400000000000 : ℝ) ≤
            (646184459056971576027 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (548851573845903 / 2000000000000000 : ℝ) ≤ Real.sqrt (481980880181 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (481980880181 / 6400000000000 : ℝ) ≤ (1372128934614759 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (481980880181 / 6400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau187 :
    Real.arctan (1372128934614759 / 5000000000000000 : ℝ) ≤
      (2678322912471147172359 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1372128934614759 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1372128934614759 : ℝ) =
              (1372128934614759 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau187)
  have hz1 :
    (5000000000000000 / 1372128934614759 : ℝ) ≤
      1 / Real.sqrt (481980880181 / 6400000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1372128934614759 : ℝ) = 1 / (1372128934614759 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 182950524615301 : ℝ) ≤
      (1333915620402408418013 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (481980880181 / 6400000000000 : ℝ) ≤
      (50000000000000 / 182950524615301 : ℝ) := by
    rw [show
        (50000000000000 / 182950524615301 : ℝ) =
          (3 / 40) / (548851573845903 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) -
        6 * (1333915620402408418013 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (481980880181 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (481980880181 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((548851573845903 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) -
          6 * (1333915620402408418013 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (481980880181 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (481980880181 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (481980880181 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_126 :
    ((72852842271510586509 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12554369707269414330891 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2749040678119169 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) -
              6 * (1331703153507762705967 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9673247551941 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9673247551941 / 128000000000000 : ℝ)) =
      Real.log (137673247551941 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9673247551941 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10393247551941 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (72852842271510586509 / 1000000000000000000000 : ℝ) ≤
      Real.log (137673247551941 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10393247551941 / 128000000000000 : ℝ) ≤
      (-(12554369707269414330891 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10393247551941 / 128000000000000 : ℝ) = (10393247551941 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10393247551941 / 8000000000000 : ℝ) ≤
            (1308573898730585669109 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2749040678119169 / 10000000000000000 : ℝ) ≤
      Real.sqrt (9673247551941 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9673247551941 / 128000000000000 : ℝ) ≤ (687260169529793 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9673247551941 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau188 :
    Real.arctan (687260169529793 / 2500000000000000 : ℝ) ≤
      (2682770213270387066649 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 687260169529793 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 687260169529793 : ℝ) =
              (687260169529793 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau188)
  have hz1 :
    (2500000000000000 / 687260169529793 : ℝ) ≤
      1 / Real.sqrt (9673247551941 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 687260169529793 : ℝ) = 1 / (687260169529793 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2749040678119169 : ℝ) ≤
      (1331703153507762705967 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9673247551941 / 128000000000000 : ℝ) ≤
      (750000000000000 / 2749040678119169 : ℝ) := by
    rw [show
        (750000000000000 / 2749040678119169 : ℝ) =
          (3 / 40) / (2749040678119169 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) -
        6 * (1331703153507762705967 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9673247551941 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9673247551941 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2749040678119169 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) -
          6 * (1331703153507762705967 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9673247551941 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9673247551941 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9673247551941 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_127 :
    ((730970861034269802467 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25076434154619059633243 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((172113448766809 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) -
              6 * (10636013313898229031 / 40000000000000000000 : ℝ)))) ≤
      Vfield (4853438750131 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4853438750131 / 64000000000000 : ℝ)) =
      Real.log (68853438750131 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4853438750131 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5213438750131 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (730970861034269802467 / 10000000000000000000000 : ℝ) ≤
      Real.log (68853438750131 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5213438750131 / 64000000000000 : ℝ) ≤
      (-(25076434154619059633243 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5213438750131 / 64000000000000 : ℝ) = (5213438750131 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5213438750131 / 4000000000000 : ℝ) ≤
            (2649453057380940366757 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (172113448766809 / 625000000000000 : ℝ) ≤ Real.sqrt (4853438750131 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4853438750131 / 64000000000000 : ℝ) ≤ (2753815180268947 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4853438750131 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau189 :
    Real.arctan (2753815180268947 / 10000000000000000 : ℝ) ≤
      (335901088212172452663 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2753815180268947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2753815180268947 : ℝ) =
              (2753815180268947 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau189)
  have hz1 :
    (10000000000000000 / 2753815180268947 : ℝ) ≤
      1 / Real.sqrt (4853438750131 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2753815180268947 : ℝ) =
          1 / (2753815180268947 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 172113448766809 : ℝ) ≤
      (10636013313898229031 / 40000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4853438750131 / 64000000000000 : ℝ) ≤
      (46875000000000 / 172113448766809 : ℝ) := by
    rw [show
        (46875000000000 / 172113448766809 : ℝ) =
          (3 / 40) / (172113448766809 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) -
        6 * (10636013313898229031 / 40000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4853438750131 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4853438750131 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((172113448766809 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) -
          6 * (10636013313898229031 / 40000000000000000000 : ℝ))) ≤
      Real.sqrt (4853438750131 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4853438750131 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4853438750131 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_128 :
    ((735853948749304669843 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5002427009599881711513 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2763339436502733 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) -
              6 * (2650262515042783265311 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1221767174613 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1221767174613 / 16000000000000 : ℝ)) =
      Real.log (17221767174613 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1221767174613 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1311767174613 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (735853948749304669843 / 10000000000000000000000 : ℝ) ≤
      Real.log (17221767174613 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1311767174613 / 16000000000000 : ℝ) ≤
      (-(5002427009599881711513 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1311767174613 / 16000000000000 : ℝ) = (1311767174613 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1311767174613 / 1000000000000 : ℝ) ≤
            (542750432800118288487 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2763339436502733 / 10000000000000000 : ℝ) ≤ Real.sqrt (1221767174613 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1221767174613 / 16000000000000 : ℝ) ≤ (172708714781421 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1221767174613 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau190 :
    Real.arctan (172708714781421 / 625000000000000 : ℝ) ≤
      (5265741098844656167 / 19531250000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 172708714781421 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 172708714781421 : ℝ) =
              (172708714781421 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau190)
  have hz1 :
    (625000000000000 / 172708714781421 : ℝ) ≤
      1 / Real.sqrt (1221767174613 / 16000000000000 : ℝ) := by
    rw [show (625000000000000 / 172708714781421 : ℝ) = 1 / (172708714781421 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 921113145500911 : ℝ) ≤
      (2650262515042783265311 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1221767174613 / 16000000000000 : ℝ) ≤
      (250000000000000 / 921113145500911 : ℝ) := by
    rw [show
        (250000000000000 / 921113145500911 : ℝ) =
          (3 / 40) / (2763339436502733 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) -
        6 * (2650262515042783265311 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1221767174613 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1221767174613 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2763339436502733 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) -
          6 * (2650262515042783265311 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1221767174613 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1221767174613 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1221767174613 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_129 :
    ((740734653173510746083 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6237061684726463436083 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1386415489272859 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) -
              6 * (52832147539552359909 / 200000000000000000000 : ℝ)))) ≤
      Vfield (4920698646773 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4920698646773 / 64000000000000 : ℝ)) =
      Real.log (68920698646773 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4920698646773 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5280698646773 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (740734653173510746083 / 10000000000000000000000 : ℝ) ≤
      Real.log (68920698646773 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5280698646773 / 64000000000000 : ℝ) ≤
      (-(6237061684726463436083 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5280698646773 / 64000000000000 : ℝ) = (5280698646773 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5280698646773 / 4000000000000 : ℝ) ≤
            (694410118273536563917 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1386415489272859 / 5000000000000000 : ℝ) ≤ Real.sqrt (4920698646773 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4920698646773 / 64000000000000 : ℝ) ≤ (2772830978545721 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4920698646773 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau191 :
    Real.arctan (2772830978545721 / 10000000000000000 : ℝ) ≤
      (676218868449462891921 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2772830978545721 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2772830978545721 : ℝ) =
              (2772830978545721 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau191)
  have hz1 :
    (10000000000000000 / 2772830978545721 : ℝ) ≤
      1 / Real.sqrt (4920698646773 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2772830978545721 : ℝ) =
          1 / (2772830978545721 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1386415489272859 : ℝ) ≤
      (52832147539552359909 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4920698646773 / 64000000000000 : ℝ) ≤
      (375000000000000 / 1386415489272859 : ℝ) := by
    rw [show
        (375000000000000 / 1386415489272859 : ℝ) =
          (3 / 40) / (1386415489272859 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) -
        6 * (52832147539552359909 / 200000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4920698646773 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4920698646773 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1386415489272859 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) -
          6 * (52832147539552359909 / 200000000000000000000 : ℝ))) ≤
      Real.sqrt (4920698646773 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4920698646773 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4920698646773 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_130 :
    ((37280648831609041759 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6221191002898389833279 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2782290141202813 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) -
              6 * (658259130780697986243 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2477164297547 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2477164297547 / 32000000000000 : ℝ)) =
      Real.log (34477164297547 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2477164297547 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2657164297547 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (37280648831609041759 / 500000000000000000000 : ℝ) ≤
      Real.log (34477164297547 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2657164297547 / 32000000000000 : ℝ) ≤
      (-(6221191002898389833279 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2657164297547 / 32000000000000 : ℝ) = (2657164297547 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2657164297547 / 2000000000000 : ℝ) ≤
            (710280800101610166721 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2782290141202813 / 10000000000000000 : ℝ) ≤ Real.sqrt (2477164297547 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2477164297547 / 32000000000000 : ℝ) ≤ (21736641728147 / 78125000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2477164297547 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau192 :
    Real.arctan (21736641728147 / 78125000000000 : ℝ) ≤
      (542731428790419567221 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (78125000000000 / 21736641728147 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (78125000000000 / 21736641728147 : ℝ) =
              (21736641728147 / 78125000000000 : ℝ)
            by
        norm_num];
        exact hau192)
  have hz1 :
    (78125000000000 / 21736641728147 : ℝ) ≤ 1 / Real.sqrt (2477164297547 / 32000000000000 : ℝ) := by
    rw [show (78125000000000 / 21736641728147 : ℝ) = 1 / (21736641728147 / 78125000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2782290141202813 : ℝ) ≤
      (658259130780697986243 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2477164297547 / 32000000000000 : ℝ) ≤
      (750000000000000 / 2782290141202813 : ℝ) := by
    rw [show
        (750000000000000 / 2782290141202813 : ℝ) =
          (3 / 40) / (2782290141202813 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) -
        6 * (658259130780697986243 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2477164297547 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2477164297547 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2782290141202813 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) -
          6 * (658259130780697986243 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2477164297547 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2477164297547 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2477164297547 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_131 :
    ((750488921447206341103 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24821681749024979579647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1395858626803403 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) -
              6 * (2624548593756629872647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (997591708683 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (997591708683 / 12800000000000 : ℝ)) =
      Real.log (13797591708683 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((997591708683 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1069591708683 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (750488921447206341103 / 10000000000000000000000 : ℝ) ≤
      Real.log (13797591708683 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1069591708683 / 12800000000000 : ℝ) ≤
      (-(24821681749024979579647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1069591708683 / 12800000000000 : ℝ) = (1069591708683 / 800000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1069591708683 / 800000000000 : ℝ) ≤
            (2904205462975020420353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1395858626803403 / 5000000000000000 : ℝ) ≤ Real.sqrt (997591708683 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (997591708683 / 12800000000000 : ℝ) ≤ (2791717253606809 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (997591708683 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau193 :
    Real.arctan (2791717253606809 / 10000000000000000 : ℝ) ≤
      (2722404791990247254829 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2791717253606809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2791717253606809 : ℝ) =
              (2791717253606809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau193)
  have hz1 :
    (10000000000000000 / 2791717253606809 : ℝ) ≤
      1 / Real.sqrt (997591708683 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2791717253606809 : ℝ) =
          1 / (2791717253606809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1395858626803403 : ℝ) ≤
      (2624548593756629872647 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (997591708683 / 12800000000000 : ℝ) ≤
      (375000000000000 / 1395858626803403 : ℝ) := by
    rw [show
        (375000000000000 / 1395858626803403 : ℝ) =
          (3 / 40) / (1395858626803403 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) -
        6 * (2624548593756629872647 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (997591708683 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (997591708683 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1395858626803403 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) -
          6 * (2624548593756629872647 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (997591708683 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (997591708683 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (997591708683 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_132 :
    ((377681244968541949289 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24758994930394767520483 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1400556319675997 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) -
              6 * (2616142259684255857913 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (627698561467 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (627698561467 / 8000000000000 : ℝ)) =
      Real.log (8627698561467 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((627698561467 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (672698561467 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (377681244968541949289 / 5000000000000000000000 : ℝ) ≤
      Real.log (8627698561467 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (672698561467 / 8000000000000 : ℝ) ≤
      (-(24758994930394767520483 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (672698561467 / 8000000000000 : ℝ) = (672698561467 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (672698561467 / 500000000000 : ℝ) ≤
            (2966892281605232479517 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1400556319675997 / 5000000000000000 : ℝ) ≤ Real.sqrt (627698561467 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (627698561467 / 8000000000000 : ℝ) ≤ (2801112639351997 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (627698561467 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau194 :
    Real.arctan (2801112639351997 / 10000000000000000 : ℝ) ≤
      (2731118751199019664549 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2801112639351997 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2801112639351997 : ℝ) =
              (2801112639351997 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau194)
  have hz1 :
    (10000000000000000 / 2801112639351997 : ℝ) ≤
      1 / Real.sqrt (627698561467 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2801112639351997 : ℝ) =
          1 / (2801112639351997 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1400556319675997 : ℝ) ≤
      (2616142259684255857913 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (627698561467 / 8000000000000 : ℝ) ≤
      (375000000000000 / 1400556319675997 : ℝ) := by
    rw [show
        (375000000000000 / 1400556319675997 : ℝ) =
          (3 / 40) / (1400556319675997 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) -
        6 * (2616142259684255857913 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (627698561467 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (627698561467 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1400556319675997 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) -
          6 * (2616142259684255857913 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (627698561467 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (627698561467 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (627698561467 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
