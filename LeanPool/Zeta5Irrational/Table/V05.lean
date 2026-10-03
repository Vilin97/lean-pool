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

/-! # V05: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_61 :
    ((283579045197899142671 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33700238312826287098913 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1695989910328919 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1680003860151625494353 / 10000000000000000000000 : ℝ)) -
              6 * (4163649465840225933501 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9204421683 / 320000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9204421683 / 320000000000 : ℝ)) = Real.log (329204421683 / 320000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9204421683 / 320000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11004421683 / 320000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (283579045197899142671 / 10000000000000000000000 : ℝ) ≤
      Real.log (329204421683 / 320000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11004421683 / 320000000000 : ℝ) ≤
      (-(33700238312826287098913 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (11004421683 / 320000000000 : ℝ) = (11004421683 / 10000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11004421683 / 10000000000 : ℝ) ≤
            (957120702173712901087 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1695989910328919 / 10000000000000000 : ℝ) ≤ Real.sqrt (9204421683 / 320000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9204421683 / 320000000000 : ℝ) ≤ (847994955164461 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9204421683 / 320000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau123 :
    Real.arctan (847994955164461 / 5000000000000000 : ℝ) ≤
      (1680003860151625494353 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1680003860151625494353 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 847994955164461 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 847994955164461 : ℝ) =
              (847994955164461 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau123)
  have hz1 :
    (5000000000000000 / 847994955164461 : ℝ) ≤ 1 / Real.sqrt (9204421683 / 320000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 847994955164461 : ℝ) = 1 / (847994955164461 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1695989910328919 : ℝ) ≤
      (4163649465840225933501 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9204421683 / 320000000000 : ℝ) ≤
      (750000000000000 / 1695989910328919 : ℝ) := by
    rw [show
        (750000000000000 / 1695989910328919 : ℝ) =
          (3 / 40) / (1695989910328919 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1680003860151625494353 / 10000000000000000000000 : ℝ)) -
        6 * (4163649465840225933501 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9204421683 / 320000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9204421683 / 320000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1695989910328919 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1680003860151625494353 / 10000000000000000000000 : ℝ)) -
          6 * (4163649465840225933501 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9204421683 / 320000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9204421683 / 320000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9204421683 / 320000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_62 :
    ((28603609146785446397 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6725398807852979702343 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((851713285760769 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (42180792698504378977 / 250000000000000000000 : ℝ)) -
              6 * (2073744912138374589189 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (928531867061 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (928531867061 / 32000000000000 : ℝ)) =
      Real.log (32928531867061 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((928531867061 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1108531867061 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (28603609146785446397 / 1000000000000000000000 : ℝ) ≤
      Real.log (32928531867061 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1108531867061 / 32000000000000 : ℝ) ≤
      (-(6725398807852979702343 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1108531867061 / 32000000000000 : ℝ) = (1108531867061 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1108531867061 / 1000000000000 : ℝ) ≤
            (206072995147020297657 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (851713285760769 / 5000000000000000 : ℝ) ≤ Real.sqrt (928531867061 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (928531867061 / 32000000000000 : ℝ) ≤ (1703426571521541 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (928531867061 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau124 :
    Real.arctan (1703426571521541 / 10000000000000000 : ℝ) ≤
      (42180792698504378977 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (42180792698504378977 / 250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1703426571521541 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1703426571521541 : ℝ) =
              (1703426571521541 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau124)
  have hz1 :
    (10000000000000000 / 1703426571521541 : ℝ) ≤
      1 / Real.sqrt (928531867061 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1703426571521541 : ℝ) =
          1 / (1703426571521541 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 283904428586923 : ℝ) ≤
      (2073744912138374589189 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (928531867061 / 32000000000000 : ℝ) ≤
      (125000000000000 / 283904428586923 : ℝ) := by
    rw [show
        (125000000000000 / 283904428586923 : ℝ) =
          (3 / 40) / (851713285760769 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (42180792698504378977 / 250000000000000000000 : ℝ)) -
        6 * (2073744912138374589189 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (928531867061 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (928531867061 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((851713285760769 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (42180792698504378977 / 250000000000000000000 : ℝ)) -
          6 * (2073744912138374589189 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (928531867061 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (928531867061 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (928531867061 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_63 :
    ((2307940273427734419 / 80000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33554282339629042240773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1710830907247629 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (847213185079392045819 / 5000000000000000000000 : ℝ)) -
              6 * (2065758707467686423337 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (468310782911 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (468310782911 / 16000000000000 : ℝ)) =
      Real.log (16468310782911 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((468310782911 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (558310782911 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2307940273427734419 / 80000000000000000000 : ℝ) ≤
      Real.log (16468310782911 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (558310782911 / 16000000000000 : ℝ) ≤
      (-(33554282339629042240773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (558310782911 / 16000000000000 : ℝ) = (558310782911 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (558310782911 / 500000000000 : ℝ) ≤
            (1103076675370957759227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1710830907247629 / 10000000000000000 : ℝ) ≤ Real.sqrt (468310782911 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (468310782911 / 16000000000000 : ℝ) ≤ (106926931702977 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (468310782911 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau125 :
    Real.arctan (106926931702977 / 625000000000000 : ℝ) ≤
      (847213185079392045819 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (847213185079392045819 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 106926931702977 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 106926931702977 : ℝ) =
              (106926931702977 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau125)
  have hz1 :
    (625000000000000 / 106926931702977 : ℝ) ≤ 1 / Real.sqrt (468310782911 / 16000000000000 : ℝ) :=
  by
    rw [show (625000000000000 / 106926931702977 : ℝ) = 1 / (106926931702977 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 570276969082543 : ℝ) ≤
      (2065758707467686423337 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (468310782911 / 16000000000000 : ℝ) ≤
      (250000000000000 / 570276969082543 : ℝ) := by
    rw [show
        (250000000000000 / 570276969082543 : ℝ) =
          (3 / 40) / (1710830907247629 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (847213185079392045819 / 5000000000000000000000 : ℝ)) -
        6 * (2065758707467686423337 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (468310782911 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (468310782911 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1710830907247629 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (847213185079392045819 / 5000000000000000000000 : ℝ)) -
          6 * (2065758707467686423337 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (468310782911 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (468310782911 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (468310782911 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_64 :
    ((290948373626185129557 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(418526194061101859357 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((429550833853069 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1701588269078549890509 / 10000000000000000000000 : ℝ)) -
              6 * (2057864319825470333217 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (944711264583 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (944711264583 / 32000000000000 : ℝ)) =
      Real.log (32944711264583 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((944711264583 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1124711264583 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (290948373626185129557 / 10000000000000000000000 : ℝ) ≤
      Real.log (32944711264583 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1124711264583 / 32000000000000 : ℝ) ≤
      (-(418526194061101859357 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1124711264583 / 32000000000000 : ℝ) = (1124711264583 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1124711264583 / 1000000000000 : ℝ) ≤
            (14690793626398140643 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (429550833853069 / 2500000000000000 : ℝ) ≤ Real.sqrt (944711264583 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (944711264583 / 32000000000000 : ℝ) ≤ (1718203335412279 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (944711264583 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau126 :
    Real.arctan (1718203335412279 / 10000000000000000 : ℝ) ≤
      (1701588269078549890509 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1701588269078549890509 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1718203335412279 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1718203335412279 : ℝ) =
              (1718203335412279 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau126)
  have hz1 :
    (10000000000000000 / 1718203335412279 : ℝ) ≤
      1 / Real.sqrt (944711264583 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1718203335412279 : ℝ) =
          1 / (1718203335412279 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 429550833853069 : ℝ) ≤
      (2057864319825470333217 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (944711264583 / 32000000000000 : ℝ) ≤
      (187500000000000 / 429550833853069 : ℝ) := by
    rw [show
        (187500000000000 / 429550833853069 : ℝ) =
          (3 / 40) / (429550833853069 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1701588269078549890509 / 10000000000000000000000 : ℝ)) -
        6 * (2057864319825470333217 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (944711264583 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (944711264583 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((429550833853069 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1701588269078549890509 / 10000000000000000000000 : ℝ)) -
          6 * (2057864319825470333217 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (944711264583 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (944711264583 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (944711264583 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_65 :
    ((293403610107240061481 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3341042607133438815809 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1725544264992931 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1708717817988970253053 / 10000000000000000000000 : ℝ)) -
              6 * (4100119996605776193839 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (59550060209 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (59550060209 / 2000000000000 : ℝ)) =
      Real.log (2059550060209 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((59550060209 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (70800060209 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (293403610107240061481 / 10000000000000000000000 : ℝ) ≤
      Real.log (2059550060209 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (70800060209 / 2000000000000 : ℝ) ≤
      (-(3341042607133438815809 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (70800060209 / 2000000000000 : ℝ) = (70800060209 / 62500000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (70800060209 / 62500000000 : ℝ) ≤
            (124693294366561184191 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1725544264992931 / 10000000000000000 : ℝ) ≤ Real.sqrt (59550060209 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (59550060209 / 2000000000000 : ℝ) ≤ (862772132496467 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (59550060209 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau127 :
    Real.arctan (862772132496467 / 5000000000000000 : ℝ) ≤
      (1708717817988970253053 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1708717817988970253053 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 862772132496467 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 862772132496467 : ℝ) =
              (862772132496467 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau127)
  have hz1 :
    (5000000000000000 / 862772132496467 : ℝ) ≤ 1 / Real.sqrt (59550060209 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 862772132496467 : ℝ) = 1 / (862772132496467 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1725544264992931 : ℝ) ≤
      (4100119996605776193839 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (59550060209 / 2000000000000 : ℝ) ≤
      (750000000000000 / 1725544264992931 : ℝ) := by
    rw [show
        (750000000000000 / 1725544264992931 : ℝ) =
          (3 / 40) / (1725544264992931 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1708717817988970253053 / 10000000000000000000000 : ℝ)) -
        6 * (4100119996605776193839 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (59550060209 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (59550060209 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1725544264992931 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1708717817988970253053 / 10000000000000000000000 : ℝ)) -
          6 * (4100119996605776193839 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (59550060209 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (59550060209 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (59550060209 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_66 :
    ((147929121958822036403 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(104185208174615246663 / 31250000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((433213524076041 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (428953855365956309143 / 2500000000000000000000 : ℝ)) -
              6 * (816937615405656711109 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (192178132421 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (192178132421 / 6400000000000 : ℝ)) =
      Real.log (6592178132421 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((192178132421 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (228178132421 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (147929121958822036403 / 5000000000000000000000 : ℝ) ≤
      Real.log (6592178132421 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (228178132421 / 6400000000000 : ℝ) ≤
      (-(104185208174615246663 / 31250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (228178132421 / 6400000000000 : ℝ) = (228178132421 / 200000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (228178132421 / 200000000000 : ℝ) ≤
            (4119038747259753337 / 31250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (433213524076041 / 2500000000000000 : ℝ) ≤ Real.sqrt (192178132421 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (192178132421 / 6400000000000 : ℝ) ≤ (1732854096304167 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (192178132421 / 6400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau128 :
    Real.arctan (1732854096304167 / 10000000000000000 : ℝ) ≤
      (428953855365956309143 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (428953855365956309143 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1732854096304167 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1732854096304167 : ℝ) =
              (1732854096304167 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau128)
  have hz1 :
    (10000000000000000 / 1732854096304167 : ℝ) ≤
      1 / Real.sqrt (192178132421 / 6400000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1732854096304167 : ℝ) =
          1 / (1732854096304167 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 144404508025347 : ℝ) ≤
      (816937615405656711109 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (192178132421 / 6400000000000 : ℝ) ≤
      (62500000000000 / 144404508025347 : ℝ) := by
    rw [show
        (62500000000000 / 144404508025347 : ℝ) =
          (3 / 40) / (433213524076041 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (428953855365956309143 / 2500000000000000000000 : ℝ)) -
        6 * (816937615405656711109 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (192178132421 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (192178132421 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((433213524076041 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (428953855365956309143 / 2500000000000000000000 : ℝ)) -
          6 * (816937615405656711109 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (192178132421 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (192178132421 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (192178132421 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_67 :
    ((9322258604787240969 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33268609951502147843163 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1740133221252397 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (861440737808505226089 / 5000000000000000000000 : ℝ)) -
              6 * (813885912405834617621 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (484490180433 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (484490180433 / 16000000000000 : ℝ)) =
      Real.log (16484490180433 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((484490180433 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (574490180433 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (9322258604787240969 / 312500000000000000000 : ℝ) ≤
      Real.log (16484490180433 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (574490180433 / 16000000000000 : ℝ) ≤
      (-(33268609951502147843163 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (574490180433 / 16000000000000 : ℝ) = (574490180433 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (574490180433 / 500000000000 : ℝ) ≤
            (1388749063497852156837 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1740133221252397 / 10000000000000000 : ℝ) ≤ Real.sqrt (484490180433 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (484490180433 / 16000000000000 : ℝ) ≤ (4350333053131 / 25000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (484490180433 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau129 :
    Real.arctan (4350333053131 / 25000000000000 : ℝ) ≤
      (861440737808505226089 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (861440737808505226089 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (25000000000000 / 4350333053131 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (25000000000000 / 4350333053131 : ℝ) = (4350333053131 / 25000000000000 : ℝ)
            by
        norm_num];
        exact hau129)
  have hz1 :
    (25000000000000 / 4350333053131 : ℝ) ≤ 1 / Real.sqrt (484490180433 / 16000000000000 : ℝ) := by
    rw [show (25000000000000 / 4350333053131 : ℝ) = 1 / (4350333053131 / 25000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1740133221252397 : ℝ) ≤
      (813885912405834617621 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (484490180433 / 16000000000000 : ℝ) ≤
      (750000000000000 / 1740133221252397 : ℝ) := by
    rw [show
        (750000000000000 / 1740133221252397 : ℝ) =
          (3 / 40) / (1740133221252397 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (861440737808505226089 / 5000000000000000000000 : ℝ)) -
        6 * (813885912405834617621 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (484490180433 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (484490180433 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1740133221252397 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (861440737808505226089 / 5000000000000000000000 : ℝ)) -
          6 * (813885912405834617621 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (484490180433 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (484490180433 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (484490180433 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_68 :
    ((75191426177364952563 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(33198449022893842451719 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1747382023581097 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1729916368348796967283 / 10000000000000000000000 : ℝ)) -
              6 * (4054341219568550892639 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (977070059627 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (977070059627 / 32000000000000 : ℝ)) =
      Real.log (32977070059627 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((977070059627 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1157070059627 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (75191426177364952563 / 2500000000000000000000 : ℝ) ≤
      Real.log (32977070059627 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1157070059627 / 32000000000000 : ℝ) ≤
      (-(33198449022893842451719 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (1157070059627 / 32000000000000 : ℝ) = (1157070059627 / 1000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1157070059627 / 1000000000000 : ℝ) ≤
            (1458909992106157548281 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1747382023581097 / 10000000000000000 : ℝ) ≤ Real.sqrt (977070059627 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (977070059627 / 32000000000000 : ℝ) ≤ (17473820235811 / 100000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (977070059627 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau130 :
    Real.arctan (17473820235811 / 100000000000000 : ℝ) ≤
      (1729916368348796967283 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1729916368348796967283 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (100000000000000 / 17473820235811 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (100000000000000 / 17473820235811 : ℝ) =
              (17473820235811 / 100000000000000 : ℝ)
            by
        norm_num];
        exact hau130)
  have hz1 :
    (100000000000000 / 17473820235811 : ℝ) ≤ 1 / Real.sqrt (977070059627 / 32000000000000 : ℝ) := by
    rw [show (100000000000000 / 17473820235811 : ℝ) = 1 / (17473820235811 / 100000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1747382023581097 : ℝ) ≤
      (4054341219568550892639 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (977070059627 / 32000000000000 : ℝ) ≤
      (750000000000000 / 1747382023581097 : ℝ) := by
    rw [show
        (750000000000000 / 1747382023581097 : ℝ) =
          (3 / 40) / (1747382023581097 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1729916368348796967283 / 10000000000000000000000 : ℝ)) -
        6 * (4054341219568550892639 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (977070059627 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (977070059627 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1747382023581097 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1729916368348796967283 / 10000000000000000000000 : ℝ)) -
          6 * (4054341219568550892639 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (977070059627 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (977070059627 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (977070059627 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_69 :
    ((303218532281807704997 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6625755384441007730879 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((43865021977671 / 250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1736920479582931750383 / 10000000000000000000000 : ℝ)) -
              6 * (201970995077376040719 / 500000000000000000000 : ℝ)))) ≤
      Vfield (246289939597 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (246289939597 / 8000000000000 : ℝ)) =
      Real.log (8246289939597 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((246289939597 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (291289939597 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (303218532281807704997 / 10000000000000000000000 : ℝ) ≤
      Real.log (8246289939597 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (291289939597 / 8000000000000 : ℝ) ≤
      (-(6625755384441007730879 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (291289939597 / 8000000000000 : ℝ) = (291289939597 / 250000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (291289939597 / 250000000000 : ℝ) ≤
            (305716418558992269121 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (43865021977671 / 250000000000000 : ℝ) ≤ Real.sqrt (246289939597 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (246289939597 / 8000000000000 : ℝ) ≤ (1754600879106843 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (246289939597 / 8000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau131 :
    Real.arctan (1754600879106843 / 10000000000000000 : ℝ) ≤
      (1736920479582931750383 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1736920479582931750383 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1754600879106843 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1754600879106843 : ℝ) =
              (1754600879106843 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau131)
  have hz1 :
    (10000000000000000 / 1754600879106843 : ℝ) ≤
      1 / Real.sqrt (246289939597 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1754600879106843 : ℝ) =
          1 / (1754600879106843 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (6250000000000 / 14621673992557 : ℝ) ≤
      (201970995077376040719 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (246289939597 / 8000000000000 : ℝ) ≤
      (6250000000000 / 14621673992557 : ℝ) := by
    rw [show
        (6250000000000 / 14621673992557 : ℝ) = (3 / 40) / (43865021977671 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1736920479582931750383 / 10000000000000000000000 : ℝ)) -
        6 * (201970995077376040719 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (246289939597 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (246289939597 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((43865021977671 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1736920479582931750383 / 10000000000000000000000 : ℝ)) -
          6 * (201970995077376040719 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (246289939597 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (246289939597 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (246289939597 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_70 :
    ((154061191627547000041 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(32990872286197016689579 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((442237553684297 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1750837838732508012519 / 10000000000000000000000 : ℝ)) -
              6 * (501258268688367222693 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (100133915591 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (100133915591 / 3200000000000 : ℝ)) =
      Real.log (3300133915591 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((100133915591 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (118133915591 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (154061191627547000041 / 5000000000000000000000 : ℝ) ≤
      Real.log (3300133915591 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (118133915591 / 3200000000000 : ℝ) ≤
      (-(32990872286197016689579 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (118133915591 / 3200000000000 : ℝ) = (118133915591 / 100000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (118133915591 / 100000000000 : ℝ) ≤
            (1666486728802983310421 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (442237553684297 / 2500000000000000 : ℝ) ≤ Real.sqrt (100133915591 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (100133915591 / 3200000000000 : ℝ) ≤ (1768950214737191 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (100133915591 / 3200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau132 :
    Real.arctan (1768950214737191 / 10000000000000000 : ℝ) ≤
      (1750837838732508012519 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1750837838732508012519 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 1768950214737191 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 1768950214737191 : ℝ) =
              (1768950214737191 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau132)
  have hz1 :
    (10000000000000000 / 1768950214737191 : ℝ) ≤
      1 / Real.sqrt (100133915591 / 3200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 1768950214737191 : ℝ) =
          1 / (1768950214737191 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 442237553684297 : ℝ) ≤
      (501258268688367222693 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (100133915591 / 3200000000000 : ℝ) ≤
      (187500000000000 / 442237553684297 : ℝ) := by
    rw [show
        (187500000000000 / 442237553684297 : ℝ) =
          (3 / 40) / (442237553684297 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1750837838732508012519 / 10000000000000000000000 : ℝ)) -
        6 * (501258268688367222693 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (100133915591 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (100133915591 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((442237553684297 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1750837838732508012519 / 10000000000000000000000 : ℝ)) -
          6 * (501258268688367222693 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (100133915591 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (100133915591 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (100133915591 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_71 :
    ((156511915315791689151 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(16427421789228452963099 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1783184084573153 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (220579555174712374839 / 1250000000000000000000 : ℝ)) -
              6 * (3981344696696963220873 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (127189819179 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (127189819179 / 4000000000000 : ℝ)) =
      Real.log (4127189819179 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((127189819179 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (149689819179 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (156511915315791689151 / 5000000000000000000000 : ℝ) ≤
      Real.log (4127189819179 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (149689819179 / 4000000000000 : ℝ) ≤
      (-(16427421789228452963099 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (149689819179 / 4000000000000 : ℝ) = (149689819179 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (149689819179 / 125000000000 : ℝ) ≤
            (901257718271547036901 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1783184084573153 / 10000000000000000 : ℝ) ≤ Real.sqrt (127189819179 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (127189819179 / 4000000000000 : ℝ) ≤ (445796021143289 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (127189819179 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau133 :
    Real.arctan (445796021143289 / 2500000000000000 : ℝ) ≤
      (220579555174712374839 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (220579555174712374839 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 445796021143289 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 445796021143289 : ℝ) =
              (445796021143289 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau133)
  have hz1 :
    (2500000000000000 / 445796021143289 : ℝ) ≤ 1 / Real.sqrt (127189819179 / 4000000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 445796021143289 : ℝ) = 1 / (445796021143289 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1783184084573153 : ℝ) ≤
      (3981344696696963220873 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (127189819179 / 4000000000000 : ℝ) ≤
      (750000000000000 / 1783184084573153 : ℝ) := by
    rw [show
        (750000000000000 / 1783184084573153 : ℝ) =
          (3 / 40) / (1783184084573153 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (220579555174712374839 / 1250000000000000000000 : ℝ)) -
        6 * (3981344696696963220873 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (127189819179 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (127189819179 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1783184084573153 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (220579555174712374839 / 1250000000000000000000 : ℝ)) -
          6 * (3981344696696963220873 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (127189819179 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (127189819179 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (127189819179 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_72 :
    ((317922876766342253191 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(32720640446352325306753 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1797305231932307 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (355663812413146259823 / 2000000000000000000000 : ℝ)) -
              6 * (1976616554840196050209 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (516848975477 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (516848975477 / 16000000000000 : ℝ)) =
      Real.log (16516848975477 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((516848975477 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (606848975477 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (317922876766342253191 / 10000000000000000000000 : ℝ) ≤
      Real.log (16516848975477 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (606848975477 / 16000000000000 : ℝ) ≤
      (-(32720640446352325306753 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (606848975477 / 16000000000000 : ℝ) = (606848975477 / 500000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (606848975477 / 500000000000 : ℝ) ≤
            (1936718568647674693247 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1797305231932307 / 10000000000000000 : ℝ) ≤ Real.sqrt (516848975477 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (516848975477 / 16000000000000 : ℝ) ≤ (179730523193231 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (516848975477 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau134 :
    Real.arctan (179730523193231 / 1000000000000000 : ℝ) ≤
      (355663812413146259823 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (355663812413146259823 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 179730523193231 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 179730523193231 : ℝ) =
              (179730523193231 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau134)
  have hz1 :
    (1000000000000000 / 179730523193231 : ℝ) ≤
      1 / Real.sqrt (516848975477 / 16000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 179730523193231 : ℝ) = 1 / (179730523193231 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 1797305231932307 : ℝ) ≤
      (1976616554840196050209 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (516848975477 / 16000000000000 : ℝ) ≤
      (750000000000000 / 1797305231932307 : ℝ) := by
    rw [show
        (750000000000000 / 1797305231932307 : ℝ) =
          (3 / 40) / (1797305231932307 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (355663812413146259823 / 2000000000000000000000 : ℝ)) -
        6 * (1976616554840196050209 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (516848975477 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (516848975477 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1797305231932307 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (355663812413146259823 / 2000000000000000000000 : ℝ)) -
          6 * (1976616554840196050209 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (516848975477 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (516848975477 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (516848975477 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
