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

/-! # V13: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_157 :
    ((206810046119531065579 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2166608875177930686979 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3300613042921201 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3188028432898504270633 / 10000000000000000000000 : ℝ)) -
              6 * (2234364613470351213961 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (278887589353 / 2560000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (278887589353 / 2560000000000 : ℝ)) =
      Real.log (2838887589353 / 2560000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((278887589353 / 2560000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (293287589353 / 2560000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (206810046119531065579 / 2000000000000000000000 : ℝ) ≤
      Real.log (2838887589353 / 2560000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (293287589353 / 2560000000000 : ℝ) ≤
      (-(2166608875177930686979 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (293287589353 / 2560000000000 : ℝ) = (293287589353 / 160000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (293287589353 / 160000000000 : ℝ) ≤
            (605979846022069313021 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3300613042921201 / 10000000000000000 : ℝ) ≤ Real.sqrt (278887589353 / 2560000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (278887589353 / 2560000000000 : ℝ) ≤ (825153260730301 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (278887589353 / 2560000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau219 :
    Real.arctan (825153260730301 / 2500000000000000 : ℝ) ≤
      (3188028432898504270633 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3188028432898504270633 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 825153260730301 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 825153260730301 : ℝ) =
              (825153260730301 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau219)
  have hz1 :
    (2500000000000000 / 825153260730301 : ℝ) ≤ 1 / Real.sqrt (278887589353 / 2560000000000 : ℝ) :=
  by
    rw [show
        (2500000000000000 / 825153260730301 : ℝ) = 1 / (825153260730301 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3300613042921201 : ℝ) ≤
      (2234364613470351213961 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (278887589353 / 2560000000000 : ℝ) ≤
      (750000000000000 / 3300613042921201 : ℝ) := by
    rw [show
        (750000000000000 / 3300613042921201 : ℝ) =
          (3 / 40) / (3300613042921201 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3188028432898504270633 / 10000000000000000000000 : ℝ)) -
        6 * (2234364613470351213961 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (278887589353 / 2560000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (278887589353 / 2560000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3300613042921201 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3188028432898504270633 / 10000000000000000000000 : ℝ)) -
          6 * (2234364613470351213961 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (278887589353 / 2560000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (278887589353 / 2560000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (278887589353 / 2560000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_158 :
    ((1037209045854065450943 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21635554721982830516497 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((330591611702887 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (798202446697152099411 / 2500000000000000000000 : ℝ)) -
              6 * (2230898265082615487957 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1748653019653 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1748653019653 / 16000000000000 : ℝ)) =
      Real.log (17748653019653 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1748653019653 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1838653019653 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1037209045854065450943 / 10000000000000000000000 : ℝ) ≤
      Real.log (17748653019653 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1838653019653 / 16000000000000 : ℝ) ≤
      (-(21635554721982830516497 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1838653019653 / 16000000000000 : ℝ) = (1838653019653 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1838653019653 / 1000000000000 : ℝ) ≤
            (6090332490017169483503 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (330591611702887 / 1000000000000000 : ℝ) ≤ Real.sqrt (1748653019653 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1748653019653 / 16000000000000 : ℝ) ≤ (3305916117028873 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1748653019653 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau220 :
    Real.arctan (3305916117028873 / 10000000000000000 : ℝ) ≤
      (798202446697152099411 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (798202446697152099411 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3305916117028873 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3305916117028873 : ℝ) =
              (3305916117028873 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau220)
  have hz1 :
    (10000000000000000 / 3305916117028873 : ℝ) ≤
      1 / Real.sqrt (1748653019653 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3305916117028873 : ℝ) =
          1 / (3305916117028873 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 330591611702887 : ℝ) ≤
      (2230898265082615487957 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1748653019653 / 16000000000000 : ℝ) ≤
      (75000000000000 / 330591611702887 : ℝ) := by
    rw [show
        (75000000000000 / 330591611702887 : ℝ) =
          (3 / 40) / (330591611702887 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (798202446697152099411 / 2500000000000000000000 : ℝ)) -
        6 * (2230898265082615487957 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1748653019653 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1748653019653 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((330591611702887 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (798202446697152099411 / 2500000000000000000000 : ℝ)) -
          6 * (2230898265082615487957 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1748653019653 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1748653019653 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1748653019653 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_159 :
    ((520183431807087761219 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5401278410286320760879 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3311210698001703 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3197581975657524269899 / 10000000000000000000000 : ℝ)) -
              6 * (445489600655899282081 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (7017034423399 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7017034423399 / 64000000000000 : ℝ)) =
      Real.log (71017034423399 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7017034423399 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7377034423399 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (520183431807087761219 / 5000000000000000000000 : ℝ) ≤
      Real.log (71017034423399 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7377034423399 / 64000000000000 : ℝ) ≤
      (-(5401278410286320760879 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7377034423399 / 64000000000000 : ℝ) = (7377034423399 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7377034423399 / 4000000000000 : ℝ) ≤
            (1530193392713679239121 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3311210698001703 / 10000000000000000 : ℝ) ≤ Real.sqrt (7017034423399 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7017034423399 / 64000000000000 : ℝ) ≤ (1655605349000853 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7017034423399 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau221 :
    Real.arctan (1655605349000853 / 5000000000000000 : ℝ) ≤
      (3197581975657524269899 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3197581975657524269899 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1655605349000853 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1655605349000853 : ℝ) =
              (1655605349000853 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau221)
  have hz1 :
    (5000000000000000 / 1655605349000853 : ℝ) ≤
      1 / Real.sqrt (7017034423399 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1655605349000853 : ℝ) = 1 / (1655605349000853 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1103736899333901 : ℝ) ≤
      (445489600655899282081 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7017034423399 / 64000000000000 : ℝ) ≤
      (250000000000000 / 1103736899333901 : ℝ) := by
    rw [show
        (250000000000000 / 1103736899333901 : ℝ) =
          (3 / 40) / (3311210698001703 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3197581975657524269899 / 10000000000000000000000 : ℝ)) -
        6 * (445489600655899282081 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7017034423399 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7017034423399 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3311210698001703 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3197581975657524269899 / 10000000000000000000000 : ℝ)) -
          6 * (445489600655899282081 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (7017034423399 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7017034423399 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7017034423399 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_160 :
    ((1043523684507768985099 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5393691236272463449183 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3316496826515987 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3202345041943094693627 / 10000000000000000000000 : ℝ)) -
              6 * (139000856499547490079 / 625000000000000000000 : ℝ)))) ≤
      Vfield (3519728384093 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3519728384093 / 32000000000000 : ℝ)) =
      Real.log (35519728384093 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3519728384093 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3699728384093 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1043523684507768985099 / 10000000000000000000000 : ℝ) ≤
      Real.log (35519728384093 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3699728384093 / 32000000000000 : ℝ) ≤
      (-(5393691236272463449183 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3699728384093 / 32000000000000 : ℝ) = (3699728384093 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3699728384093 / 2000000000000 : ℝ) ≤
            (1537780566727536550817 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3316496826515987 / 10000000000000000 : ℝ) ≤ Real.sqrt (3519728384093 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3519728384093 / 32000000000000 : ℝ) ≤ (331649682651599 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3519728384093 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau222 :
    Real.arctan (331649682651599 / 1000000000000000 : ℝ) ≤
      (3202345041943094693627 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (3202345041943094693627 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 331649682651599 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 331649682651599 : ℝ) =
              (331649682651599 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau222)
  have hz1 :
    (1000000000000000 / 331649682651599 : ℝ) ≤
      1 / Real.sqrt (3519728384093 / 32000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 331649682651599 : ℝ) = 1 / (331649682651599 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3316496826515987 : ℝ) ≤
      (139000856499547490079 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3519728384093 / 32000000000000 : ℝ) ≤
      (750000000000000 / 3316496826515987 : ℝ) := by
    rw [show
        (750000000000000 / 3316496826515987 : ℝ) =
          (3 / 40) / (3316496826515987 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (3202345041943094693627 / 10000000000000000000000 : ℝ)) -
        6 * (139000856499547490079 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3519728384093 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3519728384093 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3316496826515987 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (3202345041943094693627 / 10000000000000000000000 : ℝ)) -
          6 * (139000856499547490079 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (3519728384093 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3519728384093 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3519728384093 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_161 :
    ((1046679509164033035797 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21544508074760811294807 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1660887271462177 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (801774756937861789931 / 2500000000000000000000 : ℝ)) -
              6 * (2220595244489986577137 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7061879112973 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7061879112973 / 64000000000000 : ℝ)) =
      Real.log (71061879112973 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7061879112973 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7421879112973 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1046679509164033035797 / 10000000000000000000000 : ℝ) ≤
      Real.log (71061879112973 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7421879112973 / 64000000000000 : ℝ) ≤
      (-(21544508074760811294807 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7421879112973 / 64000000000000 : ℝ) = (7421879112973 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7421879112973 / 4000000000000 : ℝ) ≤
            (6181379137239188705193 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1660887271462177 / 5000000000000000 : ℝ) ≤ Real.sqrt (7061879112973 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7061879112973 / 64000000000000 : ℝ) ≤ (3321774542924357 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7061879112973 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau223 :
    Real.arctan (3321774542924357 / 10000000000000000 : ℝ) ≤
      (801774756937861789931 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (801774756937861789931 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3321774542924357 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3321774542924357 : ℝ) =
              (3321774542924357 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau223)
  have hz1 :
    (10000000000000000 / 3321774542924357 : ℝ) ≤
      1 / Real.sqrt (7061879112973 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3321774542924357 : ℝ) =
          1 / (3321774542924357 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1660887271462177 : ℝ) ≤
      (2220595244489986577137 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7061879112973 / 64000000000000 : ℝ) ≤
      (375000000000000 / 1660887271462177 : ℝ) := by
    rw [show
        (375000000000000 / 1660887271462177 : ℝ) =
          (3 / 40) / (1660887271462177 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (801774756937861789931 / 2500000000000000000000 : ℝ)) -
        6 * (2220595244489986577137 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7061879112973 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7061879112973 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1660887271462177 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (801774756937861789931 / 2500000000000000000000 : ℝ)) -
          6 * (2220595244489986577137 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7061879112973 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7061879112973 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7061879112973 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_162 :
    ((41993373528462375119 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21514342476161710872833 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1663521943629689 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1605921987430325739573 / 5000000000000000000000 : ℝ)) -
              6 * (138574531459758201139 / 625000000000000000000 : ℝ)))) ≤
      Vfield (44276884111 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (44276884111 / 400000000000 : ℝ)) =
      Real.log (444276884111 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((44276884111 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (46526884111 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (41993373528462375119 / 400000000000000000000 : ℝ) ≤
      Real.log (444276884111 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (46526884111 / 400000000000 : ℝ) ≤
      (-(21514342476161710872833 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (46526884111 / 400000000000 : ℝ) = (46526884111 / 25000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (46526884111 / 25000000000 : ℝ) ≤
            (6211544735838289127167 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1663521943629689 / 5000000000000000 : ℝ) ≤ Real.sqrt (44276884111 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (44276884111 / 400000000000 : ℝ) ≤ (3327043887259381 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (44276884111 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau224 :
    Real.arctan (3327043887259381 / 10000000000000000 : ℝ) ≤
      (1605921987430325739573 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1605921987430325739573 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3327043887259381 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3327043887259381 : ℝ) =
              (3327043887259381 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau224)
  have hz1 :
    (10000000000000000 / 3327043887259381 : ℝ) ≤ 1 / Real.sqrt (44276884111 / 400000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 3327043887259381 : ℝ) =
          1 / (3327043887259381 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1663521943629689 : ℝ) ≤
      (138574531459758201139 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (44276884111 / 400000000000 : ℝ) ≤
      (375000000000000 / 1663521943629689 : ℝ) := by
    rw [show
        (375000000000000 / 1663521943629689 : ℝ) =
          (3 / 40) / (1663521943629689 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1605921987430325739573 / 5000000000000000000000 : ℝ)) -
        6 * (138574531459758201139 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (44276884111 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (44276884111 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1663521943629689 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1605921987430325739573 / 5000000000000000000000 : ℝ)) -
          6 * (138574531459758201139 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (44276884111 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (44276884111 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (44276884111 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_163 :
    ((526494086139172486441 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21484267600294531528243 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((666460979847423 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (804144981181080084799 / 2500000000000000000000 : ℝ)) -
              6 * (2213805360475395042061 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7106723802547 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7106723802547 / 64000000000000 : ℝ)) =
      Real.log (71106723802547 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7106723802547 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7466723802547 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (526494086139172486441 / 5000000000000000000000 : ℝ) ≤
      Real.log (71106723802547 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7466723802547 / 64000000000000 : ℝ) ≤
      (-(21484267600294531528243 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7466723802547 / 64000000000000 : ℝ) = (7466723802547 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7466723802547 / 4000000000000 : ℝ) ≤
            (6241619611705468471757 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (666460979847423 / 2000000000000000 : ℝ) ≤ Real.sqrt (7106723802547 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7106723802547 / 64000000000000 : ℝ) ≤ (1666152449618559 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7106723802547 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau225 :
    Real.arctan (1666152449618559 / 5000000000000000 : ℝ) ≤
      (804144981181080084799 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (804144981181080084799 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1666152449618559 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1666152449618559 : ℝ) =
              (1666152449618559 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau225)
  have hz1 :
    (5000000000000000 / 1666152449618559 : ℝ) ≤
      1 / Real.sqrt (7106723802547 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1666152449618559 : ℝ) = 1 / (1666152449618559 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 222153659949141 : ℝ) ≤
      (2213805360475395042061 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7106723802547 / 64000000000000 : ℝ) ≤
      (50000000000000 / 222153659949141 : ℝ) := by
    rw [show
        (50000000000000 / 222153659949141 : ℝ) =
          (3 / 40) / (666460979847423 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (804144981181080084799 / 2500000000000000000000 : ℝ)) -
        6 * (2213805360475395042061 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7106723802547 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7106723802547 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((666460979847423 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (804144981181080084799 / 2500000000000000000000 : ℝ)) -
          6 * (2213805360475395042061 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7106723802547 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7106723802547 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7106723802547 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_164 :
    ((132017626498974098703 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21454282903099725251803 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3337557618260599 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1610653459237582293741 / 5000000000000000000000 : ℝ)) -
              6 * (442086739402679778117 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (3564573073667 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3564573073667 / 32000000000000 : ℝ)) =
      Real.log (35564573073667 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3564573073667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3744573073667 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (132017626498974098703 / 1250000000000000000000 : ℝ) ≤
      Real.log (35564573073667 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3744573073667 / 32000000000000 : ℝ) ≤
      (-(21454282903099725251803 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3744573073667 / 32000000000000 : ℝ) = (3744573073667 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3744573073667 / 2000000000000 : ℝ) ≤
            (6271604308900274748197 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3337557618260599 / 10000000000000000 : ℝ) ≤ Real.sqrt (3564573073667 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3564573073667 / 32000000000000 : ℝ) ≤ (1668778809130301 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3564573073667 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau226 :
    Real.arctan (1668778809130301 / 5000000000000000 : ℝ) ≤
      (1610653459237582293741 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1610653459237582293741 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1668778809130301 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1668778809130301 : ℝ) =
              (1668778809130301 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau226)
  have hz1 :
    (5000000000000000 / 1668778809130301 : ℝ) ≤
      1 / Real.sqrt (3564573073667 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1668778809130301 : ℝ) = 1 / (1668778809130301 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3337557618260599 : ℝ) ≤
      (442086739402679778117 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3564573073667 / 32000000000000 : ℝ) ≤
      (750000000000000 / 3337557618260599 : ℝ) := by
    rw [show
        (750000000000000 / 3337557618260599 : ℝ) =
          (3 / 40) / (3337557618260599 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1610653459237582293741 / 5000000000000000000000 : ℝ)) -
        6 * (442086739402679778117 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3564573073667 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3564573073667 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3337557618260599 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1610653459237582293741 / 5000000000000000000000 : ℝ)) -
          6 * (442086739402679778117 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (3564573073667 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3564573073667 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3564573073667 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_165 :
    ((1059292857978712554033 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2142438784539716247631 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((668560416684657 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (806506249232123808033 / 2500000000000000000000 : ℝ)) -
              6 * (2207077395399656451427 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7151568492121 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7151568492121 / 64000000000000 : ℝ)) =
      Real.log (71151568492121 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7151568492121 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7511568492121 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1059292857978712554033 / 10000000000000000000000 : ℝ) ≤
      Real.log (71151568492121 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7511568492121 / 64000000000000 : ℝ) ≤
      (-(2142438784539716247631 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (7511568492121 / 64000000000000 : ℝ) = (7511568492121 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7511568492121 / 4000000000000 : ℝ) ≤
            (630149936660283752369 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (668560416684657 / 2000000000000000 : ℝ) ≤ Real.sqrt (7151568492121 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7151568492121 / 64000000000000 : ℝ) ≤ (417850260427911 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7151568492121 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau227 :
    Real.arctan (417850260427911 / 1250000000000000 : ℝ) ≤
      (806506249232123808033 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (806506249232123808033 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 417850260427911 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 417850260427911 : ℝ) =
              (417850260427911 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau227)
  have hz1 :
    (1250000000000000 / 417850260427911 : ℝ) ≤
      1 / Real.sqrt (7151568492121 / 64000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 417850260427911 : ℝ) = 1 / (417850260427911 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 222853472228219 : ℝ) ≤
      (2207077395399656451427 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7151568492121 / 64000000000000 : ℝ) ≤
      (50000000000000 / 222853472228219 : ℝ) := by
    rw [show
        (50000000000000 / 222853472228219 : ℝ) =
          (3 / 40) / (668560416684657 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (806506249232123808033 / 2500000000000000000000 : ℝ)) -
        6 * (2207077395399656451427 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7151568492121 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7151568492121 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((668560416684657 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (806506249232123808033 / 2500000000000000000000 : ℝ)) -
          6 * (2207077395399656451427 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7151568492121 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7151568492121 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7151568492121 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_166 :
    ((531221855432660748179 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10697290946413978844261 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1674019166756219 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (807683550146417840233 / 2500000000000000000000 : ℝ)) -
              6 * (2203736339310343190637 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1793497709227 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1793497709227 / 16000000000000 : ℝ)) =
      Real.log (17793497709227 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1793497709227 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1883497709227 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (531221855432660748179 / 5000000000000000000000 : ℝ) ≤
      Real.log (17793497709227 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1883497709227 / 16000000000000 : ℝ) ≤
      (-(10697290946413978844261 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1883497709227 / 16000000000000 : ℝ) = (1883497709227 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1883497709227 / 1000000000000 : ℝ) ≤
            (3165652659586021155739 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1674019166756219 / 5000000000000000 : ℝ) ≤ Real.sqrt (1793497709227 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1793497709227 / 16000000000000 : ℝ) ≤ (3348038333512441 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1793497709227 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau228 :
    Real.arctan (3348038333512441 / 10000000000000000 : ℝ) ≤
      (807683550146417840233 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (807683550146417840233 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3348038333512441 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3348038333512441 : ℝ) =
              (3348038333512441 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau228)
  have hz1 :
    (10000000000000000 / 3348038333512441 : ℝ) ≤
      1 / Real.sqrt (1793497709227 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3348038333512441 : ℝ) =
          1 / (3348038333512441 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1674019166756219 : ℝ) ≤
      (2203736339310343190637 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1793497709227 / 16000000000000 : ℝ) ≤
      (375000000000000 / 1674019166756219 : ℝ) := by
    rw [show
        (375000000000000 / 1674019166756219 : ℝ) =
          (3 / 40) / (1674019166756219 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (807683550146417840233 / 2500000000000000000000 : ℝ)) -
        6 * (2203736339310343190637 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1793497709227 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1793497709227 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1674019166756219 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (807683550146417840233 / 2500000000000000000000 : ℝ)) -
          6 * (2203736339310343190637 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1793497709227 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1793497709227 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1793497709227 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_167 :
    ((266398392819311274443 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21364864515797159093447 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1676633203506243 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (647086913927502052769 / 2000000000000000000000 : ℝ)) -
              6 * (2200410413651344220241 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1439282636339 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1439282636339 / 12800000000000 : ℝ)) =
      Real.log (14239282636339 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1439282636339 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1511282636339 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (266398392819311274443 / 2500000000000000000000 : ℝ) ≤
      Real.log (14239282636339 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1511282636339 / 12800000000000 : ℝ) ≤
      (-(21364864515797159093447 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1511282636339 / 12800000000000 : ℝ) = (1511282636339 / 800000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1511282636339 / 800000000000 : ℝ) ≤
            (6361022696202840906553 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1676633203506243 / 5000000000000000 : ℝ) ≤ Real.sqrt (1439282636339 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1439282636339 / 12800000000000 : ℝ) ≤ (3353266407012489 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1439282636339 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau229 :
    Real.arctan (3353266407012489 / 10000000000000000 : ℝ) ≤
      (647086913927502052769 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (647086913927502052769 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3353266407012489 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3353266407012489 : ℝ) =
              (3353266407012489 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau229)
  have hz1 :
    (10000000000000000 / 3353266407012489 : ℝ) ≤
      1 / Real.sqrt (1439282636339 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 3353266407012489 : ℝ) =
          1 / (3353266407012489 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 558877734502081 : ℝ) ≤
      (2200410413651344220241 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1439282636339 / 12800000000000 : ℝ) ≤
      (125000000000000 / 558877734502081 : ℝ) := by
    rw [show
        (125000000000000 / 558877734502081 : ℝ) =
          (3 / 40) / (1676633203506243 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (647086913927502052769 / 2000000000000000000000 : ℝ)) -
        6 * (2200410413651344220241 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1439282636339 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1439282636339 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1676633203506243 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (647086913927502052769 / 2000000000000000000000 : ℝ)) -
          6 * (2200410413651344220241 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1439282636339 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1439282636339 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1439282636339 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_168 :
    ((16699100622492466183 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21335235189417287986779 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3358486342108319 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1620063071983821825819 / 5000000000000000000000 : ℝ)) -
              6 * (137318719033849222699 / 625000000000000000000 : ℝ)))) ≤
      Vfield (3609417763241 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3609417763241 / 32000000000000 : ℝ)) =
      Real.log (35609417763241 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3609417763241 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (3789417763241 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (16699100622492466183 / 156250000000000000000 : ℝ) ≤
      Real.log (35609417763241 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (3789417763241 / 32000000000000 : ℝ) ≤
      (-(21335235189417287986779 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (3789417763241 / 32000000000000 : ℝ) = (3789417763241 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3789417763241 / 2000000000000 : ℝ) ≤
            (6390652022582712013221 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3358486342108319 / 10000000000000000 : ℝ) ≤ Real.sqrt (3609417763241 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3609417763241 / 32000000000000 : ℝ) ≤ (1679243171054161 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3609417763241 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau230 :
    Real.arctan (1679243171054161 / 5000000000000000 : ℝ) ≤
      (1620063071983821825819 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1620063071983821825819 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1679243171054161 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1679243171054161 : ℝ) =
              (1679243171054161 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau230)
  have hz1 :
    (5000000000000000 / 1679243171054161 : ℝ) ≤
      1 / Real.sqrt (3609417763241 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1679243171054161 : ℝ) = 1 / (1679243171054161 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 3358486342108319 : ℝ) ≤
      (137318719033849222699 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (3609417763241 / 32000000000000 : ℝ) ≤
      (750000000000000 / 3358486342108319 : ℝ) := by
    rw [show
        (750000000000000 / 3358486342108319 : ℝ) =
          (3 / 40) / (3358486342108319 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1620063071983821825819 / 5000000000000000000000 : ℝ)) -
        6 * (137318719033849222699 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3609417763241 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3609417763241 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3358486342108319 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1620063071983821825819 / 5000000000000000000000 : ℝ)) -
          6 * (137318719033849222699 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (3609417763241 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3609417763241 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3609417763241 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
