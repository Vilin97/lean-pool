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

/-! # V45: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_541 :
    ((1203010037783684061843 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4721718145366935286647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1965358351613251 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1665586163161638182387 / 5000000000000000000000 : ℝ))) -
              6 * (951145802866699611319 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (39553366530621 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39553366530621 / 64000000000000 : ℝ)) =
      Real.log (103553366530621 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39553366530621 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (39913366530621 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1203010037783684061843 / 2500000000000000000000 : ℝ) ≤
      Real.log (103553366530621 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (39913366530621 / 64000000000000 : ℝ) ≤
      (-(4721718145366935286647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39913366530621 / 64000000000000 : ℝ) = (39913366530621 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39913366530621 / 32000000000000 : ℝ) ≤
            (2209753657633064713353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1965358351613251 / 2500000000000000 : ℝ) ≤ Real.sqrt (39553366530621 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39553366530621 / 64000000000000 : ℝ) ≤
      (7861433406453007 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39553366530621 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau854 :
    Real.arctan (7861433406453007 / 22720146823212981 : ℝ) ≤
      (1665586163161638182387 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau853 :
    Real.arctan (7861433406453007 / 10000000000000000 : ℝ) ≤
      (2 * (1665586163161638182387 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12720146823212981 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7861433406453007 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7861433406453007 / 10000000000000000 : ℝ) /
                (1 + (12720146823212981 / 10000000000000000 : ℝ)) =
              (7861433406453007 / 22720146823212981 : ℝ)
            by
        norm_num];
        exact hau854)
  have hat1 :
    (Real.pi / 2 - (2 * (1665586163161638182387 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7861433406453007 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7861433406453007 : ℝ) =
              (7861433406453007 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau853)
  have hz1 :
    (10000000000000000 / 7861433406453007 : ℝ) ≤
      1 / Real.sqrt (39553366530621 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7861433406453007 : ℝ) =
          1 / (7861433406453007 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1965358351613251 : ℝ) ≤
      (951145802866699611319 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39553366530621 / 64000000000000 : ℝ) ≤
      (187500000000000 / 1965358351613251 : ℝ) := by
    rw [show
        (187500000000000 / 1965358351613251 : ℝ) =
          (3 / 40) / (1965358351613251 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1665586163161638182387 / 5000000000000000000000 : ℝ))) -
        6 * (951145802866699611319 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39553366530621 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39553366530621 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1965358351613251 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1665586163161638182387 / 5000000000000000000000 : ℝ))) -
          6 * (951145802866699611319 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (39553366530621 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39553366530621 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39553366530621 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_542 :
    ((481868114864098952669 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(117612437523516345031 / 250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1573653375420513 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3333283300374232651811 / 10000000000000000000000 : ℝ))) -
              6 * (118790589224961794759 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (19811079567779 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19811079567779 / 32000000000000 : ℝ)) =
      Real.log (51811079567779 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19811079567779 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (19991079567779 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (481868114864098952669 / 1000000000000000000000 : ℝ) ≤
      Real.log (51811079567779 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (19991079567779 / 32000000000000 : ℝ) ≤
      (-(117612437523516345031 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19991079567779 / 32000000000000 : ℝ) = (19991079567779 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19991079567779 / 16000000000000 : ℝ) ≤
            (55674357551483654969 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1573653375420513 / 2000000000000000 : ℝ) ≤ Real.sqrt (19811079567779 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19811079567779 / 32000000000000 : ℝ) ≤ (983533359637821 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19811079567779 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau856 :
    Real.arctan (3934133438551284 / 11362185623850293 : ℝ) ≤
      (3333283300374232651811 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau855 :
    Real.arctan (983533359637821 / 1250000000000000 : ℝ) ≤
      (2 * (3333283300374232651811 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6362185623850293 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (983533359637821 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (983533359637821 / 1250000000000000 : ℝ) /
                (1 + (6362185623850293 / 5000000000000000 : ℝ)) =
              (3934133438551284 / 11362185623850293 : ℝ)
            by
        norm_num];
        exact hau856)
  have hat1 :
    (Real.pi / 2 - (2 * (3333283300374232651811 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 983533359637821 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 983533359637821 : ℝ) =
              (983533359637821 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau855)
  have hz1 :
    (1250000000000000 / 983533359637821 : ℝ) ≤
      1 / Real.sqrt (19811079567779 / 32000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 983533359637821 : ℝ) = 1 / (983533359637821 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 524551125140171 : ℝ) ≤
      (118790589224961794759 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19811079567779 / 32000000000000 : ℝ) ≤
      (50000000000000 / 524551125140171 : ℝ) := by
    rw [show
        (50000000000000 / 524551125140171 : ℝ) =
          (3 / 40) / (1573653375420513 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3333283300374232651811 / 10000000000000000000000 : ℝ))) -
        6 * (118790589224961794759 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19811079567779 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19811079567779 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1573653375420513 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3333283300374232651811 / 10000000000000000000000 : ℝ))) -
          6 * (118790589224961794759 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (19811079567779 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19811079567779 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19811079567779 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_543 :
    ((603164717348652311 / 1250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4687306460600976406899 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7875094418133881 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (66707820858295245557 / 200000000000000000000 : ℝ))) -
              6 * (237376436882747463663 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (7938190348099 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7938190348099 / 12800000000000 : ℝ)) =
      Real.log (20738190348099 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7938190348099 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8010190348099 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (603164717348652311 / 1250000000000000000 : ℝ) ≤
      Real.log (20738190348099 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8010190348099 / 12800000000000 : ℝ) ≤
      (-(4687306460600976406899 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8010190348099 / 12800000000000 : ℝ) = (8010190348099 / 6400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8010190348099 / 6400000000000 : ℝ) ≤
            (2244165342399023593101 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7875094418133881 / 10000000000000000 : ℝ) ≤ Real.sqrt (7938190348099 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7938190348099 / 12800000000000 : ℝ) ≤ (1968773604533471 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7938190348099 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau858 :
    Real.arctan (7875094418133884 / 22728594270166813 : ℝ) ≤
      (66707820858295245557 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau857 :
    Real.arctan (1968773604533471 / 2500000000000000 : ℝ) ≤
      (2 * (66707820858295245557 / 200000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12728594270166813 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1968773604533471 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1968773604533471 / 2500000000000000 : ℝ) /
                (1 + (12728594270166813 / 10000000000000000 : ℝ)) =
              (7875094418133884 / 22728594270166813 : ℝ)
            by
        norm_num];
        exact hau858)
  have hat1 :
    (Real.pi / 2 - (2 * (66707820858295245557 / 200000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1968773604533471 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1968773604533471 : ℝ) =
              (1968773604533471 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau857)
  have hz1 :
    (2500000000000000 / 1968773604533471 : ℝ) ≤
      1 / Real.sqrt (7938190348099 / 12800000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1968773604533471 : ℝ) = 1 / (1968773604533471 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7875094418133881 : ℝ) ≤
      (237376436882747463663 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7938190348099 / 12800000000000 : ℝ) ≤
      (750000000000000 / 7875094418133881 : ℝ) := by
    rw [show
        (750000000000000 / 7875094418133881 : ℝ) =
          (3 / 40) / (7875094418133881 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (66707820858295245557 / 200000000000000000000 : ℝ))) -
        6 * (237376436882747463663 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7938190348099 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7938190348099 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7875094418133881 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (66707820858295245557 / 200000000000000000000 : ℝ))) -
          6 * (237376436882747463663 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (7938190348099 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7938190348099 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7938190348099 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_544 :
    ((603993740928188690151 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4670144922737522464169 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((985239505619521 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3337495562985116148511 / 10000000000000000000000 : ℝ))) -
              6 * (948688894929314443929 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4969968043179 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4969968043179 / 8000000000000 : ℝ)) =
      Real.log (12969968043179 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4969968043179 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5014968043179 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (603993740928188690151 / 1250000000000000000000 : ℝ) ≤
      Real.log (12969968043179 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5014968043179 / 8000000000000 : ℝ) ≤
      (-(4670144922737522464169 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5014968043179 / 8000000000000 : ℝ) = (5014968043179 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5014968043179 / 4000000000000 : ℝ) ≤
            (2261326880262477535831 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (985239505619521 / 1250000000000000 : ℝ) ≤ Real.sqrt (4969968043179 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4969968043179 / 8000000000000 : ℝ) ≤ (7881916044956171 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4969968043179 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau860 :
    Real.arctan (7881916044956171 / 22732815892006665 : ℝ) ≤
      (3337495562985116148511 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau859 :
    Real.arctan (7881916044956171 / 10000000000000000 : ℝ) ≤
      (2 * (3337495562985116148511 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2546563178401333 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7881916044956171 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7881916044956171 / 10000000000000000 : ℝ) /
                (1 + (2546563178401333 / 2000000000000000 : ℝ)) =
              (7881916044956171 / 22732815892006665 : ℝ)
            by
        norm_num];
        exact hau860)
  have hat1 :
    (Real.pi / 2 - (2 * (3337495562985116148511 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7881916044956171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7881916044956171 : ℝ) =
              (7881916044956171 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau859)
  have hz1 :
    (10000000000000000 / 7881916044956171 : ℝ) ≤
      1 / Real.sqrt (4969968043179 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7881916044956171 : ℝ) =
          1 / (7881916044956171 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 985239505619521 : ℝ) ≤
      (948688894929314443929 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4969968043179 / 8000000000000 : ℝ) ≤
      (93750000000000 / 985239505619521 : ℝ) := by
    rw [show
        (93750000000000 / 985239505619521 : ℝ) =
          (3 / 40) / (985239505619521 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3337495562985116148511 / 10000000000000000000000 : ℝ))) -
        6 * (948688894929314443929 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4969968043179 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4969968043179 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((985239505619521 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3337495562985116148511 / 10000000000000000000000 : ℝ))) -
          6 * (948688894929314443929 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4969968043179 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4969968043179 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4969968043179 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_545 :
    ((38708621763074600159 / 80000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4653012786262152590651 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1577746354582403 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3339596869587028725083 / 10000000000000000000000 : ℝ))) -
              6 * (947874146918292524199 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (39828536950369 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39828536950369 / 64000000000000 : ℝ)) =
      Real.log (103828536950369 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39828536950369 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (40188536950369 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (38708621763074600159 / 80000000000000000000 : ℝ) ≤
      Real.log (103828536950369 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (40188536950369 / 64000000000000 : ℝ) ≤
      (-(4653012786262152590651 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40188536950369 / 64000000000000 : ℝ) = (40188536950369 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (40188536950369 / 32000000000000 : ℝ) ≤
            (2278459016737847409349 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1577746354582403 / 2000000000000000 : ℝ) ≤ Real.sqrt (39828536950369 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39828536950369 / 64000000000000 : ℝ) ≤ (3944365886456009 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39828536950369 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau862 :
    Real.arctan (3944365886456009 / 11368518057306416 : ℝ) ≤
      (3339596869587028725083 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau861 :
    Real.arctan (3944365886456009 / 5000000000000000 : ℝ) ≤
      (2 * (3339596869587028725083 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (398032378581651 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (3944365886456009 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3944365886456009 / 5000000000000000 : ℝ) /
                (1 + (398032378581651 / 312500000000000 : ℝ)) =
              (3944365886456009 / 11368518057306416 : ℝ)
            by
        norm_num];
        exact hau862)
  have hat1 :
    (Real.pi / 2 - (2 * (3339596869587028725083 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3944365886456009 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3944365886456009 : ℝ) =
              (3944365886456009 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau861)
  have hz1 :
    (5000000000000000 / 3944365886456009 : ℝ) ≤
      1 / Real.sqrt (39828536950369 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3944365886456009 : ℝ) = 1 / (3944365886456009 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1577746354582403 : ℝ) ≤
      (947874146918292524199 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39828536950369 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1577746354582403 : ℝ) := by
    rw [show
        (150000000000000 / 1577746354582403 : ℝ) =
          (3 / 40) / (1577746354582403 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3339596869587028725083 / 10000000000000000000000 : ℝ))) -
        6 * (947874146918292524199 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39828536950369 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39828536950369 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1577746354582403 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3339596869587028725083 / 10000000000000000000000 : ℝ))) -
          6 * (947874146918292524199 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (39828536950369 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39828536950369 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39828536950369 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_546 :
    ((4845201123488534177387 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2317954975302697975151 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7895541617277791 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1670847485841972874563 / 5000000000000000000000 : ℝ))) -
              6 * (947061494476020427973 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19948664777653 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19948664777653 / 32000000000000 : ℝ)) =
      Real.log (51948664777653 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19948664777653 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20128664777653 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4845201123488534177387 / 10000000000000000000000 : ℝ) ≤
      Real.log (51948664777653 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20128664777653 / 32000000000000 : ℝ) ≤
      (-(2317954975302697975151 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20128664777653 / 32000000000000 : ℝ) = (20128664777653 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20128664777653 / 16000000000000 : ℝ) ≤
            (1147780926197302024849 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7895541617277791 / 10000000000000000 : ℝ) ≤
      Real.sqrt (19948664777653 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19948664777653 / 32000000000000 : ℝ) ≤ (3947770808638897 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19948664777653 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau864 :
    Real.arctan (7895541617277794 / 22741254939375697 : ℝ) ≤
      (1670847485841972874563 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau863 :
    Real.arctan (3947770808638897 / 5000000000000000 : ℝ) ≤
      (2 * (1670847485841972874563 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12741254939375697 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3947770808638897 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3947770808638897 / 5000000000000000 : ℝ) /
                (1 + (12741254939375697 / 10000000000000000 : ℝ)) =
              (7895541617277794 / 22741254939375697 : ℝ)
            by
        norm_num];
        exact hau864)
  have hat1 :
    (Real.pi / 2 - (2 * (1670847485841972874563 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3947770808638897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3947770808638897 : ℝ) =
              (3947770808638897 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau863)
  have hz1 :
    (5000000000000000 / 3947770808638897 : ℝ) ≤
      1 / Real.sqrt (19948664777653 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3947770808638897 : ℝ) = 1 / (3947770808638897 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7895541617277791 : ℝ) ≤
      (947061494476020427973 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (19948664777653 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7895541617277791 : ℝ) := by
    rw [show
        (750000000000000 / 7895541617277791 : ℝ) =
          (3 / 40) / (7895541617277791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1670847485841972874563 / 5000000000000000000000 : ℝ))) -
        6 * (947061494476020427973 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19948664777653 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19948664777653 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7895541617277791 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1670847485841972874563 / 5000000000000000000000 : ℝ))) -
          6 * (947061494476020427973 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (19948664777653 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19948664777653 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19948664777653 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_547 :
    ((4851820142549443681207 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4618836315712907967727 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1580469118652809 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1671894939100624160823 / 5000000000000000000000 : ℝ))) -
              6 * (946250928634646755839 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (39966122160243 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (39966122160243 / 64000000000000 : ℝ)) =
      Real.log (103966122160243 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((39966122160243 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (40326122160243 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4851820142549443681207 / 10000000000000000000000 : ℝ) ≤
      Real.log (103966122160243 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (40326122160243 / 64000000000000 : ℝ) ≤
      (-(4618836315712907967727 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40326122160243 / 64000000000000 : ℝ) = (40326122160243 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (40326122160243 / 32000000000000 : ℝ) ≤
            (2312635487287092032273 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1580469118652809 / 2000000000000000 : ℝ) ≤ Real.sqrt (39966122160243 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (39966122160243 / 64000000000000 : ℝ) ≤ (493896599579003 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (39966122160243 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau866 :
    Real.arctan (7902345593264048 / 22745472367683345 : ℝ) ≤
      (1671894939100624160823 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau865 :
    Real.arctan (493896599579003 / 625000000000000 : ℝ) ≤
      (2 * (1671894939100624160823 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2549094473536669 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (493896599579003 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (493896599579003 / 625000000000000 : ℝ) /
                (1 + (2549094473536669 / 2000000000000000 : ℝ)) =
              (7902345593264048 / 22745472367683345 : ℝ)
            by
        norm_num];
        exact hau866)
  have hat1 :
    (Real.pi / 2 - (2 * (1671894939100624160823 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 493896599579003 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 493896599579003 : ℝ) =
              (493896599579003 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau865)
  have hz1 :
    (625000000000000 / 493896599579003 : ℝ) ≤
      1 / Real.sqrt (39966122160243 / 64000000000000 : ℝ) := by
    rw [show (625000000000000 / 493896599579003 : ℝ) = 1 / (493896599579003 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1580469118652809 : ℝ) ≤
      (946250928634646755839 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (39966122160243 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1580469118652809 : ℝ) := by
    rw [show
        (150000000000000 / 1580469118652809 : ℝ) =
          (3 / 40) / (1580469118652809 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1671894939100624160823 / 5000000000000000000000 : ℝ))) -
        6 * (946250928634646755839 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (39966122160243 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (39966122160243 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1580469118652809 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1671894939100624160823 / 5000000000000000000000 : ℝ))) -
          6 * (946250928634646755839 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (39966122160243 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (39966122160243 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (39966122160243 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_548 :
    ((2429217391683414152803 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4601791782041958375991 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1581828743203179 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3345881598026473956461 / 10000000000000000000000 : ℝ))) -
              6 * (236360610119989398587 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2001745738259 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2001745738259 / 3200000000000 : ℝ)) =
      Real.log (5201745738259 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2001745738259 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2019745738259 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2429217391683414152803 / 5000000000000000000000 : ℝ) ≤
      Real.log (5201745738259 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2019745738259 / 3200000000000 : ℝ) ≤
      (-(4601791782041958375991 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2019745738259 / 3200000000000 : ℝ) = (2019745738259 / 1600000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2019745738259 / 1600000000000 : ℝ) ≤
            (2329680020958041624009 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1581828743203179 / 2000000000000000 : ℝ) ≤ Real.sqrt (2001745738259 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2001745738259 / 3200000000000 : ℝ) ≤ (3954571858007949 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2001745738259 / 3200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau868 :
    Real.arctan (2636381238671966 / 7583229466973853 : ℝ) ≤
      (3345881598026473956461 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau867 :
    Real.arctan (3954571858007949 / 5000000000000000 : ℝ) ≤
      (2 * (3345881598026473956461 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12749688400921559 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3954571858007949 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3954571858007949 / 5000000000000000 : ℝ) /
                (1 + (12749688400921559 / 10000000000000000 : ℝ)) =
              (2636381238671966 / 7583229466973853 : ℝ)
            by
        norm_num];
        exact hau868)
  have hat1 :
    (Real.pi / 2 - (2 * (3345881598026473956461 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3954571858007949 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3954571858007949 : ℝ) =
              (3954571858007949 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau867)
  have hz1 :
    (5000000000000000 / 3954571858007949 : ℝ) ≤
      1 / Real.sqrt (2001745738259 / 3200000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3954571858007949 : ℝ) = 1 / (3954571858007949 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 527276247734393 : ℝ) ≤
      (236360610119989398587 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2001745738259 / 3200000000000 : ℝ) ≤
      (50000000000000 / 527276247734393 : ℝ) := by
    rw [show
        (50000000000000 / 527276247734393 : ℝ) =
          (3 / 40) / (1581828743203179 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3345881598026473956461 / 10000000000000000000000 : ℝ))) -
        6 * (236360610119989398587 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2001745738259 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2001745738259 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1581828743203179 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3345881598026473956461 / 10000000000000000000000 : ℝ))) -
          6 * (236360610119989398587 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2001745738259 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2001745738259 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2001745738259 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_549 :
    ((2432522525864480701643 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4584776250557949002001 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7915936000613433 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (418496267501192554361 / 1250000000000000000000 : ℝ))) -
              6 * (472318010575481681801 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (40103707370117 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (40103707370117 / 64000000000000 : ℝ)) =
      Real.log (104103707370117 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((40103707370117 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (40463707370117 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2432522525864480701643 / 5000000000000000000000 : ℝ) ≤
      Real.log (104103707370117 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (40463707370117 / 64000000000000 : ℝ) ≤
      (-(4584776250557949002001 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40463707370117 / 64000000000000 : ℝ) = (40463707370117 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (40463707370117 / 32000000000000 : ℝ) ≤
            (2346695552442050997999 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7915936000613433 / 10000000000000000 : ℝ) ≤
      Real.sqrt (40103707370117 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (40103707370117 / 64000000000000 : ℝ) ≤ (1978984000153359 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (40103707370117 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau870 :
    Real.arctan (3957968000306718 / 11376951520236919 : ℝ) ≤
      (418496267501192554361 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau869 :
    Real.arctan (1978984000153359 / 2500000000000000 : ℝ) ≤
      (2 * (418496267501192554361 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6376951520236919 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1978984000153359 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1978984000153359 / 2500000000000000 : ℝ) /
                (1 + (6376951520236919 / 5000000000000000 : ℝ)) =
              (3957968000306718 / 11376951520236919 : ℝ)
            by
        norm_num];
        exact hau870)
  have hat1 :
    (Real.pi / 2 - (2 * (418496267501192554361 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1978984000153359 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1978984000153359 : ℝ) =
              (1978984000153359 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau869)
  have hz1 :
    (2500000000000000 / 1978984000153359 : ℝ) ≤
      1 / Real.sqrt (40103707370117 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1978984000153359 : ℝ) = 1 / (1978984000153359 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2638645333537811 : ℝ) ≤
      (472318010575481681801 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (40103707370117 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2638645333537811 : ℝ) := by
    rw [show
        (250000000000000 / 2638645333537811 : ℝ) =
          (3 / 40) / (7915936000613433 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (418496267501192554361 / 1250000000000000000000 : ℝ))) -
        6 * (472318010575481681801 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (40103707370117 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (40103707370117 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7915936000613433 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (418496267501192554361 / 1250000000000000000000 : ℝ))) -
          6 * (472318010575481681801 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (40103707370117 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (40103707370117 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (40103707370117 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_550 :
    ((4871650953412645296287 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4567789622730961196307 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7922722462072103 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3350055512962961865401 / 10000000000000000000000 : ℝ))) -
              6 * (943831661839492373971 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20086249987527 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20086249987527 / 32000000000000 : ℝ)) =
      Real.log (52086249987527 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20086249987527 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20266249987527 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4871650953412645296287 / 10000000000000000000000 : ℝ) ≤
      Real.log (52086249987527 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20266249987527 / 32000000000000 : ℝ) ≤
      (-(4567789622730961196307 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20266249987527 / 32000000000000 : ℝ) = (20266249987527 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20266249987527 / 16000000000000 : ℝ) ≤
            (2363682180269038803693 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7922722462072103 / 10000000000000000 : ℝ) ≤
      Real.sqrt (20086249987527 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20086249987527 / 32000000000000 : ℝ) ≤ (3961361231036053 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20086249987527 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau872 :
    Real.arctan (7922722462072106 / 22758116287721391 : ℝ) ≤
      (3350055512962961865401 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau871 :
    Real.arctan (3961361231036053 / 5000000000000000 : ℝ) ≤
      (2 * (3350055512962961865401 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12758116287721391 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3961361231036053 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3961361231036053 / 5000000000000000 : ℝ) /
                (1 + (12758116287721391 / 10000000000000000 : ℝ)) =
              (7922722462072106 / 22758116287721391 : ℝ)
            by
        norm_num];
        exact hau872)
  have hat1 :
    (Real.pi / 2 - (2 * (3350055512962961865401 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3961361231036053 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3961361231036053 : ℝ) =
              (3961361231036053 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau871)
  have hz1 :
    (5000000000000000 / 3961361231036053 : ℝ) ≤
      1 / Real.sqrt (20086249987527 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3961361231036053 : ℝ) = 1 / (3961361231036053 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7922722462072103 : ℝ) ≤
      (943831661839492373971 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20086249987527 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7922722462072103 : ℝ) := by
    rw [show
        (750000000000000 / 7922722462072103 : ℝ) =
          (3 / 40) / (7922722462072103 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3350055512962961865401 / 10000000000000000000000 : ℝ))) -
        6 * (943831661839492373971 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20086249987527 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20086249987527 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7922722462072103 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3350055512962961865401 / 10000000000000000000000 : ℝ))) -
          6 * (943831661839492373971 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (20086249987527 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20086249987527 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20086249987527 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_551 :
    ((609781561772905195823 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1137707950133083130891 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7929503115343099 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3352137725662069253959 / 10000000000000000000000 : ℝ))) -
              6 * (471514676894892731199 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (40241292579991 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (40241292579991 / 64000000000000 : ℝ)) =
      Real.log (104241292579991 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((40241292579991 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (40601292579991 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (609781561772905195823 / 1250000000000000000000 : ℝ) ≤
      Real.log (104241292579991 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (40601292579991 / 64000000000000 : ℝ) ≤
      (-(1137707950133083130891 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40601292579991 / 64000000000000 : ℝ) = (40601292579991 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (40601292579991 / 32000000000000 : ℝ) ≤
            (595160000616916869109 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7929503115343099 / 10000000000000000 : ℝ) ≤
      Real.sqrt (40241292579991 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (40241292579991 / 64000000000000 : ℝ) ≤ (3964751557671551 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (40241292579991 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau874 :
    Real.arctan (3964751557671551 / 11381164072021576 : ℝ) ≤
      (3352137725662069253959 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau873 :
    Real.arctan (3964751557671551 / 5000000000000000 : ℝ) ≤
      (2 * (3352137725662069253959 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (797645509002697 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (3964751557671551 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3964751557671551 / 5000000000000000 : ℝ) /
                (1 + (797645509002697 / 625000000000000 : ℝ)) =
              (3964751557671551 / 11381164072021576 : ℝ)
            by
        norm_num];
        exact hau874)
  have hat1 :
    (Real.pi / 2 - (2 * (3352137725662069253959 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3964751557671551 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3964751557671551 : ℝ) =
              (3964751557671551 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau873)
  have hz1 :
    (5000000000000000 / 3964751557671551 : ℝ) ≤
      1 / Real.sqrt (40241292579991 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3964751557671551 : ℝ) = 1 / (3964751557671551 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7929503115343099 : ℝ) ≤
      (471514676894892731199 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (40241292579991 / 64000000000000 : ℝ) ≤
      (750000000000000 / 7929503115343099 : ℝ) := by
    rw [show
        (750000000000000 / 7929503115343099 : ℝ) =
          (3 / 40) / (7929503115343099 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3352137725662069253959 / 10000000000000000000000 : ℝ))) -
        6 * (471514676894892731199 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (40241292579991 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (40241292579991 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7929503115343099 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3352137725662069253959 / 10000000000000000000000 : ℝ))) -
          6 * (471514676894892731199 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (40241292579991 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (40241292579991 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (40241292579991 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_552 :
    ((2442424839897350623381 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4533902686431262429811 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7936277975313741 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3354216786845224709769 / 10000000000000000000000 : ℝ))) -
              6 * (942229088298096658871 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1259690162029 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1259690162029 / 2000000000000 : ℝ)) =
      Real.log (3259690162029 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1259690162029 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1270940162029 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2442424839897350623381 / 5000000000000000000000 : ℝ) ≤
      Real.log (3259690162029 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1270940162029 / 2000000000000 : ℝ) ≤
      (-(4533902686431262429811 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (1270940162029 / 2000000000000 : ℝ) = (1270940162029 / 1000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1270940162029 / 1000000000000 : ℝ) ≤
            (2397569116568737570189 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7936277975313741 / 10000000000000000 : ℝ) ≤ Real.sqrt (1259690162029 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1259690162029 / 2000000000000 : ℝ) ≤ (496017373457109 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1259690162029 / 2000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau876 :
    Real.arctan (7936277975313744 / 22766538610815775 : ℝ) ≤
      (3354216786845224709769 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau875 :
    Real.arctan (496017373457109 / 625000000000000 : ℝ) ≤
      (2 * (3354216786845224709769 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (510661544432631 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (496017373457109 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (496017373457109 / 625000000000000 : ℝ) /
                (1 + (510661544432631 / 400000000000000 : ℝ)) =
              (7936277975313744 / 22766538610815775 : ℝ)
            by
        norm_num];
        exact hau876)
  have hat1 :
    (Real.pi / 2 - (2 * (3354216786845224709769 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 496017373457109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 496017373457109 : ℝ) =
              (496017373457109 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau875)
  have hz1 :
    (625000000000000 / 496017373457109 : ℝ) ≤ 1 / Real.sqrt (1259690162029 / 2000000000000 : ℝ) :=
  by
    rw [show (625000000000000 / 496017373457109 : ℝ) = 1 / (496017373457109 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2645425991771247 : ℝ) ≤
      (942229088298096658871 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1259690162029 / 2000000000000 : ℝ) ≤
      (250000000000000 / 2645425991771247 : ℝ) := by
    rw [show
        (250000000000000 / 2645425991771247 : ℝ) =
          (3 / 40) / (7936277975313741 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3354216786845224709769 / 10000000000000000000000 : ℝ))) -
        6 * (942229088298096658871 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1259690162029 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1259690162029 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7936277975313741 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3354216786845224709769 / 10000000000000000000000 : ℝ))) -
          6 * (942229088298096658871 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1259690162029 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1259690162029 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1259690162029 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
