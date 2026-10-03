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

/-! # V42: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_505 :
    ((4409976854913976428969 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5800290439484741597991 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7444844558462607 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3199809025526181901943 / 10000000000000000000000 : ℝ))) -
              6 * (1004021175411097253659 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (35472454719789 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (35472454719789 / 64000000000000 : ℝ)) =
      Real.log (99472454719789 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((35472454719789 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (35832454719789 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4409976854913976428969 / 10000000000000000000000 : ℝ) ≤
      Real.log (99472454719789 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (35832454719789 / 64000000000000 : ℝ) ≤
      (-(5800290439484741597991 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (35832454719789 / 64000000000000 : ℝ) = (35832454719789 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (35832454719789 / 32000000000000 : ℝ) ≤
            (1131181363515258402009 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7444844558462607 / 10000000000000000 : ℝ) ≤
      Real.sqrt (35472454719789 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (35472454719789 / 64000000000000 : ℝ) ≤ (744484455846261 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (35472454719789 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau782 :
    Real.arctan (3722422279231305 / 11233492409951068 : ℝ) ≤
      (3199809025526181901943 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau781 :
    Real.arctan (744484455846261 / 1000000000000000 : ℝ) ≤
      (2 * (3199809025526181901943 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1558373102487767 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (744484455846261 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (744484455846261 / 1000000000000000 : ℝ) /
                (1 + (1558373102487767 / 1250000000000000 : ℝ)) =
              (3722422279231305 / 11233492409951068 : ℝ)
            by
        norm_num];
        exact hau782)
  have hat1 :
    (Real.pi / 2 - (2 * (3199809025526181901943 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 744484455846261 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 744484455846261 : ℝ) =
              (744484455846261 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau781)
  have hz1 :
    (1000000000000000 / 744484455846261 : ℝ) ≤
      1 / Real.sqrt (35472454719789 / 64000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 744484455846261 : ℝ) = 1 / (744484455846261 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2481614852820869 : ℝ) ≤
      (1004021175411097253659 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (35472454719789 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2481614852820869 : ℝ) := by
    rw [show
        (250000000000000 / 2481614852820869 : ℝ) =
          (3 / 40) / (7444844558462607 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3199809025526181901943 / 10000000000000000000000 : ℝ))) -
        6 * (1004021175411097253659 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (35472454719789 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (35472454719789 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7444844558462607 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3199809025526181901943 / 10000000000000000000000 : ℝ))) -
          6 * (1004021175411097253659 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (35472454719789 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (35472454719789 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (35472454719789 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_506 :
    ((883600937481077002919 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5778020694737567426223 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((931652880577461 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3202503278670062354709 / 10000000000000000000000 : ℝ))) -
              6 * (250725017368404689187 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1111010675057 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1111010675057 / 2000000000000 : ℝ)) =
      Real.log (3111010675057 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1111010675057 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1122260675057 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (883600937481077002919 / 2000000000000000000000 : ℝ) ≤
      Real.log (3111010675057 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1122260675057 / 2000000000000 : ℝ) ≤
      (-(5778020694737567426223 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (1122260675057 / 2000000000000 : ℝ) = (1122260675057 / 1000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1122260675057 / 1000000000000 : ℝ) ≤
            (1153451108262432573777 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (931652880577461 / 1250000000000000 : ℝ) ≤ Real.sqrt (1111010675057 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1111010675057 / 2000000000000 : ℝ) ≤ (7453223044619691 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1111010675057 / 2000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau784 :
    Real.arctan (2484407681539897 / 7490663322545827 : ℝ) ≤
      (3202503278670062354709 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau783 :
    Real.arctan (7453223044619691 / 10000000000000000 : ℝ) ≤
      (2 * (3202503278670062354709 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12471989967637481 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7453223044619691 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7453223044619691 / 10000000000000000 : ℝ) /
                (1 + (12471989967637481 / 10000000000000000 : ℝ)) =
              (2484407681539897 / 7490663322545827 : ℝ)
            by
        norm_num];
        exact hau784)
  have hat1 :
    (Real.pi / 2 - (2 * (3202503278670062354709 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7453223044619691 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7453223044619691 : ℝ) =
              (7453223044619691 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau783)
  have hz1 :
    (10000000000000000 / 7453223044619691 : ℝ) ≤
      1 / Real.sqrt (1111010675057 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7453223044619691 : ℝ) =
          1 / (7453223044619691 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 310550960192487 : ℝ) ≤
      (250725017368404689187 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1111010675057 / 2000000000000 : ℝ) ≤
      (31250000000000 / 310550960192487 : ℝ) := by
    rw [show
        (31250000000000 / 310550960192487 : ℝ) =
          (3 / 40) / (931652880577461 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3202503278670062354709 / 10000000000000000000000 : ℝ))) -
        6 * (250725017368404689187 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1111010675057 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1111010675057 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((931652880577461 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3202503278670062354709 / 10000000000000000000000 : ℝ))) -
          6 * (250725017368404689187 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1111010675057 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1111010675057 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1111010675057 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_507 :
    ((885205216091294371751 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(719475054245545283031 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((74615921227329 / 100000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3205192347747627695933 / 10000000000000000000000 : ℝ))) -
              6 * (500891355368140157209 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (35632228483859 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (35632228483859 / 64000000000000 : ℝ)) =
      Real.log (99632228483859 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((35632228483859 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (35992228483859 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (885205216091294371751 / 2000000000000000000000 : ℝ) ≤
      Real.log (99632228483859 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (35992228483859 / 64000000000000 : ℝ) ≤
      (-(719475054245545283031 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (35992228483859 / 64000000000000 : ℝ) = (35992228483859 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (35992228483859 / 32000000000000 : ℝ) ≤
            (146958921129454716969 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (74615921227329 / 100000000000000 : ℝ) ≤ Real.sqrt (35632228483859 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (35632228483859 / 64000000000000 : ℝ) ≤
      (7461592122732903 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (35632228483859 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau786 :
    Real.arctan (7461592122732903 / 22476993107557192 : ℝ) ≤
      (3205192347747627695933 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau785 :
    Real.arctan (7461592122732903 / 10000000000000000 : ℝ) ≤
      (2 * (3205192347747627695933 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1559624138444649 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (7461592122732903 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7461592122732903 / 10000000000000000 : ℝ) /
                (1 + (1559624138444649 / 1250000000000000 : ℝ)) =
              (7461592122732903 / 22476993107557192 : ℝ)
            by
        norm_num];
        exact hau786)
  have hat1 :
    (Real.pi / 2 - (2 * (3205192347747627695933 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7461592122732903 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7461592122732903 : ℝ) =
              (7461592122732903 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau785)
  have hz1 :
    (10000000000000000 / 7461592122732903 : ℝ) ≤
      1 / Real.sqrt (35632228483859 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7461592122732903 : ℝ) =
          1 / (7461592122732903 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (2500000000000 / 24871973742443 : ℝ) ≤
      (500891355368140157209 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (35632228483859 / 64000000000000 : ℝ) ≤
      (2500000000000 / 24871973742443 : ℝ) := by
    rw [show
        (2500000000000 / 24871973742443 : ℝ) = (3 / 40) / (74615921227329 / 100000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3205192347747627695933 / 10000000000000000000000 : ℝ))) -
        6 * (500891355368140157209 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (35632228483859 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (35632228483859 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((74615921227329 / 100000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3205192347747627695933 / 10000000000000000000000 : ℝ))) -
          6 * (500891355368140157209 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (35632228483859 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (35632228483859 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (35632228483859 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_508 :
    ((2217020522194807226801 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5733629437743145774003 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((933743978052949 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1603938125610509220697 / 5000000000000000000000 : ℝ))) -
              6 * (125083634796351411801 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (17856057682947 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17856057682947 / 32000000000000 : ℝ)) =
      Real.log (49856057682947 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17856057682947 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18036057682947 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2217020522194807226801 / 5000000000000000000000 : ℝ) ≤
      Real.log (49856057682947 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18036057682947 / 32000000000000 : ℝ) ≤
      (-(5733629437743145774003 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18036057682947 / 32000000000000 : ℝ) = (18036057682947 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18036057682947 / 16000000000000 : ℝ) ≤
            (1197842365256854225997 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (933743978052949 / 1250000000000000 : ℝ) ≤ Real.sqrt (17856057682947 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17856057682947 / 32000000000000 : ℝ) ≤ (1493990364884719 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17856057682947 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau788 :
    Real.arctan (7469951824423595 / 22481994242075637 : ℝ) ≤
      (1603938125610509220697 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau787 :
    Real.arctan (1493990364884719 / 2000000000000000 : ℝ) ≤
      (2 * (1603938125610509220697 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12481994242075637 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1493990364884719 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1493990364884719 / 2000000000000000 : ℝ) /
                (1 + (12481994242075637 / 10000000000000000 : ℝ)) =
              (7469951824423595 / 22481994242075637 : ℝ)
            by
        norm_num];
        exact hau788)
  have hat1 :
    (Real.pi / 2 - (2 * (1603938125610509220697 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1493990364884719 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1493990364884719 : ℝ) =
              (1493990364884719 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau787)
  have hz1 :
    (2000000000000000 / 1493990364884719 : ℝ) ≤
      1 / Real.sqrt (17856057682947 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1493990364884719 : ℝ) = 1 / (1493990364884719 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 933743978052949 : ℝ) ≤
      (125083634796351411801 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17856057682947 / 32000000000000 : ℝ) ≤
      (93750000000000 / 933743978052949 : ℝ) := by
    rw [show
        (93750000000000 / 933743978052949 : ℝ) =
          (3 / 40) / (933743978052949 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1603938125610509220697 / 5000000000000000000000 : ℝ))) -
        6 * (125083634796351411801 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17856057682947 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17856057682947 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((933743978052949 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1603938125610509220697 / 5000000000000000000000 : ℝ))) -
          6 * (125083634796351411801 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (17856057682947 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17856057682947 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17856057682947 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_509 :
    ((111051239737559752989 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5711507488108152006311 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7478302181136373 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (128422200298052838079 / 400000000000000000000 : ℝ))) -
              6 * (999559151710662100997 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (35792002247929 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (35792002247929 / 64000000000000 : ℝ)) =
      Real.log (99792002247929 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((35792002247929 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (36152002247929 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (111051239737559752989 / 250000000000000000000 : ℝ) ≤
      Real.log (99792002247929 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (36152002247929 / 64000000000000 : ℝ) ≤
      (-(5711507488108152006311 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36152002247929 / 64000000000000 : ℝ) = (36152002247929 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36152002247929 / 32000000000000 : ℝ) ≤
            (1219964314891847993689 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7478302181136373 / 10000000000000000 : ℝ) ≤
      Real.sqrt (35792002247929 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (35792002247929 / 64000000000000 : ℝ) ≤ (934787772642047 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (35792002247929 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau790 :
    Real.arctan (934787772642047 / 2810874171700294 : ℝ) ≤
      (128422200298052838079 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau789 :
    Real.arctan (934787772642047 / 1250000000000000 : ℝ) ≤
      (2 * (128422200298052838079 / 400000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (780437085850147 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (934787772642047 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (934787772642047 / 1250000000000000 : ℝ) /
                (1 + (780437085850147 / 625000000000000 : ℝ)) =
              (934787772642047 / 2810874171700294 : ℝ)
            by
        norm_num];
        exact hau790)
  have hat1 :
    (Real.pi / 2 - (2 * (128422200298052838079 / 400000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 934787772642047 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 934787772642047 : ℝ) =
              (934787772642047 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau789)
  have hz1 :
    (1250000000000000 / 934787772642047 : ℝ) ≤
      1 / Real.sqrt (35792002247929 / 64000000000000 : ℝ) := by
    rw [show
        (1250000000000000 / 934787772642047 : ℝ) = 1 / (934787772642047 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7478302181136373 : ℝ) ≤
      (999559151710662100997 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (35792002247929 / 64000000000000 : ℝ) ≤
      (750000000000000 / 7478302181136373 : ℝ) := by
    rw [show
        (750000000000000 / 7478302181136373 : ℝ) =
          (3 / 40) / (7478302181136373 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (128422200298052838079 / 400000000000000000000 : ℝ))) -
        6 * (999559151710662100997 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (35792002247929 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (35792002247929 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7478302181136373 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (128422200298052838079 / 400000000000000000000 : ℝ))) -
          6 * (999559151710662100997 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (35792002247929 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (35792002247929 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (35792002247929 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_510 :
    ((4450051726067655387087 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5689434368536972102147 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7486643224140491 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (803307158674833361741 / 2500000000000000000000 : ℝ))) -
              6 * (499226455124696702811 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (8967972282491 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8967972282491 / 16000000000000 : ℝ)) =
      Real.log (24967972282491 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8967972282491 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9057972282491 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4450051726067655387087 / 10000000000000000000000 : ℝ) ≤
      Real.log (24967972282491 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9057972282491 / 16000000000000 : ℝ) ≤
      (-(5689434368536972102147 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9057972282491 / 16000000000000 : ℝ) = (9057972282491 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9057972282491 / 8000000000000 : ℝ) ≤
            (1242037434463027897853 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7486643224140491 / 10000000000000000 : ℝ) ≤ Real.sqrt (8967972282491 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8967972282491 / 16000000000000 : ℝ) ≤ (3743321612070247 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8967972282491 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau792 :
    Real.arctan (3743321612070247 / 11245995252271025 : ℝ) ≤
      (803307158674833361741 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau791 :
    Real.arctan (3743321612070247 / 5000000000000000 : ℝ) ≤
      (2 * (803307158674833361741 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (249839810090841 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (3743321612070247 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3743321612070247 / 5000000000000000 : ℝ) /
                (1 + (249839810090841 / 200000000000000 : ℝ)) =
              (3743321612070247 / 11245995252271025 : ℝ)
            by
        norm_num];
        exact hau792)
  have hat1 :
    (Real.pi / 2 - (2 * (803307158674833361741 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3743321612070247 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3743321612070247 : ℝ) =
              (3743321612070247 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau791)
  have hz1 :
    (5000000000000000 / 3743321612070247 : ℝ) ≤
      1 / Real.sqrt (8967972282491 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3743321612070247 : ℝ) = 1 / (3743321612070247 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7486643224140491 : ℝ) ≤
      (499226455124696702811 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8967972282491 / 16000000000000 : ℝ) ≤
      (750000000000000 / 7486643224140491 : ℝ) := by
    rw [show
        (750000000000000 / 7486643224140491 : ℝ) =
          (3 / 40) / (7486643224140491 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (803307158674833361741 / 2500000000000000000000 : ℝ))) -
        6 * (499226455124696702811 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8967972282491 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8967972282491 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7486643224140491 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (803307158674833361741 / 2500000000000000000000 : ℝ))) -
          6 * (499226455124696702811 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (8967972282491 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8967972282491 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8967972282491 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_511 :
    ((2229023732166812530537 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5667409863937838582023 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7494974984531197 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (100496785972697601687 / 312500000000000000000 : ℝ))) -
              6 * (997350333639085100309 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (35951776011999 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (35951776011999 / 64000000000000 : ℝ)) =
      Real.log (99951776011999 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((35951776011999 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (36311776011999 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2229023732166812530537 / 5000000000000000000000 : ℝ) ≤
      Real.log (99951776011999 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (36311776011999 / 64000000000000 : ℝ) ≤
      (-(5667409863937838582023 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36311776011999 / 64000000000000 : ℝ) = (36311776011999 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36311776011999 / 32000000000000 : ℝ) ≤
            (1264061939062161417977 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7494974984531197 / 10000000000000000 : ℝ) ≤
      Real.sqrt (35951776011999 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (35951776011999 / 64000000000000 : ℝ) ≤ (1171089841333 / 1562500000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (35951776011999 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau794 :
    Real.arctan (1873743746132800 / 5624246409323659 : ℝ) ≤
      (100496785972697601687 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau793 :
    Real.arctan (1171089841333 / 1562500000000 : ℝ) ≤
      (2 * (100496785972697601687 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3124246409323659 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1171089841333 / 1562500000000 : ℝ) ^ 2))
      (by
        rw [show
            (1171089841333 / 1562500000000 : ℝ) /
                (1 + (3124246409323659 / 2500000000000000 : ℝ)) =
              (1873743746132800 / 5624246409323659 : ℝ)
            by
        norm_num];
        exact hau794)
  have hat1 :
    (Real.pi / 2 - (2 * (100496785972697601687 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (1562500000000 / 1171089841333 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1562500000000 / 1171089841333 : ℝ) = (1171089841333 / 1562500000000 : ℝ) by
            norm_num];
        exact hau793)
  have hz1 :
    (1562500000000 / 1171089841333 : ℝ) ≤ 1 / Real.sqrt (35951776011999 / 64000000000000 : ℝ) := by
    rw [show (1562500000000 / 1171089841333 : ℝ) = 1 / (1171089841333 / 1562500000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7494974984531197 : ℝ) ≤
      (997350333639085100309 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (35951776011999 / 64000000000000 : ℝ) ≤
      (750000000000000 / 7494974984531197 : ℝ) := by
    rw [show
        (750000000000000 / 7494974984531197 : ℝ) =
          (3 / 40) / (7494974984531197 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (100496785972697601687 / 312500000000000000000 : ℝ))) -
        6 * (997350333639085100309 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (35951776011999 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (35951776011999 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7494974984531197 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (100496785972697601687 / 312500000000000000000 : ℝ))) -
          6 * (997350333639085100309 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (35951776011999 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (35951776011999 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (35951776011999 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_512 :
    ((4466036814523950969417 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5645433760637049356529 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((75032974932311 / 100000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (643712114958955676583 / 2000000000000000000000 : ℝ))) -
              6 * (498125700844381961051 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (18015831447017 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18015831447017 / 32000000000000 : ℝ)) =
      Real.log (50015831447017 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18015831447017 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18195831447017 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4466036814523950969417 / 10000000000000000000000 : ℝ) ≤
      Real.log (50015831447017 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18195831447017 / 32000000000000 : ℝ) ≤
      (-(5645433760637049356529 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18195831447017 / 32000000000000 : ℝ) = (18195831447017 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18195831447017 / 16000000000000 : ℝ) ≤
            (1286038042362950643471 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (75032974932311 / 100000000000000 : ℝ) ≤ Real.sqrt (18015831447017 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18015831447017 / 32000000000000 : ℝ) ≤
      (7503297493231103 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18015831447017 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau796 :
    Real.arctan (7503297493231103 / 22501978774255223 : ℝ) ≤
      (643712114958955676583 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau795 :
    Real.arctan (7503297493231103 / 10000000000000000 : ℝ) ≤
      (2 * (643712114958955676583 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12501978774255223 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7503297493231103 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7503297493231103 / 10000000000000000 : ℝ) /
                (1 + (12501978774255223 / 10000000000000000 : ℝ)) =
              (7503297493231103 / 22501978774255223 : ℝ)
            by
        norm_num];
        exact hau796)
  have hat1 :
    (Real.pi / 2 - (2 * (643712114958955676583 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7503297493231103 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7503297493231103 : ℝ) =
              (7503297493231103 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau795)
  have hz1 :
    (10000000000000000 / 7503297493231103 : ℝ) ≤
      1 / Real.sqrt (18015831447017 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7503297493231103 : ℝ) =
          1 / (7503297493231103 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (7500000000000 / 75032974932311 : ℝ) ≤
      (498125700844381961051 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18015831447017 / 32000000000000 : ℝ) ≤
      (7500000000000 / 75032974932311 : ℝ) := by
    rw [show
        (7500000000000 / 75032974932311 : ℝ) = (3 / 40) / (75032974932311 / 100000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (643712114958955676583 / 2000000000000000000000 : ℝ))) -
        6 * (498125700844381961051 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18015831447017 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18015831447017 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((75032974932311 / 100000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (643712114958955676583 / 2000000000000000000000 : ℝ))) -
          6 * (498125700844381961051 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (18015831447017 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18015831447017 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18015831447017 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_513 :
    ((4474019786837800397257 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1124701169273305923953 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((469475673811969 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (161060946183457558827 / 500000000000000000000 : ℝ))) -
              6 * (124394511795356336081 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (36111549776069 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (36111549776069 / 64000000000000 : ℝ)) =
      Real.log (100111549776069 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((36111549776069 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (36471549776069 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4474019786837800397257 / 10000000000000000000000 : ℝ) ≤
      Real.log (100111549776069 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (36471549776069 / 64000000000000 : ℝ) ≤
      (-(1124701169273305923953 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36471549776069 / 64000000000000 : ℝ) = (36471549776069 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36471549776069 / 32000000000000 : ℝ) ≤
            (261593191326694076047 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (469475673811969 / 625000000000000 : ℝ) ≤ Real.sqrt (36111549776069 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (36111549776069 / 64000000000000 : ℝ) ≤
      (7511610780991507 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (36111549776069 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau798 :
    Real.arctan (7511610780991507 / 22506969917814139 : ℝ) ≤
      (161060946183457558827 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau797 :
    Real.arctan (7511610780991507 / 10000000000000000 : ℝ) ≤
      (2 * (161060946183457558827 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12506969917814139 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7511610780991507 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7511610780991507 / 10000000000000000 : ℝ) /
                (1 + (12506969917814139 / 10000000000000000 : ℝ)) =
              (7511610780991507 / 22506969917814139 : ℝ)
            by
        norm_num];
        exact hau798)
  have hat1 :
    (Real.pi / 2 - (2 * (161060946183457558827 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7511610780991507 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7511610780991507 : ℝ) =
              (7511610780991507 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau797)
  have hz1 :
    (10000000000000000 / 7511610780991507 : ℝ) ≤
      1 / Real.sqrt (36111549776069 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7511610780991507 : ℝ) =
          1 / (7511610780991507 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 469475673811969 : ℝ) ≤
      (124394511795356336081 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (36111549776069 / 64000000000000 : ℝ) ≤
      (46875000000000 / 469475673811969 : ℝ) := by
    rw [show
        (46875000000000 / 469475673811969 : ℝ) =
          (3 / 40) / (469475673811969 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (161060946183457558827 / 500000000000000000000 : ℝ))) -
        6 * (124394511795356336081 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (36111549776069 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (36111549776069 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((469475673811969 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (161060946183457558827 / 500000000000000000000 : ℝ))) -
          6 * (124394511795356336081 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (36111549776069 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (36111549776069 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (36111549776069 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_514 :
    ((2240998195724967104201 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5601625910251529815539 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((939989359799217 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3223872215616594728717 / 10000000000000000000000 : ℝ))) -
              6 * (497032195889812852133 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (4523929582263 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4523929582263 / 8000000000000 : ℝ)) =
      Real.log (12523929582263 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4523929582263 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4568929582263 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2240998195724967104201 / 5000000000000000000000 : ℝ) ≤
      Real.log (12523929582263 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4568929582263 / 8000000000000 : ℝ) ≤
      (-(5601625910251529815539 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4568929582263 / 8000000000000 : ℝ) = (4568929582263 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4568929582263 / 4000000000000 : ℝ) ≤
            (1329845892748470184461 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (939989359799217 / 1250000000000000 : ℝ) ≤ Real.sqrt (4523929582263 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4523929582263 / 8000000000000 : ℝ) ≤ (7519914878393739 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4523929582263 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau800 :
    Real.arctan (2506638292797913 / 7503986356785649 : ℝ) ≤
      (3223872215616594728717 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau799 :
    Real.arctan (7519914878393739 / 10000000000000000 : ℝ) ≤
      (2 * (3223872215616594728717 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12511959070356947 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7519914878393739 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7519914878393739 / 10000000000000000 : ℝ) /
                (1 + (12511959070356947 / 10000000000000000 : ℝ)) =
              (2506638292797913 / 7503986356785649 : ℝ)
            by
        norm_num];
        exact hau800)
  have hat1 :
    (Real.pi / 2 - (2 * (3223872215616594728717 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7519914878393739 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7519914878393739 : ℝ) =
              (7519914878393739 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau799)
  have hz1 :
    (10000000000000000 / 7519914878393739 : ℝ) ≤
      1 / Real.sqrt (4523929582263 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7519914878393739 : ℝ) =
          1 / (7519914878393739 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 313329786599739 : ℝ) ≤
      (497032195889812852133 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4523929582263 / 8000000000000 : ℝ) ≤
      (31250000000000 / 313329786599739 : ℝ) := by
    rw [show
        (31250000000000 / 313329786599739 : ℝ) =
          (3 / 40) / (939989359799217 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3223872215616594728717 / 10000000000000000000000 : ℝ))) -
        6 * (497032195889812852133 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4523929582263 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4523929582263 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((939989359799217 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3223872215616594728717 / 10000000000000000000000 : ℝ))) -
          6 * (497032195889812852133 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (4523929582263 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4523929582263 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4523929582263 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_515 :
    ((2248965269073266439973 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5558009135882844102449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7536495623606959 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3229163699717176018831 / 10000000000000000000000 : ℝ))) -
              6 * (30996616314830743811 / 312500000000000000000 : ℝ)))) ≤
      Vfield (18175605211087 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18175605211087 / 32000000000000 : ℝ)) =
      Real.log (50175605211087 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18175605211087 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18355605211087 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2248965269073266439973 / 5000000000000000000000 : ℝ) ≤
      Real.log (50175605211087 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18355605211087 / 32000000000000 : ℝ) ≤
      (-(5558009135882844102449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18355605211087 / 32000000000000 : ℝ) = (18355605211087 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18355605211087 / 16000000000000 : ℝ) ≤
            (1373462667117155897551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7536495623606959 / 10000000000000000 : ℝ) ≤
      Real.sqrt (18175605211087 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18175605211087 / 32000000000000 : ℝ) ≤ (3768247811803481 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18175605211087 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau802 :
    Real.arctan (7536495623606962 / 22521931411912735 : ℝ) ≤
      (3229163699717176018831 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau801 :
    Real.arctan (3768247811803481 / 5000000000000000 : ℝ) ≤
      (2 * (3229163699717176018831 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2504386282382547 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3768247811803481 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3768247811803481 / 5000000000000000 : ℝ) /
                (1 + (2504386282382547 / 2000000000000000 : ℝ)) =
              (7536495623606962 / 22521931411912735 : ℝ)
            by
        norm_num];
        exact hau802)
  have hat1 :
    (Real.pi / 2 - (2 * (3229163699717176018831 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3768247811803481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3768247811803481 : ℝ) =
              (3768247811803481 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau801)
  have hz1 :
    (5000000000000000 / 3768247811803481 : ℝ) ≤
      1 / Real.sqrt (18175605211087 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3768247811803481 : ℝ) = 1 / (3768247811803481 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7536495623606959 : ℝ) ≤
      (30996616314830743811 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18175605211087 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7536495623606959 : ℝ) := by
    rw [show
        (750000000000000 / 7536495623606959 : ℝ) =
          (3 / 40) / (7536495623606959 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3229163699717176018831 / 10000000000000000000000 : ℝ))) -
        6 * (30996616314830743811 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18175605211087 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18175605211087 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7536495623606959 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3229163699717176018831 / 10000000000000000000000 : ℝ))) -
          6 * (30996616314830743811 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (18175605211087 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18175605211087 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18175605211087 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_516 :
    ((4513839335526654517601 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5514581777940426081753 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7553039970171363 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1617217584057645801541 / 5000000000000000000000 : ℝ))) -
              6 * (989733236539927218279 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9127746046561 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9127746046561 / 16000000000000 : ℝ)) =
      Real.log (25127746046561 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9127746046561 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9217746046561 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4513839335526654517601 / 10000000000000000000000 : ℝ) ≤
      Real.log (25127746046561 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9217746046561 / 16000000000000 : ℝ) ≤
      (-(5514581777940426081753 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (9217746046561 / 16000000000000 : ℝ) = (9217746046561 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9217746046561 / 8000000000000 : ℝ) ≤
            (1416890025059573918247 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7553039970171363 / 10000000000000000 : ℝ) ≤ Real.sqrt (9127746046561 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9127746046561 / 16000000000000 : ℝ) ≤ (3776519985085683 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9127746046561 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau804 :
    Real.arctan (3776519985085683 / 11265947908956119 : ℝ) ≤
      (1617217584057645801541 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau803 :
    Real.arctan (3776519985085683 / 5000000000000000 : ℝ) ≤
      (2 * (1617217584057645801541 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6265947908956119 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3776519985085683 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3776519985085683 / 5000000000000000 : ℝ) /
                (1 + (6265947908956119 / 5000000000000000 : ℝ)) =
              (3776519985085683 / 11265947908956119 : ℝ)
            by
        norm_num];
        exact hau804)
  have hat1 :
    (Real.pi / 2 - (2 * (1617217584057645801541 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3776519985085683 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3776519985085683 : ℝ) =
              (3776519985085683 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau803)
  have hz1 :
    (5000000000000000 / 3776519985085683 : ℝ) ≤
      1 / Real.sqrt (9127746046561 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3776519985085683 : ℝ) = 1 / (3776519985085683 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2517679990057121 : ℝ) ≤
      (989733236539927218279 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9127746046561 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2517679990057121 : ℝ) := by
    rw [show
        (250000000000000 / 2517679990057121 : ℝ) =
          (3 / 40) / (7553039970171363 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1617217584057645801541 / 5000000000000000000000 : ℝ))) -
        6 * (989733236539927218279 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9127746046561 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9127746046561 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7553039970171363 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1617217584057645801541 / 5000000000000000000000 : ℝ))) -
          6 * (989733236539927218279 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (9127746046561 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9127746046561 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9127746046561 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
