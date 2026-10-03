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

/-! # V34: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_409 :
    ((1809669122496870992029 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(408529462049720624371 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1320763270114671 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2918193984890556559269 / 10000000000000000000000 : ℝ))) -
              6 * (1130861477778600441087 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (436103903921 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (436103903921 / 1000000000000 : ℝ)) =
      Real.log (1436103903921 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((436103903921 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (441728903921 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1809669122496870992029 / 5000000000000000000000 : ℝ) ≤
      Real.log (1436103903921 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (441728903921 / 1000000000000 : ℝ) ≤
      (-(408529462049720624371 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (441728903921 / 1000000000000 : ℝ) = (441728903921 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (441728903921 / 250000000000 : ℝ) ≤
            (284617718250279375629 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1320763270114671 / 2000000000000000 : ℝ) ≤ Real.sqrt (436103903921 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (436103903921 / 1000000000000 : ℝ) ≤ (3301908175286679 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (436103903921 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau590 :
    Real.arctan (6603816350573358 / 21983755270869811 : ℝ) ≤
      (2918193984890556559269 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau589 :
    Real.arctan (3301908175286679 / 5000000000000000 : ℝ) ≤
      (2 * (2918193984890556559269 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11983755270869811 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3301908175286679 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3301908175286679 / 5000000000000000 : ℝ) /
                (1 + (11983755270869811 / 10000000000000000 : ℝ)) =
              (6603816350573358 / 21983755270869811 : ℝ)
            by
        norm_num];
        exact hau590)
  have hat1 :
    (Real.pi / 2 - (2 * (2918193984890556559269 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3301908175286679 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3301908175286679 : ℝ) =
              (3301908175286679 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau589)
  have hz1 :
    (5000000000000000 / 3301908175286679 : ℝ) ≤
      1 / Real.sqrt (436103903921 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3301908175286679 : ℝ) = 1 / (3301908175286679 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 440254423371557 : ℝ) ≤
      (1130861477778600441087 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (436103903921 / 1000000000000 : ℝ) ≤
      (50000000000000 / 440254423371557 : ℝ) := by
    rw [show
        (50000000000000 / 440254423371557 : ℝ) =
          (3 / 40) / (1320763270114671 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2918193984890556559269 / 10000000000000000000000 : ℝ))) -
        6 * (1130861477778600441087 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (436103903921 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (436103903921 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1320763270114671 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2918193984890556559269 / 10000000000000000000000 : ℝ))) -
          6 * (1130861477778600441087 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (436103903921 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (436103903921 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (436103903921 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_410 :
    ((28420032908242764527 / 78125000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8110808437737774119867 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((103497492949001 / 156250000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1462579464314678080479 / 5000000000000000000000 : ℝ))) -
              6 * (563735968840652122499 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (219376251837 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (219376251837 / 500000000000 : ℝ)) =
      Real.log (719376251837 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((219376251837 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (222188751837 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (28420032908242764527 / 78125000000000000000 : ℝ) ≤
      Real.log (719376251837 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (222188751837 / 500000000000 : ℝ) ≤
      (-(8110808437737774119867 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (222188751837 / 500000000000 : ℝ) = (222188751837 / 125000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (222188751837 / 125000000000 : ℝ) ≤
            (5752135168262225880133 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (103497492949001 / 156250000000000 : ℝ) ≤ Real.sqrt (219376251837 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (219376251837 / 500000000000 : ℝ) ≤ (6623839548736067 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (219376251837 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau592 :
    Real.arctan (6623839548736067 / 21994800972396332 : ℝ) ≤
      (1462579464314678080479 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau591 :
    Real.arctan (6623839548736067 / 10000000000000000 : ℝ) ≤
      (2 * (1462579464314678080479 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2998700243099083 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (6623839548736067 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6623839548736067 / 10000000000000000 : ℝ) /
                (1 + (2998700243099083 / 2500000000000000 : ℝ)) =
              (6623839548736067 / 21994800972396332 : ℝ)
            by
        norm_num];
        exact hau592)
  have hat1 :
    (Real.pi / 2 - (2 * (1462579464314678080479 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6623839548736067 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6623839548736067 : ℝ) =
              (6623839548736067 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau591)
  have hz1 :
    (10000000000000000 / 6623839548736067 : ℝ) ≤
      1 / Real.sqrt (219376251837 / 500000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6623839548736067 : ℝ) =
          1 / (6623839548736067 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (11718750000000 / 103497492949001 : ℝ) ≤
      (563735968840652122499 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (219376251837 / 500000000000 : ℝ) ≤
      (11718750000000 / 103497492949001 : ℝ) := by
    rw [show
        (11718750000000 / 103497492949001 : ℝ) =
          (3 / 40) / (103497492949001 / 156250000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1462579464314678080479 / 5000000000000000000000 : ℝ))) -
        6 * (563735968840652122499 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (219376251837 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (219376251837 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((103497492949001 / 156250000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1462579464314678080479 / 5000000000000000000000 : ℝ))) -
          6 * (563735968840652122499 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (219376251837 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (219376251837 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (219376251837 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_411 :
    ((91174111991140909019 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8081051519608223970771 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6633828483993989 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (292862872001000197323 / 1000000000000000000000 : ℝ))) -
              6 * (1125788557400433642409 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (880153607101 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (880153607101 / 2000000000000 : ℝ)) =
      Real.log (2880153607101 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((880153607101 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (891403607101 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (91174111991140909019 / 250000000000000000000 : ℝ) ≤
      Real.log (2880153607101 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (891403607101 / 2000000000000 : ℝ) ≤
      (-(8081051519608223970771 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (891403607101 / 2000000000000 : ℝ) = (891403607101 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (891403607101 / 500000000000 : ℝ) ≤
            (5781892086391776029229 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6633828483993989 / 10000000000000000 : ℝ) ≤ Real.sqrt (880153607101 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (880153607101 / 2000000000000 : ℝ) ≤ (829228560499249 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (880153607101 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau594 :
    Real.arctan (3316914241996996 / 11000160005263401 : ℝ) ≤
      (292862872001000197323 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau593 :
    Real.arctan (829228560499249 / 1250000000000000 : ℝ) ≤
      (2 * (292862872001000197323 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6000160005263401 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (829228560499249 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (829228560499249 / 1250000000000000 : ℝ) /
                (1 + (6000160005263401 / 5000000000000000 : ℝ)) =
              (3316914241996996 / 11000160005263401 : ℝ)
            by
        norm_num];
        exact hau594)
  have hat1 :
    (Real.pi / 2 - (2 * (292862872001000197323 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 829228560499249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 829228560499249 : ℝ) =
              (829228560499249 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau593)
  have hz1 :
    (1250000000000000 / 829228560499249 : ℝ) ≤ 1 / Real.sqrt (880153607101 / 2000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 829228560499249 : ℝ) = 1 / (829228560499249 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6633828483993989 : ℝ) ≤
      (1125788557400433642409 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (880153607101 / 2000000000000 : ℝ) ≤
      (750000000000000 / 6633828483993989 : ℝ) := by
    rw [show
        (750000000000000 / 6633828483993989 : ℝ) =
          (3 / 40) / (6633828483993989 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (292862872001000197323 / 1000000000000000000000 : ℝ))) -
        6 * (1125788557400433642409 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (880153607101 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (880153607101 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6633828483993989 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (292862872001000197323 / 1000000000000000000000 : ℝ))) -
          6 * (1125788557400433642409 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (880153607101 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (880153607101 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (880153607101 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_412 :
    ((3656156290323998442747 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(503211430390812632561 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6643802400937281 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (586418022000673760631 / 2000000000000000000000 : ℝ))) -
              6 * (224822538986222456981 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (441401103427 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (441401103427 / 1000000000000 : ℝ)) =
      Real.log (1441401103427 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((441401103427 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (447026103427 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3656156290323998442747 / 10000000000000000000000 : ℝ) ≤
      Real.log (1441401103427 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (447026103427 / 1000000000000 : ℝ) ≤
      (-(503211430390812632561 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (447026103427 / 1000000000000 : ℝ) = (447026103427 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (447026103427 / 250000000000 : ℝ) ≤
            (363222544984187367439 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6643802400937281 / 10000000000000000 : ℝ) ≤ Real.sqrt (441401103427 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (441401103427 / 1000000000000 : ℝ) ≤ (1660950600234321 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (441401103427 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau596 :
    Real.arctan (3321901200468642 / 11002918255788179 : ℝ) ≤
      (586418022000673760631 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau595 :
    Real.arctan (1660950600234321 / 2500000000000000 : ℝ) ≤
      (2 * (586418022000673760631 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6002918255788179 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1660950600234321 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1660950600234321 / 2500000000000000 : ℝ) /
                (1 + (6002918255788179 / 5000000000000000 : ℝ)) =
              (3321901200468642 / 11002918255788179 : ℝ)
            by
        norm_num];
        exact hau596)
  have hat1 :
    (Real.pi / 2 - (2 * (586418022000673760631 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1660950600234321 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1660950600234321 : ℝ) =
              (1660950600234321 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau595)
  have hz1 :
    (2500000000000000 / 1660950600234321 : ℝ) ≤
      1 / Real.sqrt (441401103427 / 1000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1660950600234321 : ℝ) = 1 / (1660950600234321 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2214600800312427 : ℝ) ≤
      (224822538986222456981 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (441401103427 / 1000000000000 : ℝ) ≤
      (250000000000000 / 2214600800312427 : ℝ) := by
    rw [show
        (250000000000000 / 2214600800312427 : ℝ) =
          (3 / 40) / (6643802400937281 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (586418022000673760631 / 2000000000000000000000 : ℝ))) -
        6 * (224822538986222456981 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (441401103427 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (441401103427 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6643802400937281 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (586418022000673760631 / 2000000000000000000000 : ℝ))) -
          6 * (224822538986222456981 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (441401103427 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (441401103427 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (441401103427 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_413 :
    ((733067931964476973299 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8021802015363241262467 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6653761367102819 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2935543137456839238447 / 10000000000000000000000 : ℝ))) -
              6 * (1122444294482276282733 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (885450806607 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (885450806607 / 2000000000000 : ℝ)) =
      Real.log (2885450806607 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((885450806607 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (896700806607 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (733067931964476973299 / 2000000000000000000000 : ℝ) ≤
      Real.log (2885450806607 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (896700806607 / 2000000000000 : ℝ) ≤
      (-(8021802015363241262467 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (896700806607 / 2000000000000 : ℝ) = (896700806607 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (896700806607 / 500000000000 : ℝ) ≤
            (5841141590636758737533 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6653761367102819 / 10000000000000000 : ℝ) ≤ Real.sqrt (885450806607 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (885450806607 / 2000000000000 : ℝ) ≤ (3326880683551411 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (885450806607 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau598 :
    Real.arctan (6653761367102822 / 22011350479040647 : ℝ) ≤
      (2935543137456839238447 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau597 :
    Real.arctan (3326880683551411 / 5000000000000000 : ℝ) ≤
      (2 * (2935543137456839238447 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12011350479040647 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3326880683551411 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3326880683551411 / 5000000000000000 : ℝ) /
                (1 + (12011350479040647 / 10000000000000000 : ℝ)) =
              (6653761367102822 / 22011350479040647 : ℝ)
            by
        norm_num];
        exact hau598)
  have hat1 :
    (Real.pi / 2 - (2 * (2935543137456839238447 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3326880683551411 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3326880683551411 : ℝ) =
              (3326880683551411 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau597)
  have hz1 :
    (5000000000000000 / 3326880683551411 : ℝ) ≤
      1 / Real.sqrt (885450806607 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3326880683551411 : ℝ) = 1 / (3326880683551411 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6653761367102819 : ℝ) ≤
      (1122444294482276282733 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (885450806607 / 2000000000000 : ℝ) ≤
      (750000000000000 / 6653761367102819 : ℝ) := by
    rw [show
        (750000000000000 / 6653761367102819 : ℝ) =
          (3 / 40) / (6653761367102819 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2935543137456839238447 / 10000000000000000000000 : ℝ))) -
        6 * (1122444294482276282733 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (885450806607 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (885450806607 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6653761367102819 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2935543137456839238447 / 10000000000000000000000 : ℝ))) -
          6 * (1122444294482276282733 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (885450806607 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (885450806607 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (885450806607 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_414 :
    ((146980584145210727889 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7992308389251518931253 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6663705449522809 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (587797568187209344421 / 2000000000000000000000 : ℝ))) -
              6 * (560391650420402333093 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (22202485159 / 50000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22202485159 / 50000000000 : ℝ)) = Real.log (72202485159 / 50000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22202485159 / 50000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22483735159 / 50000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (146980584145210727889 / 400000000000000000000 : ℝ) ≤
      Real.log (72202485159 / 50000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22483735159 / 50000000000 : ℝ) ≤
      (-(7992308389251518931253 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (22483735159 / 50000000000 : ℝ) = (22483735159 / 12500000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22483735159 / 12500000000 : ℝ) ≤
            (5870635216748481068747 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6663705449522809 / 10000000000000000 : ℝ) ≤ Real.sqrt (22202485159 / 50000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22202485159 / 50000000000 : ℝ) ≤ (1665926362380703 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22202485159 / 50000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau600 :
    Real.arctan (3331852724761406 / 11008430958203647 : ℝ) ≤
      (587797568187209344421 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau599 :
    Real.arctan (1665926362380703 / 2500000000000000 : ℝ) ≤
      (2 * (587797568187209344421 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6008430958203647 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1665926362380703 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1665926362380703 / 2500000000000000 : ℝ) /
                (1 + (6008430958203647 / 5000000000000000 : ℝ)) =
              (3331852724761406 / 11008430958203647 : ℝ)
            by
        norm_num];
        exact hau600)
  have hat1 :
    (Real.pi / 2 - (2 * (587797568187209344421 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1665926362380703 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1665926362380703 : ℝ) =
              (1665926362380703 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau599)
  have hz1 :
    (2500000000000000 / 1665926362380703 : ℝ) ≤ 1 / Real.sqrt (22202485159 / 50000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1665926362380703 : ℝ) = 1 / (1665926362380703 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6663705449522809 : ℝ) ≤
      (560391650420402333093 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22202485159 / 50000000000 : ℝ) ≤
      (750000000000000 / 6663705449522809 : ℝ) := by
    rw [show
        (750000000000000 / 6663705449522809 : ℝ) =
          (3 / 40) / (6663705449522809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (587797568187209344421 / 2000000000000000000000 : ℝ))) -
        6 * (560391650420402333093 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22202485159 / 50000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22202485159 / 50000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6663705449522809 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (587797568187209344421 / 2000000000000000000000 : ℝ))) -
          6 * (560391650420402333093 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (22202485159 / 50000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22202485159 / 50000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22202485159 / 50000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_415 :
    ((1841840568597262780059 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1592580298959499282641 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3336817357365023 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2942424258727729199681 / 10000000000000000000000 : ℝ))) -
              6 * (559564829681922406319 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (890748006113 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (890748006113 / 2000000000000 : ℝ)) =
      Real.log (2890748006113 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((890748006113 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (901998006113 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1841840568597262780059 / 5000000000000000000000 : ℝ) ≤
      Real.log (2890748006113 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (901998006113 / 2000000000000 : ℝ) ≤
      (-(1592580298959499282641 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (901998006113 / 2000000000000 : ℝ) = (901998006113 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (901998006113 / 500000000000 : ℝ) ≤
            (1180008422240500717359 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3336817357365023 / 5000000000000000 : ℝ) ≤ Real.sqrt (890748006113 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (890748006113 / 2000000000000 : ℝ) ≤ (6673634714730049 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (890748006113 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau602 :
    Real.arctan (6673634714730049 / 22022370827155931 : ℝ) ≤
      (2942424258727729199681 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau601 :
    Real.arctan (6673634714730049 / 10000000000000000 : ℝ) ≤
      (2 * (2942424258727729199681 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12022370827155931 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6673634714730049 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6673634714730049 / 10000000000000000 : ℝ) /
                (1 + (12022370827155931 / 10000000000000000 : ℝ)) =
              (6673634714730049 / 22022370827155931 : ℝ)
            by
        norm_num];
        exact hau602)
  have hat1 :
    (Real.pi / 2 - (2 * (2942424258727729199681 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6673634714730049 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6673634714730049 : ℝ) =
              (6673634714730049 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau601)
  have hz1 :
    (10000000000000000 / 6673634714730049 : ℝ) ≤
      1 / Real.sqrt (890748006113 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6673634714730049 : ℝ) =
          1 / (6673634714730049 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3336817357365023 : ℝ) ≤
      (559564829681922406319 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (890748006113 / 2000000000000 : ℝ) ≤
      (375000000000000 / 3336817357365023 : ℝ) := by
    rw [show
        (375000000000000 / 3336817357365023 : ℝ) =
          (3 / 40) / (3336817357365023 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2942424258727729199681 / 10000000000000000000000 : ℝ))) -
        6 * (559564829681922406319 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (890748006113 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (890748006113 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3336817357365023 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2942424258727729199681 / 10000000000000000000000 : ℝ))) -
          6 * (559564829681922406319 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (890748006113 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (890748006113 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (890748006113 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_416 :
    ((923209818979901109979 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1983395205848588651167 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6683549228763111 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2945852428842548212577 / 10000000000000000000000 : ℝ))) -
              6 * (558741657985630589877 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (446698302933 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (446698302933 / 1000000000000 : ℝ)) =
      Real.log (1446698302933 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((446698302933 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (452323302933 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (923209818979901109979 / 2500000000000000000000 : ℝ) ≤
      Real.log (1446698302933 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (452323302933 / 1000000000000 : ℝ) ≤
      (-(1983395205848588651167 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (452323302933 / 1000000000000 : ℝ) = (452323302933 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (452323302933 / 250000000000 : ℝ) ≤
            (1482340695651411348833 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6683549228763111 / 10000000000000000 : ℝ) ≤ Real.sqrt (446698302933 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (446698302933 / 1000000000000 : ℝ) ≤ (3341774614381557 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (446698302933 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau604 :
    Real.arctan (6683549228763114 / 22027877214758221 : ℝ) ≤
      (2945852428842548212577 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau603 :
    Real.arctan (3341774614381557 / 5000000000000000 : ℝ) ≤
      (2 * (2945852428842548212577 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12027877214758221 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3341774614381557 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3341774614381557 / 5000000000000000 : ℝ) /
                (1 + (12027877214758221 / 10000000000000000 : ℝ)) =
              (6683549228763114 / 22027877214758221 : ℝ)
            by
        norm_num];
        exact hau604)
  have hat1 :
    (Real.pi / 2 - (2 * (2945852428842548212577 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3341774614381557 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3341774614381557 : ℝ) =
              (3341774614381557 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau603)
  have hz1 :
    (5000000000000000 / 3341774614381557 : ℝ) ≤
      1 / Real.sqrt (446698302933 / 1000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3341774614381557 : ℝ) = 1 / (3341774614381557 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2227849742921037 : ℝ) ≤
      (558741657985630589877 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (446698302933 / 1000000000000 : ℝ) ≤
      (250000000000000 / 2227849742921037 : ℝ) := by
    rw [show
        (250000000000000 / 2227849742921037 : ℝ) =
          (3 / 40) / (6683549228763111 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2945852428842548212577 / 10000000000000000000000 : ℝ))) -
        6 * (558741657985630589877 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (446698302933 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (446698302933 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6683549228763111 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2945852428842548212577 / 10000000000000000000000 : ℝ))) -
          6 * (558741657985630589877 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (446698302933 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (446698302933 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (446698302933 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_417 :
    ((3701989035167639417921 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3952172935448006424207 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1338689811434299 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2949272389017869224799 / 10000000000000000000000 : ℝ))) -
              6 * (1115844217138206506899 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (896045205619 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (896045205619 / 2000000000000 : ℝ)) =
      Real.log (2896045205619 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((896045205619 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (907295205619 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3701989035167639417921 / 10000000000000000000000 : ℝ) ≤
      Real.log (2896045205619 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (907295205619 / 2000000000000 : ℝ) ≤
      (-(3952172935448006424207 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (907295205619 / 2000000000000 : ℝ) = (907295205619 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (907295205619 / 500000000000 : ℝ) ≤
            (2979298867551993575793 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1338689811434299 / 2000000000000000 : ℝ) ≤ Real.sqrt (896045205619 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (896045205619 / 2000000000000 : ℝ) ≤ (3346724528585749 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (896045205619 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau606 :
    Real.arctan (6693449057171498 / 22033381082677885 : ℝ) ≤
      (2949272389017869224799 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau605 :
    Real.arctan (3346724528585749 / 5000000000000000 : ℝ) ≤
      (2 * (2949272389017869224799 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2406676216535577 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3346724528585749 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3346724528585749 / 5000000000000000 : ℝ) /
                (1 + (2406676216535577 / 2000000000000000 : ℝ)) =
              (6693449057171498 / 22033381082677885 : ℝ)
            by
        norm_num];
        exact hau606)
  have hat1 :
    (Real.pi / 2 - (2 * (2949272389017869224799 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3346724528585749 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3346724528585749 : ℝ) =
              (3346724528585749 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau605)
  have hz1 :
    (5000000000000000 / 3346724528585749 : ℝ) ≤
      1 / Real.sqrt (896045205619 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3346724528585749 : ℝ) = 1 / (3346724528585749 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1338689811434299 : ℝ) ≤
      (1115844217138206506899 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (896045205619 / 2000000000000 : ℝ) ≤
      (150000000000000 / 1338689811434299 : ℝ) := by
    rw [show
        (150000000000000 / 1338689811434299 : ℝ) =
          (3 / 40) / (1338689811434299 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2949272389017869224799 / 10000000000000000000000 : ℝ))) -
        6 * (1115844217138206506899 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (896045205619 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (896045205619 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1338689811434299 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2949272389017869224799 / 10000000000000000000000 : ℝ))) -
          6 * (1115844217138206506899 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (896045205619 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (896045205619 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (896045205619 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_418 :
    ((926640194319229491321 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1972440095724352398719 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6698393484618157 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2950979302097091334933 / 10000000000000000000000 : ℝ))) -
              6 * (278756841963755830087 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1794739010991 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1794739010991 / 4000000000000 : ℝ)) =
      Real.log (5794739010991 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1794739010991 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1817239010991 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (926640194319229491321 / 2500000000000000000000 : ℝ) ≤
      Real.log (5794739010991 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1817239010991 / 4000000000000 : ℝ) ≤
      (-(1972440095724352398719 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1817239010991 / 4000000000000 : ℝ) = (1817239010991 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1817239010991 / 1000000000000 : ℝ) ≤
            (1493295805775647601281 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6698393484618157 / 10000000000000000 : ℝ) ≤ Real.sqrt (1794739010991 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1794739010991 / 4000000000000 : ℝ) ≤ (83729918557727 / 125000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1794739010991 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau608 :
    Real.arctan (3349196742309080 / 11018066036418489 : ℝ) ≤
      (2950979302097091334933 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau607 :
    Real.arctan (83729918557727 / 125000000000000 : ℝ) ≤
      (2 * (2950979302097091334933 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6018066036418489 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (83729918557727 / 125000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (83729918557727 / 125000000000000 : ℝ) /
                (1 + (6018066036418489 / 5000000000000000 : ℝ)) =
              (3349196742309080 / 11018066036418489 : ℝ)
            by
        norm_num];
        exact hau608)
  have hat1 :
    (Real.pi / 2 - (2 * (2950979302097091334933 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (125000000000000 / 83729918557727 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 83729918557727 : ℝ) =
              (83729918557727 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hau607)
  have hz1 :
    (125000000000000 / 83729918557727 : ℝ) ≤ 1 / Real.sqrt (1794739010991 / 4000000000000 : ℝ) := by
    rw [show (125000000000000 / 83729918557727 : ℝ) = 1 / (83729918557727 / 125000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6698393484618157 : ℝ) ≤
      (278756841963755830087 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1794739010991 / 4000000000000 : ℝ) ≤
      (750000000000000 / 6698393484618157 : ℝ) := by
    rw [show
        (750000000000000 / 6698393484618157 : ℝ) =
          (3 / 40) / (6698393484618157 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2950979302097091334933 / 10000000000000000000000 : ℝ))) -
        6 * (278756841963755830087 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1794739010991 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1794739010991 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6698393484618157 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2950979302097091334933 / 10000000000000000000000 : ℝ))) -
          6 * (278756841963755830087 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1794739010991 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1794739010991 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1794739010991 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_419 :
    ((3711130430258663998133 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1968799034391279262693 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6703334265020653 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (738171044180126359817 / 2500000000000000000000 : ℝ))) -
              6 * (222842461977562569229 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (224673451343 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (224673451343 / 500000000000 : ℝ)) =
      Real.log (724673451343 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((224673451343 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (227485951343 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3711130430258663998133 / 10000000000000000000000 : ℝ) ≤
      Real.log (724673451343 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (227485951343 / 500000000000 : ℝ) ≤
      (-(1968799034391279262693 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (227485951343 / 500000000000 : ℝ) = (227485951343 / 125000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (227485951343 / 125000000000 : ℝ) ≤
            (1496936867108720737307 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6703334265020653 / 10000000000000000 : ℝ) ≤ Real.sqrt (224673451343 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (224673451343 / 500000000000 : ℝ) ≤ (418958391563791 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (224673451343 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau610 :
    Real.arctan (6703334265020656 / 22038882434370725 : ℝ) ≤
      (738171044180126359817 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau609 :
    Real.arctan (418958391563791 / 625000000000000 : ℝ) ≤
      (2 * (738171044180126359817 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (481555297374829 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (418958391563791 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (418958391563791 / 625000000000000 : ℝ) /
                (1 + (481555297374829 / 400000000000000 : ℝ)) =
              (6703334265020656 / 22038882434370725 : ℝ)
            by
        norm_num];
        exact hau610)
  have hat1 :
    (Real.pi / 2 - (2 * (738171044180126359817 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 418958391563791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 418958391563791 : ℝ) =
              (418958391563791 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau609)
  have hz1 :
    (625000000000000 / 418958391563791 : ℝ) ≤ 1 / Real.sqrt (224673451343 / 500000000000 : ℝ) := by
    rw [show (625000000000000 / 418958391563791 : ℝ) = 1 / (418958391563791 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6703334265020653 : ℝ) ≤
      (222842461977562569229 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (224673451343 / 500000000000 : ℝ) ≤
      (750000000000000 / 6703334265020653 : ℝ) := by
    rw [show
        (750000000000000 / 6703334265020653 : ℝ) =
          (3 / 40) / (6703334265020653 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (738171044180126359817 / 2500000000000000000000 : ℝ))) -
        6 * (222842461977562569229 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (224673451343 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (224673451343 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6703334265020653 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (738171044180126359817 / 2500000000000000000000 : ℝ))) -
          6 * (222842461977562569229 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (224673451343 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (224673451343 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (224673451343 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_420 :
    ((1857848998010661530569 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(786065307311242032783 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6708271406437353 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (5908774035059268563 / 20000000000000000000 : ℝ))) -
              6 * (278349759174727094639 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1800036210497 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1800036210497 / 4000000000000 : ℝ)) =
      Real.log (5800036210497 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1800036210497 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1822536210497 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1857848998010661530569 / 5000000000000000000000 : ℝ) ≤
      Real.log (5800036210497 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1822536210497 / 4000000000000 : ℝ) ≤
      (-(786065307311242032783 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1822536210497 / 4000000000000 : ℝ) = (1822536210497 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1822536210497 / 1000000000000 : ℝ) ≤
            (600229053288757967217 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6708271406437353 / 10000000000000000 : ℝ) ≤ Real.sqrt (1800036210497 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1800036210497 / 4000000000000 : ℝ) ≤ (1677067851609339 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1800036210497 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau612 :
    Real.arctan (2236090468812452 / 7347210722569955 : ℝ) ≤
      (5908774035059268563 / 20000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau611 :
    Real.arctan (1677067851609339 / 2500000000000000 : ℝ) ≤
      (2 * (5908774035059268563 / 20000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2408326433541973 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1677067851609339 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1677067851609339 / 2500000000000000 : ℝ) /
                (1 + (2408326433541973 / 2000000000000000 : ℝ)) =
              (2236090468812452 / 7347210722569955 : ℝ)
            by
        norm_num];
        exact hau612)
  have hat1 :
    (Real.pi / 2 - (2 * (5908774035059268563 / 20000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1677067851609339 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1677067851609339 : ℝ) =
              (1677067851609339 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau611)
  have hz1 :
    (2500000000000000 / 1677067851609339 : ℝ) ≤
      1 / Real.sqrt (1800036210497 / 4000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1677067851609339 : ℝ) = 1 / (1677067851609339 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2236090468812451 : ℝ) ≤
      (278349759174727094639 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1800036210497 / 4000000000000 : ℝ) ≤
      (250000000000000 / 2236090468812451 : ℝ) := by
    rw [show
        (250000000000000 / 2236090468812451 : ℝ) =
          (3 / 40) / (6708271406437353 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (5908774035059268563 / 20000000000000000000 : ℝ))) -
        6 * (278349759174727094639 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1800036210497 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1800036210497 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6708271406437353 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (5908774035059268563 / 20000000000000000000 : ℝ))) -
          6 * (278349759174727094639 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1800036210497 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1800036210497 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1800036210497 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
