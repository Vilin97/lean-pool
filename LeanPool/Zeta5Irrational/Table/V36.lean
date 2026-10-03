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

/-! # V36: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_433 :
    ((3774887277605171324213 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(479593316593176151771 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3386063355216127 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2976340953035626311821 / 10000000000000000000000 : ℝ))) -
              6 * (11029859851979670127 / 100000000000000000000 : ℝ)))) ≤
      Vfield (917234003643 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (917234003643 / 2000000000000 : ℝ)) =
      Real.log (2917234003643 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((917234003643 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (928484003643 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3774887277605171324213 / 10000000000000000000000 : ℝ) ≤
      Real.log (2917234003643 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (928484003643 / 2000000000000 : ℝ) ≤
      (-(479593316593176151771 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (928484003643 / 2000000000000 : ℝ) = (928484003643 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (928484003643 / 500000000000 : ℝ) ≤
            (386840658781823848229 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3386063355216127 / 5000000000000000 : ℝ) ≤ Real.sqrt (917234003643 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (917234003643 / 2000000000000 : ℝ) ≤ (6772126710432257 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (917234003643 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau638 :
    Real.arctan (6772126710432257 / 22077321730505898 : ℝ) ≤
      (2976340953035626311821 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau637 :
    Real.arctan (6772126710432257 / 10000000000000000 : ℝ) ≤
      (2 * (2976340953035626311821 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6038660865252949 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6772126710432257 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6772126710432257 / 10000000000000000 : ℝ) /
                (1 + (6038660865252949 / 5000000000000000 : ℝ)) =
              (6772126710432257 / 22077321730505898 : ℝ)
            by
        norm_num];
        exact hau638)
  have hat1 :
    (Real.pi / 2 - (2 * (2976340953035626311821 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6772126710432257 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6772126710432257 : ℝ) =
              (6772126710432257 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau637)
  have hz1 :
    (10000000000000000 / 6772126710432257 : ℝ) ≤
      1 / Real.sqrt (917234003643 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6772126710432257 : ℝ) =
          1 / (6772126710432257 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3386063355216127 : ℝ) ≤
      (11029859851979670127 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (917234003643 / 2000000000000 : ℝ) ≤
      (375000000000000 / 3386063355216127 : ℝ) := by
    rw [show
        (375000000000000 / 3386063355216127 : ℝ) =
          (3 / 40) / (3386063355216127 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2976340953035626311821 / 10000000000000000000000 : ℝ))) -
        6 * (11029859851979670127 / 100000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (917234003643 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (917234003643 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3386063355216127 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2976340953035626311821 / 10000000000000000000000 : ℝ))) -
          6 * (11029859851979670127 / 100000000000000000000 : ℝ))) ≤
      Real.sqrt (917234003643 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (917234003643 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (917234003643 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_434 :
    ((377942582123225227881 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7659240193694681880157 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6777013735855563 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2978015798672107485851 / 10000000000000000000000 : ℝ))) -
              6 * (1102197030739536467523 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1837116607039 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1837116607039 / 4000000000000 : ℝ)) =
      Real.log (5837116607039 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1837116607039 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1859616607039 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (377942582123225227881 / 1000000000000000000000 : ℝ) ≤
      Real.log (5837116607039 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1859616607039 / 4000000000000 : ℝ) ≤
      (-(7659240193694681880157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1859616607039 / 4000000000000 : ℝ) = (1859616607039 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1859616607039 / 1000000000000 : ℝ) ≤
            (6203703412305318119843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6777013735855563 / 10000000000000000 : ℝ) ≤ Real.sqrt (1837116607039 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1837116607039 / 4000000000000 : ℝ) ≤ (3388506867927783 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1837116607039 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau640 :
    Real.arctan (6777013735855566 / 22080062714074583 : ℝ) ≤
      (2978015798672107485851 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau639 :
    Real.arctan (3388506867927783 / 5000000000000000 : ℝ) ≤
      (2 * (2978015798672107485851 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12080062714074583 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3388506867927783 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3388506867927783 / 5000000000000000 : ℝ) /
                (1 + (12080062714074583 / 10000000000000000 : ℝ)) =
              (6777013735855566 / 22080062714074583 : ℝ)
            by
        norm_num];
        exact hau640)
  have hat1 :
    (Real.pi / 2 - (2 * (2978015798672107485851 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3388506867927783 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3388506867927783 : ℝ) =
              (3388506867927783 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau639)
  have hz1 :
    (5000000000000000 / 3388506867927783 : ℝ) ≤
      1 / Real.sqrt (1837116607039 / 4000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3388506867927783 : ℝ) = 1 / (3388506867927783 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2259004578618521 : ℝ) ≤
      (1102197030739536467523 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1837116607039 / 4000000000000 : ℝ) ≤
      (250000000000000 / 2259004578618521 : ℝ) := by
    rw [show
        (250000000000000 / 2259004578618521 : ℝ) =
          (3 / 40) / (6777013735855563 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2978015798672107485851 / 10000000000000000000000 : ℝ))) -
        6 * (1102197030739536467523 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1837116607039 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1837116607039 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6777013735855563 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2978015798672107485851 / 10000000000000000000000 : ℝ))) -
          6 * (1102197030739536467523 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1837116607039 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1837116607039 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1837116607039 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_435 :
    ((18919811529779573573 / 50000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1529001521484943568809 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6781897239696277 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2979688678173779422881 / 10000000000000000000000 : ℝ))) -
              6 * (34419055214933789157 / 312500000000000000000 : ℝ)))) ≤
      Vfield (229970650849 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (229970650849 / 500000000000 : ℝ)) =
      Real.log (729970650849 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((229970650849 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (232783150849 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (18919811529779573573 / 50000000000000000000 : ℝ) ≤
      Real.log (729970650849 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (232783150849 / 500000000000 : ℝ) ≤
      (-(1529001521484943568809 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (232783150849 / 500000000000 : ℝ) = (232783150849 / 125000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (232783150849 / 125000000000 : ℝ) ≤
            (1243587199715056431191 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6781897239696277 / 10000000000000000 : ℝ) ≤ Real.sqrt (229970650849 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (229970650849 / 500000000000 : ℝ) ≤ (169547430992407 / 250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (229970650849 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau642 :
    Real.arctan (65210550381695 / 212334644960108 : ℝ) ≤
      (2979688678173779422881 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau641 :
    Real.arctan (169547430992407 / 250000000000000 : ℝ) ≤
      (2 * (2979688678173779422881 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (377587596120351 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (169547430992407 / 250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (169547430992407 / 250000000000000 : ℝ) /
                (1 + (377587596120351 / 312500000000000 : ℝ)) =
              (65210550381695 / 212334644960108 : ℝ)
            by
        norm_num];
        exact hau642)
  have hat1 :
    (Real.pi / 2 - (2 * (2979688678173779422881 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (250000000000000 / 169547430992407 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 169547430992407 : ℝ) =
              (169547430992407 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hau641)
  have hz1 :
    (250000000000000 / 169547430992407 : ℝ) ≤ 1 / Real.sqrt (229970650849 / 500000000000 : ℝ) := by
    rw [show (250000000000000 / 169547430992407 : ℝ) = 1 / (169547430992407 / 250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6781897239696277 : ℝ) ≤
      (34419055214933789157 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (229970650849 / 500000000000 : ℝ) ≤
      (750000000000000 / 6781897239696277 : ℝ) := by
    rw [show
        (750000000000000 / 6781897239696277 : ℝ) =
          (3 / 40) / (6781897239696277 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2979688678173779422881 / 10000000000000000000000 : ℝ))) -
        6 * (34419055214933789157 / 312500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (229970650849 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (229970650849 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6781897239696277 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2979688678173779422881 / 10000000000000000000000 : ℝ))) -
          6 * (34419055214933789157 / 312500000000000000000 : ℝ))) ≤
      Real.sqrt (229970650849 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (229970650849 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (229970650849 / 500000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_436 :
    ((3788496733643348428943 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1907698812254968296973 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6786777229556381 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2981359595926635812237 / 10000000000000000000000 : ℝ))) -
              6 * (44024967503350408363 / 400000000000000000000 : ℝ)))) ≤
      Vfield (368482761309 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (368482761309 / 800000000000 : ℝ)) =
      Real.log (1168482761309 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((368482761309 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (372982761309 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3788496733643348428943 / 10000000000000000000000 : ℝ) ≤
      Real.log (1168482761309 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (372982761309 / 800000000000 : ℝ) ≤
      (-(1907698812254968296973 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (372982761309 / 800000000000 : ℝ) = (372982761309 / 200000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (372982761309 / 200000000000 : ℝ) ≤
            (1558037089245031703027 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6786777229556381 / 10000000000000000 : ℝ) ≤ Real.sqrt (368482761309 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (368482761309 / 800000000000 : ℝ) ≤ (212086788423637 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (368482761309 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau644 :
    Real.arctan (6786777229556384 / 22085542816258813 : ℝ) ≤
      (2981359595926635812237 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau643 :
    Real.arctan (212086788423637 / 312500000000000 : ℝ) ≤
      (2 * (2981359595926635812237 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12085542816258813 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (212086788423637 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (212086788423637 / 312500000000000 : ℝ) /
                (1 + (12085542816258813 / 10000000000000000 : ℝ)) =
              (6786777229556384 / 22085542816258813 : ℝ)
            by
        norm_num];
        exact hau644)
  have hat1 :
    (Real.pi / 2 - (2 * (2981359595926635812237 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 212086788423637 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 212086788423637 : ℝ) =
              (212086788423637 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau643)
  have hz1 :
    (312500000000000 / 212086788423637 : ℝ) ≤ 1 / Real.sqrt (368482761309 / 800000000000 : ℝ) := by
    rw [show (312500000000000 / 212086788423637 : ℝ) = 1 / (212086788423637 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6786777229556381 : ℝ) ≤
      (44024967503350408363 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (368482761309 / 800000000000 : ℝ) ≤
      (750000000000000 / 6786777229556381 : ℝ) := by
    rw [show
        (750000000000000 / 6786777229556381 : ℝ) =
          (3 / 40) / (6786777229556381 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2981359595926635812237 / 10000000000000000000000 : ℝ))) -
        6 * (44024967503350408363 / 400000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (368482761309 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (368482761309 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6786777229556381 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2981359595926635812237 / 10000000000000000000000 : ℝ))) -
          6 * (44024967503350408363 / 400000000000000000000 : ℝ))) ≤
      Real.sqrt (368482761309 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (368482761309 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (368482761309 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_437 :
    ((3793029106159204379151 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7616603061064595854687 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6791653713010549 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2983028556301359654301 / 10000000000000000000000 : ℝ))) -
              6 * (549920143428996453391 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (922531203149 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (922531203149 / 2000000000000 : ℝ)) =
      Real.log (2922531203149 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((922531203149 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (933781203149 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3793029106159204379151 / 10000000000000000000000 : ℝ) ≤
      Real.log (2922531203149 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (933781203149 / 2000000000000 : ℝ) ≤
      (-(7616603061064595854687 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (933781203149 / 2000000000000 : ℝ) = (933781203149 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (933781203149 / 500000000000 : ℝ) ≤
            (6246340544935404145313 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6791653713010549 / 10000000000000000 : ℝ) ≤ Real.sqrt (922531203149 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (922531203149 / 2000000000000 : ℝ) ≤ (848956714126319 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (922531203149 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau646 :
    Real.arctan (3395826856505276 / 11044140967859907 : ℝ) ≤
      (2983028556301359654301 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau645 :
    Real.arctan (848956714126319 / 1250000000000000 : ℝ) ≤
      (2 * (2983028556301359654301 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6044140967859907 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (848956714126319 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (848956714126319 / 1250000000000000 : ℝ) /
                (1 + (6044140967859907 / 5000000000000000 : ℝ)) =
              (3395826856505276 / 11044140967859907 : ℝ)
            by
        norm_num];
        exact hau646)
  have hat1 :
    (Real.pi / 2 - (2 * (2983028556301359654301 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 848956714126319 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 848956714126319 : ℝ) =
              (848956714126319 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau645)
  have hz1 :
    (1250000000000000 / 848956714126319 : ℝ) ≤ 1 / Real.sqrt (922531203149 / 2000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 848956714126319 : ℝ) = 1 / (848956714126319 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6791653713010549 : ℝ) ≤
      (549920143428996453391 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (922531203149 / 2000000000000 : ℝ) ≤
      (750000000000000 / 6791653713010549 : ℝ) := by
    rw [show
        (750000000000000 / 6791653713010549 : ℝ) =
          (3 / 40) / (6791653713010549 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2983028556301359654301 / 10000000000000000000000 : ℝ))) -
        6 * (549920143428996453391 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (922531203149 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (922531203149 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6791653713010549 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2983028556301359654301 / 10000000000000000000000 : ℝ))) -
          6 * (549920143428996453391 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (922531203149 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (922531203149 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (922531203149 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_438 :
    ((1898779712682799641597 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7602430986387443157753 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1699131674401571 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2984695563653398434181 / 10000000000000000000000 : ℝ))) -
              6 * (549529029365633383129 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1847711006051 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1847711006051 / 4000000000000 : ℝ)) =
      Real.log (5847711006051 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1847711006051 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1870211006051 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1898779712682799641597 / 5000000000000000000000 : ℝ) ≤
      Real.log (5847711006051 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1870211006051 / 4000000000000 : ℝ) ≤
      (-(7602430986387443157753 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1870211006051 / 4000000000000 : ℝ) = (1870211006051 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1870211006051 / 1000000000000 : ℝ) ≤
            (6260512619612556842247 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1699131674401571 / 2500000000000000 : ℝ) ≤ Real.sqrt (1847711006051 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1847711006051 / 4000000000000 : ℝ) ≤ (6796526697606287 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1847711006051 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau648 :
    Real.arctan (6796526697606287 / 22091020434656249 : ℝ) ≤
      (2984695563653398434181 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau647 :
    Real.arctan (6796526697606287 / 10000000000000000 : ℝ) ≤
      (2 * (2984695563653398434181 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12091020434656249 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6796526697606287 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6796526697606287 / 10000000000000000 : ℝ) /
                (1 + (12091020434656249 / 10000000000000000 : ℝ)) =
              (6796526697606287 / 22091020434656249 : ℝ)
            by
        norm_num];
        exact hau648)
  have hat1 :
    (Real.pi / 2 - (2 * (2984695563653398434181 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6796526697606287 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6796526697606287 : ℝ) =
              (6796526697606287 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau647)
  have hz1 :
    (10000000000000000 / 6796526697606287 : ℝ) ≤
      1 / Real.sqrt (1847711006051 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6796526697606287 : ℝ) =
          1 / (6796526697606287 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1699131674401571 : ℝ) ≤
      (549529029365633383129 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1847711006051 / 4000000000000 : ℝ) ≤
      (187500000000000 / 1699131674401571 : ℝ) := by
    rw [show
        (187500000000000 / 1699131674401571 : ℝ) =
          (3 / 40) / (1699131674401571 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2984695563653398434181 / 10000000000000000000000 : ℝ))) -
        6 * (549529029365633383129 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1847711006051 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1847711006051 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1699131674401571 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2984695563653398434181 / 10000000000000000000000 : ℝ))) -
          6 * (549529029365633383129 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1847711006051 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1847711006051 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1847711006051 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_439 :
    ((3802087693122120209983 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(758827896805969992371 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((425087261929003 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2986360622323037088307 / 10000000000000000000000 : ℝ))) -
              6 * (1098277497263947141799 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (462589901451 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (462589901451 / 1000000000000 : ℝ)) =
      Real.log (1462589901451 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((462589901451 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (468214901451 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3802087693122120209983 / 10000000000000000000000 : ℝ) ≤
      Real.log (1462589901451 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (468214901451 / 1000000000000 : ℝ) ≤
      (-(758827896805969992371 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (468214901451 / 1000000000000 : ℝ) = (468214901451 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (468214901451 / 250000000000 : ℝ) ≤
            (627466463794030007629 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (425087261929003 / 625000000000000 : ℝ) ≤ Real.sqrt (462589901451 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (462589901451 / 1000000000000 : ℝ) ≤ (6801396190864051 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (462589901451 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau650 :
    Real.arctan (6801396190864051 / 22093758313489648 : ℝ) ≤
      (2986360622323037088307 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau649 :
    Real.arctan (6801396190864051 / 10000000000000000 : ℝ) ≤
      (2 * (2986360622323037088307 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (755859894593103 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (6801396190864051 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6801396190864051 / 10000000000000000 : ℝ) /
                (1 + (755859894593103 / 625000000000000 : ℝ)) =
              (6801396190864051 / 22093758313489648 : ℝ)
            by
        norm_num];
        exact hau650)
  have hat1 :
    (Real.pi / 2 - (2 * (2986360622323037088307 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6801396190864051 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6801396190864051 : ℝ) =
              (6801396190864051 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau649)
  have hz1 :
    (10000000000000000 / 6801396190864051 : ℝ) ≤
      1 / Real.sqrt (462589901451 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6801396190864051 : ℝ) =
          1 / (6801396190864051 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (46875000000000 / 425087261929003 : ℝ) ≤
      (1098277497263947141799 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (462589901451 / 1000000000000 : ℝ) ≤
      (46875000000000 / 425087261929003 : ℝ) := by
    rw [show
        (46875000000000 / 425087261929003 : ℝ) =
          (3 / 40) / (425087261929003 / 625000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2986360622323037088307 / 10000000000000000000000 : ℝ))) -
        6 * (1098277497263947141799 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (462589901451 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (462589901451 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((425087261929003 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2986360622323037088307 / 10000000000000000000000 : ℝ))) -
          6 * (1098277497263947141799 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (462589901451 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (462589901451 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (462589901451 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_440 :
    ((3806613911285829159271 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(946768368674250799957 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3403131100138701 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (597604747327094440931 / 2000000000000000000000 : ℝ))) -
              6 * (274374649136471787029 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1853008205557 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1853008205557 / 4000000000000 : ℝ)) =
      Real.log (5853008205557 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1853008205557 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1875508205557 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3806613911285829159271 / 10000000000000000000000 : ℝ) ≤
      Real.log (5853008205557 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1875508205557 / 4000000000000 : ℝ) ≤
      (-(946768368674250799957 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1875508205557 / 4000000000000 : ℝ) = (1875508205557 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1875508205557 / 1000000000000 : ℝ) ≤
            (786099582075749200043 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3403131100138701 / 5000000000000000 : ℝ) ≤ Real.sqrt (1853008205557 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1853008205557 / 4000000000000 : ℝ) ≤ (1361252440055481 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1853008205557 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau652 :
    Real.arctan (6806262200277405 / 22096495572641069 : ℝ) ≤
      (597604747327094440931 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau651 :
    Real.arctan (1361252440055481 / 2000000000000000 : ℝ) ≤
      (2 * (597604747327094440931 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12096495572641069 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1361252440055481 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1361252440055481 / 2000000000000000 : ℝ) /
                (1 + (12096495572641069 / 10000000000000000 : ℝ)) =
              (6806262200277405 / 22096495572641069 : ℝ)
            by
        norm_num];
        exact hau652)
  have hat1 :
    (Real.pi / 2 - (2 * (597604747327094440931 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1361252440055481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1361252440055481 : ℝ) =
              (1361252440055481 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau651)
  have hz1 :
    (2000000000000000 / 1361252440055481 : ℝ) ≤
      1 / Real.sqrt (1853008205557 / 4000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1361252440055481 : ℝ) = 1 / (1361252440055481 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1134377033379567 : ℝ) ≤
      (274374649136471787029 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1853008205557 / 4000000000000 : ℝ) ≤
      (125000000000000 / 1134377033379567 : ℝ) := by
    rw [show
        (125000000000000 / 1134377033379567 : ℝ) =
          (3 / 40) / (3403131100138701 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (597604747327094440931 / 2000000000000000000000 : ℝ))) -
        6 * (274374649136471787029 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1853008205557 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1853008205557 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3403131100138701 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (597604747327094440931 / 2000000000000000000000 : ℝ))) -
          6 * (274374649136471787029 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (1853008205557 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1853008205557 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1853008205557 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_441 :
    ((1905569040855633815593 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(75600348739429958419 / 100000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6811124733313139 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (298968491090088576719 / 1000000000000000000000 : ℝ))) -
              6 * (68545084418514996731 / 625000000000000000000 : ℝ)))) ≤
      Vfield (185565680531 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (185565680531 / 400000000000 : ℝ)) =
      Real.log (585565680531 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((185565680531 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (187815680531 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1905569040855633815593 / 5000000000000000000000 : ℝ) ≤
      Real.log (585565680531 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (187815680531 / 400000000000 : ℝ) ≤
      (-(75600348739429958419 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (187815680531 / 400000000000 : ℝ) = (187815680531 / 100000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (187815680531 / 100000000000 : ℝ) ≤
            (63029087320570041581 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6811124733313139 / 10000000000000000 : ℝ) ≤ Real.sqrt (185565680531 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (185565680531 / 400000000000 : ℝ) ≤ (3405562366656571 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (185565680531 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau654 :
    Real.arctan (3405562366656571 / 11049616106265545 : ℝ) ≤
      (298968491090088576719 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau653 :
    Real.arctan (3405562366656571 / 5000000000000000 : ℝ) ≤
      (2 * (298968491090088576719 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1209923221253109 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3405562366656571 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3405562366656571 / 5000000000000000 : ℝ) /
                (1 + (1209923221253109 / 1000000000000000 : ℝ)) =
              (3405562366656571 / 11049616106265545 : ℝ)
            by
        norm_num];
        exact hau654)
  have hat1 :
    (Real.pi / 2 - (2 * (298968491090088576719 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3405562366656571 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3405562366656571 : ℝ) =
              (3405562366656571 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau653)
  have hz1 :
    (5000000000000000 / 3405562366656571 : ℝ) ≤ 1 / Real.sqrt (185565680531 / 400000000000 : ℝ) :=
  by
    rw [show
        (5000000000000000 / 3405562366656571 : ℝ) = 1 / (3405562366656571 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6811124733313139 : ℝ) ≤
      (68545084418514996731 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (185565680531 / 400000000000 : ℝ) ≤
      (750000000000000 / 6811124733313139 : ℝ) := by
    rw [show
        (750000000000000 / 6811124733313139 : ℝ) =
          (3 / 40) / (6811124733313139 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (298968491090088576719 / 1000000000000000000000 : ℝ))) -
        6 * (68545084418514996731 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (185565680531 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (185565680531 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6811124733313139 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (298968491090088576719 / 1000000000000000000000 : ℝ))) -
          6 * (68545084418514996731 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (185565680531 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (185565680531 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (185565680531 / 400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_442 :
    ((23847876289065382409 / 62500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7545942685497941771449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3407991898705709 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2991344149414517301659 / 10000000000000000000000 : ℝ))) -
              6 * (1095945753863272201041 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1858305405063 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1858305405063 / 4000000000000 : ℝ)) =
      Real.log (5858305405063 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1858305405063 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1880805405063 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (23847876289065382409 / 62500000000000000000 : ℝ) ≤
      Real.log (5858305405063 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1880805405063 / 4000000000000 : ℝ) ≤
      (-(7545942685497941771449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1880805405063 / 4000000000000 : ℝ) = (1880805405063 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1880805405063 / 1000000000000 : ℝ) ≤
            (6317000920502058228551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3407991898705709 / 5000000000000000 : ℝ) ≤ Real.sqrt (1858305405063 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1858305405063 / 4000000000000 : ℝ) ≤ (6815983797411421 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1858305405063 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau656 :
    Real.arctan (6815983797411421 / 22101968233579816 : ℝ) ≤
      (2991344149414517301659 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau655 :
    Real.arctan (6815983797411421 / 10000000000000000 : ℝ) ≤
      (2 * (2991344149414517301659 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1512746029197477 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (6815983797411421 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6815983797411421 / 10000000000000000 : ℝ) /
                (1 + (1512746029197477 / 1250000000000000 : ℝ)) =
              (6815983797411421 / 22101968233579816 : ℝ)
            by
        norm_num];
        exact hau656)
  have hat1 :
    (Real.pi / 2 - (2 * (2991344149414517301659 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6815983797411421 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6815983797411421 : ℝ) =
              (6815983797411421 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau655)
  have hz1 :
    (10000000000000000 / 6815983797411421 : ℝ) ≤
      1 / Real.sqrt (1858305405063 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6815983797411421 : ℝ) =
          1 / (6815983797411421 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3407991898705709 : ℝ) ≤
      (1095945753863272201041 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1858305405063 / 4000000000000 : ℝ) ≤
      (375000000000000 / 3407991898705709 : ℝ) := by
    rw [show
        (375000000000000 / 3407991898705709 : ℝ) =
          (3 / 40) / (3407991898705709 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2991344149414517301659 / 10000000000000000000000 : ℝ))) -
        6 * (1095945753863272201041 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1858305405063 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1858305405063 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3407991898705709 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2991344149414517301659 / 10000000000000000000000 : ℝ))) -
          6 * (1095945753863272201041 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1858305405063 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1858305405063 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1858305405063 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_443 :
    ((382018028675292399023 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3765935164043707208489 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3410419699992949 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (598600291291347412667 / 2000000000000000000000 : ℝ))) -
              6 * (136896475028022353711 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (116309625301 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (116309625301 / 250000000000 : ℝ)) =
      Real.log (366309625301 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((116309625301 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (117715875301 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (382018028675292399023 / 1000000000000000000000 : ℝ) ≤
      Real.log (366309625301 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (117715875301 / 250000000000 : ℝ) ≤
      (-(3765935164043707208489 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (117715875301 / 250000000000 : ℝ) = (117715875301 / 62500000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (117715875301 / 62500000000 : ℝ) ≤
            (3165536638956292791511 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3410419699992949 / 5000000000000000 : ℝ) ≤ Real.sqrt (116309625301 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (116309625301 / 250000000000 : ℝ) ≤ (6820839399985901 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (116309625301 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau658 :
    Real.arctan (6820839399985901 / 22104703636206877 : ℝ) ≤
      (598600291291347412667 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau657 :
    Real.arctan (6820839399985901 / 10000000000000000 : ℝ) ≤
      (2 * (598600291291347412667 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12104703636206877 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6820839399985901 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6820839399985901 / 10000000000000000 : ℝ) /
                (1 + (12104703636206877 / 10000000000000000 : ℝ)) =
              (6820839399985901 / 22104703636206877 : ℝ)
            by
        norm_num];
        exact hau658)
  have hat1 :
    (Real.pi / 2 - (2 * (598600291291347412667 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6820839399985901 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6820839399985901 : ℝ) =
              (6820839399985901 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau657)
  have hz1 :
    (10000000000000000 / 6820839399985901 : ℝ) ≤
      1 / Real.sqrt (116309625301 / 250000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6820839399985901 : ℝ) =
          1 / (6820839399985901 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3410419699992949 : ℝ) ≤
      (136896475028022353711 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (116309625301 / 250000000000 : ℝ) ≤
      (375000000000000 / 3410419699992949 : ℝ) := by
    rw [show
        (375000000000000 / 3410419699992949 : ℝ) =
          (3 / 40) / (3410419699992949 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (598600291291347412667 / 2000000000000000000000 : ℝ))) -
        6 * (136896475028022353711 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (116309625301 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (116309625301 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3410419699992949 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (598600291291347412667 / 2000000000000000000000 : ℝ))) -
          6 * (136896475028022353711 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (116309625301 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (116309625301 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (116309625301 / 250000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_444 :
    ((3824698325065663360863 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1879454436493986812577 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1365138309684773 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2994656836293116231503 / 10000000000000000000000 : ℝ))) -
              6 * (68399967749056262157 / 625000000000000000000 : ℝ)))) ≤
      Vfield (1863602604569 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1863602604569 / 4000000000000 : ℝ)) =
      Real.log (5863602604569 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1863602604569 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1886102604569 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3824698325065663360863 / 10000000000000000000000 : ℝ) ≤
      Real.log (5863602604569 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1886102604569 / 4000000000000 : ℝ) ≤
      (-(1879454436493986812577 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1886102604569 / 4000000000000 : ℝ) = (1886102604569 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1886102604569 / 1000000000000 : ℝ) ≤
            (1586281465006013187423 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1365138309684773 / 2000000000000000 : ℝ) ≤ Real.sqrt (1863602604569 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1863602604569 / 4000000000000 : ℝ) ≤ (1706422887105967 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1863602604569 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau660 :
    Real.arctan (3412845774211934 / 11053719210415713 : ℝ) ≤
      (2994656836293116231503 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau659 :
    Real.arctan (1706422887105967 / 2500000000000000 : ℝ) ≤
      (2 * (2994656836293116231503 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6053719210415713 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1706422887105967 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1706422887105967 / 2500000000000000 : ℝ) /
                (1 + (6053719210415713 / 5000000000000000 : ℝ)) =
              (3412845774211934 / 11053719210415713 : ℝ)
            by
        norm_num];
        exact hau660)
  have hat1 :
    (Real.pi / 2 - (2 * (2994656836293116231503 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1706422887105967 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1706422887105967 : ℝ) =
              (1706422887105967 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau659)
  have hz1 :
    (2500000000000000 / 1706422887105967 : ℝ) ≤
      1 / Real.sqrt (1863602604569 / 4000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1706422887105967 : ℝ) = 1 / (1706422887105967 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1365138309684773 : ℝ) ≤
      (68399967749056262157 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1863602604569 / 4000000000000 : ℝ) ≤
      (150000000000000 / 1365138309684773 : ℝ) := by
    rw [show
        (150000000000000 / 1365138309684773 : ℝ) =
          (3 / 40) / (1365138309684773 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2994656836293116231503 / 10000000000000000000000 : ℝ))) -
        6 * (68399967749056262157 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1863602604569 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1863602604569 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1365138309684773 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2994656836293116231503 / 10000000000000000000000 : ℝ))) -
          6 * (68399967749056262157 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (1863602604569 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1863602604569 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1863602604569 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
