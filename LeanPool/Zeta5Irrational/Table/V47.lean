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

/-! # V47: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_565 :
    ((156339399393304630697 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1058494856331202102067 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2014312849883663 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3391110724922073870779 / 10000000000000000000000 : ℝ))) -
              6 * (464081982859780515481 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (20774176036897 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20774176036897 / 32000000000000 : ℝ)) =
      Real.log (52774176036897 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20774176036897 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (20954176036897 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (156339399393304630697 / 312500000000000000000 : ℝ) ≤
      Real.log (52774176036897 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (20954176036897 / 32000000000000 : ℝ) ≤
      (-(1058494856331202102067 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20954176036897 / 32000000000000 : ℝ) = (20954176036897 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20954176036897 / 16000000000000 : ℝ) ≤
            (674373094418797897933 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2014312849883663 / 2500000000000000 : ℝ) ≤ Real.sqrt (20774176036897 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20774176036897 / 32000000000000 : ℝ) ≤ (1611450279906931 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20774176036897 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau902 :
    Real.arctan (8057251399534655 / 22842090955732369 : ℝ) ≤
      (3391110724922073870779 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau901 :
    Real.arctan (1611450279906931 / 2000000000000000 : ℝ) ≤
      (2 * (3391110724922073870779 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12842090955732369 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1611450279906931 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1611450279906931 / 2000000000000000 : ℝ) /
                (1 + (12842090955732369 / 10000000000000000 : ℝ)) =
              (8057251399534655 / 22842090955732369 : ℝ)
            by
        norm_num];
        exact hau902)
  have hat1 :
    (Real.pi / 2 - (2 * (3391110724922073870779 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1611450279906931 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1611450279906931 : ℝ) =
              (1611450279906931 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau901)
  have hz1 :
    (2000000000000000 / 1611450279906931 : ℝ) ≤
      1 / Real.sqrt (20774176036897 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1611450279906931 : ℝ) = 1 / (1611450279906931 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2014312849883663 : ℝ) ≤
      (464081982859780515481 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20774176036897 / 32000000000000 : ℝ) ≤
      (187500000000000 / 2014312849883663 : ℝ) := by
    rw [show
        (187500000000000 / 2014312849883663 : ℝ) =
          (3 / 40) / (2014312849883663 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3391110724922073870779 / 10000000000000000000000 : ℝ))) -
        6 * (464081982859780515481 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20774176036897 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20774176036897 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2014312849883663 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3391110724922073870779 / 10000000000000000000000 : ℝ))) -
          6 * (464081982859780515481 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (20774176036897 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20774176036897 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20774176036897 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_566 :
    ((2507943784957586433653 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4201203176702343280537 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((63051413737327 / 78125000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (169757466539305760399 / 500000000000000000000 : ℝ))) -
              6 * (926639756078741289001 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10421484320917 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10421484320917 / 16000000000000 : ℝ)) =
      Real.log (26421484320917 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10421484320917 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10511484320917 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2507943784957586433653 / 5000000000000000000000 : ℝ) ≤
      Real.log (26421484320917 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10511484320917 / 16000000000000 : ℝ) ≤
      (-(4201203176702343280537 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10511484320917 / 16000000000000 : ℝ) = (10511484320917 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10511484320917 / 8000000000000 : ℝ) ≤
            (2730268626297656719463 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (63051413737327 / 78125000000000 : ℝ) ≤ Real.sqrt (10421484320917 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10421484320917 / 16000000000000 : ℝ) ≤
      (8070580958377859 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10421484320917 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau904 :
    Real.arctan (8070580958377859 / 22850458241079625 : ℝ) ≤
      (169757466539305760399 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau903 :
    Real.arctan (8070580958377859 / 10000000000000000 : ℝ) ≤
      (2 * (169757466539305760399 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (102803665928637 / 80000000000000 : ℝ) ≤
          Real.sqrt (1 + (8070580958377859 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8070580958377859 / 10000000000000000 : ℝ) /
                (1 + (102803665928637 / 80000000000000 : ℝ)) =
              (8070580958377859 / 22850458241079625 : ℝ)
            by
        norm_num];
        exact hau904)
  have hat1 :
    (Real.pi / 2 - (2 * (169757466539305760399 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8070580958377859 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8070580958377859 : ℝ) =
              (8070580958377859 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau903)
  have hz1 :
    (10000000000000000 / 8070580958377859 : ℝ) ≤
      1 / Real.sqrt (10421484320917 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8070580958377859 : ℝ) =
          1 / (8070580958377859 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (5859375000000 / 63051413737327 : ℝ) ≤
      (926639756078741289001 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10421484320917 / 16000000000000 : ℝ) ≤
      (5859375000000 / 63051413737327 : ℝ) := by
    rw [show
        (5859375000000 / 63051413737327 : ℝ) = (3 / 40) / (63051413737327 / 78125000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (169757466539305760399 / 500000000000000000000 : ℝ))) -
        6 * (926639756078741289001 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10421484320917 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10421484320917 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((63051413737327 / 78125000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (169757466539305760399 / 500000000000000000000 : ℝ))) -
          6 * (926639756078741289001 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10421484320917 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10421484320917 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10421484320917 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_567 :
    ((314306088224720380513 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4168534005463306455681 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8083888538083597 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3399176031881748881431 / 10000000000000000000000 : ℝ))) -
              6 * (925123030975232317823 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20911761246771 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (20911761246771 / 32000000000000 : ℝ)) =
      Real.log (52911761246771 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((20911761246771 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21091761246771 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (314306088224720380513 / 625000000000000000000 : ℝ) ≤
      Real.log (52911761246771 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21091761246771 / 32000000000000 : ℝ) ≤
      (-(4168534005463306455681 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21091761246771 / 32000000000000 : ℝ) = (21091761246771 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21091761246771 / 16000000000000 : ℝ) ≤
            (2762937797536693544319 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8083888538083597 / 10000000000000000 : ℝ) ≤
      Real.sqrt (20911761246771 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (20911761246771 / 32000000000000 : ℝ) ≤ (20209721345209 / 25000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (20911761246771 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau906 :
    Real.arctan (8083888538083600 / 22858820081802193 : ℝ) ≤
      (3399176031881748881431 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau905 :
    Real.arctan (20209721345209 / 25000000000000 : ℝ) ≤
      (2 * (3399176031881748881431 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12858820081802193 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (20209721345209 / 25000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (20209721345209 / 25000000000000 : ℝ) /
                (1 + (12858820081802193 / 10000000000000000 : ℝ)) =
              (8083888538083600 / 22858820081802193 : ℝ)
            by
        norm_num];
        exact hau906)
  have hat1 :
    (Real.pi / 2 - (2 * (3399176031881748881431 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (25000000000000 / 20209721345209 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (25000000000000 / 20209721345209 : ℝ) =
              (20209721345209 / 25000000000000 : ℝ)
            by
        norm_num];
        exact hau905)
  have hz1 :
    (25000000000000 / 20209721345209 : ℝ) ≤ 1 / Real.sqrt (20911761246771 / 32000000000000 : ℝ) :=
  by
    rw [show (25000000000000 / 20209721345209 : ℝ) = 1 / (20209721345209 / 25000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8083888538083597 : ℝ) ≤
      (925123030975232317823 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (20911761246771 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8083888538083597 : ℝ) := by
    rw [show
        (750000000000000 / 8083888538083597 : ℝ) =
          (3 / 40) / (8083888538083597 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3399176031881748881431 / 10000000000000000000000 : ℝ))) -
        6 * (925123030975232317823 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (20911761246771 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (20911761246771 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8083888538083597 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3399176031881748881431 / 10000000000000000000000 : ℝ))) -
          6 * (925123030975232317823 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (20911761246771 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (20911761246771 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (20911761246771 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_568 :
    ((1008378069933354245329 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2067985607129381824541 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4048587123509493 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3403190891892478111163 / 10000000000000000000000 : ℝ))) -
              6 * (923613729354546866129 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5245138462927 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5245138462927 / 8000000000000 : ℝ)) =
      Real.log (13245138462927 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5245138462927 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5290138462927 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1008378069933354245329 / 2000000000000000000000 : ℝ) ≤
      Real.log (13245138462927 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5290138462927 / 8000000000000 : ℝ) ≤
      (-(2067985607129381824541 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5290138462927 / 8000000000000 : ℝ) = (5290138462927 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5290138462927 / 4000000000000 : ℝ) ≤
            (1397750294370618175459 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4048587123509493 / 5000000000000000 : ℝ) ≤ Real.sqrt (5245138462927 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5245138462927 / 8000000000000 : ℝ) ≤ (8097174247018989 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5245138462927 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau908 :
    Real.arctan (8097174247018989 / 22867176488514778 : ℝ) ≤
      (3403190891892478111163 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau907 :
    Real.arctan (8097174247018989 / 10000000000000000 : ℝ) ≤
      (2 * (3403190891892478111163 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6433588244257389 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8097174247018989 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8097174247018989 / 10000000000000000 : ℝ) /
                (1 + (6433588244257389 / 5000000000000000 : ℝ)) =
              (8097174247018989 / 22867176488514778 : ℝ)
            by
        norm_num];
        exact hau908)
  have hat1 :
    (Real.pi / 2 - (2 * (3403190891892478111163 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8097174247018989 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8097174247018989 : ℝ) =
              (8097174247018989 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau907)
  have hz1 :
    (10000000000000000 / 8097174247018989 : ℝ) ≤
      1 / Real.sqrt (5245138462927 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8097174247018989 : ℝ) =
          1 / (8097174247018989 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1349529041169831 : ℝ) ≤
      (923613729354546866129 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5245138462927 / 8000000000000 : ℝ) ≤
      (125000000000000 / 1349529041169831 : ℝ) := by
    rw [show
        (125000000000000 / 1349529041169831 : ℝ) =
          (3 / 40) / (4048587123509493 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3403190891892478111163 / 10000000000000000000000 : ℝ))) -
        6 * (923613729354546866129 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5245138462927 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5245138462927 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4048587123509493 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3403190891892478111163 / 10000000000000000000000 : ℝ))) -
          6 * (923613729354546866129 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5245138462927 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5245138462927 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5245138462927 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_569 :
    ((2533912845142745232631 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1017790504105132442423 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8123680481619383 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1705592670410026563051 / 5000000000000000000000 : ℝ))) -
              6 * (920617155808572349771 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10559069530791 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10559069530791 / 16000000000000 : ℝ)) =
      Real.log (26559069530791 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10559069530791 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10649069530791 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2533912845142745232631 / 5000000000000000000000 : ℝ) ≤
      Real.log (26559069530791 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10649069530791 / 16000000000000 : ℝ) ≤
      (-(1017790504105132442423 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10649069530791 / 16000000000000 : ℝ) = (10649069530791 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10649069530791 / 8000000000000 : ℝ) ≤
            (715077446644867557577 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8123680481619383 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10559069530791 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10559069530791 / 16000000000000 : ℝ) ≤ (4061840240809693 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10559069530791 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau910 :
    Real.arctan (8123680481619386 / 22883873042196735 : ℝ) ≤
      (1705592670410026563051 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau909 :
    Real.arctan (4061840240809693 / 5000000000000000 : ℝ) ≤
      (2 * (1705592670410026563051 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2576774608439347 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4061840240809693 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4061840240809693 / 5000000000000000 : ℝ) /
                (1 + (2576774608439347 / 2000000000000000 : ℝ)) =
              (8123680481619386 / 22883873042196735 : ℝ)
            by
        norm_num];
        exact hau910)
  have hat1 :
    (Real.pi / 2 - (2 * (1705592670410026563051 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4061840240809693 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4061840240809693 : ℝ) =
              (4061840240809693 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau909)
  have hz1 :
    (5000000000000000 / 4061840240809693 : ℝ) ≤
      1 / Real.sqrt (10559069530791 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4061840240809693 : ℝ) = 1 / (4061840240809693 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8123680481619383 : ℝ) ≤
      (920617155808572349771 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10559069530791 / 16000000000000 : ℝ) ≤
      (750000000000000 / 8123680481619383 : ℝ) := by
    rw [show
        (750000000000000 / 8123680481619383 : ℝ) =
          (3 / 40) / (8123680481619383 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1705592670410026563051 / 5000000000000000000000 : ℝ))) -
        6 * (920617155808572349771 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10559069530791 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10559069530791 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8123680481619383 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1705592670410026563051 / 5000000000000000000000 : ℝ))) -
          6 * (920617155808572349771 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10559069530791 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10559069530791 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10559069530791 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_570 :
    ((1018738788135635374369 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(801354027725657851151 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8150100511545853 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1709566588411900250929 / 5000000000000000000000 : ℝ))) -
              6 * (9176495607237304067 / 100000000000000000000 : ℝ)))) ≤
      Vfield (664241383483 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (664241383483 / 1000000000000 : ℝ)) =
      Real.log (1664241383483 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((664241383483 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (669866383483 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1018738788135635374369 / 2000000000000000000000 : ℝ) ≤
      Real.log (1664241383483 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (669866383483 / 1000000000000 : ℝ) ≤
      (-(801354027725657851151 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (669866383483 / 1000000000000 : ℝ) = (669866383483 / 500000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (669866383483 / 500000000000 : ℝ) ≤
            (584940332874342148849 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8150100511545853 / 10000000000000000 : ℝ) ≤ Real.sqrt (664241383483 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (664241383483 / 1000000000000 : ℝ) ≤ (15918165061613 / 19531250000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (664241383483 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau912 :
    Real.arctan (8150100511545856 / 22900547986357013 : ℝ) ≤
      (1709566588411900250929 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau911 :
    Real.arctan (15918165061613 / 19531250000000 : ℝ) ≤
      (2 * (1709566588411900250929 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12900547986357013 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (15918165061613 / 19531250000000 : ℝ) ^ 2))
      (by
        rw [show
            (15918165061613 / 19531250000000 : ℝ) /
                (1 + (12900547986357013 / 10000000000000000 : ℝ)) =
              (8150100511545856 / 22900547986357013 : ℝ)
            by
        norm_num];
        exact hau912)
  have hat1 :
    (Real.pi / 2 - (2 * (1709566588411900250929 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (19531250000000 / 15918165061613 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (19531250000000 / 15918165061613 : ℝ) =
              (15918165061613 / 19531250000000 : ℝ)
            by
        norm_num];
        exact hau911)
  have hz1 :
    (19531250000000 / 15918165061613 : ℝ) ≤ 1 / Real.sqrt (664241383483 / 1000000000000 : ℝ) := by
    rw [show (19531250000000 / 15918165061613 : ℝ) = 1 / (15918165061613 / 19531250000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8150100511545853 : ℝ) ≤
      (9176495607237304067 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (664241383483 / 1000000000000 : ℝ) ≤
      (750000000000000 / 8150100511545853 : ℝ) := by
    rw [show
        (750000000000000 / 8150100511545853 : ℝ) =
          (3 / 40) / (8150100511545853 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1709566588411900250929 / 5000000000000000000000 : ℝ))) -
        6 * (9176495607237304067 / 100000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (664241383483 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (664241383483 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8150100511545853 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1709566588411900250929 / 5000000000000000000000 : ℝ))) -
          6 * (9176495607237304067 / 100000000000000000000 : ℝ))) ≤
      Real.sqrt (664241383483 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (664241383483 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (664241383483 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_571 :
    ((510343822688833403141 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(796515710353325413713 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8160048151107357 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1711060181048130356787 / 5000000000000000000000 : ℝ))) -
              6 * (183307428647100260073 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4261528693017 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4261528693017 / 6400000000000 : ℝ)) =
      Real.log (10661528693017 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4261528693017 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4297528693017 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (510343822688833403141 / 1000000000000000000000 : ℝ) ≤
      Real.log (10661528693017 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4297528693017 / 6400000000000 : ℝ) ≤
      (-(796515710353325413713 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4297528693017 / 6400000000000 : ℝ) = (4297528693017 / 3200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4297528693017 / 3200000000000 : ℝ) ≤
            (589778650246674586287 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8160048151107357 / 10000000000000000 : ℝ) ≤ Real.sqrt (4261528693017 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4261528693017 / 6400000000000 : ℝ) ≤ (51000300944421 / 62500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4261528693017 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau914 :
    Real.arctan (32000188827872 / 89830724899411 : ℝ) ≤
      (1711060181048130356787 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau913 :
    Real.arctan (51000300944421 / 62500000000000 : ℝ) ≤
      (2 * (1711060181048130356787 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2581366969869961 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (51000300944421 / 62500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (51000300944421 / 62500000000000 : ℝ) /
                (1 + (2581366969869961 / 2000000000000000 : ℝ)) =
              (32000188827872 / 89830724899411 : ℝ)
            by
        norm_num];
        exact hau914)
  have hat1 :
    (Real.pi / 2 - (2 * (1711060181048130356787 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (62500000000000 / 51000300944421 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (62500000000000 / 51000300944421 : ℝ) =
              (51000300944421 / 62500000000000 : ℝ)
            by
        norm_num];
        exact hau913)
  have hz1 :
    (62500000000000 / 51000300944421 : ℝ) ≤ 1 / Real.sqrt (4261528693017 / 6400000000000 : ℝ) := by
    rw [show (62500000000000 / 51000300944421 : ℝ) = 1 / (51000300944421 / 62500000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2720016050369119 : ℝ) ≤
      (183307428647100260073 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4261528693017 / 6400000000000 : ℝ) ≤
      (250000000000000 / 2720016050369119 : ℝ) := by
    rw [show
        (250000000000000 / 2720016050369119 : ℝ) =
          (3 / 40) / (8160048151107357 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1711060181048130356787 / 5000000000000000000000 : ℝ))) -
        6 * (183307428647100260073 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4261528693017 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4261528693017 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8160048151107357 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1711060181048130356787 / 5000000000000000000000 : ℝ))) -
          6 * (183307428647100260073 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (4261528693017 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4261528693017 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4261528693017 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_572 :
    ((5113173027229668871761 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(791689069397068086157 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8169983678593319 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (428137625724666504333 / 1250000000000000000000 : ℝ))) -
              6 * (915428761561533214527 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (10679781329357 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (10679781329357 / 16000000000000 : ℝ)) =
      Real.log (26679781329357 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((10679781329357 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10769781329357 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5113173027229668871761 / 10000000000000000000000 : ℝ) ≤
      Real.log (26679781329357 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10769781329357 / 16000000000000 : ℝ) ≤
      (-(791689069397068086157 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10769781329357 / 16000000000000 : ℝ) = (10769781329357 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10769781329357 / 8000000000000 : ℝ) ≤
            (594605291202931913843 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8169983678593319 / 10000000000000000 : ℝ) ≤
      Real.sqrt (10679781329357 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (10679781329357 / 16000000000000 : ℝ) ≤ (4084991839296661 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (10679781329357 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau916 :
    Real.arctan (4084991839296661 / 11456559325764792 : ℝ) ≤
      (428137625724666504333 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau915 :
    Real.arctan (4084991839296661 / 5000000000000000 : ℝ) ≤
      (2 * (428137625724666504333 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (807069915720599 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (4084991839296661 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4084991839296661 / 5000000000000000 : ℝ) /
                (1 + (807069915720599 / 625000000000000 : ℝ)) =
              (4084991839296661 / 11456559325764792 : ℝ)
            by
        norm_num];
        exact hau916)
  have hat1 :
    (Real.pi / 2 - (2 * (428137625724666504333 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4084991839296661 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4084991839296661 : ℝ) =
              (4084991839296661 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau915)
  have hz1 :
    (5000000000000000 / 4084991839296661 : ℝ) ≤
      1 / Real.sqrt (10679781329357 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4084991839296661 : ℝ) = 1 / (4084991839296661 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8169983678593319 : ℝ) ≤
      (915428761561533214527 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (10679781329357 / 16000000000000 : ℝ) ≤
      (750000000000000 / 8169983678593319 : ℝ) := by
    rw [show
        (750000000000000 / 8169983678593319 : ℝ) =
          (3 / 40) / (8169983678593319 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (428137625724666504333 / 1250000000000000000000 : ℝ))) -
        6 * (915428761561533214527 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (10679781329357 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (10679781329357 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8169983678593319 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (428137625724666504333 / 1250000000000000000000 : ℝ))) -
          6 * (915428761561533214527 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (10679781329357 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (10679781329357 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (10679781329357 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_573 :
    ((5122898360152830778087 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1967185121586613830879 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8179907138138663 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3428075133878351375991 / 10000000000000000000000 : ℝ))) -
              6 * (3571579653740407077 / 39062500000000000000 : ℝ)))) ≤
      Vfield (21411481852343 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21411481852343 / 32000000000000 : ℝ)) =
      Real.log (53411481852343 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21411481852343 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21591481852343 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5122898360152830778087 / 10000000000000000000000 : ℝ) ≤
      Real.log (53411481852343 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21591481852343 / 32000000000000 : ℝ) ≤
      (-(1967185121586613830879 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21591481852343 / 32000000000000 : ℝ) = (21591481852343 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21591481852343 / 16000000000000 : ℝ) ≤
            (1498550779913386169121 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8179907138138663 / 10000000000000000 : ℝ) ≤
      Real.sqrt (21411481852343 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21411481852343 / 32000000000000 : ℝ) ≤ (4089953569069333 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21411481852343 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau918 :
    Real.arctan (584279081295619 / 1637099956954468 : ℝ) ≤
      (3428075133878351375991 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau917 :
    Real.arctan (4089953569069333 / 5000000000000000 : ℝ) ≤
      (2 * (3428075133878351375991 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1614924924670319 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (4089953569069333 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4089953569069333 / 5000000000000000 : ℝ) /
                (1 + (1614924924670319 / 1250000000000000 : ℝ)) =
              (584279081295619 / 1637099956954468 : ℝ)
            by
        norm_num];
        exact hau918)
  have hat1 :
    (Real.pi / 2 - (2 * (3428075133878351375991 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4089953569069333 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4089953569069333 : ℝ) =
              (4089953569069333 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau917)
  have hz1 :
    (5000000000000000 / 4089953569069333 : ℝ) ≤
      1 / Real.sqrt (21411481852343 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4089953569069333 : ℝ) = 1 / (4089953569069333 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8179907138138663 : ℝ) ≤
      (3571579653740407077 / 39062500000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21411481852343 / 32000000000000 : ℝ) ≤
      (750000000000000 / 8179907138138663 : ℝ) := by
    rw [show
        (750000000000000 / 8179907138138663 : ℝ) =
          (3 / 40) / (8179907138138663 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3428075133878351375991 / 10000000000000000000000 : ℝ))) -
        6 * (3571579653740407077 / 39062500000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21411481852343 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21411481852343 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8179907138138663 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3428075133878351375991 / 10000000000000000000000 : ℝ))) -
          6 * (3571579653740407077 / 39062500000000000000 : ℝ))) ≤
      Real.sqrt (21411481852343 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21411481852343 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21411481852343 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_574 :
    ((320788390253418113291 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1955176480622274021633 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2047454643402731 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (85776069303373838337 / 250000000000000000000 : ℝ))) -
              6 * (182644801696868735909 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (5365850261493 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5365850261493 / 8000000000000 : ℝ)) =
      Real.log (13365850261493 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5365850261493 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5410850261493 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (320788390253418113291 / 625000000000000000000 : ℝ) ≤
      Real.log (13365850261493 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5410850261493 / 8000000000000 : ℝ) ≤
      (-(1955176480622274021633 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5410850261493 / 8000000000000 : ℝ) = (5410850261493 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5410850261493 / 4000000000000 : ℝ) ≤
            (1510559420877725978367 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2047454643402731 / 2500000000000000 : ℝ) ≤ Real.sqrt (5365850261493 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5365850261493 / 8000000000000 : ℝ) ≤ (8189818573610927 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5365850261493 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau920 :
    Real.arctan (8189818573610927 / 22925677091304056 : ℝ) ≤
      (85776069303373838337 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau919 :
    Real.arctan (8189818573610927 / 10000000000000000 : ℝ) ≤
      (2 * (85776069303373838337 / 250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1615709636413007 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (8189818573610927 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8189818573610927 / 10000000000000000 : ℝ) /
                (1 + (1615709636413007 / 1250000000000000 : ℝ)) =
              (8189818573610927 / 22925677091304056 : ℝ)
            by
        norm_num];
        exact hau920)
  have hat1 :
    (Real.pi / 2 - (2 * (85776069303373838337 / 250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8189818573610927 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8189818573610927 : ℝ) =
              (8189818573610927 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau919)
  have hz1 :
    (10000000000000000 / 8189818573610927 : ℝ) ≤
      1 / Real.sqrt (5365850261493 / 8000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8189818573610927 : ℝ) =
          1 / (8189818573610927 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2047454643402731 : ℝ) ≤
      (182644801696868735909 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5365850261493 / 8000000000000 : ℝ) ≤
      (187500000000000 / 2047454643402731 : ℝ) := by
    rw [show
        (187500000000000 / 2047454643402731 : ℝ) =
          (3 / 40) / (2047454643402731 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (85776069303373838337 / 250000000000000000000 : ℝ))) -
        6 * (182644801696868735909 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5365850261493 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5365850261493 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2047454643402731 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (85776069303373838337 / 250000000000000000000 : ℝ))) -
          6 * (182644801696868735909 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (5365850261493 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5365850261493 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5365850261493 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_575 :
    ((5142320697278545517473 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3886393224119610109169 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4099859014306257 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (686800789241670516879 / 2000000000000000000000 : ℝ))) -
              6 * (114015948625701972549 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (21515320239601 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21515320239601 / 32000000000000 : ℝ)) =
      Real.log (53515320239601 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21515320239601 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (21695320239601 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5142320697278545517473 / 10000000000000000000000 : ℝ) ≤
      Real.log (53515320239601 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (21695320239601 / 32000000000000 : ℝ) ≤
      (-(3886393224119610109169 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21695320239601 / 32000000000000 : ℝ) = (21695320239601 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21695320239601 / 16000000000000 : ℝ) ≤
            (3045078578880389890831 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4099859014306257 / 5000000000000000 : ℝ) ≤ Real.sqrt (21515320239601 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (21515320239601 / 32000000000000 : ℝ) ≤
      (8199718028612517 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21515320239601 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau922 :
    Real.arctan (8199718028612517 / 22931951737798634 : ℝ) ≤
      (686800789241670516879 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau921 :
    Real.arctan (8199718028612517 / 10000000000000000 : ℝ) ≤
      (2 * (686800789241670516879 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6465975868899317 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8199718028612517 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8199718028612517 / 10000000000000000 : ℝ) /
                (1 + (6465975868899317 / 5000000000000000 : ℝ)) =
              (8199718028612517 / 22931951737798634 : ℝ)
            by
        norm_num];
        exact hau922)
  have hat1 :
    (Real.pi / 2 - (2 * (686800789241670516879 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8199718028612517 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8199718028612517 : ℝ) =
              (8199718028612517 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau921)
  have hz1 :
    (10000000000000000 / 8199718028612517 : ℝ) ≤
      1 / Real.sqrt (21515320239601 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8199718028612517 : ℝ) =
          1 / (8199718028612517 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1366619671435419 : ℝ) ≤
      (114015948625701972549 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (21515320239601 / 32000000000000 : ℝ) ≤
      (125000000000000 / 1366619671435419 : ℝ) := by
    rw [show
        (125000000000000 / 1366619671435419 : ℝ) =
          (3 / 40) / (4099859014306257 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (686800789241670516879 / 2000000000000000000000 : ℝ))) -
        6 * (114015948625701972549 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21515320239601 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21515320239601 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4099859014306257 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (686800789241670516879 / 2000000000000000000000 : ℝ))) -
          6 * (114015948625701972549 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (21515320239601 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21515320239601 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21515320239601 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_576 :
    ((5147170393103906195523 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1937217424407472507173 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8204663276990617 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1717741058573659101171 / 5000000000000000000000 : ℝ))) -
              6 * (911580858114015239713 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (43082559672831 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (43082559672831 / 64000000000000 : ℝ)) =
      Real.log (107082559672831 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((43082559672831 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (43442559672831 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5147170393103906195523 / 10000000000000000000000 : ℝ) ≤
      Real.log (107082559672831 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (43442559672831 / 64000000000000 : ℝ) ≤
      (-(1937217424407472507173 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43442559672831 / 64000000000000 : ℝ) = (43442559672831 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43442559672831 / 32000000000000 : ℝ) ≤
            (1528518477092527492827 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8204663276990617 / 10000000000000000 : ℝ) ≤
      Real.sqrt (43082559672831 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (43082559672831 / 64000000000000 : ℝ) ≤ (410233163849531 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (43082559672831 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau924 :
    Real.arctan (1640932655398124 / 4587017583927859 : ℝ) ≤
      (1717741058573659101171 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau923 :
    Real.arctan (410233163849531 / 500000000000000 : ℝ) ≤
      (2 * (1717741058573659101171 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2587017583927859 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (410233163849531 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (410233163849531 / 500000000000000 : ℝ) /
                (1 + (2587017583927859 / 2000000000000000 : ℝ)) =
              (1640932655398124 / 4587017583927859 : ℝ)
            by
        norm_num];
        exact hau924)
  have hat1 :
    (Real.pi / 2 - (2 * (1717741058573659101171 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 410233163849531 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 410233163849531 : ℝ) =
              (410233163849531 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau923)
  have hz1 :
    (500000000000000 / 410233163849531 : ℝ) ≤
      1 / Real.sqrt (43082559672831 / 64000000000000 : ℝ) := by
    rw [show (500000000000000 / 410233163849531 : ℝ) = 1 / (410233163849531 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8204663276990617 : ℝ) ≤
      (911580858114015239713 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (43082559672831 / 64000000000000 : ℝ) ≤
      (750000000000000 / 8204663276990617 : ℝ) := by
    rw [show
        (750000000000000 / 8204663276990617 : ℝ) =
          (3 / 40) / (8204663276990617 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1717741058573659101171 / 5000000000000000000000 : ℝ))) -
        6 * (911580858114015239713 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (43082559672831 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (43082559672831 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8204663276990617 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1717741058573659101171 / 5000000000000000000000 : ℝ))) -
          6 * (911580858114015239713 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (43082559672831 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (43082559672831 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (43082559672831 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
