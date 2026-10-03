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

/-! # V50: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_601 :
    ((5267654647466773897281 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(895007670617208076217 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4163670045462633 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (138876894475193245607 / 400000000000000000000 : ℝ))) -
              6 * (898224269702467027377 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11095134878389 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11095134878389 / 16000000000000 : ℝ)) =
      Real.log (27095134878389 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11095134878389 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11185134878389 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5267654647466773897281 / 10000000000000000000000 : ℝ) ≤
      Real.log (27095134878389 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11185134878389 / 16000000000000 : ℝ) ≤
      (-(895007670617208076217 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11185134878389 / 16000000000000 : ℝ) = (11185134878389 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11185134878389 / 8000000000000 : ℝ) ≤
            (837860280132791923783 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4163670045462633 / 5000000000000000 : ℝ) ≤ Real.sqrt (11095134878389 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11095134878389 / 16000000000000 : ℝ) ≤
      (8327340090925269 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11095134878389 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau974 :
    Real.arctan (2775780030308423 / 7671082275788410 : ℝ) ≤
      (138876894475193245607 / 400000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau973 :
    Real.arctan (8327340090925269 / 10000000000000000 : ℝ) ≤
      (2 * (138876894475193245607 / 400000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1301324682736523 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8327340090925269 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8327340090925269 / 10000000000000000 : ℝ) /
                (1 + (1301324682736523 / 1000000000000000 : ℝ)) =
              (2775780030308423 / 7671082275788410 : ℝ)
            by
        norm_num];
        exact hau974)
  have hat1 :
    (Real.pi / 2 - (2 * (138876894475193245607 / 400000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8327340090925269 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8327340090925269 : ℝ) =
              (8327340090925269 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau973)
  have hz1 :
    (10000000000000000 / 8327340090925269 : ℝ) ≤
      1 / Real.sqrt (11095134878389 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8327340090925269 : ℝ) =
          1 / (8327340090925269 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1387890015154211 : ℝ) ≤
      (898224269702467027377 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11095134878389 / 16000000000000 : ℝ) ≤
      (125000000000000 / 1387890015154211 : ℝ) := by
    rw [show
        (125000000000000 / 1387890015154211 : ℝ) =
          (3 / 40) / (4163670045462633 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (138876894475193245607 / 400000000000000000000 : ℝ))) -
        6 * (898224269702467027377 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11095134878389 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11095134878389 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4163670045462633 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (138876894475193245607 / 400000000000000000000 : ℝ))) -
          6 * (898224269702467027377 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11095134878389 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11095134878389 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11095134878389 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_602 :
    ((5272443953924180262591 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1784216451385933877829 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2083052398674487 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1736679883824976458027 / 5000000000000000000000 : ℝ))) -
              6 * (897702146630215959721 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (8886491741437 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8886491741437 / 12800000000000 : ℝ)) =
      Real.log (21686491741437 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8886491741437 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8958491741437 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5272443953924180262591 / 10000000000000000000000 : ℝ) ≤
      Real.log (21686491741437 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8958491741437 / 12800000000000 : ℝ) ≤
      (-(1784216451385933877829 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8958491741437 / 12800000000000 : ℝ) = (8958491741437 / 6400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8958491741437 / 6400000000000 : ℝ) ≤
            (1681519450114066122171 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2083052398674487 / 2500000000000000 : ℝ) ≤ Real.sqrt (8886491741437 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8886491741437 / 12800000000000 : ℝ) ≤ (8332209594697951 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8886491741437 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau976 :
    Real.arctan (490129976158703 / 1353903730697741 : ℝ) ≤
      (1736679883824976458027 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau975 :
    Real.arctan (8332209594697951 / 10000000000000000 : ℝ) ≤
      (2 * (1736679883824976458027 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13016363421861597 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8332209594697951 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8332209594697951 / 10000000000000000 : ℝ) /
                (1 + (13016363421861597 / 10000000000000000 : ℝ)) =
              (490129976158703 / 1353903730697741 : ℝ)
            by
        norm_num];
        exact hau976)
  have hat1 :
    (Real.pi / 2 - (2 * (1736679883824976458027 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8332209594697951 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8332209594697951 : ℝ) =
              (8332209594697951 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau975)
  have hz1 :
    (10000000000000000 / 8332209594697951 : ℝ) ≤
      1 / Real.sqrt (8886491741437 / 12800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8332209594697951 : ℝ) =
          1 / (8332209594697951 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2083052398674487 : ℝ) ≤
      (897702146630215959721 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8886491741437 / 12800000000000 : ℝ) ≤
      (187500000000000 / 2083052398674487 : ℝ) := by
    rw [show
        (187500000000000 / 2083052398674487 : ℝ) =
          (3 / 40) / (2083052398674487 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1736679883824976458027 / 5000000000000000000000 : ℝ))) -
        6 * (897702146630215959721 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8886491741437 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8886491741437 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2083052398674487 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1736679883824976458027 / 5000000000000000000000 : ℝ))) -
          6 * (897702146630215959721 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (8886491741437 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8886491741437 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8886491741437 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_603 :
    ((5277230967733927753499 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(111151517448245887379 / 312500000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1042134531787567 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (434349455772083549517 / 1250000000000000000000 : ℝ))) -
              6 * (897180933010781682679 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22242188950407 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22242188950407 / 32000000000000 : ℝ)) =
      Real.log (54242188950407 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22242188950407 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22422188950407 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5277230967733927753499 / 10000000000000000000000 : ℝ) ≤
      Real.log (54242188950407 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22422188950407 / 32000000000000 : ℝ) ≤
      (-(111151517448245887379 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22422188950407 / 32000000000000 : ℝ) = (22422188950407 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22422188950407 / 16000000000000 : ℝ) ≤
            (105456976395504112621 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1042134531787567 / 1250000000000000 : ℝ) ≤ Real.sqrt (22242188950407 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22242188950407 / 32000000000000 : ℝ) ≤
      (8337076254300539 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22242188950407 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau978 :
    Real.arctan (8337076254300539 / 23019479270309618 : ℝ) ≤
      (434349455772083549517 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau977 :
    Real.arctan (8337076254300539 / 10000000000000000 : ℝ) ≤
      (2 * (434349455772083549517 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6509739635154809 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8337076254300539 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8337076254300539 / 10000000000000000 : ℝ) /
                (1 + (6509739635154809 / 5000000000000000 : ℝ)) =
              (8337076254300539 / 23019479270309618 : ℝ)
            by
        norm_num];
        exact hau978)
  have hat1 :
    (Real.pi / 2 - (2 * (434349455772083549517 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8337076254300539 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8337076254300539 : ℝ) =
              (8337076254300539 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau977)
  have hz1 :
    (10000000000000000 / 8337076254300539 : ℝ) ≤
      1 / Real.sqrt (22242188950407 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8337076254300539 : ℝ) =
          1 / (8337076254300539 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 1042134531787567 : ℝ) ≤
      (897180933010781682679 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22242188950407 / 32000000000000 : ℝ) ≤
      (93750000000000 / 1042134531787567 : ℝ) := by
    rw [show
        (93750000000000 / 1042134531787567 : ℝ) =
          (3 / 40) / (1042134531787567 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (434349455772083549517 / 1250000000000000000000 : ℝ))) -
        6 * (897180933010781682679 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22242188950407 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22242188950407 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1042134531787567 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (434349455772083549517 / 1250000000000000000000 : ℝ))) -
          6 * (897180933010781682679 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22242188950407 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22242188950407 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22242188950407 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_604 :
    ((5286798126183046578949 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3533720051035585403877 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8346801060892279 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3477662833209266870603 / 10000000000000000000000 : ℝ))) -
              6 * (448070611796229685211 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5573527036009 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5573527036009 / 8000000000000 : ℝ)) =
      Real.log (13573527036009 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5573527036009 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5618527036009 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5286798126183046578949 / 10000000000000000000000 : ℝ) ≤
      Real.log (13573527036009 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5618527036009 / 8000000000000 : ℝ) ≤
      (-(3533720051035585403877 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5618527036009 / 8000000000000 : ℝ) = (5618527036009 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5618527036009 / 4000000000000 : ℝ) ≤
            (3397751751964414596123 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8346801060892279 / 10000000000000000 : ℝ) ≤ Real.sqrt (5573527036009 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5573527036009 / 8000000000000 : ℝ) ≤ (4173400530446141 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5573527036009 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau980 :
    Real.arctan (4173400530446141 / 11512854365601009 : ℝ) ≤
      (3477662833209266870603 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau979 :
    Real.arctan (4173400530446141 / 5000000000000000 : ℝ) ≤
      (2 * (3477662833209266870603 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6512854365601009 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4173400530446141 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4173400530446141 / 5000000000000000 : ℝ) /
                (1 + (6512854365601009 / 5000000000000000 : ℝ)) =
              (4173400530446141 / 11512854365601009 : ℝ)
            by
        norm_num];
        exact hau980)
  have hat1 :
    (Real.pi / 2 - (2 * (3477662833209266870603 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4173400530446141 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4173400530446141 : ℝ) =
              (4173400530446141 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau979)
  have hz1 :
    (5000000000000000 / 4173400530446141 : ℝ) ≤
      1 / Real.sqrt (5573527036009 / 8000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4173400530446141 : ℝ) = 1 / (4173400530446141 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8346801060892279 : ℝ) ≤
      (448070611796229685211 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5573527036009 / 8000000000000 : ℝ) ≤
      (750000000000000 / 8346801060892279 : ℝ) := by
    rw [show
        (750000000000000 / 8346801060892279 : ℝ) =
          (3 / 40) / (8346801060892279 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3477662833209266870603 / 10000000000000000000000 : ℝ))) -
        6 * (448070611796229685211 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5573527036009 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5573527036009 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8346801060892279 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3477662833209266870603 / 10000000000000000000000 : ℝ))) -
          6 * (448070611796229685211 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (5573527036009 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5573527036009 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5573527036009 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_605 :
    ((5296356140327890318239 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3510644913100674866389 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1044564318793689 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3480523946311819555931 / 10000000000000000000000 : ℝ))) -
              6 * (111888140059786550771 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (4469205467533 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4469205467533 / 6400000000000 : ℝ)) =
      Real.log (10869205467533 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4469205467533 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4505205467533 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5296356140327890318239 / 10000000000000000000000 : ℝ) ≤
      Real.log (10869205467533 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4505205467533 / 6400000000000 : ℝ) ≤
      (-(3510644913100674866389 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (4505205467533 / 6400000000000 : ℝ) = (4505205467533 / 3200000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4505205467533 / 3200000000000 : ℝ) ≤
            (3420826889899325133611 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1044564318793689 / 1250000000000000 : ℝ) ≤ Real.sqrt (4469205467533 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4469205467533 / 6400000000000 : ℝ) ≤ (1671302910069903 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4469205467533 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau982 :
    Real.arctan (2785504850116505 / 7677311738106276 : ℝ) ≤
      (3480523946311819555931 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau981 :
    Real.arctan (1671302910069903 / 2000000000000000 : ℝ) ≤
      (2 * (3480523946311819555931 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3257983803579707 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1671302910069903 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1671302910069903 / 2000000000000000 : ℝ) /
                (1 + (3257983803579707 / 2500000000000000 : ℝ)) =
              (2785504850116505 / 7677311738106276 : ℝ)
            by
        norm_num];
        exact hau982)
  have hat1 :
    (Real.pi / 2 - (2 * (3480523946311819555931 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1671302910069903 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1671302910069903 : ℝ) =
              (1671302910069903 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau981)
  have hz1 :
    (2000000000000000 / 1671302910069903 : ℝ) ≤
      1 / Real.sqrt (4469205467533 / 6400000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1671302910069903 : ℝ) = 1 / (1671302910069903 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 348188106264563 : ℝ) ≤
      (111888140059786550771 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4469205467533 / 6400000000000 : ℝ) ≤
      (31250000000000 / 348188106264563 : ℝ) := by
    rw [show
        (31250000000000 / 348188106264563 : ℝ) =
          (3 / 40) / (1044564318793689 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3480523946311819555931 / 10000000000000000000000 : ℝ))) -
        6 * (111888140059786550771 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4469205467533 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4469205467533 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1044564318793689 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3480523946311819555931 / 10000000000000000000000 : ℝ))) -
          6 * (111888140059786550771 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (4469205467533 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4469205467533 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4469205467533 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_606 :
    ((5305905027632047828519 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3487622898804823612337 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4183108381045539 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (870844752170985371119 / 2500000000000000000000 : ℝ))) -
              6 * (894072602868394696077 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11198973265647 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11198973265647 / 16000000000000 : ℝ)) =
      Real.log (27198973265647 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11198973265647 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11288973265647 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5305905027632047828519 / 10000000000000000000000 : ℝ) ≤
      Real.log (27198973265647 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11288973265647 / 16000000000000 : ℝ) ≤
      (-(3487622898804823612337 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (11288973265647 / 16000000000000 : ℝ) = (11288973265647 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11288973265647 / 8000000000000 : ℝ) ≤
            (3443848904195176387663 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4183108381045539 / 5000000000000000 : ℝ) ≤ Real.sqrt (11198973265647 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11198973265647 / 16000000000000 : ℝ) ≤
      (8366216762091081 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11198973265647 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau984 :
    Real.arctan (8366216762091081 / 23038158723926233 : ℝ) ≤
      (870844752170985371119 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau983 :
    Real.arctan (8366216762091081 / 10000000000000000 : ℝ) ≤
      (2 * (870844752170985371119 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13038158723926233 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8366216762091081 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8366216762091081 / 10000000000000000 : ℝ) /
                (1 + (13038158723926233 / 10000000000000000 : ℝ)) =
              (8366216762091081 / 23038158723926233 : ℝ)
            by
        norm_num];
        exact hau984)
  have hat1 :
    (Real.pi / 2 - (2 * (870844752170985371119 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8366216762091081 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8366216762091081 : ℝ) =
              (8366216762091081 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau983)
  have hz1 :
    (10000000000000000 / 8366216762091081 : ℝ) ≤
      1 / Real.sqrt (11198973265647 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8366216762091081 : ℝ) =
          1 / (8366216762091081 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1394369460348513 : ℝ) ≤
      (894072602868394696077 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11198973265647 / 16000000000000 : ℝ) ≤
      (125000000000000 / 1394369460348513 : ℝ) := by
    rw [show
        (125000000000000 / 1394369460348513 : ℝ) =
          (3 / 40) / (4183108381045539 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (870844752170985371119 / 2500000000000000000000 : ℝ))) -
        6 * (894072602868394696077 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11198973265647 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11198973265647 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4183108381045539 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (870844752170985371119 / 2500000000000000000000 : ℝ))) -
          6 * (894072602868394696077 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11198973265647 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11198973265647 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11198973265647 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_607 :
    ((332215300344320520497 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(866163441026753018953 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6543677918209 / 7812500000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3486228043391734482853 / 10000000000000000000000 : ℝ))) -
              6 * (446521825065223545333 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (22449865724923 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22449865724923 / 32000000000000 : ℝ)) =
      Real.log (54449865724923 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22449865724923 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22629865724923 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (332215300344320520497 / 625000000000000000000 : ℝ) ≤
      Real.log (54449865724923 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22629865724923 / 32000000000000 : ℝ) ≤
      (-(866163441026753018953 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22629865724923 / 32000000000000 : ℝ) = (22629865724923 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22629865724923 / 16000000000000 : ℝ) ≤
            (866704509723246981047 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6543677918209 / 7812500000000 : ℝ) ≤ Real.sqrt (22449865724923 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22449865724923 / 32000000000000 : ℝ) ≤
      (8375907735307523 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22449865724923 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau986 :
    Real.arctan (8375907735307523 / 23044379264280242 : ℝ) ≤
      (3486228043391734482853 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau985 :
    Real.arctan (8375907735307523 / 10000000000000000 : ℝ) ≤
      (2 * (3486228043391734482853 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6522189632140121 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8375907735307523 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8375907735307523 / 10000000000000000 : ℝ) /
                (1 + (6522189632140121 / 5000000000000000 : ℝ)) =
              (8375907735307523 / 23044379264280242 : ℝ)
            by
        norm_num];
        exact hau986)
  have hat1 :
    (Real.pi / 2 - (2 * (3486228043391734482853 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8375907735307523 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8375907735307523 : ℝ) =
              (8375907735307523 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau985)
  have hz1 :
    (10000000000000000 / 8375907735307523 : ℝ) ≤
      1 / Real.sqrt (22449865724923 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8375907735307523 : ℝ) =
          1 / (8375907735307523 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (585937500000 / 6543677918209 : ℝ) ≤
      (446521825065223545333 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22449865724923 / 32000000000000 : ℝ) ≤
      (585937500000 / 6543677918209 : ℝ) := by
    rw [show (585937500000 / 6543677918209 : ℝ) = (3 / 40) / (6543677918209 / 7812500000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3486228043391734482853 / 10000000000000000000000 : ℝ))) -
        6 * (446521825065223545333 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22449865724923 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22449865724923 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6543677918209 / 7812500000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3486228043391734482853 / 10000000000000000000000 : ℝ))) -
          6 * (446521825065223545333 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (22449865724923 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22449865724923 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22449865724923 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_608 :
    ((1064995098264590386373 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3441737266643992525549 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8385587508962921 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3489071073368835962193 / 10000000000000000000000 : ℝ))) -
              6 * (892018241797966445617 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2812723114819 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2812723114819 / 4000000000000 : ℝ)) =
      Real.log (6812723114819 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2812723114819 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2835223114819 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1064995098264590386373 / 2000000000000000000000 : ℝ) ≤
      Real.log (6812723114819 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2835223114819 / 4000000000000 : ℝ) ≤
      (-(3441737266643992525549 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2835223114819 / 4000000000000 : ℝ) = (2835223114819 / 2000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2835223114819 / 2000000000000 : ℝ) ≤
            (3489734536356007474451 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8385587508962921 / 10000000000000000 : ℝ) ≤ Real.sqrt (2812723114819 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2812723114819 / 4000000000000 : ℝ) ≤ (2096396877240731 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2812723114819 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau988 :
    Real.arctan (4192793754481462 / 11525298419813361 : ℝ) ≤
      (3489071073368835962193 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau987 :
    Real.arctan (2096396877240731 / 2500000000000000 : ℝ) ≤
      (2 * (3489071073368835962193 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6525298419813361 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2096396877240731 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2096396877240731 / 2500000000000000 : ℝ) /
                (1 + (6525298419813361 / 5000000000000000 : ℝ)) =
              (4192793754481462 / 11525298419813361 : ℝ)
            by
        norm_num];
        exact hau988)
  have hat1 :
    (Real.pi / 2 - (2 * (3489071073368835962193 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2096396877240731 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2096396877240731 : ℝ) =
              (2096396877240731 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau987)
  have hz1 :
    (2500000000000000 / 2096396877240731 : ℝ) ≤
      1 / Real.sqrt (2812723114819 / 4000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 2096396877240731 : ℝ) = 1 / (2096396877240731 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 8385587508962921 : ℝ) ≤
      (892018241797966445617 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2812723114819 / 4000000000000 : ℝ) ≤
      (750000000000000 / 8385587508962921 : ℝ) := by
    rw [show
        (750000000000000 / 8385587508962921 : ℝ) =
          (3 / 40) / (8385587508962921 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3489071073368835962193 / 10000000000000000000000 : ℝ))) -
        6 * (892018241797966445617 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2812723114819 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2812723114819 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8385587508962921 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3489071073368835962193 / 10000000000000000000000 : ℝ))) -
          6 * (892018241797966445617 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2812723114819 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2812723114819 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2812723114819 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_609 :
    ((5334497102387739281797 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3418873165714944740207 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4197628060898369 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3491908121417462665577 / 10000000000000000000000 : ℝ))) -
              6 * (890996357568595104887 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22553704112181 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22553704112181 / 32000000000000 : ℝ)) =
      Real.log (54553704112181 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22553704112181 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22733704112181 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (5334497102387739281797 / 10000000000000000000000 : ℝ) ≤
      Real.log (54553704112181 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22733704112181 / 32000000000000 : ℝ) ≤
      (-(3418873165714944740207 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22733704112181 / 32000000000000 : ℝ) = (22733704112181 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22733704112181 / 16000000000000 : ℝ) ≤
            (3512598637285055259793 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (4197628060898369 / 5000000000000000 : ℝ) ≤ Real.sqrt (22553704112181 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22553704112181 / 32000000000000 : ℝ) ≤
      (8395256121796741 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22553704112181 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau990 :
    Real.arctan (8395256121796741 / 23056811454201428 : ℝ) ≤
      (3491908121417462665577 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau989 :
    Real.arctan (8395256121796741 / 10000000000000000 : ℝ) ≤
      (2 * (3491908121417462665577 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3264202863550357 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8395256121796741 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8395256121796741 / 10000000000000000 : ℝ) /
                (1 + (3264202863550357 / 2500000000000000 : ℝ)) =
              (8395256121796741 / 23056811454201428 : ℝ)
            by
        norm_num];
        exact hau990)
  have hat1 :
    (Real.pi / 2 - (2 * (3491908121417462665577 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8395256121796741 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8395256121796741 : ℝ) =
              (8395256121796741 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau989)
  have hz1 :
    (10000000000000000 / 8395256121796741 : ℝ) ≤
      1 / Real.sqrt (22553704112181 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8395256121796741 : ℝ) =
          1 / (8395256121796741 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 4197628060898369 : ℝ) ≤
      (890996357568595104887 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22553704112181 / 32000000000000 : ℝ) ≤
      (375000000000000 / 4197628060898369 : ℝ) := by
    rw [show
        (375000000000000 / 4197628060898369 : ℝ) =
          (3 / 40) / (4197628060898369 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3491908121417462665577 / 10000000000000000000000 : ℝ))) -
        6 * (890996357568595104887 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22553704112181 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22553704112181 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4197628060898369 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3491908121417462665577 / 10000000000000000000000 : ℝ))) -
          6 * (890996357568595104887 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22553704112181 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22553704112181 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22553704112181 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_610 :
    ((2672004827984150136307 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(339606122226630670097 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8404913612325603 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3494739210209437387999 / 10000000000000000000000 : ℝ))) -
              6 * (889977977302413373633 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2260562330581 / 3200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2260562330581 / 3200000000000 : ℝ)) =
      Real.log (5460562330581 / 3200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2260562330581 / 3200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2278562330581 / 3200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2672004827984150136307 / 5000000000000000000000 : ℝ) ≤
      Real.log (5460562330581 / 3200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2278562330581 / 3200000000000 : ℝ) ≤
      (-(339606122226630670097 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (2278562330581 / 3200000000000 : ℝ) = (2278562330581 / 1600000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2278562330581 / 1600000000000 : ℝ) ≤
            (353541058073369329903 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8404913612325603 / 10000000000000000 : ℝ) ≤ Real.sqrt (2260562330581 / 3200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2260562330581 / 3200000000000 : ℝ) ≤ (4202456806162803 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2260562330581 / 3200000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau992 :
    Real.arctan (2801637870775202 / 7687674370743347 : ℝ) ≤
      (3494739210209437387999 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau991 :
    Real.arctan (4202456806162803 / 5000000000000000 : ℝ) ≤
      (2 * (3494739210209437387999 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13063023112230041 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4202456806162803 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4202456806162803 / 5000000000000000 : ℝ) /
                (1 + (13063023112230041 / 10000000000000000 : ℝ)) =
              (2801637870775202 / 7687674370743347 : ℝ)
            by
        norm_num];
        exact hau992)
  have hat1 :
    (Real.pi / 2 - (2 * (3494739210209437387999 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4202456806162803 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4202456806162803 : ℝ) =
              (4202456806162803 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau991)
  have hz1 :
    (5000000000000000 / 4202456806162803 : ℝ) ≤
      1 / Real.sqrt (2260562330581 / 3200000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 4202456806162803 : ℝ) = 1 / (4202456806162803 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2801637870775201 : ℝ) ≤
      (889977977302413373633 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2260562330581 / 3200000000000 : ℝ) ≤
      (250000000000000 / 2801637870775201 : ℝ) := by
    rw [show
        (250000000000000 / 2801637870775201 : ℝ) =
          (3 / 40) / (8404913612325603 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3494739210209437387999 / 10000000000000000000000 : ℝ))) -
        6 * (889977977302413373633 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2260562330581 / 3200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2260562330581 / 3200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((8404913612325603 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3494739210209437387999 / 10000000000000000000000 : ℝ))) -
          6 * (889977977302413373633 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (2260562330581 / 3200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2260562330581 / 3200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2260562330581 / 3200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_611 :
    ((1070702633856044376569 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(674660239775355582283 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2103640004711281 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1748782181143606580643 / 5000000000000000000000 : ℝ))) -
              6 * (888963081020271195629 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22657542499439 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22657542499439 / 32000000000000 : ℝ)) =
      Real.log (54657542499439 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22657542499439 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (22837542499439 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1070702633856044376569 / 2000000000000000000000 : ℝ) ≤
      Real.log (54657542499439 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (22837542499439 / 32000000000000 : ℝ) ≤
      (-(674660239775355582283 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22837542499439 / 32000000000000 : ℝ) = (22837542499439 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22837542499439 / 16000000000000 : ℝ) ≤
            (711634120824644417717 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2103640004711281 / 2500000000000000 : ℝ) ≤ Real.sqrt (22657542499439 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22657542499439 / 32000000000000 : ℝ) ≤
      (8414560018845127 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22657542499439 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau994 :
    Real.arctan (8414560018845127 / 23069231817928201 : ℝ) ≤
      (1748782181143606580643 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau993 :
    Real.arctan (8414560018845127 / 10000000000000000 : ℝ) ≤
      (2 * (1748782181143606580643 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13069231817928201 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8414560018845127 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8414560018845127 / 10000000000000000 : ℝ) /
                (1 + (13069231817928201 / 10000000000000000 : ℝ)) =
              (8414560018845127 / 23069231817928201 : ℝ)
            by
        norm_num];
        exact hau994)
  have hat1 :
    (Real.pi / 2 - (2 * (1748782181143606580643 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8414560018845127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8414560018845127 : ℝ) =
              (8414560018845127 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau993)
  have hz1 :
    (10000000000000000 / 8414560018845127 : ℝ) ≤
      1 / Real.sqrt (22657542499439 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 8414560018845127 : ℝ) =
          1 / (8414560018845127 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 2103640004711281 : ℝ) ≤
      (888963081020271195629 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22657542499439 / 32000000000000 : ℝ) ≤
      (187500000000000 / 2103640004711281 : ℝ) := by
    rw [show
        (187500000000000 / 2103640004711281 : ℝ) =
          (3 / 40) / (2103640004711281 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1748782181143606580643 / 5000000000000000000000 : ℝ))) -
        6 * (888963081020271195629 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22657542499439 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22657542499439 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2103640004711281 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1748782181143606580643 / 5000000000000000000000 : ℝ))) -
          6 * (888963081020271195629 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22657542499439 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22657542499439 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22657542499439 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_612 :
    ((1340751914872513778333 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1675296429871246496299 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1684839075886329 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3500383600064879102301 / 10000000000000000000000 : ℝ))) -
              6 * (887951648902143076857 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5677365423267 / 8000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (5677365423267 / 8000000000000 : ℝ)) =
      Real.log (13677365423267 / 8000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((5677365423267 / 8000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5722365423267 / 8000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1340751914872513778333 / 2500000000000000000000 : ℝ) ≤
      Real.log (13677365423267 / 8000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5722365423267 / 8000000000000 : ℝ) ≤
      (-(1675296429871246496299 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5722365423267 / 8000000000000 : ℝ) = (5722365423267 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5722365423267 / 4000000000000 : ℝ) ≤
            (1790439471628753503701 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1684839075886329 / 2000000000000000 : ℝ) ≤ Real.sqrt (5677365423267 / 8000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (5677365423267 / 8000000000000 : ℝ) ≤ (263256105607239 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (5677365423267 / 8000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau996 :
    Real.arctan (263256105607239 / 721107424234423 : ℝ) ≤
      (3500383600064879102301 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau995 :
    Real.arctan (263256105607239 / 312500000000000 : ℝ) ≤
      (2 * (3500383600064879102301 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (408607424234423 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (263256105607239 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (263256105607239 / 312500000000000 : ℝ) /
                (1 + (408607424234423 / 312500000000000 : ℝ)) =
              (263256105607239 / 721107424234423 : ℝ)
            by
        norm_num];
        exact hau996)
  have hat1 :
    (Real.pi / 2 - (2 * (3500383600064879102301 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 263256105607239 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 263256105607239 : ℝ) =
              (263256105607239 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau995)
  have hz1 :
    (312500000000000 / 263256105607239 : ℝ) ≤ 1 / Real.sqrt (5677365423267 / 8000000000000 : ℝ) :=
  by
    rw [show (312500000000000 / 263256105607239 : ℝ) = 1 / (263256105607239 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 561613025295443 : ℝ) ≤
      (887951648902143076857 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (5677365423267 / 8000000000000 : ℝ) ≤
      (50000000000000 / 561613025295443 : ℝ) := by
    rw [show
        (50000000000000 / 561613025295443 : ℝ) =
          (3 / 40) / (1684839075886329 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3500383600064879102301 / 10000000000000000000000 : ℝ))) -
        6 * (887951648902143076857 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (5677365423267 / 8000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (5677365423267 / 8000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1684839075886329 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3500383600064879102301 / 10000000000000000000000 : ℝ))) -
          6 * (887951648902143076857 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (5677365423267 / 8000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (5677365423267 / 8000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (5677365423267 / 8000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
