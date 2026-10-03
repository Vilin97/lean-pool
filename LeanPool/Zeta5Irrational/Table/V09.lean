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

/-! # V09: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_109 :
    ((83409097129161147991 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3244034354456449727219 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2626859288543901 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1284411327890970380713 / 5000000000000000000000 : ℝ)) -
              6 * (695281708072396394957 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2208124710979 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2208124710979 / 32000000000000 : ℝ)) =
      Real.log (34208124710979 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2208124710979 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2388124710979 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (83409097129161147991 / 1250000000000000000000 : ℝ) ≤
      Real.log (34208124710979 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2388124710979 / 32000000000000 : ℝ) ≤
      (-(3244034354456449727219 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2388124710979 / 32000000000000 : ℝ) = (2388124710979 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2388124710979 / 2000000000000 : ℝ) ≤
            (221701547043550272781 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2626859288543901 / 10000000000000000 : ℝ) ≤ Real.sqrt (2208124710979 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2208124710979 / 32000000000000 : ℝ) ≤ (82089352766997 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2208124710979 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau171 :
    Real.arctan (82089352766997 / 312500000000000 : ℝ) ≤
      (1284411327890970380713 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1284411327890970380713 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (312500000000000 / 82089352766997 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 82089352766997 : ℝ) =
              (82089352766997 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau171)
  have hz1 :
    (312500000000000 / 82089352766997 : ℝ) ≤ 1 / Real.sqrt (2208124710979 / 32000000000000 : ℝ) :=
  by
    rw [show (312500000000000 / 82089352766997 : ℝ) = 1 / (82089352766997 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 875619762847967 : ℝ) ≤
      (695281708072396394957 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2208124710979 / 32000000000000 : ℝ) ≤
      (250000000000000 / 875619762847967 : ℝ) := by
    rw [show
        (250000000000000 / 875619762847967 : ℝ) =
          (3 / 40) / (2626859288543901 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1284411327890970380713 / 5000000000000000000000 : ℝ)) -
        6 * (695281708072396394957 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2208124710979 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2208124710979 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2626859288543901 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1284411327890970380713 / 5000000000000000000000 : ℝ)) -
          6 * (695281708072396394957 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (2208124710979 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2208124710979 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2208124710979 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_110 :
    ((16804676517263733869 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6470527693651944065921 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((659210537122859 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1289079416002930597313 / 5000000000000000000000 : ℝ)) -
              6 * (554225892774949028251 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4449879370279 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4449879370279 / 64000000000000 : ℝ)) =
      Real.log (68449879370279 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4449879370279 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4809879370279 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (16804676517263733869 / 250000000000000000000 : ℝ) ≤
      Real.log (68449879370279 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4809879370279 / 64000000000000 : ℝ) ≤
      (-(6470527693651944065921 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (4809879370279 / 64000000000000 : ℝ) = (4809879370279 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4809879370279 / 4000000000000 : ℝ) ≤
            (460944109348055934079 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (659210537122859 / 2500000000000000 : ℝ) ≤ Real.sqrt (4449879370279 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4449879370279 / 64000000000000 : ℝ) ≤ (2636842148491439 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4449879370279 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau172 :
    Real.arctan (2636842148491439 / 10000000000000000 : ℝ) ≤
      (1289079416002930597313 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1289079416002930597313 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2636842148491439 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2636842148491439 : ℝ) =
              (2636842148491439 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau172)
  have hz1 :
    (10000000000000000 / 2636842148491439 : ℝ) ≤
      1 / Real.sqrt (4449879370279 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2636842148491439 : ℝ) =
          1 / (2636842148491439 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 659210537122859 : ℝ) ≤
      (554225892774949028251 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4449879370279 / 64000000000000 : ℝ) ≤
      (187500000000000 / 659210537122859 : ℝ) := by
    rw [show
        (187500000000000 / 659210537122859 : ℝ) =
          (3 / 40) / (659210537122859 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1289079416002930597313 / 5000000000000000000000 : ℝ)) -
        6 * (554225892774949028251 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4449879370279 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4449879370279 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((659210537122859 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1289079416002930597313 / 5000000000000000000000 : ℝ)) -
          6 * (554225892774949028251 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (4449879370279 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4449879370279 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4449879370279 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_111 :
    ((33854946525780009319 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1613277224061336718483 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((66169683911481 / 250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2587455226799105179707 / 10000000000000000000000 : ℝ)) -
              6 * (2761239196892071779283 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22417546593 / 320000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (22417546593 / 320000000000 : ℝ)) =
      Real.log (342417546593 / 320000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((22417546593 / 320000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (24217546593 / 320000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (33854946525780009319 / 500000000000000000000 : ℝ) ≤
      Real.log (342417546593 / 320000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (24217546593 / 320000000000 : ℝ) ≤
      (-(1613277224061336718483 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (24217546593 / 320000000000 : ℝ) = (24217546593 / 20000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24217546593 / 20000000000 : ℝ) ≤
            (119590726688663281517 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (66169683911481 / 250000000000000 : ℝ) ≤ Real.sqrt (22417546593 / 320000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (22417546593 / 320000000000 : ℝ) ≤ (2646787356459243 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (22417546593 / 320000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau173 :
    Real.arctan (2646787356459243 / 10000000000000000 : ℝ) ≤
      (2587455226799105179707 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2587455226799105179707 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2646787356459243 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2646787356459243 : ℝ) =
              (2646787356459243 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau173)
  have hz1 :
    (10000000000000000 / 2646787356459243 : ℝ) ≤ 1 / Real.sqrt (22417546593 / 320000000000 : ℝ) :=
  by
    rw [show
        (10000000000000000 / 2646787356459243 : ℝ) =
          1 / (2646787356459243 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (6250000000000 / 22056561303827 : ℝ) ≤
      (2761239196892071779283 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (22417546593 / 320000000000 : ℝ) ≤
      (6250000000000 / 22056561303827 : ℝ) := by
    rw [show
        (6250000000000 / 22056561303827 : ℝ) = (3 / 40) / (66169683911481 / 250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2587455226799105179707 / 10000000000000000000000 : ℝ)) -
        6 * (2761239196892071779283 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (22417546593 / 320000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (22417546593 / 320000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((66169683911481 / 250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2587455226799105179707 / 10000000000000000000000 : ℝ)) -
          6 * (2761239196892071779283 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (22417546593 / 320000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (22417546593 / 320000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (22417546593 / 320000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_112 :
    ((170502097219640879853 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25743242501413712938097 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((531339067058467 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (40573629285751086729 / 156250000000000000000 : ℝ)) -
              6 * (343931766448437447047 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (4517139266921 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4517139266921 / 64000000000000 : ℝ)) =
      Real.log (68517139266921 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4517139266921 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4877139266921 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (170502097219640879853 / 2500000000000000000000 : ℝ) ≤
      Real.log (68517139266921 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4877139266921 / 64000000000000 : ℝ) ≤
      (-(25743242501413712938097 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (4877139266921 / 64000000000000 : ℝ) = (4877139266921 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4877139266921 / 4000000000000 : ℝ) ≤
            (1982644710586287061903 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (531339067058467 / 2000000000000000 : ℝ) ≤ Real.sqrt (4517139266921 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4517139266921 / 64000000000000 : ℝ) ≤ (1328347667646169 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4517139266921 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau174 :
    Real.arctan (1328347667646169 / 5000000000000000 : ℝ) ≤
      (40573629285751086729 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (40573629285751086729 / 156250000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1328347667646169 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1328347667646169 : ℝ) =
              (1328347667646169 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau174)
  have hz1 :
    (5000000000000000 / 1328347667646169 : ℝ) ≤
      1 / Real.sqrt (4517139266921 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1328347667646169 : ℝ) = 1 / (1328347667646169 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 531339067058467 : ℝ) ≤
      (343931766448437447047 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4517139266921 / 64000000000000 : ℝ) ≤
      (150000000000000 / 531339067058467 : ℝ) := by
    rw [show
        (150000000000000 / 531339067058467 : ℝ) =
          (3 / 40) / (531339067058467 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (40573629285751086729 / 156250000000000000000 : ℝ)) -
        6 * (343931766448437447047 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4517139266921 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4517139266921 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((531339067058467 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (40573629285751086729 / 156250000000000000000 : ℝ)) -
          6 * (343931766448437447047 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (4517139266921 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4517139266921 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4517139266921 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_113 :
    ((343457719073036051437 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12837262449008737335481 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1333283249990003 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2605930400624028400873 / 10000000000000000000000 : ℝ)) -
              6 * (1370886207538278677507 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2275384607621 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2275384607621 / 32000000000000 : ℝ)) =
      Real.log (34275384607621 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2275384607621 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2455384607621 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (343457719073036051437 / 5000000000000000000000 : ℝ) ≤
      Real.log (34275384607621 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2455384607621 / 32000000000000 : ℝ) ≤
      (-(12837262449008737335481 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2455384607621 / 32000000000000 : ℝ) = (2455384607621 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2455384607621 / 2000000000000 : ℝ) ≤
            (1025681156991262664519 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1333283249990003 / 5000000000000000 : ℝ) ≤ Real.sqrt (2275384607621 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2275384607621 / 32000000000000 : ℝ) ≤ (2666566499980009 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2275384607621 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau175 :
    Real.arctan (2666566499980009 / 10000000000000000 : ℝ) ≤
      (2605930400624028400873 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2605930400624028400873 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2666566499980009 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2666566499980009 : ℝ) =
              (2666566499980009 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau175)
  have hz1 :
    (10000000000000000 / 2666566499980009 : ℝ) ≤
      1 / Real.sqrt (2275384607621 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2666566499980009 : ℝ) =
          1 / (2666566499980009 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 1333283249990003 : ℝ) ≤
      (1370886207538278677507 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2275384607621 / 32000000000000 : ℝ) ≤
      (375000000000000 / 1333283249990003 : ℝ) := by
    rw [show
        (375000000000000 / 1333283249990003 : ℝ) =
          (3 / 40) / (1333283249990003 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2605930400624028400873 / 10000000000000000000000 : ℝ)) -
        6 * (1370886207538278677507 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2275384607621 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2275384607621 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1333283249990003 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2605930400624028400873 / 10000000000000000000000 : ℝ)) -
          6 * (1370886207538278677507 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2275384607621 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2275384607621 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2275384607621 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_114 :
    ((345910040340638219639 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3200784535571160288559 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((334550157232327 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1307555012094042014081 / 5000000000000000000000 : ℝ)) -
              6 * (170762014991703940461 / 625000000000000000000 : ℝ)))) ≤
      Vfield (4584399163563 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4584399163563 / 64000000000000 : ℝ)) =
      Real.log (68584399163563 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4584399163563 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4944399163563 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (345910040340638219639 / 5000000000000000000000 : ℝ) ≤
      Real.log (68584399163563 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4944399163563 / 64000000000000 : ℝ) ≤
      (-(3200784535571160288559 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (4944399163563 / 64000000000000 : ℝ) = (4944399163563 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4944399163563 / 4000000000000 : ℝ) ≤
            (264951365928839711441 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (334550157232327 / 1250000000000000 : ℝ) ≤ Real.sqrt (4584399163563 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4584399163563 / 64000000000000 : ℝ) ≤ (2676401257858619 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4584399163563 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau176 :
    Real.arctan (2676401257858619 / 10000000000000000 : ℝ) ≤
      (1307555012094042014081 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1307555012094042014081 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2676401257858619 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2676401257858619 : ℝ) =
              (2676401257858619 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau176)
  have hz1 :
    (10000000000000000 / 2676401257858619 : ℝ) ≤
      1 / Real.sqrt (4584399163563 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 2676401257858619 : ℝ) =
          1 / (2676401257858619 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 334550157232327 : ℝ) ≤
      (170762014991703940461 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4584399163563 / 64000000000000 : ℝ) ≤
      (93750000000000 / 334550157232327 : ℝ) := by
    rw [show
        (93750000000000 / 334550157232327 : ℝ) =
          (3 / 40) / (334550157232327 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1307555012094042014081 / 5000000000000000000000 : ℝ)) -
        6 * (170762014991703940461 / 625000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4584399163563 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4584399163563 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((334550157232327 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1307555012094042014081 / 5000000000000000000000 : ℝ)) -
          6 * (170762014991703940461 / 625000000000000000000 : ℝ))) ≤
      Real.sqrt (4584399163563 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4584399163563 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4584399163563 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_115 :
    ((13934446376877032259 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25538490302831131762179 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2686200008807747 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (524850311157877829367 / 2000000000000000000000 : ℝ)) -
              6 * (2722711842439540008903 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1154507277971 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1154507277971 / 16000000000000 : ℝ)) =
      Real.log (17154507277971 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1154507277971 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1244507277971 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (13934446376877032259 / 200000000000000000000 : ℝ) ≤
      Real.log (17154507277971 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1244507277971 / 16000000000000 : ℝ) ≤
      (-(25538490302831131762179 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1244507277971 / 16000000000000 : ℝ) = (1244507277971 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1244507277971 / 1000000000000 : ℝ) ≤
            (2187396909168868237821 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2686200008807747 / 10000000000000000 : ℝ) ≤ Real.sqrt (1154507277971 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1154507277971 / 16000000000000 : ℝ) ≤ (10744800035231 / 40000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1154507277971 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau177 :
    Real.arctan (10744800035231 / 40000000000000 : ℝ) ≤
      (524850311157877829367 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (524850311157877829367 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (40000000000000 / 10744800035231 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (40000000000000 / 10744800035231 : ℝ) =
              (10744800035231 / 40000000000000 : ℝ)
            by
        norm_num];
        exact hau177)
  have hz1 :
    (40000000000000 / 10744800035231 : ℝ) ≤ 1 / Real.sqrt (1154507277971 / 16000000000000 : ℝ) := by
    rw [show (40000000000000 / 10744800035231 : ℝ) = 1 / (10744800035231 / 40000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2686200008807747 : ℝ) ≤
      (2722711842439540008903 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1154507277971 / 16000000000000 : ℝ) ≤
      (750000000000000 / 2686200008807747 : ℝ) := by
    rw [show
        (750000000000000 / 2686200008807747 : ℝ) =
          (3 / 40) / (2686200008807747 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (524850311157877829367 / 2000000000000000000000 : ℝ)) -
        6 * (2722711842439540008903 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1154507277971 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1154507277971 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2686200008807747 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (524850311157877829367 / 2000000000000000000000 : ℝ)) -
          6 * (2722711842439540008903 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1154507277971 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1154507277971 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1154507277971 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_116 :
    ((701622154990004101623 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6367790180748935590831 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2695963145439919 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2633355398856895131241 / 10000000000000000000000 : ℝ)) -
              6 * (1356664750939314845041 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (930331812041 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (930331812041 / 12800000000000 : ℝ)) =
      Real.log (13730331812041 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((930331812041 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1002331812041 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (701622154990004101623 / 10000000000000000000000 : ℝ) ≤
      Real.log (13730331812041 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1002331812041 / 12800000000000 : ℝ) ≤
      (-(6367790180748935590831 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1002331812041 / 12800000000000 : ℝ) = (1002331812041 / 800000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1002331812041 / 800000000000 : ℝ) ≤
            (563681622251064409169 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2695963145439919 / 10000000000000000 : ℝ) ≤ Real.sqrt (930331812041 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (930331812041 / 12800000000000 : ℝ) ≤ (1347981572719961 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (930331812041 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau178 :
    Real.arctan (1347981572719961 / 5000000000000000 : ℝ) ≤
      (2633355398856895131241 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (2633355398856895131241 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1347981572719961 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1347981572719961 : ℝ) =
              (1347981572719961 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau178)
  have hz1 :
    (5000000000000000 / 1347981572719961 : ℝ) ≤
      1 / Real.sqrt (930331812041 / 12800000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 1347981572719961 : ℝ) = 1 / (1347981572719961 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 2695963145439919 : ℝ) ≤
      (1356664750939314845041 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (930331812041 / 12800000000000 : ℝ) ≤
      (750000000000000 / 2695963145439919 : ℝ) := by
    rw [show
        (750000000000000 / 2695963145439919 : ℝ) =
          (3 / 40) / (2695963145439919 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2633355398856895131241 / 10000000000000000000000 : ℝ)) -
        6 * (1356664750939314845041 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (930331812041 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (930331812041 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2695963145439919 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2633355398856895131241 / 10000000000000000000000 : ℝ)) -
          6 * (1356664750939314845041 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (930331812041 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (930331812041 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (930331812041 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_117 :
    ((706519591472478571351 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5080856288050152583271 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((541138210656829 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (21139375596999086211 / 80000000000000000000 : ℝ)) -
              6 * (338005442320010944411 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (2342644504263 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2342644504263 / 32000000000000 : ℝ)) =
      Real.log (34342644504263 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2342644504263 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2522644504263 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (706519591472478571351 / 10000000000000000000000 : ℝ) ≤
      Real.log (34342644504263 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2522644504263 / 32000000000000 : ℝ) ≤
      (-(5080856288050152583271 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2522644504263 / 32000000000000 : ℝ) = (2522644504263 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2522644504263 / 2000000000000 : ℝ) ≤
            (464321154349847416729 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (541138210656829 / 2000000000000000 : ℝ) ≤ Real.sqrt (2342644504263 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2342644504263 / 32000000000000 : ℝ) ≤ (676422763321037 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2342644504263 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau179 :
    Real.arctan (676422763321037 / 2500000000000000 : ℝ) ≤
      (21139375596999086211 / 80000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (21139375596999086211 / 80000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 676422763321037 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 676422763321037 : ℝ) =
              (676422763321037 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau179)
  have hz1 :
    (2500000000000000 / 676422763321037 : ℝ) ≤
      1 / Real.sqrt (2342644504263 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 676422763321037 : ℝ) = 1 / (676422763321037 / 2500000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 541138210656829 : ℝ) ≤
      (338005442320010944411 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2342644504263 / 32000000000000 : ℝ) ≤
      (150000000000000 / 541138210656829 : ℝ) := by
    rw [show
        (150000000000000 / 541138210656829 : ℝ) =
          (3 / 40) / (541138210656829 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (21139375596999086211 / 80000000000000000000 : ℝ)) -
        6 * (338005442320010944411 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2342644504263 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2342644504263 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((541138210656829 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (21139375596999086211 / 80000000000000000000 : ℝ)) -
          6 * (338005442320010944411 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (2342644504263 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2342644504263 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2342644504263 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_118 :
    ((354483705287062168277 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3171376098236488809029 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((677635478748883 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1323470681148397034747 / 5000000000000000000000 : ℝ)) -
              6 * (1349718092230963117081 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9404207965373 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9404207965373 / 128000000000000 : ℝ)) =
      Real.log (137404207965373 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9404207965373 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (10124207965373 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (354483705287062168277 / 5000000000000000000000 : ℝ) ≤
      Real.log (137404207965373 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (10124207965373 / 128000000000000 : ℝ) ≤
      (-(3171376098236488809029 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10124207965373 / 128000000000000 : ℝ) = (10124207965373 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10124207965373 / 8000000000000 : ℝ) ≤
            (294359803263511190971 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (677635478748883 / 2500000000000000 : ℝ) ≤ Real.sqrt (9404207965373 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9404207965373 / 128000000000000 : ℝ) ≤ (542108382999107 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9404207965373 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau180 :
    Real.arctan (542108382999107 / 2000000000000000 : ℝ) ≤
      (1323470681148397034747 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1323470681148397034747 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 542108382999107 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 542108382999107 : ℝ) =
              (542108382999107 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau180)
  have hz1 :
    (2000000000000000 / 542108382999107 : ℝ) ≤
      1 / Real.sqrt (9404207965373 / 128000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 542108382999107 : ℝ) = 1 / (542108382999107 / 2000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 677635478748883 : ℝ) ≤
      (1349718092230963117081 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9404207965373 / 128000000000000 : ℝ) ≤
      (187500000000000 / 677635478748883 : ℝ) := by
    rw [show
        (187500000000000 / 677635478748883 : ℝ) =
          (3 / 40) / (677635478748883 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1323470681148397034747 / 5000000000000000000000 : ℝ)) -
        6 * (1349718092230963117081 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9404207965373 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9404207965373 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((677635478748883 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1323470681148397034747 / 5000000000000000000000 : ℝ)) -
          6 * (1349718092230963117081 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (9404207965373 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9404207965373 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9404207965373 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_119 :
    ((711414630640564654789 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12668923235728554122461 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((678846027740893 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (662862899328136929311 / 2500000000000000000000 : ℝ)) -
              6 * (2694852312884068981851 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4718918956847 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4718918956847 / 64000000000000 : ℝ)) =
      Real.log (68718918956847 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4718918956847 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5078918956847 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (711414630640564654789 / 10000000000000000000000 : ℝ) ≤
      Real.log (68718918956847 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5078918956847 / 64000000000000 : ℝ) ≤
      (-(12668923235728554122461 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5078918956847 / 64000000000000 : ℝ) = (5078918956847 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5078918956847 / 4000000000000 : ℝ) ≤
            (1194020370271445877539 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (678846027740893 / 2500000000000000 : ℝ) ≤ Real.sqrt (4718918956847 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4718918956847 / 64000000000000 : ℝ) ≤ (108615364438543 / 400000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4718918956847 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau181 :
    Real.arctan (108615364438543 / 400000000000000 : ℝ) ≤
      (662862899328136929311 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (662862899328136929311 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (400000000000000 / 108615364438543 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 108615364438543 : ℝ) =
              (108615364438543 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau181)
  have hz1 :
    (400000000000000 / 108615364438543 : ℝ) ≤
      1 / Real.sqrt (4718918956847 / 64000000000000 : ℝ) := by
    rw [show (400000000000000 / 108615364438543 : ℝ) = 1 / (108615364438543 / 400000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 678846027740893 : ℝ) ≤
      (2694852312884068981851 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4718918956847 / 64000000000000 : ℝ) ≤
      (187500000000000 / 678846027740893 : ℝ) := by
    rw [show
        (187500000000000 / 678846027740893 : ℝ) =
          (3 / 40) / (678846027740893 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (662862899328136929311 / 2500000000000000000000 : ℝ)) -
        6 * (2694852312884068981851 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4718918956847 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4718918956847 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((678846027740893 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (662862899328136929311 / 2500000000000000000000 : ℝ)) -
          6 * (2694852312884068981851 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4718918956847 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4718918956847 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4718918956847 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_120 :
    ((713861251964921990511 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1581549610471153343741 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2720217687465327 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (663988175564238770757 / 2500000000000000000000 : ℝ)) -
              6 * (2690291724930460355717 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1894293572403 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1894293572403 / 25600000000000 : ℝ)) =
      Real.log (27494293572403 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1894293572403 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2038293572403 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (713861251964921990511 / 10000000000000000000000 : ℝ) ≤
      Real.log (27494293572403 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2038293572403 / 25600000000000 : ℝ) ≤
      (-(1581549610471153343741 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2038293572403 / 25600000000000 : ℝ) = (2038293572403 / 1600000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2038293572403 / 1600000000000 : ℝ) ≤
            (151318340278846656259 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2720217687465327 / 10000000000000000 : ℝ) ≤ Real.sqrt (1894293572403 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1894293572403 / 25600000000000 : ℝ) ≤ (272021768746533 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1894293572403 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau182 :
    Real.arctan (272021768746533 / 1000000000000000 : ℝ) ≤
      (663988175564238770757 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (663988175564238770757 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 272021768746533 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 272021768746533 : ℝ) =
              (272021768746533 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau182)
  have hz1 :
    (1000000000000000 / 272021768746533 : ℝ) ≤
      1 / Real.sqrt (1894293572403 / 25600000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 272021768746533 : ℝ) = 1 / (272021768746533 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 906739229155109 : ℝ) ≤
      (2690291724930460355717 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1894293572403 / 25600000000000 : ℝ) ≤
      (250000000000000 / 906739229155109 : ℝ) := by
    rw [show
        (250000000000000 / 906739229155109 : ℝ) =
          (3 / 40) / (2720217687465327 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (663988175564238770757 / 2500000000000000000000 : ℝ)) -
        6 * (2690291724930460355717 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1894293572403 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1894293572403 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2720217687465327 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (663988175564238770757 / 2500000000000000000000 : ℝ)) -
          6 * (2690291724930460355717 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1894293572403 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1894293572403 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1894293572403 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
