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

/-! # V25: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_301 :
    ((1240130691140485734679 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12478605076626120675669 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5305595421098193 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) -
              6 * (175537173293389352119 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (9007789687161 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9007789687161 / 32000000000000 : ℝ)) =
      Real.log (41007789687161 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9007789687161 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9187789687161 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1240130691140485734679 / 5000000000000000000000 : ℝ) ≤
      Real.log (41007789687161 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9187789687161 / 32000000000000 : ℝ) ≤
      (-(12478605076626120675669 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9187789687161 / 32000000000000 : ℝ) = (9187789687161 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9187789687161 / 8000000000000 : ℝ) ≤
            (1384338529373879324331 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5305595421098193 / 10000000000000000 : ℝ) ≤ Real.sqrt (9007789687161 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9007789687161 / 32000000000000 : ℝ) ≤ (1326398855274549 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9007789687161 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau374 :
    Real.arctan (1326398855274549 / 5330076663850934 : ℝ) ≤
      (152436035464757284741 / 625000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau373 :
    Real.arctan (1326398855274549 / 2500000000000000 : ℝ) ≤
      (2 * (152436035464757284741 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1415038331925467 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (1326398855274549 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1326398855274549 / 2500000000000000 : ℝ) /
                (1 + (1415038331925467 / 1250000000000000 : ℝ)) =
              (1326398855274549 / 5330076663850934 : ℝ)
            by
        norm_num];
        exact hau374)
  have hat1 :
    (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1326398855274549 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1326398855274549 : ℝ) =
              (1326398855274549 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau373)
  have hz1 :
    (2500000000000000 / 1326398855274549 : ℝ) ≤
      1 / Real.sqrt (9007789687161 / 32000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1326398855274549 : ℝ) = 1 / (1326398855274549 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1768531807032731 : ℝ) ≤
      (175537173293389352119 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9007789687161 / 32000000000000 : ℝ) ≤
      (250000000000000 / 1768531807032731 : ℝ) := by
    rw [show
        (250000000000000 / 1768531807032731 : ℝ) =
          (3 / 40) / (5305595421098193 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) -
        6 * (175537173293389352119 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9007789687161 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9007789687161 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5305595421098193 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) -
          6 * (175537173293389352119 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (9007789687161 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9007789687161 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9007789687161 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_302 :
    ((1244868006543635756541 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12436386238777361036033 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5317030851949791 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) -
              6 * (10947785663169174833 / 78125000000000000000 : ℝ)))) ≤
      Vfield (723732917263 / 2560000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (723732917263 / 2560000000000 : ℝ)) =
      Real.log (3283732917263 / 2560000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((723732917263 / 2560000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (738132917263 / 2560000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1244868006543635756541 / 5000000000000000000000 : ℝ) ≤
      Real.log (3283732917263 / 2560000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (738132917263 / 2560000000000 : ℝ) ≤
      (-(12436386238777361036033 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (738132917263 / 2560000000000 : ℝ) = (738132917263 / 640000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (738132917263 / 640000000000 : ℝ) ≤
            (1426557367222638963967 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5317030851949791 / 10000000000000000 : ℝ) ≤ Real.sqrt (723732917263 / 2560000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (723732917263 / 2560000000000 : ℝ) ≤ (2658515425974897 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (723732917263 / 2560000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau376 :
    Real.arctan (2658515425974897 / 10662835356086779 : ℝ) ≤
      (2443436214313161845841 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau375 :
    Real.arctan (2658515425974897 / 5000000000000000 : ℝ) ≤
      (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5662835356086779 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2658515425974897 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2658515425974897 / 5000000000000000 : ℝ) /
                (1 + (5662835356086779 / 5000000000000000 : ℝ)) =
              (2658515425974897 / 10662835356086779 : ℝ)
            by
        norm_num];
        exact hau376)
  have hat1 :
    (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2658515425974897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2658515425974897 : ℝ) =
              (2658515425974897 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau375)
  have hz1 :
    (5000000000000000 / 2658515425974897 : ℝ) ≤
      1 / Real.sqrt (723732917263 / 2560000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2658515425974897 : ℝ) = 1 / (2658515425974897 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1772343617316597 : ℝ) ≤
      (10947785663169174833 / 78125000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (723732917263 / 2560000000000 : ℝ) ≤
      (250000000000000 / 1772343617316597 : ℝ) := by
    rw [show
        (250000000000000 / 1772343617316597 : ℝ) =
          (3 / 40) / (5317030851949791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) -
        6 * (10947785663169174833 / 78125000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (723732917263 / 2560000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (723732917263 / 2560000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5317030851949791 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) -
          6 * (10947785663169174833 / 78125000000000000000 : ℝ))) ≤
      Real.sqrt (723732917263 / 2560000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (723732917263 / 2560000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (723732917263 / 2560000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_303 :
    ((2499201675527205748003 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6197172447429658443921 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((532844174114663 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) -
              6 * (349588661375526816723 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (4542766622207 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4542766622207 / 16000000000000 : ℝ)) =
      Real.log (20542766622207 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4542766622207 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4632766622207 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2499201675527205748003 / 10000000000000000000000 : ℝ) ≤
      Real.log (20542766622207 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4632766622207 / 16000000000000 : ℝ) ≤
      (-(6197172447429658443921 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4632766622207 / 16000000000000 : ℝ) = (4632766622207 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4632766622207 / 4000000000000 : ℝ) ≤
            (734299355570341556079 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (532844174114663 / 1000000000000000 : ℝ) ≤ Real.sqrt (4542766622207 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4542766622207 / 16000000000000 : ℝ) ≤ (5328441741146633 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4542766622207 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau378 :
    Real.arctan (5328441741146633 / 21331032229624701 : ℝ) ≤
      (2447882078016176642779 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau377 :
    Real.arctan (5328441741146633 / 10000000000000000 : ℝ) ≤
      (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11331032229624701 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5328441741146633 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5328441741146633 / 10000000000000000 : ℝ) /
                (1 + (11331032229624701 / 10000000000000000 : ℝ)) =
              (5328441741146633 / 21331032229624701 : ℝ)
            by
        norm_num];
        exact hau378)
  have hat1 :
    (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5328441741146633 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5328441741146633 : ℝ) =
              (5328441741146633 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau377)
  have hz1 :
    (10000000000000000 / 5328441741146633 : ℝ) ≤
      1 / Real.sqrt (4542766622207 / 16000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5328441741146633 : ℝ) =
          1 / (5328441741146633 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (75000000000000 / 532844174114663 : ℝ) ≤
      (349588661375526816723 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4542766622207 / 16000000000000 : ℝ) ≤
      (75000000000000 / 532844174114663 : ℝ) := by
    rw [show
        (75000000000000 / 532844174114663 : ℝ) =
          (3 / 40) / (532844174114663 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) -
        6 * (349588661375526816723 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4542766622207 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4542766622207 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((532844174114663 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) -
          6 * (349588661375526816723 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (4542766622207 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4542766622207 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4542766622207 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_304 :
    ((62598278722809241977 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6186695158982756371369 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((666767253982059 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) -
              6 * (698440355903575839597 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (36419876534909 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (36419876534909 / 128000000000000 : ℝ)) =
      Real.log (164419876534909 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((36419876534909 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (37139876534909 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (62598278722809241977 / 250000000000000000000 : ℝ) ≤
      Real.log (164419876534909 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (37139876534909 / 128000000000000 : ℝ) ≤
      (-(6186695158982756371369 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (37139876534909 / 128000000000000 : ℝ) = (37139876534909 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37139876534909 / 32000000000000 : ℝ) ≤
            (744776644017243628631 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (666767253982059 / 1250000000000000 : ℝ) ≤ Real.sqrt (36419876534909 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (36419876534909 / 128000000000000 : ℝ) ≤ (213365521274259 / 400000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (36419876534909 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau380 :
    Real.arctan (1066827606371295 / 4266742407446401 : ℝ) ≤
      (1225049934248501779659 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau379 :
    Real.arctan (213365521274259 / 400000000000000 : ℝ) ≤
      (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2266742407446401 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (213365521274259 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (213365521274259 / 400000000000000 : ℝ) /
                (1 + (2266742407446401 / 2000000000000000 : ℝ)) =
              (1066827606371295 / 4266742407446401 : ℝ)
            by
        norm_num];
        exact hau380)
  have hat1 :
    (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 213365521274259 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 213365521274259 : ℝ) =
              (213365521274259 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau379)
  have hz1 :
    (400000000000000 / 213365521274259 : ℝ) ≤
      1 / Real.sqrt (36419876534909 / 128000000000000 : ℝ) := by
    rw [show (400000000000000 / 213365521274259 : ℝ) = 1 / (213365521274259 / 400000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (31250000000000 / 222255751327353 : ℝ) ≤
      (698440355903575839597 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (36419876534909 / 128000000000000 : ℝ) ≤
      (31250000000000 / 222255751327353 : ℝ) := by
    rw [show
        (31250000000000 / 222255751327353 : ℝ) =
          (3 / 40) / (666767253982059 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) -
        6 * (698440355903575839597 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (36419876534909 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (36419876534909 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((666767253982059 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) -
          6 * (698440355903575839597 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (36419876534909 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (36419876534909 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (36419876534909 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_305 :
    ((1254329193281513271393 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2470495911739800849337 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5339828246020797 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) -
              6 * (348852857314937662517 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (18248810046081 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18248810046081 / 64000000000000 : ℝ)) =
      Real.log (82248810046081 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18248810046081 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18608810046081 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1254329193281513271393 / 5000000000000000000000 : ℝ) ≤
      Real.log (82248810046081 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18608810046081 / 64000000000000 : ℝ) ≤
      (-(2470495911739800849337 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (18608810046081 / 64000000000000 : ℝ) = (18608810046081 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18608810046081 / 16000000000000 : ℝ) ≤
            (302092809460199150663 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5339828246020797 / 10000000000000000 : ℝ) ≤
      Real.sqrt (18248810046081 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18248810046081 / 64000000000000 : ℝ) ≤ (3337392653763 / 6250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18248810046081 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau382 :
    Real.arctan (762832606574400 / 3048055887337151 : ℝ) ≤
      (245231424585502598539 / 1000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau381 :
    Real.arctan (3337392653763 / 6250000000000 : ℝ) ≤
      (2 * (245231424585502598539 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11336391211360057 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3337392653763 / 6250000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3337392653763 / 6250000000000 : ℝ) /
                (1 + (11336391211360057 / 10000000000000000 : ℝ)) =
              (762832606574400 / 3048055887337151 : ℝ)
            by
        norm_num];
        exact hau382)
  have hat1 :
    (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (6250000000000 / 3337392653763 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (6250000000000 / 3337392653763 : ℝ) = (3337392653763 / 6250000000000 : ℝ) by
            norm_num];
        exact hau381)
  have hz1 :
    (6250000000000 / 3337392653763 : ℝ) ≤ 1 / Real.sqrt (18248810046081 / 64000000000000 : ℝ) := by
    rw [show (6250000000000 / 3337392653763 : ℝ) = 1 / (3337392653763 / 6250000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1779942748673599 : ℝ) ≤
      (348852857314937662517 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18248810046081 / 64000000000000 : ℝ) ≤
      (250000000000000 / 1779942748673599 : ℝ) := by
    rw [show
        (250000000000000 / 1779942748673599 : ℝ) =
          (3 / 40) / (5339828246020797 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) -
        6 * (348852857314937662517 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18248810046081 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18248810046081 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5339828246020797 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) -
          6 * (348852857314937662517 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (18248810046081 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18248810046081 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18248810046081 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_306 :
    ((2513383390591947328477 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6165806217095040688203 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((167047262595149 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) -
              6 * (1393946773448474205463 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7315072729883 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7315072729883 / 25600000000000 : ℝ)) =
      Real.log (32915072729883 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7315072729883 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7459072729883 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2513383390591947328477 / 10000000000000000000000 : ℝ) ≤
      Real.log (32915072729883 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7459072729883 / 25600000000000 : ℝ) ≤
      (-(6165806217095040688203 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (7459072729883 / 25600000000000 : ℝ) = (7459072729883 / 6400000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7459072729883 / 6400000000000 : ℝ) ≤
            (765665585904959311797 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (167047262595149 / 312500000000000 : ℝ) ≤ Real.sqrt (7315072729883 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7315072729883 / 25600000000000 : ℝ) ≤ (5345512403044771 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7315072729883 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau384 :
    Real.arctan (5345512403044771 / 21339069752457891 : ℝ) ≤
      (2454525220863704290673 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau383 :
    Real.arctan (5345512403044771 / 10000000000000000 : ℝ) ≤
      (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11339069752457891 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5345512403044771 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5345512403044771 / 10000000000000000 : ℝ) /
                (1 + (11339069752457891 / 10000000000000000 : ℝ)) =
              (5345512403044771 / 21339069752457891 : ℝ)
            by
        norm_num];
        exact hau384)
  have hat1 :
    (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5345512403044771 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5345512403044771 : ℝ) =
              (5345512403044771 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau383)
  have hz1 :
    (10000000000000000 / 5345512403044771 : ℝ) ≤
      1 / Real.sqrt (7315072729883 / 25600000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5345512403044771 : ℝ) =
          1 / (5345512403044771 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 167047262595149 : ℝ) ≤
      (1393946773448474205463 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7315072729883 / 25600000000000 : ℝ) ≤
      (23437500000000 / 167047262595149 : ℝ) := by
    rw [show
        (23437500000000 / 167047262595149 : ℝ) =
          (3 / 40) / (167047262595149 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) -
        6 * (1393946773448474205463 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7315072729883 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7315072729883 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((167047262595149 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) -
          6 * (1393946773448474205463 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (7315072729883 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7315072729883 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7315072729883 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_307 :
    ((314763270388613698039 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6155394381355720490859 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1337797630557621 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) -
              6 * (278497344028178964147 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (9163276801667 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9163276801667 / 32000000000000 : ℝ)) =
      Real.log (41163276801667 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9163276801667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9343276801667 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (314763270388613698039 / 1250000000000000000000 : ℝ) ≤
      Real.log (41163276801667 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9343276801667 / 32000000000000 : ℝ) ≤
      (-(6155394381355720490859 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9343276801667 / 32000000000000 : ℝ) = (9343276801667 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9343276801667 / 8000000000000 : ℝ) ≤
            (776077421644279509141 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1337797630557621 / 2500000000000000 : ℝ) ≤ Real.sqrt (9163276801667 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9163276801667 / 32000000000000 : ℝ) ≤ (5351190522230487 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9163276801667 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau386 :
    Real.arctan (5351190522230487 / 21341747660974007 : ℝ) ≤
      (1228366402120582497673 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau385 :
    Real.arctan (5351190522230487 / 10000000000000000 : ℝ) ≤
      (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11341747660974007 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5351190522230487 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5351190522230487 / 10000000000000000 : ℝ) /
                (1 + (11341747660974007 / 10000000000000000 : ℝ)) =
              (5351190522230487 / 21341747660974007 : ℝ)
            by
        norm_num];
        exact hau386)
  have hat1 :
    (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5351190522230487 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5351190522230487 : ℝ) =
              (5351190522230487 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau385)
  have hz1 :
    (10000000000000000 / 5351190522230487 : ℝ) ≤
      1 / Real.sqrt (9163276801667 / 32000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5351190522230487 : ℝ) =
          1 / (5351190522230487 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 445932543519207 : ℝ) ≤
      (278497344028178964147 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9163276801667 / 32000000000000 : ℝ) ≤
      (62500000000000 / 445932543519207 : ℝ) := by
    rw [show
        (62500000000000 / 445932543519207 : ℝ) =
          (3 / 40) / (1337797630557621 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) -
        6 * (278497344028178964147 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9163276801667 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9163276801667 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1337797630557621 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) -
          6 * (278497344028178964147 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (9163276801667 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9163276801667 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9163276801667 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_308 :
    ((2522826706220703069523 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12290008363668690903519 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1071372524555549 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) -
              6 * (347757811320475804929 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (36730850763921 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (36730850763921 / 128000000000000 : ℝ)) =
      Real.log (164730850763921 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((36730850763921 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (37450850763921 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2522826706220703069523 / 10000000000000000000000 : ℝ) ≤
      Real.log (164730850763921 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (37450850763921 / 128000000000000 : ℝ) ≤
      (-(12290008363668690903519 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (37450850763921 / 128000000000000 : ℝ) = (37450850763921 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37450850763921 / 32000000000000 : ℝ) ≤
            (1572935242331309096481 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1071372524555549 / 2000000000000000 : ℝ) ≤
      Real.sqrt (36730850763921 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (36730850763921 / 128000000000000 : ℝ) ≤
      (1339215655694437 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (36730850763921 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau388 :
    Real.arctan (2678431311388874 / 10672212468678189 : ℝ) ≤
      (2458937006650601874589 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau387 :
    Real.arctan (1339215655694437 / 2500000000000000 : ℝ) ≤
      (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5672212468678189 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1339215655694437 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1339215655694437 / 2500000000000000 : ℝ) /
                (1 + (5672212468678189 / 5000000000000000 : ℝ)) =
              (2678431311388874 / 10672212468678189 : ℝ)
            by
        norm_num];
        exact hau388)
  have hat1 :
    (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1339215655694437 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1339215655694437 : ℝ) =
              (1339215655694437 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau387)
  have hz1 :
    (2500000000000000 / 1339215655694437 : ℝ) ≤
      1 / Real.sqrt (36730850763921 / 128000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1339215655694437 : ℝ) = 1 / (1339215655694437 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1071372524555549 : ℝ) ≤
      (347757811320475804929 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (36730850763921 / 128000000000000 : ℝ) ≤
      (150000000000000 / 1071372524555549 : ℝ) := by
    rw [show
        (150000000000000 / 1071372524555549 : ℝ) =
          (3 / 40) / (1071372524555549 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) -
        6 * (347757811320475804929 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (36730850763921 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (36730850763921 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1071372524555549 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) -
          6 * (347757811320475804929 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (36730850763921 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (36730850763921 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (36730850763921 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_309 :
    ((2527545022031135393343 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12269271057590952551449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5362528723784813 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) -
              6 * (1389580324992042662019 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (18404297160587 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (18404297160587 / 64000000000000 : ℝ)) =
      Real.log (82404297160587 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((18404297160587 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18764297160587 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2527545022031135393343 / 10000000000000000000000 : ℝ) ≤
      Real.log (82404297160587 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18764297160587 / 64000000000000 : ℝ) ≤
      (-(12269271057590952551449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (18764297160587 / 64000000000000 : ℝ) = (18764297160587 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18764297160587 / 16000000000000 : ℝ) ≤
            (1593672548409047448551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5362528723784813 / 10000000000000000 : ℝ) ≤
      Real.sqrt (18404297160587 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (18404297160587 / 64000000000000 : ℝ) ≤ (335158045236551 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (18404297160587 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau390 :
    Real.arctan (335158045236551 / 1334193848878278 : ℝ) ≤
      (492227567740135145223 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau389 :
    Real.arctan (335158045236551 / 625000000000000 : ℝ) ≤
      (2 * (492227567740135145223 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (354596924439139 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (335158045236551 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (335158045236551 / 625000000000000 : ℝ) /
                (1 + (354596924439139 / 312500000000000 : ℝ)) =
              (335158045236551 / 1334193848878278 : ℝ)
            by
        norm_num];
        exact hau390)
  have hat1 :
    (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 335158045236551 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 335158045236551 : ℝ) =
              (335158045236551 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau389)
  have hz1 :
    (625000000000000 / 335158045236551 : ℝ) ≤
      1 / Real.sqrt (18404297160587 / 64000000000000 : ℝ) := by
    rw [show (625000000000000 / 335158045236551 : ℝ) = 1 / (335158045236551 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 5362528723784813 : ℝ) ≤
      (1389580324992042662019 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (18404297160587 / 64000000000000 : ℝ) ≤
      (750000000000000 / 5362528723784813 : ℝ) := by
    rw [show
        (750000000000000 / 5362528723784813 : ℝ) =
          (3 / 40) / (5362528723784813 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) -
        6 * (1389580324992042662019 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (18404297160587 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (18404297160587 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5362528723784813 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) -
          6 * (1389580324992042662019 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (18404297160587 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (18404297160587 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (18404297160587 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_310 :
    ((50645222252820752813 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(122485766661215607187 / 100000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1073637768849831 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) -
              6 * (277626787113173012921 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (36886337878427 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (36886337878427 / 128000000000000 : ℝ)) =
      Real.log (164886337878427 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((36886337878427 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (37606337878427 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (50645222252820752813 / 200000000000000000000 : ℝ) ≤
      Real.log (164886337878427 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (37606337878427 / 128000000000000 : ℝ) ≤
      (-(122485766661215607187 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (37606337878427 / 128000000000000 : ℝ) = (37606337878427 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37606337878427 / 32000000000000 : ℝ) ≤
            (16143669398784392813 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1073637768849831 / 2000000000000000 : ℝ) ≤
      Real.sqrt (36886337878427 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (36886337878427 / 128000000000000 : ℝ) ≤
      (2684094422124579 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (36886337878427 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau392 :
    Real.arctan (5368188844249158 / 21349777595509133 : ℝ) ≤
      (24633353109459053127 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau391 :
    Real.arctan (2684094422124579 / 5000000000000000 : ℝ) ≤
      (2 * (24633353109459053127 / 100000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11349777595509133 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2684094422124579 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2684094422124579 / 5000000000000000 : ℝ) /
                (1 + (11349777595509133 / 10000000000000000 : ℝ)) =
              (5368188844249158 / 21349777595509133 : ℝ)
            by
        norm_num];
        exact hau392)
  have hat1 :
    (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2684094422124579 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2684094422124579 : ℝ) =
              (2684094422124579 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau391)
  have hz1 :
    (5000000000000000 / 2684094422124579 : ℝ) ≤
      1 / Real.sqrt (36886337878427 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2684094422124579 : ℝ) = 1 / (2684094422124579 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (50000000000000 / 357879256283277 : ℝ) ≤
      (277626787113173012921 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (36886337878427 / 128000000000000 : ℝ) ≤
      (50000000000000 / 357879256283277 : ℝ) := by
    rw [show
        (50000000000000 / 357879256283277 : ℝ) =
          (3 / 40) / (1073637768849831 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) -
        6 * (277626787113173012921 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (36886337878427 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (36886337878427 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1073637768849831 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) -
          6 * (277626787113173012921 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (36886337878427 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (36886337878427 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (36886337878427 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_311 :
    ((2536974980148269984337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12227925012008859438829 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2686921501534097 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) -
              6 * (693346026735151028923 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (231025508973 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (231025508973 / 800000000000 : ℝ)) =
      Real.log (1031025508973 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((231025508973 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (235525508973 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2536974980148269984337 / 10000000000000000000000 : ℝ) ≤
      Real.log (1031025508973 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (235525508973 / 800000000000 : ℝ) ≤
      (-(12227925012008859438829 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (235525508973 / 800000000000 : ℝ) = (235525508973 / 200000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (235525508973 / 200000000000 : ℝ) ≤
            (1635018593991140561171 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (2686921501534097 / 5000000000000000 : ℝ) ≤ Real.sqrt (231025508973 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (231025508973 / 800000000000 : ℝ) ≤ (5373843003068197 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (231025508973 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau394 :
    Real.arctan (5373843003068197 / 21352452978172822 : ℝ) ≤
      (308191179235882659497 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau393 :
    Real.arctan (5373843003068197 / 10000000000000000 : ℝ) ≤
      (2 * (308191179235882659497 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5676226489086411 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5373843003068197 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5373843003068197 / 10000000000000000 : ℝ) /
                (1 + (5676226489086411 / 5000000000000000 : ℝ)) =
              (5373843003068197 / 21352452978172822 : ℝ)
            by
        norm_num];
        exact hau394)
  have hat1 :
    (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5373843003068197 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5373843003068197 : ℝ) =
              (5373843003068197 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau393)
  have hz1 :
    (10000000000000000 / 5373843003068197 : ℝ) ≤
      1 / Real.sqrt (231025508973 / 800000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 5373843003068197 : ℝ) =
          1 / (5373843003068197 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 2686921501534097 : ℝ) ≤
      (693346026735151028923 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (231025508973 / 800000000000 : ℝ) ≤
      (375000000000000 / 2686921501534097 : ℝ) := by
    rw [show
        (375000000000000 / 2686921501534097 : ℝ) =
          (3 / 40) / (2686921501534097 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) -
        6 * (693346026735151028923 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (231025508973 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (231025508973 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((2686921501534097 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) -
          6 * (693346026735151028923 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (231025508973 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (231025508973 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (231025508973 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_312 :
    ((2541686626647727284469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3051828979774273160183 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5379491219040039 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) -
              6 * (277050931068611634373 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (37041824992933 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (37041824992933 / 128000000000000 : ℝ)) =
      Real.log (165041824992933 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((37041824992933 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (37761824992933 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2541686626647727284469 / 10000000000000000000000 : ℝ) ≤
      Real.log (165041824992933 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (37761824992933 / 128000000000000 : ℝ) ≤
      (-(3051828979774273160183 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (37761824992933 / 128000000000000 : ℝ) = (37761824992933 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37761824992933 / 32000000000000 : ℝ) ≤
            (413906921725726839817 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (5379491219040039 / 10000000000000000 : ℝ) ≤
      Real.sqrt (37041824992933 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (37041824992933 / 128000000000000 : ℝ) ≤
      (2689745609520021 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (37041824992933 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau396 :
    Real.arctan (5379491219040042 / 21355127730489379 : ℝ) ≤
      (1233860108985775068049 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau395 :
    Real.arctan (2689745609520021 / 5000000000000000 : ℝ) ≤
      (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11355127730489379 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2689745609520021 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2689745609520021 / 5000000000000000 : ℝ) /
                (1 + (11355127730489379 / 10000000000000000 : ℝ)) =
              (5379491219040042 / 21355127730489379 : ℝ)
            by
        norm_num];
        exact hau396)
  have hat1 :
    (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2689745609520021 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2689745609520021 : ℝ) =
              (2689745609520021 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau395)
  have hz1 :
    (5000000000000000 / 2689745609520021 : ℝ) ≤
      1 / Real.sqrt (37041824992933 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 2689745609520021 : ℝ) = 1 / (2689745609520021 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 1793163739680013 : ℝ) ≤
      (277050931068611634373 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (37041824992933 / 128000000000000 : ℝ) ≤
      (250000000000000 / 1793163739680013 : ℝ) := by
    rw [show
        (250000000000000 / 1793163739680013 : ℝ) =
          (3 / 40) / (5379491219040039 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) -
        6 * (277050931068611634373 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (37041824992933 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (37041824992933 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5379491219040039 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) -
          6 * (277050931068611634373 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (37041824992933 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (37041824992933 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (37041824992933 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
