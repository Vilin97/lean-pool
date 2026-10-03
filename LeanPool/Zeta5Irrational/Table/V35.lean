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

/-! # V35: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_421 :
    ((1860131738235363403791 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1569226225604356732877 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3356602458448497 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) -
              6 * (222517508356799869161 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (7210739241 / 16000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7210739241 / 16000000000 : ℝ)) = Real.log (23210739241 / 16000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((7210739241 / 16000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (7300739241 / 16000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1860131738235363403791 / 5000000000000000000000 : ℝ) ≤
      Real.log (23210739241 / 16000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (7300739241 / 16000000000 : ℝ) ≤
      (-(1569226225604356732877 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (7300739241 / 16000000000 : ℝ) = (7300739241 / 4000000000 : ℝ) / 2 ^ 2 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7300739241 / 4000000000 : ℝ) ≤
            (1203362495595643267123 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3356602458448497 / 5000000000000000 : ℝ) ≤ Real.sqrt (7210739241 / 16000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7210739241 / 16000000000 : ℝ) ≤ (6713204916896997 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7210739241 / 16000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau614 :
    Real.arctan (6713204916896997 / 22044381273284651 : ℝ) ≤
      (1478043914574713354633 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau613 :
    Real.arctan (6713204916896997 / 10000000000000000 : ℝ) ≤
      (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12044381273284651 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6713204916896997 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6713204916896997 / 10000000000000000 : ℝ) /
                (1 + (12044381273284651 / 10000000000000000 : ℝ)) =
              (6713204916896997 / 22044381273284651 : ℝ)
            by
        norm_num];
        exact hau614)
  have hat1 :
    (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6713204916896997 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6713204916896997 : ℝ) =
              (6713204916896997 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau613)
  have hz1 :
    (10000000000000000 / 6713204916896997 : ℝ) ≤ 1 / Real.sqrt (7210739241 / 16000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6713204916896997 : ℝ) =
          1 / (6713204916896997 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1118867486149499 : ℝ) ≤
      (222517508356799869161 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (7210739241 / 16000000000 : ℝ) ≤
      (125000000000000 / 1118867486149499 : ℝ) := by
    rw [show
        (125000000000000 / 1118867486149499 : ℝ) =
          (3 / 40) / (3356602458448497 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) -
        6 * (222517508356799869161 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7210739241 / 16000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7210739241 / 16000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3356602458448497 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) -
          6 * (222517508356799869161 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (7210739241 / 16000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7210739241 / 16000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7210739241 / 16000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_422 :
    ((116400839797190555333 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1957907560260822272463 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1679533701099709 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) -
              6 * (555888909335956105031 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1805333410003 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1805333410003 / 4000000000000 : ℝ)) =
      Real.log (5805333410003 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1805333410003 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1827833410003 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (116400839797190555333 / 312500000000000000000 : ℝ) ≤
      Real.log (5805333410003 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1827833410003 / 4000000000000 : ℝ) ≤
      (-(1957907560260822272463 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1827833410003 / 4000000000000 : ℝ) = (1827833410003 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1827833410003 / 1000000000000 : ℝ) ≤
            (1507828341239177727537 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1679533701099709 / 2500000000000000 : ℝ) ≤ Real.sqrt (1805333410003 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1805333410003 / 4000000000000 : ℝ) ≤ (6718134804398839 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1805333410003 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau616 :
    Real.arctan (6718134804398839 / 22047129751524842 : ℝ) ≤
      (2957786616188343050519 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau615 :
    Real.arctan (6718134804398839 / 10000000000000000 : ℝ) ≤
      (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6023564875762421 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6718134804398839 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6718134804398839 / 10000000000000000 : ℝ) /
                (1 + (6023564875762421 / 5000000000000000 : ℝ)) =
              (6718134804398839 / 22047129751524842 : ℝ)
            by
        norm_num];
        exact hau616)
  have hat1 :
    (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6718134804398839 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6718134804398839 : ℝ) =
              (6718134804398839 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau615)
  have hz1 :
    (10000000000000000 / 6718134804398839 : ℝ) ≤
      1 / Real.sqrt (1805333410003 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6718134804398839 : ℝ) =
          1 / (6718134804398839 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1679533701099709 : ℝ) ≤
      (555888909335956105031 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1805333410003 / 4000000000000 : ℝ) ≤
      (187500000000000 / 1679533701099709 : ℝ) := by
    rw [show
        (187500000000000 / 1679533701099709 : ℝ) =
          (3 / 40) / (1679533701099709 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) -
        6 * (555888909335956105031 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1805333410003 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1805333410003 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1679533701099709 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) -
          6 * (555888909335956105031 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1805333410003 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1805333410003 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1805333410003 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_423 :
    ((3729388189040054123869 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7817150351193086393177 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3361530538456403 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) -
              6 * (1110969860924394921403 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (451995502439 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (451995502439 / 1000000000000 : ℝ)) =
      Real.log (1451995502439 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((451995502439 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (457620502439 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3729388189040054123869 / 10000000000000000000000 : ℝ) ≤
      Real.log (1451995502439 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (457620502439 / 1000000000000 : ℝ) ≤
      (-(7817150351193086393177 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (457620502439 / 1000000000000 : ℝ) = (457620502439 / 250000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (457620502439 / 250000000000 : ℝ) ≤
            (6045793254806913606823 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3361530538456403 / 5000000000000000 : ℝ) ≤ Real.sqrt (451995502439 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (451995502439 / 1000000000000 : ℝ) ≤ (6723061076912809 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (451995502439 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau618 :
    Real.arctan (6723061076912809 / 22049877602859706 : ℝ) ≤
      (2959483383238434001347 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau617 :
    Real.arctan (6723061076912809 / 10000000000000000 : ℝ) ≤
      (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6024938801429853 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6723061076912809 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6723061076912809 / 10000000000000000 : ℝ) /
                (1 + (6024938801429853 / 5000000000000000 : ℝ)) =
              (6723061076912809 / 22049877602859706 : ℝ)
            by
        norm_num];
        exact hau618)
  have hat1 :
    (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6723061076912809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6723061076912809 : ℝ) =
              (6723061076912809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau617)
  have hz1 :
    (10000000000000000 / 6723061076912809 : ℝ) ≤
      1 / Real.sqrt (451995502439 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6723061076912809 : ℝ) =
          1 / (6723061076912809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3361530538456403 : ℝ) ≤
      (1110969860924394921403 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (451995502439 / 1000000000000 : ℝ) ≤
      (375000000000000 / 3361530538456403 : ℝ) := by
    rw [show
        (375000000000000 / 3361530538456403 : ℝ) =
          (3 / 40) / (3361530538456403 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) -
        6 * (1110969860924394921403 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (451995502439 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (451995502439 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3361530538456403 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) -
          6 * (1110969860924394921403 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (451995502439 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (451995502439 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (451995502439 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_424 :
    ((3733947424958614430597 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(975336424718981787153 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6727983742379657 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) -
              6 * (1110163662135900473617 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1810630609509 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1810630609509 / 4000000000000 : ℝ)) =
      Real.log (5810630609509 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1810630609509 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1833130609509 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3733947424958614430597 / 10000000000000000000000 : ℝ) ≤
      Real.log (5810630609509 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1833130609509 / 4000000000000 : ℝ) ≤
      (-(975336424718981787153 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1833130609509 / 4000000000000 : ℝ) = (1833130609509 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1833130609509 / 1000000000000 : ℝ) ≤
            (757531526031018212847 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6727983742379657 / 10000000000000000 : ℝ) ≤ Real.sqrt (1810630609509 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1810630609509 / 4000000000000 : ℝ) ≤ (336399187118983 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1810630609509 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau620 :
    Real.arctan (3363991871189830 / 11026312413859013 : ℝ) ≤
      (2961178134875425243097 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau619 :
    Real.arctan (336399187118983 / 500000000000000 : ℝ) ≤
      (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6026312413859013 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (336399187118983 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (336399187118983 / 500000000000000 : ℝ) /
                (1 + (6026312413859013 / 5000000000000000 : ℝ)) =
              (3363991871189830 / 11026312413859013 : ℝ)
            by
        norm_num];
        exact hau620)
  have hat1 :
    (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 336399187118983 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 336399187118983 : ℝ) =
              (336399187118983 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau619)
  have hz1 :
    (500000000000000 / 336399187118983 : ℝ) ≤ 1 / Real.sqrt (1810630609509 / 4000000000000 : ℝ) :=
  by
    rw [show (500000000000000 / 336399187118983 : ℝ) = 1 / (336399187118983 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6727983742379657 : ℝ) ≤
      (1110163662135900473617 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1810630609509 / 4000000000000 : ℝ) ≤
      (750000000000000 / 6727983742379657 : ℝ) := by
    rw [show
        (750000000000000 / 6727983742379657 : ℝ) =
          (3 / 40) / (6727983742379657 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) -
        6 * (1110163662135900473617 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1810630609509 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1810630609509 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6727983742379657 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) -
          6 * (1110163662135900473617 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1810630609509 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1810630609509 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1810630609509 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_425 :
    ((3738504583161202382823 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1557650664052654548403 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((841612851088889 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) -
              6 * (1109359215933374475979 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (906639604631 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (906639604631 / 2000000000000 : ℝ)) =
      Real.log (2906639604631 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((906639604631 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (917889604631 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3738504583161202382823 / 10000000000000000000000 : ℝ) ≤
      Real.log (2906639604631 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (917889604631 / 2000000000000 : ℝ) ≤
      (-(1557650664052654548403 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (917889604631 / 2000000000000 : ℝ) = (917889604631 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (917889604631 / 500000000000 : ℝ) ≤
            (1214938057147345451597 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (841612851088889 / 1250000000000000 : ℝ) ≤ Real.sqrt (906639604631 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (906639604631 / 2000000000000 : ℝ) ≤ (1346580561742223 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (906639604631 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau622 :
    Real.arctan (6732902808711115 / 22055371426528093 : ℝ) ≤
      (592574175131759472259 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau621 :
    Real.arctan (1346580561742223 / 2000000000000000 : ℝ) ≤
      (2 * (592574175131759472259 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12055371426528093 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1346580561742223 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1346580561742223 / 2000000000000000 : ℝ) /
                (1 + (12055371426528093 / 10000000000000000 : ℝ)) =
              (6732902808711115 / 22055371426528093 : ℝ)
            by
        norm_num];
        exact hau622)
  have hat1 :
    (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1346580561742223 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1346580561742223 : ℝ) =
              (1346580561742223 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau621)
  have hz1 :
    (2000000000000000 / 1346580561742223 : ℝ) ≤
      1 / Real.sqrt (906639604631 / 2000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1346580561742223 : ℝ) = 1 / (1346580561742223 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (93750000000000 / 841612851088889 : ℝ) ≤
      (1109359215933374475979 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (906639604631 / 2000000000000 : ℝ) ≤
      (93750000000000 / 841612851088889 : ℝ) := by
    rw [show
        (93750000000000 / 841612851088889 : ℝ) =
          (3 / 40) / (841612851088889 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) -
        6 * (1109359215933374475979 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (906639604631 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (906639604631 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((841612851088889 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) -
          6 * (1109359215933374475979 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (906639604631 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (906639604631 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (906639604631 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_426 :
    ((93576491638516288227 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7773836058532506180713 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1684454570947503 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) -
              6 * (1108556515976043602471 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (363185561803 / 800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (363185561803 / 800000000000 : ℝ)) =
      Real.log (1163185561803 / 800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((363185561803 / 800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (367685561803 / 800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (93576491638516288227 / 250000000000000000000 : ℝ) ≤
      Real.log (1163185561803 / 800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (367685561803 / 800000000000 : ℝ) ≤
      (-(7773836058532506180713 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (367685561803 / 800000000000 : ℝ) = (367685561803 / 200000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (367685561803 / 200000000000 : ℝ) ≤
            (6089107547467493819287 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1684454570947503 / 2500000000000000 : ℝ) ≤ Real.sqrt (363185561803 / 800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (363185561803 / 800000000000 : ℝ) ≤ (1347563656758003 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (363185561803 / 800000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau624 :
    Real.arctan (1347563656758003 / 4411623479943542 : ℝ) ≤
      (1482280805065932959781 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau623 :
    Real.arctan (1347563656758003 / 2000000000000000 : ℝ) ≤
      (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1205811739971771 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1347563656758003 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1347563656758003 / 2000000000000000 : ℝ) /
                (1 + (1205811739971771 / 1000000000000000 : ℝ)) =
              (1347563656758003 / 4411623479943542 : ℝ)
            by
        norm_num];
        exact hau624)
  have hat1 :
    (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1347563656758003 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1347563656758003 : ℝ) =
              (1347563656758003 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau623)
  have hz1 :
    (2000000000000000 / 1347563656758003 : ℝ) ≤ 1 / Real.sqrt (363185561803 / 800000000000 : ℝ) :=
  by
    rw [show
        (2000000000000000 / 1347563656758003 : ℝ) = 1 / (1347563656758003 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (62500000000000 / 561484856982501 : ℝ) ≤
      (1108556515976043602471 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (363185561803 / 800000000000 : ℝ) ≤
      (62500000000000 / 561484856982501 : ℝ) := by
    rw [show
        (62500000000000 / 561484856982501 : ℝ) =
          (3 / 40) / (1684454570947503 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) -
        6 * (1108556515976043602471 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (363185561803 / 800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (363185561803 / 800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1684454570947503 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) -
          6 * (1108556515976043602471 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (363185561803 / 800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (363185561803 / 800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (363185561803 / 800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_427 :
    ((1873806336993604995811 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3879719776312348896627 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3371365087735233 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) -
              6 * (1107755555955205237929 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (28415256387 / 62500000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (28415256387 / 62500000000 : ℝ)) = Real.log (90915256387 / 62500000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((28415256387 / 62500000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (28766818887 / 62500000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1873806336993604995811 / 5000000000000000000000 : ℝ) ≤
      Real.log (90915256387 / 62500000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (28766818887 / 62500000000 : ℝ) ≤
      (-(3879719776312348896627 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (28766818887 / 62500000000 : ℝ) = (28766818887 / 15625000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28766818887 / 15625000000 : ℝ) ≤
            (3051752026687651103373 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3371365087735233 / 5000000000000000 : ℝ) ≤ Real.sqrt (28415256387 / 62500000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (28415256387 / 62500000000 : ℝ) ≤ (6742730175470469 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (28415256387 / 62500000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau626 :
    Real.arctan (6742730175470469 / 22060862747714194 : ℝ) ≤
      (92695323213183203139 / 312500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau625 :
    Real.arctan (6742730175470469 / 10000000000000000 : ℝ) ≤
      (2 * (92695323213183203139 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6030431373857097 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6742730175470469 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6742730175470469 / 10000000000000000 : ℝ) /
                (1 + (6030431373857097 / 5000000000000000 : ℝ)) =
              (6742730175470469 / 22060862747714194 : ℝ)
            by
        norm_num];
        exact hau626)
  have hat1 :
    (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6742730175470469 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6742730175470469 : ℝ) =
              (6742730175470469 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau625)
  have hz1 :
    (10000000000000000 / 6742730175470469 : ℝ) ≤ 1 / Real.sqrt (28415256387 / 62500000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6742730175470469 : ℝ) =
          1 / (6742730175470469 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1123788362578411 : ℝ) ≤
      (1107755555955205237929 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (28415256387 / 62500000000 : ℝ) ≤
      (125000000000000 / 1123788362578411 : ℝ) := by
    rw [show
        (125000000000000 / 1123788362578411 : ℝ) =
          (3 / 40) / (3371365087735233 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) -
        6 * (1107755555955205237929 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (28415256387 / 62500000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (28415256387 / 62500000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3371365087735233 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) -
          6 * (1107755555955205237929 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (28415256387 / 62500000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (28415256387 / 62500000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (28415256387 / 62500000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_428 :
    ((938040902597136293219 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(968132967857934315427 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1686909622894499 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) -
              6 * (2213912659188038901 / 20000000000000000000 : ℝ)))) ≤
      Vfield (1821225008521 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1821225008521 / 4000000000000 : ℝ)) =
      Real.log (5821225008521 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1821225008521 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1843725008521 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (938040902597136293219 / 2500000000000000000000 : ℝ) ≤
      Real.log (5821225008521 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1843725008521 / 4000000000000 : ℝ) ≤
      (-(968132967857934315427 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1843725008521 / 4000000000000 : ℝ) = (1843725008521 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1843725008521 / 1000000000000 : ℝ) ≤
            (764734982892065684573 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1686909622894499 / 2500000000000000 : ℝ) ≤ Real.sqrt (1821225008521 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1821225008521 / 4000000000000 : ℝ) ≤ (6747638491577999 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1821225008521 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau628 :
    Real.arctan (6747638491577999 / 22063607470944377 : ℝ) ≤
      (593587415648002736951 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau627 :
    Real.arctan (6747638491577999 / 10000000000000000 : ℝ) ≤
      (2 * (593587415648002736951 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12063607470944377 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6747638491577999 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6747638491577999 / 10000000000000000 : ℝ) /
                (1 + (12063607470944377 / 10000000000000000 : ℝ)) =
              (6747638491577999 / 22063607470944377 : ℝ)
            by
        norm_num];
        exact hau628)
  have hat1 :
    (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6747638491577999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6747638491577999 : ℝ) =
              (6747638491577999 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau627)
  have hz1 :
    (10000000000000000 / 6747638491577999 : ℝ) ≤
      1 / Real.sqrt (1821225008521 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6747638491577999 : ℝ) =
          1 / (6747638491577999 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (187500000000000 / 1686909622894499 : ℝ) ≤
      (2213912659188038901 / 20000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1821225008521 / 4000000000000 : ℝ) ≤
      (187500000000000 / 1686909622894499 : ℝ) := by
    rw [show
        (187500000000000 / 1686909622894499 : ℝ) =
          (3 / 40) / (1686909622894499 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) -
        6 * (2213912659188038901 / 20000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1821225008521 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1821225008521 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1686909622894499 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) -
          6 * (2213912659188038901 / 20000000000000000000 : ℝ))) ≤
      Real.sqrt (1821225008521 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1821225008521 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1821225008521 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_429 :
    ((3756712476629748451179 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(386535428491473142307 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1350508647981937 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) -
              6 * (276539707661825492393 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (911936804137 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (911936804137 / 2000000000000 : ℝ)) =
      Real.log (2911936804137 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((911936804137 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (923186804137 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3756712476629748451179 / 10000000000000000000000 : ℝ) ≤
      Real.log (2911936804137 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (923186804137 / 2000000000000 : ℝ) ≤
      (-(386535428491473142307 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (923186804137 / 2000000000000 : ℝ) = (923186804137 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (923186804137 / 500000000000 : ℝ) ≤
            (306611751808526857693 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1350508647981937 / 2000000000000000 : ℝ) ≤ Real.sqrt (911936804137 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (911936804137 / 2000000000000 : ℝ) ≤ (844067904988711 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (911936804137 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau630 :
    Real.arctan (6752543239909688 / 22066351569834603 : ℝ) ≤
      (1484810910440810834293 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau629 :
    Real.arctan (844067904988711 / 1250000000000000 : ℝ) ≤
      (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12066351569834603 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (844067904988711 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (844067904988711 / 1250000000000000 : ℝ) /
                (1 + (12066351569834603 / 10000000000000000 : ℝ)) =
              (6752543239909688 / 22066351569834603 : ℝ)
            by
        norm_num];
        exact hau630)
  have hat1 :
    (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 844067904988711 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 844067904988711 : ℝ) =
              (844067904988711 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau629)
  have hz1 :
    (1250000000000000 / 844067904988711 : ℝ) ≤ 1 / Real.sqrt (911936804137 / 2000000000000 : ℝ) :=
  by
    rw [show
        (1250000000000000 / 844067904988711 : ℝ) = 1 / (844067904988711 / 1250000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1350508647981937 : ℝ) ≤
      (276539707661825492393 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (911936804137 / 2000000000000 : ℝ) ≤
      (150000000000000 / 1350508647981937 : ℝ) := by
    rw [show
        (150000000000000 / 1350508647981937 : ℝ) =
          (3 / 40) / (1350508647981937 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) -
        6 * (276539707661825492393 / 2500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (911936804137 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (911936804137 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1350508647981937 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) -
          6 * (276539707661825492393 / 2500000000000000000000 : ℝ))) ≤
      Real.sqrt (911936804137 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (911936804137 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (911936804137 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_430 :
    ((3761259274593339865841 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1929093493589703793197 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3378722214117157 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) -
              6 * (1105363052901320432927 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1826522208027 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1826522208027 / 4000000000000 : ℝ)) =
      Real.log (5826522208027 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1826522208027 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1849022208027 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3761259274593339865841 / 10000000000000000000000 : ℝ) ≤
      Real.log (5826522208027 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1849022208027 / 4000000000000 : ℝ) ≤
      (-(1929093493589703793197 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1849022208027 / 4000000000000 : ℝ) = (1849022208027 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1849022208027 / 1000000000000 : ℝ) ≤
            (1536642407910296206803 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3378722214117157 / 5000000000000000 : ℝ) ≤ Real.sqrt (1826522208027 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1826522208027 / 4000000000000 : ℝ) ≤ (6757444428234317 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1826522208027 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau632 :
    Real.arctan (6757444428234317 / 22069095044810733 : ℝ) ≤
      (2971304575226139195549 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau631 :
    Real.arctan (6757444428234317 / 10000000000000000 : ℝ) ≤
      (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12069095044810733 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6757444428234317 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6757444428234317 / 10000000000000000 : ℝ) /
                (1 + (12069095044810733 / 10000000000000000 : ℝ)) =
              (6757444428234317 / 22069095044810733 : ℝ)
            by
        norm_num];
        exact hau632)
  have hat1 :
    (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6757444428234317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6757444428234317 : ℝ) =
              (6757444428234317 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau631)
  have hz1 :
    (10000000000000000 / 6757444428234317 : ℝ) ≤
      1 / Real.sqrt (1826522208027 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6757444428234317 : ℝ) =
          1 / (6757444428234317 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3378722214117157 : ℝ) ≤
      (1105363052901320432927 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1826522208027 / 4000000000000 : ℝ) ≤
      (375000000000000 / 3378722214117157 : ℝ) := by
    rw [show
        (375000000000000 / 3378722214117157 : ℝ) =
          (3 / 40) / (3378722214117157 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) -
        6 * (1105363052901320432927 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1826522208027 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1826522208027 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3378722214117157 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) -
          6 * (1105363052901320432927 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (1826522208027 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1826522208027 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1826522208027 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_431 :
    ((1882902003079636395783 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1925514974385436700747 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6762342064292517 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) -
              6 * (1104568990173589174241 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (91458540389 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (91458540389 / 200000000000 : ℝ)) =
      Real.log (291458540389 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((91458540389 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (92583540389 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1882902003079636395783 / 5000000000000000000000 : ℝ) ≤
      Real.log (291458540389 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (92583540389 / 200000000000 : ℝ) ≤
      (-(1925514974385436700747 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (92583540389 / 200000000000 : ℝ) = (92583540389 / 50000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (92583540389 / 50000000000 : ℝ) ≤
            (1540220927114563299253 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6762342064292517 / 10000000000000000 : ℝ) ≤ Real.sqrt (91458540389 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (91458540389 / 200000000000 : ℝ) ≤ (169058551607313 / 250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (91458540389 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau634 :
    Real.arctan (6762342064292520 / 22071837896298143 : ℝ) ≤
      (2972985345737252723841 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau633 :
    Real.arctan (169058551607313 / 250000000000000 : ℝ) ≤
      (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12071837896298143 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (169058551607313 / 250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (169058551607313 / 250000000000000 : ℝ) /
                (1 + (12071837896298143 / 10000000000000000 : ℝ)) =
              (6762342064292520 / 22071837896298143 : ℝ)
            by
        norm_num];
        exact hau634)
  have hat1 :
    (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (250000000000000 / 169058551607313 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 169058551607313 : ℝ) =
              (169058551607313 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hau633)
  have hz1 :
    (250000000000000 / 169058551607313 : ℝ) ≤ 1 / Real.sqrt (91458540389 / 200000000000 : ℝ) := by
    rw [show (250000000000000 / 169058551607313 : ℝ) = 1 / (169058551607313 / 250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2254114021430839 : ℝ) ≤
      (1104568990173589174241 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (91458540389 / 200000000000 : ℝ) ≤
      (250000000000000 / 2254114021430839 : ℝ) := by
    rw [show
        (250000000000000 / 2254114021430839 : ℝ) =
          (3 / 40) / (6762342064292517 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) -
        6 * (1104568990173589174241 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (91458540389 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (91458540389 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6762342064292517 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) -
          6 * (1104568990173589174241 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (91458540389 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (91458540389 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (91458540389 / 200000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_432 :
    ((1885173336602469301127 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(768776628072108333261 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6767236155796913 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) -
              6 * (551888318156334600501 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1831819407533 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1831819407533 / 4000000000000 : ℝ)) =
      Real.log (5831819407533 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1831819407533 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1854319407533 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1885173336602469301127 / 5000000000000000000000 : ℝ) ≤
      Real.log (5831819407533 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1854319407533 / 4000000000000 : ℝ) ≤
      (-(768776628072108333261 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1854319407533 / 4000000000000 : ℝ) = (1854319407533 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1854319407533 / 1000000000000 : ℝ) ≤
            (617517732527891666739 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6767236155796913 / 10000000000000000 : ℝ) ≤ Real.sqrt (1831819407533 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1831819407533 / 4000000000000 : ℝ) ≤ (1691809038949229 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1831819407533 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau636 :
    Real.arctan (1691809038949229 / 5518645031180432 : ℝ) ≤
      (2974664136862955190747 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau635 :
    Real.arctan (1691809038949229 / 2500000000000000 : ℝ) ≤
      (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (188665314448777 / 156250000000000 : ℝ) ≤
          Real.sqrt (1 + (1691809038949229 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1691809038949229 / 2500000000000000 : ℝ) /
                (1 + (188665314448777 / 156250000000000 : ℝ)) =
              (1691809038949229 / 5518645031180432 : ℝ)
            by
        norm_num];
        exact hau636)
  have hat1 :
    (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1691809038949229 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1691809038949229 : ℝ) =
              (1691809038949229 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau635)
  have hz1 :
    (2500000000000000 / 1691809038949229 : ℝ) ≤
      1 / Real.sqrt (1831819407533 / 4000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1691809038949229 : ℝ) = 1 / (1691809038949229 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6767236155796913 : ℝ) ≤
      (551888318156334600501 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1831819407533 / 4000000000000 : ℝ) ≤
      (750000000000000 / 6767236155796913 : ℝ) := by
    rw [show
        (750000000000000 / 6767236155796913 : ℝ) =
          (3 / 40) / (6767236155796913 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) -
        6 * (551888318156334600501 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1831819407533 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1831819407533 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6767236155796913 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) -
          6 * (551888318156334600501 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1831819407533 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1831819407533 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1831819407533 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
