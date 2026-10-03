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

/-! # V40: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_481 :
    ((536605400492879213153 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(306445109372711187137 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7322279244099123 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3160148103563553089317 / 10000000000000000000000 : ℝ))) -
              6 * (10207116303724433279 / 100000000000000000000 : ℝ)))) ≤
      Vfield (68628189860563 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (68628189860563 / 128000000000000 : ℝ)) =
      Real.log (196628189860563 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((68628189860563 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69348189860563 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (536605400492879213153 / 1250000000000000000000 : ℝ) ≤
      Real.log (196628189860563 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69348189860563 / 128000000000000 : ℝ) ≤
      (-(306445109372711187137 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69348189860563 / 128000000000000 : ℝ) = (69348189860563 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69348189860563 / 64000000000000 : ℝ) ≤
            (40128480777288812863 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7322279244099123 / 10000000000000000 : ℝ) ≤
      Real.sqrt (68628189860563 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (68628189860563 / 128000000000000 : ℝ) ≤
      (3661139622049563 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (68628189860563 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau734 :
    Real.arctan (2440759748033042 / 7464727681338547 : ℝ) ≤
      (3160148103563553089317 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau733 :
    Real.arctan (3661139622049563 / 5000000000000000 : ℝ) ≤
      (2 * (3160148103563553089317 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12394183044015641 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3661139622049563 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3661139622049563 / 5000000000000000 : ℝ) /
                (1 + (12394183044015641 / 10000000000000000 : ℝ)) =
              (2440759748033042 / 7464727681338547 : ℝ)
            by
        norm_num];
        exact hau734)
  have hat1 :
    (Real.pi / 2 - (2 * (3160148103563553089317 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3661139622049563 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3661139622049563 : ℝ) =
              (3661139622049563 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau733)
  have hz1 :
    (5000000000000000 / 3661139622049563 : ℝ) ≤
      1 / Real.sqrt (68628189860563 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3661139622049563 : ℝ) = 1 / (3661139622049563 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2440759748033041 : ℝ) ≤
      (10207116303724433279 / 100000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (68628189860563 / 128000000000000 : ℝ) ≤
      (250000000000000 / 2440759748033041 : ℝ) := by
    rw [show
        (250000000000000 / 2440759748033041 : ℝ) =
          (3 / 40) / (7322279244099123 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3160148103563553089317 / 10000000000000000000000 : ℝ))) -
        6 * (10207116303724433279 / 100000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (68628189860563 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (68628189860563 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7322279244099123 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3160148103563553089317 / 10000000000000000000000 : ℝ))) -
          6 * (10207116303724433279 / 100000000000000000000 : ℝ))) ≤
      Real.sqrt (68628189860563 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (68628189860563 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (68628189860563 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_482 :
    ((537113152319473669229 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(122347782789297651323 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1465307953368911 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3161534568468916080673 / 10000000000000000000000 : ℝ))) -
              6 * (1020122177634482114133 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (34354038371299 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34354038371299 / 64000000000000 : ℝ)) =
      Real.log (98354038371299 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34354038371299 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34714038371299 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (537113152319473669229 / 1250000000000000000000 : ℝ) ≤
      Real.log (98354038371299 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34714038371299 / 64000000000000 : ℝ) ≤
      (-(122347782789297651323 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34714038371299 / 64000000000000 : ℝ) = (34714038371299 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34714038371299 / 32000000000000 : ℝ) ≤
            (16281653270702348677 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1465307953368911 / 2000000000000000 : ℝ) ≤ Real.sqrt (34354038371299 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34354038371299 / 64000000000000 : ℝ) ≤ (3663269883422279 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34354038371299 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau736 :
    Real.arctan (3663269883422279 / 11198350283647147 : ℝ) ≤
      (3161534568468916080673 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau735 :
    Real.arctan (3663269883422279 / 5000000000000000 : ℝ) ≤
      (2 * (3161534568468916080673 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6198350283647147 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3663269883422279 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3663269883422279 / 5000000000000000 : ℝ) /
                (1 + (6198350283647147 / 5000000000000000 : ℝ)) =
              (3663269883422279 / 11198350283647147 : ℝ)
            by
        norm_num];
        exact hau736)
  have hat1 :
    (Real.pi / 2 - (2 * (3161534568468916080673 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3663269883422279 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3663269883422279 : ℝ) =
              (3663269883422279 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau735)
  have hz1 :
    (5000000000000000 / 3663269883422279 : ℝ) ≤
      1 / Real.sqrt (34354038371299 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3663269883422279 : ℝ) = 1 / (3663269883422279 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (150000000000000 / 1465307953368911 : ℝ) ≤
      (1020122177634482114133 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (34354038371299 / 64000000000000 : ℝ) ≤
      (150000000000000 / 1465307953368911 : ℝ) := by
    rw [show
        (150000000000000 / 1465307953368911 : ℝ) =
          (3 / 40) / (1465307953368911 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3161534568468916080673 / 10000000000000000000000 : ℝ))) -
        6 * (1020122177634482114133 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34354038371299 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34354038371299 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1465307953368911 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3161534568468916080673 / 10000000000000000000000 : ℝ))) -
          6 * (1020122177634482114133 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (34354038371299 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34354038371299 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34354038371299 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_483 :
    ((4300965583842209674487 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6105889331261373677087 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((293231912538167 / 400000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1581459832479321819787 / 5000000000000000000000 : ℝ))) -
              6 * (1019533744940917633747 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (68787963624633 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (68787963624633 / 128000000000000 : ℝ)) =
      Real.log (196787963624633 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((68787963624633 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69507963624633 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4300965583842209674487 / 10000000000000000000000 : ℝ) ≤
      Real.log (196787963624633 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69507963624633 / 128000000000000 : ℝ) ≤
      (-(6105889331261373677087 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69507963624633 / 128000000000000 : ℝ) = (69507963624633 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69507963624633 / 64000000000000 : ℝ) ≤
            (825582471738626322913 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (293231912538167 / 400000000000000 : ℝ) ≤ Real.sqrt (68787963624633 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (68787963624633 / 128000000000000 : ℝ) ≤
      (3665398906727089 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (68787963624633 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau738 :
    Real.arctan (7330797813454178 / 22399217579417845 : ℝ) ≤
      (1581459832479321819787 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau737 :
    Real.arctan (3665398906727089 / 5000000000000000 : ℝ) ≤
      (2 * (1581459832479321819787 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2479843515883569 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3665398906727089 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3665398906727089 / 5000000000000000 : ℝ) /
                (1 + (2479843515883569 / 2000000000000000 : ℝ)) =
              (7330797813454178 / 22399217579417845 : ℝ)
            by
        norm_num];
        exact hau738)
  have hat1 :
    (Real.pi / 2 - (2 * (1581459832479321819787 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3665398906727089 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3665398906727089 : ℝ) =
              (3665398906727089 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau737)
  have hz1 :
    (5000000000000000 / 3665398906727089 : ℝ) ≤
      1 / Real.sqrt (68787963624633 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3665398906727089 : ℝ) = 1 / (3665398906727089 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (30000000000000 / 293231912538167 : ℝ) ≤
      (1019533744940917633747 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (68787963624633 / 128000000000000 : ℝ) ≤
      (30000000000000 / 293231912538167 : ℝ) := by
    rw [show
        (30000000000000 / 293231912538167 : ℝ) =
          (3 / 40) / (293231912538167 / 400000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1581459832479321819787 / 5000000000000000000000 : ℝ))) -
        6 * (1019533744940917633747 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (68787963624633 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (68787963624633 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((293231912538167 / 400000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1581459832479321819787 / 5000000000000000000000 : ℝ))) -
          6 * (1019533744940917633747 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (68787963624633 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (68787963624633 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (68787963624633 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_484 :
    ((2152512150570562284839 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6094402732427668675489 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7335053388240221 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (791075848886423354773 / 2500000000000000000000 : ℝ))) -
              6 * (203789265870628778459 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (17216962626667 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17216962626667 / 32000000000000 : ℝ)) =
      Real.log (49216962626667 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17216962626667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (17396962626667 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2152512150570562284839 / 5000000000000000000000 : ℝ) ≤
      Real.log (49216962626667 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (17396962626667 / 32000000000000 : ℝ) ≤
      (-(6094402732427668675489 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17396962626667 / 32000000000000 : ℝ) = (17396962626667 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17396962626667 / 16000000000000 : ℝ) ≤
            (837069070572331324511 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7335053388240221 / 10000000000000000 : ℝ) ≤
      Real.sqrt (17216962626667 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17216962626667 / 32000000000000 : ℝ) ≤ (229220418382507 / 312500000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17216962626667 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau740 :
    Real.arctan (458440836765014 / 1400108380043595 : ℝ) ≤
      (791075848886423354773 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau739 :
    Real.arctan (229220418382507 / 312500000000000 : ℝ) ≤
      (2 * (791075848886423354773 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (155021676008719 / 125000000000000 : ℝ) ≤
          Real.sqrt (1 + (229220418382507 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (229220418382507 / 312500000000000 : ℝ) /
                (1 + (155021676008719 / 125000000000000 : ℝ)) =
              (458440836765014 / 1400108380043595 : ℝ)
            by
        norm_num];
        exact hau740)
  have hat1 :
    (Real.pi / 2 - (2 * (791075848886423354773 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 229220418382507 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 229220418382507 : ℝ) =
              (229220418382507 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau739)
  have hz1 :
    (312500000000000 / 229220418382507 : ℝ) ≤
      1 / Real.sqrt (17216962626667 / 32000000000000 : ℝ) := by
    rw [show (312500000000000 / 229220418382507 : ℝ) = 1 / (229220418382507 / 312500000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7335053388240221 : ℝ) ≤
      (203789265870628778459 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17216962626667 / 32000000000000 : ℝ) ≤
      (750000000000000 / 7335053388240221 : ℝ) := by
    rw [show
        (750000000000000 / 7335053388240221 : ℝ) =
          (3 / 40) / (7335053388240221 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (791075848886423354773 / 2500000000000000000000 : ℝ))) -
        6 * (203789265870628778459 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17216962626667 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17216962626667 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7335053388240221 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (791075848886423354773 / 2500000000000000000000 : ℝ))) -
          6 * (203789265870628778459 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (17216962626667 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17216962626667 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17216962626667 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_485 :
    ((4309081371789734423577 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3041464656326215977173 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((229353327984451 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3165685762735902141383 / 10000000000000000000000 : ℝ))) -
              6 * (1018359927944392969983 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (68947737388703 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (68947737388703 / 128000000000000 : ℝ)) =
      Real.log (196947737388703 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((68947737388703 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69667737388703 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4309081371789734423577 / 10000000000000000000000 : ℝ) ≤
      Real.log (196947737388703 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69667737388703 / 128000000000000 : ℝ) ≤
      (-(3041464656326215977173 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69667737388703 / 128000000000000 : ℝ) = (69667737388703 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69667737388703 / 64000000000000 : ℝ) ≤
            (424271245173784022827 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (229353327984451 / 312500000000000 : ℝ) ≤ Real.sqrt (68947737388703 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (68947737388703 / 128000000000000 : ℝ) ≤
      (1467861299100487 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (68947737388703 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau742 :
    Real.arctan (1467861299100487 / 4480850014288846 : ℝ) ≤
      (3165685762735902141383 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau741 :
    Real.arctan (1467861299100487 / 2000000000000000 : ℝ) ≤
      (2 * (3165685762735902141383 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1240425007144423 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1467861299100487 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1467861299100487 / 2000000000000000 : ℝ) /
                (1 + (1240425007144423 / 1000000000000000 : ℝ)) =
              (1467861299100487 / 4480850014288846 : ℝ)
            by
        norm_num];
        exact hau742)
  have hat1 :
    (Real.pi / 2 - (2 * (3165685762735902141383 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1467861299100487 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1467861299100487 : ℝ) =
              (1467861299100487 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau741)
  have hz1 :
    (2000000000000000 / 1467861299100487 : ℝ) ≤
      1 / Real.sqrt (68947737388703 / 128000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1467861299100487 : ℝ) = 1 / (1467861299100487 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (23437500000000 / 229353327984451 : ℝ) ≤
      (1018359927944392969983 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (68947737388703 / 128000000000000 : ℝ) ≤
      (23437500000000 / 229353327984451 : ℝ) := by
    rw [show
        (23437500000000 / 229353327984451 : ℝ) =
          (3 / 40) / (229353327984451 / 312500000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3165685762735902141383 / 10000000000000000000000 : ℝ))) -
        6 * (1018359927944392969983 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (68947737388703 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (68947737388703 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((229353327984451 / 312500000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3165685762735902141383 / 10000000000000000000000 : ℝ))) -
          6 * (1018359927944392969983 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (68947737388703 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (68947737388703 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (68947737388703 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_486 :
    ((4313136797123612745393 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3035734520864270388191 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3671778569764047 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (633413353805602304743 / 2000000000000000000000 : ℝ))) -
              6 * (6361090861247965123 / 62500000000000000000 : ℝ)))) ≤
      Vfield (34513812135369 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34513812135369 / 64000000000000 : ℝ)) =
      Real.log (98513812135369 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34513812135369 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (34873812135369 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4313136797123612745393 / 10000000000000000000000 : ℝ) ≤
      Real.log (98513812135369 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (34873812135369 / 64000000000000 : ℝ) ≤
      (-(3035734520864270388191 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34873812135369 / 64000000000000 : ℝ) = (34873812135369 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34873812135369 / 32000000000000 : ℝ) ≤
            (430001380635729611809 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3671778569764047 / 5000000000000000 : ℝ) ≤ Real.sqrt (34513812135369 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34513812135369 / 64000000000000 : ℝ) ≤
      (7343557139528097 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34513812135369 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau744 :
    Real.arctan (2447852379842699 / 7468921850656191 : ℝ) ≤
      (633413353805602304743 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau743 :
    Real.arctan (7343557139528097 / 10000000000000000 : ℝ) ≤
      (2 * (633413353805602304743 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12406765551968573 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7343557139528097 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7343557139528097 / 10000000000000000 : ℝ) /
                (1 + (12406765551968573 / 10000000000000000 : ℝ)) =
              (2447852379842699 / 7468921850656191 : ℝ)
            by
        norm_num];
        exact hau744)
  have hat1 :
    (Real.pi / 2 - (2 * (633413353805602304743 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7343557139528097 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7343557139528097 : ℝ) =
              (7343557139528097 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau743)
  have hz1 :
    (10000000000000000 / 7343557139528097 : ℝ) ≤
      1 / Real.sqrt (34513812135369 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7343557139528097 : ℝ) =
          1 / (7343557139528097 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (125000000000000 / 1223926189921349 : ℝ) ≤
      (6361090861247965123 / 62500000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (34513812135369 / 64000000000000 : ℝ) ≤
      (125000000000000 / 1223926189921349 : ℝ) := by
    rw [show
        (125000000000000 / 1223926189921349 : ℝ) =
          (3 / 40) / (3671778569764047 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (633413353805602304743 / 2000000000000000000000 : ℝ))) -
        6 * (6361090861247965123 / 62500000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34513812135369 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34513812135369 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3671778569764047 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (633413353805602304743 / 2000000000000000000000 : ℝ))) -
          6 * (6361090861247965123 / 62500000000000000000 : ℝ))) ≤
      Real.sqrt (34513812135369 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34513812135369 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34513812135369 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_487 :
    ((1079297644619177201843 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6060021889552608097611 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7347805324592091 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (63368928338273947477 / 200000000000000000000 : ℝ))) -
              6 * (127148769501964290459 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (69107511152773 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (69107511152773 / 128000000000000 : ℝ)) =
      Real.log (197107511152773 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((69107511152773 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69827511152773 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1079297644619177201843 / 2500000000000000000000 : ℝ) ≤
      Real.log (197107511152773 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69827511152773 / 128000000000000 : ℝ) ≤
      (-(6060021889552608097611 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69827511152773 / 128000000000000 : ℝ) = (69827511152773 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69827511152773 / 64000000000000 : ℝ) ≤
            (871449913447391902389 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7347805324592091 / 10000000000000000 : ℝ) ≤
      Real.sqrt (69107511152773 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (69107511152773 / 128000000000000 : ℝ) ≤
      (3673902662296047 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (69107511152773 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau746 :
    Real.arctan (2449268441530698 / 7469760174193609 : ℝ) ≤
      (63368928338273947477 / 200000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau745 :
    Real.arctan (3673902662296047 / 5000000000000000 : ℝ) ≤
      (2 * (63368928338273947477 / 200000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12409280522580827 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3673902662296047 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3673902662296047 / 5000000000000000 : ℝ) /
                (1 + (12409280522580827 / 10000000000000000 : ℝ)) =
              (2449268441530698 / 7469760174193609 : ℝ)
            by
        norm_num];
        exact hau746)
  have hat1 :
    (Real.pi / 2 - (2 * (63368928338273947477 / 200000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3673902662296047 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3673902662296047 : ℝ) =
              (3673902662296047 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau745)
  have hz1 :
    (5000000000000000 / 3673902662296047 : ℝ) ≤
      1 / Real.sqrt (69107511152773 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3673902662296047 : ℝ) = 1 / (3673902662296047 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2449268441530697 : ℝ) ≤
      (127148769501964290459 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (69107511152773 / 128000000000000 : ℝ) ≤
      (250000000000000 / 2449268441530697 : ℝ) := by
    rw [show
        (250000000000000 / 2449268441530697 : ℝ) =
          (3 / 40) / (7347805324592091 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (63368928338273947477 / 200000000000000000000 : ℝ))) -
        6 * (127148769501964290459 / 1250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (69107511152773 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (69107511152773 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7347805324592091 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (63368928338273947477 / 200000000000000000000 : ℝ))) -
          6 * (127148769501964290459 / 1250000000000000000000 : ℝ))) ≤
      Real.sqrt (69107511152773 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (69107511152773 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (69107511152773 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_488 :
    ((4321242717181350277451 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1209717565224901623787 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7352051054956959 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (79245617721939937011 / 250000000000000000000 : ℝ))) -
              6 * (1016606779700894286959 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (8648424754351 / 16000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8648424754351 / 16000000000000 : ℝ)) =
      Real.log (24648424754351 / 16000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8648424754351 / 16000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (8738424754351 / 16000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4321242717181350277451 / 10000000000000000000000 : ℝ) ≤
      Real.log (24648424754351 / 16000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (8738424754351 / 16000000000000 : ℝ) ≤
      (-(1209717565224901623787 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8738424754351 / 16000000000000 : ℝ) = (8738424754351 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8738424754351 / 8000000000000 : ℝ) ≤
            (176576795375098376213 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7352051054956959 / 10000000000000000 : ℝ) ≤ Real.sqrt (8648424754351 / 16000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8648424754351 / 16000000000000 : ℝ) ≤ (3676025527478481 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8648424754351 / 16000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau748 :
    Real.arctan (7352051054956962 / 22411794983590961 : ℝ) ≤
      (79245617721939937011 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau747 :
    Real.arctan (3676025527478481 / 5000000000000000 : ℝ) ≤
      (2 * (79245617721939937011 / 250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12411794983590961 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3676025527478481 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3676025527478481 / 5000000000000000 : ℝ) /
                (1 + (12411794983590961 / 10000000000000000 : ℝ)) =
              (7352051054956962 / 22411794983590961 : ℝ)
            by
        norm_num];
        exact hau748)
  have hat1 :
    (Real.pi / 2 - (2 * (79245617721939937011 / 250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3676025527478481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3676025527478481 : ℝ) =
              (3676025527478481 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau747)
  have hz1 :
    (5000000000000000 / 3676025527478481 : ℝ) ≤
      1 / Real.sqrt (8648424754351 / 16000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3676025527478481 : ℝ) = 1 / (3676025527478481 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2450683684985653 : ℝ) ≤
      (1016606779700894286959 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (8648424754351 / 16000000000000 : ℝ) ≤
      (250000000000000 / 2450683684985653 : ℝ) := by
    rw [show
        (250000000000000 / 2450683684985653 : ℝ) =
          (3 / 40) / (7352051054956959 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (79245617721939937011 / 250000000000000000000 : ℝ))) -
        6 * (1016606779700894286959 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8648424754351 / 16000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8648424754351 / 16000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7352051054956959 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (79245617721939937011 / 250000000000000000000 : ℝ))) -
          6 * (1016606779700894286959 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (8648424754351 / 16000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8648424754351 / 16000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8648424754351 / 16000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_489 :
    ((270330825910515365411 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6037166821546904547073 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7356294334872931 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1585600823698669241149 / 5000000000000000000000 : ℝ))) -
              6 * (508012202987596007037 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (69267284916843 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (69267284916843 / 128000000000000 : ℝ)) =
      Real.log (197267284916843 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((69267284916843 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (69987284916843 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (270330825910515365411 / 625000000000000000000 : ℝ) ≤
      Real.log (197267284916843 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (69987284916843 / 128000000000000 : ℝ) ≤
      (-(6037166821546904547073 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69987284916843 / 128000000000000 : ℝ) = (69987284916843 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69987284916843 / 64000000000000 : ℝ) ≤
            (894304981453095452927 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7356294334872931 / 10000000000000000 : ℝ) ≤
      Real.sqrt (69267284916843 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (69267284916843 / 128000000000000 : ℝ) ≤
      (3678147167436467 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (69267284916843 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau750 :
    Real.arctan (3678147167436467 / 11207154467654313 : ℝ) ≤
      (1585600823698669241149 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau749 :
    Real.arctan (3678147167436467 / 5000000000000000 : ℝ) ≤
      (2 * (1585600823698669241149 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6207154467654313 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3678147167436467 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3678147167436467 / 5000000000000000 : ℝ) /
                (1 + (6207154467654313 / 5000000000000000 : ℝ)) =
              (3678147167436467 / 11207154467654313 : ℝ)
            by
        norm_num];
        exact hau750)
  have hat1 :
    (Real.pi / 2 - (2 * (1585600823698669241149 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3678147167436467 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3678147167436467 : ℝ) =
              (3678147167436467 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau749)
  have hz1 :
    (5000000000000000 / 3678147167436467 : ℝ) ≤
      1 / Real.sqrt (69267284916843 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3678147167436467 : ℝ) = 1 / (3678147167436467 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7356294334872931 : ℝ) ≤
      (508012202987596007037 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (69267284916843 / 128000000000000 : ℝ) ≤
      (750000000000000 / 7356294334872931 : ℝ) := by
    rw [show
        (750000000000000 / 7356294334872931 : ℝ) =
          (3 / 40) / (7356294334872931 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1585600823698669241149 / 5000000000000000000000 : ℝ))) -
        6 * (508012202987596007037 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (69267284916843 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (69267284916843 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7356294334872931 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1585600823698669241149 / 5000000000000000000000 : ℝ))) -
          6 * (508012202987596007037 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (69267284916843 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (69267284916843 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (69267284916843 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_490 :
    ((432934207196648785071 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6025758846024781546297 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((736053516857799 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3172577234943563944481 / 10000000000000000000000 : ℝ))) -
              6 * (203088606394024225601 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (34673585899439 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (34673585899439 / 64000000000000 : ℝ)) =
      Real.log (98673585899439 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((34673585899439 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (35033585899439 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (432934207196648785071 / 1000000000000000000000 : ℝ) ≤
      Real.log (98673585899439 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (35033585899439 / 64000000000000 : ℝ) ≤
      (-(6025758846024781546297 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (35033585899439 / 64000000000000 : ℝ) = (35033585899439 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (35033585899439 / 32000000000000 : ℝ) ≤
            (905712956975218453703 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (736053516857799 / 1000000000000000 : ℝ) ≤ Real.sqrt (34673585899439 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (34673585899439 / 64000000000000 : ℝ) ≤
      (7360535168577993 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (34673585899439 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau752 :
    Real.arctan (2453511722859331 / 7472274126014387 : ℝ) ≤
      (3172577234943563944481 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau751 :
    Real.arctan (7360535168577993 / 10000000000000000 : ℝ) ≤
      (2 * (3172577234943563944481 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12416822378043161 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7360535168577993 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7360535168577993 / 10000000000000000 : ℝ) /
                (1 + (12416822378043161 / 10000000000000000 : ℝ)) =
              (2453511722859331 / 7472274126014387 : ℝ)
            by
        norm_num];
        exact hau752)
  have hat1 :
    (Real.pi / 2 - (2 * (3172577234943563944481 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7360535168577993 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7360535168577993 : ℝ) =
              (7360535168577993 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau751)
  have hz1 :
    (10000000000000000 / 7360535168577993 : ℝ) ≤
      1 / Real.sqrt (34673585899439 / 64000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 7360535168577993 : ℝ) =
          1 / (7360535168577993 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (25000000000000 / 245351172285933 : ℝ) ≤
      (203088606394024225601 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (34673585899439 / 64000000000000 : ℝ) ≤
      (25000000000000 / 245351172285933 : ℝ) := by
    rw [show
        (25000000000000 / 245351172285933 : ℝ) =
          (3 / 40) / (736053516857799 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (3172577234943563944481 / 10000000000000000000000 : ℝ))) -
        6 * (203088606394024225601 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (34673585899439 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (34673585899439 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((736053516857799 / 1000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (3172577234943563944481 / 10000000000000000000000 : ℝ))) -
          6 * (203088606394024225601 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (34673585899439 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (34673585899439 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (34673585899439 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_491 :
    ((4333389290703554887527 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1202872773972995472511 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7364773560297917 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (634790294795992208869 / 2000000000000000000000 : ℝ))) -
              6 * (1014862654828672016827 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (69427058680913 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (69427058680913 / 128000000000000 : ℝ)) =
      Real.log (197427058680913 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((69427058680913 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (70147058680913 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (4333389290703554887527 / 10000000000000000000000 : ℝ) ≤
      Real.log (197427058680913 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (70147058680913 / 128000000000000 : ℝ) ≤
      (-(1202872773972995472511 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (70147058680913 / 128000000000000 : ℝ) = (70147058680913 / 64000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (70147058680913 / 64000000000000 : ℝ) ≤
            (183421586627004527489 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (7364773560297917 / 10000000000000000 : ℝ) ≤
      Real.sqrt (69427058680913 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (69427058680913 / 128000000000000 : ℝ) ≤ (23014917375931 / 31250000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (69427058680913 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau754 :
    Real.arctan (3682386780148960 / 11209667656051797 : ℝ) ≤
      (634790294795992208869 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau753 :
    Real.arctan (23014917375931 / 31250000000000 : ℝ) ≤
      (2 * (634790294795992208869 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6209667656051797 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (23014917375931 / 31250000000000 : ℝ) ^ 2))
      (by
        rw [show
            (23014917375931 / 31250000000000 : ℝ) /
                (1 + (6209667656051797 / 5000000000000000 : ℝ)) =
              (3682386780148960 / 11209667656051797 : ℝ)
            by
        norm_num];
        exact hau754)
  have hat1 :
    (Real.pi / 2 - (2 * (634790294795992208869 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (31250000000000 / 23014917375931 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (31250000000000 / 23014917375931 : ℝ) =
              (23014917375931 / 31250000000000 : ℝ)
            by
        norm_num];
        exact hau753)
  have hz1 :
    (31250000000000 / 23014917375931 : ℝ) ≤
      1 / Real.sqrt (69427058680913 / 128000000000000 : ℝ) := by
    rw [show (31250000000000 / 23014917375931 : ℝ) = 1 / (23014917375931 / 31250000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 7364773560297917 : ℝ) ≤
      (1014862654828672016827 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (69427058680913 / 128000000000000 : ℝ) ≤
      (750000000000000 / 7364773560297917 : ℝ) := by
    rw [show
        (750000000000000 / 7364773560297917 : ℝ) =
          (3 / 40) / (7364773560297917 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (634790294795992208869 / 2000000000000000000000 : ℝ))) -
        6 * (1014862654828672016827 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (69427058680913 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (69427058680913 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((7364773560297917 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (634790294795992208869 / 2000000000000000000000 : ℝ))) -
          6 * (1014862654828672016827 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (69427058680913 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (69427058680913 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (69427058680913 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_492 :
    ((542179359013164303477 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1200596372695144120349 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3684504757123171 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1587662183481644612061 / 5000000000000000000000 : ℝ))) -
              6 * (25357081792631315167 / 250000000000000000000 : ℝ)))) ≤
      Vfield (17376736390737 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (17376736390737 / 32000000000000 : ℝ)) =
      Real.log (49376736390737 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((17376736390737 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (17556736390737 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (542179359013164303477 / 1250000000000000000000 : ℝ) ≤
      Real.log (49376736390737 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (17556736390737 / 32000000000000 : ℝ) ≤
      (-(1200596372695144120349 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17556736390737 / 32000000000000 : ℝ) = (17556736390737 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17556736390737 / 16000000000000 : ℝ) ≤
            (185697987904855879651 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3684504757123171 / 5000000000000000 : ℝ) ≤ Real.sqrt (17376736390737 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (17376736390737 / 32000000000000 : ℝ) ≤ (1473801902849269 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (17376736390737 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau756 :
    Real.arctan (7369009514246345 / 22421847737798637 : ℝ) ≤
      (1587662183481644612061 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau755 :
    Real.arctan (1473801902849269 / 2000000000000000 : ℝ) ≤
      (2 * (1587662183481644612061 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12421847737798637 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1473801902849269 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1473801902849269 / 2000000000000000 : ℝ) /
                (1 + (12421847737798637 / 10000000000000000 : ℝ)) =
              (7369009514246345 / 22421847737798637 : ℝ)
            by
        norm_num];
        exact hau756)
  have hat1 :
    (Real.pi / 2 - (2 * (1587662183481644612061 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1473801902849269 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1473801902849269 : ℝ) =
              (1473801902849269 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau755)
  have hz1 :
    (2000000000000000 / 1473801902849269 : ℝ) ≤
      1 / Real.sqrt (17376736390737 / 32000000000000 : ℝ) := by
    rw [show
        (2000000000000000 / 1473801902849269 : ℝ) = 1 / (1473801902849269 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3684504757123171 : ℝ) ≤
      (25357081792631315167 / 250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (17376736390737 / 32000000000000 : ℝ) ≤
      (375000000000000 / 3684504757123171 : ℝ) := by
    rw [show
        (375000000000000 / 3684504757123171 : ℝ) =
          (3 / 40) / (3684504757123171 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1587662183481644612061 / 5000000000000000000000 : ℝ))) -
        6 * (25357081792631315167 / 250000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (17376736390737 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (17376736390737 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3684504757123171 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1587662183481644612061 / 5000000000000000000000 : ℝ))) -
          6 * (25357081792631315167 / 250000000000000000000 : ℝ))) ≤
      Real.sqrt (17376736390737 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (17376736390737 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (17376736390737 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
