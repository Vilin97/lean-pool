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

/-! # V00: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_1 :
    ((8967502915859873 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25870887852728765963031 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((14973028876951 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (7174131 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7174131 / 200000000000 : ℝ)) = Real.log (200007174131 / 200000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((7174131 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1132174131 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (8967502915859873 / 250000000000000000000 : ℝ) ≤ Real.log (200007174131 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1132174131 / 200000000000 : ℝ) ≤
      (-(25870887852728765963031 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1132174131 / 200000000000 : ℝ) = (1132174131 / 781250000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1132174131 / 781250000 : ℝ) ≤
            (1854999359271234036969 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (59892115507801 / 10000000000000000 : ℝ) ≤ Real.sqrt (7174131 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi : Real.sqrt (7174131 / 200000000000 : ℝ) ≤ (14973028876951 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7174131 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau3 :
    Real.arctan (14973028876951 / 2500000000000000 : ℝ) ≤
      (11978279880015751031 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 14973028876951 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 14973028876951 : ℝ) =
              (14973028876951 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau3)
  have hz1 :
    (2500000000000000 / 14973028876951 : ℝ) ≤ 1 / Real.sqrt (7174131 / 200000000000 : ℝ) := by
    rw [show (2500000000000000 / 14973028876951 : ℝ) = 1 / (14973028876951 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal4 :
    (796870528491162609301 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (59892115507801 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 59892115507801 : ℝ) ≤
      (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 59892115507801 : ℝ) =
              (59892115507801 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal4)
  have hz2 :
    (3 / 40) / Real.sqrt (7174131 / 200000000000 : ℝ) ≤ (750000000000000 / 59892115507801 : ℝ) := by
    rw [show
        (750000000000000 / 59892115507801 : ℝ) =
          (3 / 40) / (59892115507801 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7174131 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7174131 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((14973028876951 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (7174131 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7174131 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7174131 / 200000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (7174131 / 200000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_2 :
    ((67255668762557231 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25855071403081196359633 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4584535081561 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (21522393 / 400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (21522393 / 400000000000 : ℝ)) = Real.log (400021522393 / 400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((21522393 / 400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2271522393 / 400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (67255668762557231 / 1250000000000000000000 : ℝ) ≤
      Real.log (400021522393 / 400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2271522393 / 400000000000 : ℝ) ≤
      (-(25855071403081196359633 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (2271522393 / 400000000000 : ℝ) = (2271522393 / 1562500000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2271522393 / 1562500000 : ℝ) ≤
            (1870815808918803640367 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (73352561304973 / 10000000000000000 : ℝ) ≤ Real.sqrt (21522393 / 400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi : Real.sqrt (21522393 / 400000000000 : ℝ) ≤ (4584535081561 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (21522393 / 400000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau5 :
    Real.arctan (4584535081561 / 625000000000000 : ℝ) ≤
      (73351245745236760791 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 4584535081561 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 4584535081561 : ℝ) =
              (4584535081561 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau5)
  have hz1 :
    (625000000000000 / 4584535081561 : ℝ) ≤ 1 / Real.sqrt (21522393 / 400000000000 : ℝ) := by
    rw [show (625000000000000 / 4584535081561 : ℝ) = 1 / (4584535081561 / 625000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal6 :
    (974933462669317096681 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (73352561304973 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 73352561304973 : ℝ) ≤
      (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 73352561304973 : ℝ) =
              (73352561304973 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal6)
  have hz2 :
    (3 / 40) / Real.sqrt (21522393 / 400000000000 : ℝ) ≤ (750000000000000 / 73352561304973 : ℝ) :=
  by
    rw [show
        (750000000000000 / 73352561304973 : ℝ) =
          (3 / 40) / (73352561304973 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (21522393 / 400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (21522393 / 400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((4584535081561 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (21522393 / 400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (21522393 / 400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (21522393 / 400000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (21522393 / 400000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_3 :
    ((358693683576464417 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25839304827724134032909 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5293765126897 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ))))) ≤
      Vfield (7174131 / 100000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7174131 / 100000000000 : ℝ)) = Real.log (100007174131 / 100000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((7174131 / 100000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (569674131 / 100000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (358693683576464417 / 5000000000000000000000 : ℝ) ≤
      Real.log (100007174131 / 100000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (569674131 / 100000000000 : ℝ) ≤
      (-(25839304827724134032909 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (569674131 / 100000000000 : ℝ) = (569674131 / 390625000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (569674131 / 390625000 : ℝ) ≤
            (1886582384275865967091 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (84700242030349 / 10000000000000000 : ℝ) ≤ Real.sqrt (7174131 / 100000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi : Real.sqrt (7174131 / 100000000000 : ℝ) ≤ (5293765126897 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7174131 / 100000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau7 :
    Real.arctan (5293765126897 / 625000000000000 : ℝ) ≤
      (16939643323085595789 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 5293765126897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 5293765126897 : ℝ) =
              (5293765126897 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau7)
  have hz1 : (625000000000000 / 5293765126897 : ℝ) ≤ 1 / Real.sqrt (7174131 / 100000000000 : ℝ) :=
  by
    rw [show (625000000000000 / 5293765126897 : ℝ) = 1 / (5293765126897 / 625000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal8 :
    (35142868108192574273 / 312500000000000000000 : ℝ) ≤
      Real.arctan (84700242030349 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 84700242030349 : ℝ) ≤
      (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 84700242030349 : ℝ) =
              (84700242030349 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal8)
  have hz2 :
    (3 / 40) / Real.sqrt (7174131 / 100000000000 : ℝ) ≤ (750000000000000 / 84700242030349 : ℝ) := by
    rw [show
        (750000000000000 / 84700242030349 : ℝ) =
          (3 / 40) / (84700242030349 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7174131 / 100000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7174131 / 100000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((5293765126897 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ)))) ≤
      Real.sqrt (7174131 / 100000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7174131 / 100000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7174131 / 100000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (7174131 / 100000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_4 :
    ((37063408769787157 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51674418216178446788859 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((86098527861981 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (14825913 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (14825913 / 200000000000 : ℝ)) = Real.log (200014825913 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((14825913 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1139825913 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (37063408769787157 / 500000000000000000000 : ℝ) ≤
      Real.log (200014825913 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1139825913 / 200000000000 : ℝ) ≤
      (-(51674418216178446788859 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1139825913 / 200000000000 : ℝ) = (1139825913 / 781250000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1139825913 / 781250000 : ℝ) ≤
            (3777356207821553211141 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (43049263930989 / 5000000000000000 : ℝ) ≤ Real.sqrt (14825913 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (14825913 / 200000000000 : ℝ) ≤ (86098527861981 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (14825913 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau9 :
    Real.arctan (86098527861981 / 10000000000000000 : ℝ) ≤
      (17219280094892480421 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 86098527861981 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 86098527861981 : ℝ) =
              (86098527861981 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau9)
  have hz1 :
    (10000000000000000 / 86098527861981 : ℝ) ≤ 1 / Real.sqrt (14825913 / 200000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 86098527861981 : ℝ) = 1 / (86098527861981 / 10000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal10 :
    (1142976954465331252621 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (14349754643663 / 125000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (125000000000000 / 14349754643663 : ℝ) ≤
      (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 14349754643663 : ℝ) =
              (14349754643663 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal10)
  have hz2 :
    (3 / 40) / Real.sqrt (14825913 / 200000000000 : ℝ) ≤ (125000000000000 / 14349754643663 : ℝ) :=
  by
    rw [show
        (125000000000000 / 14349754643663 : ℝ) =
          (3 / 40) / (43049263930989 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (14825913 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (14825913 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((86098527861981 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (14825913 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (14825913 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (14825913 / 200000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (14825913 / 200000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_5 :
    ((196661542144736661 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51666458509222761164599 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((88694820029133 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ))))) ≤
      Vfield (78667711 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (78667711 / 1000000000000 : ℝ)) =
      Real.log (1000078667711 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((78667711 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5703667711 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (196661542144736661 / 2500000000000000000000 : ℝ) ≤
      Real.log (1000078667711 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5703667711 / 1000000000000 : ℝ) ≤
      (-(51666458509222761164599 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (5703667711 / 1000000000000 : ℝ) = (5703667711 / 3906250000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5703667711 / 3906250000 : ℝ) ≤
            (3785315914777238835401 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (8869482002913 / 1000000000000000 : ℝ) ≤ Real.sqrt (78667711 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (78667711 / 1000000000000 : ℝ) ≤ (88694820029133 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (78667711 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau11 :
    Real.arctan (88694820029133 / 10000000000000000 : ℝ) ≤
      (44346247166374961649 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 88694820029133 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 88694820029133 : ℝ) =
              (88694820029133 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau11)
  have hz1 :
    (10000000000000000 / 88694820029133 : ℝ) ≤ 1 / Real.sqrt (78667711 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 88694820029133 : ℝ) = 1 / (88694820029133 / 10000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal12 :
    (117713038222569168397 / 1000000000000000000000 : ℝ) ≤
      Real.arctan (2956494000971 / 25000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (25000000000000 / 2956494000971 : ℝ) ≤
      (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (25000000000000 / 2956494000971 : ℝ) = (2956494000971 / 25000000000000 : ℝ)
            by
        norm_num];
        exact hal12)
  have hz2 :
    (3 / 40) / Real.sqrt (78667711 / 1000000000000 : ℝ) ≤ (25000000000000 / 2956494000971 : ℝ) := by
    rw [show
        (25000000000000 / 2956494000971 : ℝ) = (3 / 40) / (8869482002913 / 1000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (78667711 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (78667711 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((88694820029133 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ)))) ≤
      Real.sqrt (78667711 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (78667711 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (78667711 / 1000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (78667711 / 1000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_6 :
    ((85811957048696007 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51653934194779139713727 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((92636730836101 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (85815639 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (85815639 / 1000000000000 : ℝ)) =
      Real.log (1000085815639 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((85815639 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (5710815639 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (85811957048696007 / 1000000000000000000000 : ℝ) ≤
      Real.log (1000085815639 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (5710815639 / 1000000000000 : ℝ) ≤
      (-(51653934194779139713727 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (5710815639 / 1000000000000 : ℝ) = (5710815639 / 3906250000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5710815639 / 3906250000 : ℝ) ≤
            (3797840229220860286273 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (46318365418049 / 5000000000000000 : ℝ) ≤ Real.sqrt (85815639 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (85815639 / 1000000000000 : ℝ) ≤ (92636730836101 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (85815639 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau13 :
    Real.arctan (92636730836101 / 10000000000000000 : ℝ) ≤
      (92634081079116824847 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 92636730836101 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 92636730836101 : ℝ) =
              (92636730836101 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau13)
  have hz1 :
    (10000000000000000 / 92636730836101 : ℝ) ≤ 1 / Real.sqrt (85815639 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 92636730836101 : ℝ) = 1 / (92636730836101 / 10000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal14 :
    (614466029692359913717 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (46318365418049 / 375000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (375000000000000 / 46318365418049 : ℝ) ≤
      (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 46318365418049 : ℝ) =
              (46318365418049 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal14)
  have hz2 :
    (3 / 40) / Real.sqrt (85815639 / 1000000000000 : ℝ) ≤
      (375000000000000 / 46318365418049 : ℝ) := by
    rw [show
        (375000000000000 / 46318365418049 : ℝ) =
          (3 / 40) / (46318365418049 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (85815639 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (85815639 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((92636730836101 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (85815639 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (85815639 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (85815639 / 1000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (85815639 / 1000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_7 :
    ((30107723030942933 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25817752990537051829671 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((19631541457563 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (19269871 / 200000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19269871 / 200000000000 : ℝ)) = Real.log (200019269871 / 200000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19269871 / 200000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1144269871 / 200000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (30107723030942933 / 312500000000000000000 : ℝ) ≤
      Real.log (200019269871 / 200000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1144269871 / 200000000000 : ℝ) ≤
      (-(25817752990537051829671 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1144269871 / 200000000000 : ℝ) = (1144269871 / 781250000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1144269871 / 781250000 : ℝ) ≤
            (1908134221462948170329 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (24539426821953 / 2500000000000000 : ℝ) ≤ Real.sqrt (19269871 / 200000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19269871 / 200000000000 : ℝ) ≤ (19631541457563 / 2000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19269871 / 200000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau15 :
    Real.arctan (19631541457563 / 2000000000000000 : ℝ) ≤
      (49077277496392064609 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 19631541457563 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 19631541457563 : ℝ) =
              (19631541457563 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau15)
  have hz1 :
    (2000000000000000 / 19631541457563 : ℝ) ≤ 1 / Real.sqrt (19269871 / 200000000000 : ℝ) := by
    rw [show (2000000000000000 / 19631541457563 : ℝ) = 1 / (19631541457563 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal16 :
    (1301372761809135071741 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (8179808940651 / 62500000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (62500000000000 / 8179808940651 : ℝ) ≤
      (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (62500000000000 / 8179808940651 : ℝ) = (8179808940651 / 62500000000000 : ℝ)
            by
        norm_num];
        exact hal16)
  have hz2 :
    (3 / 40) / Real.sqrt (19269871 / 200000000000 : ℝ) ≤ (62500000000000 / 8179808940651 : ℝ) := by
    rw [show
        (62500000000000 / 8179808940651 : ℝ) = (3 / 40) / (24539426821953 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19269871 / 200000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19269871 / 200000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((19631541457563 / 2000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (19269871 / 200000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19269871 / 200000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19269871 / 200000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (19269871 / 200000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_8 :
    ((278789739678365227 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51609021536891161835761 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((105604031173059 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (55761057 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (55761057 / 500000000000 : ℝ)) = Real.log (500055761057 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((55761057 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2868261057 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (278789739678365227 / 2500000000000000000000 : ℝ) ≤
      Real.log (500055761057 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2868261057 / 500000000000 : ℝ) ≤
      (-(51609021536891161835761 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (2868261057 / 500000000000 : ℝ) = (2868261057 / 1953125000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2868261057 / 1953125000 : ℝ) ≤
            (3842752887108838164239 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo : (1650062987079 / 156250000000000 : ℝ) ≤ Real.sqrt (55761057 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (55761057 / 500000000000 : ℝ) ≤ (105604031173059 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (55761057 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau17 :
    Real.arctan (105604031173059 / 10000000000000000 : ℝ) ≤
      (52800052853726802719 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 105604031173059 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 105604031173059 : ℝ) =
              (105604031173059 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau17)
  have hz1 :
    (10000000000000000 / 105604031173059 : ℝ) ≤ 1 / Real.sqrt (55761057 / 500000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 105604031173059 : ℝ) = 1 / (105604031173059 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal18 :
    (1398857469718843080699 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (550020995693 / 3906250000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (3906250000000 / 550020995693 : ℝ) ≤
      (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show (1 : ℝ) / (3906250000000 / 550020995693 : ℝ) = (550020995693 / 3906250000000 : ℝ)
            by
        norm_num];
        exact hal18)
  have hz2 :
    (3 / 40) / Real.sqrt (55761057 / 500000000000 : ℝ) ≤ (3906250000000 / 550020995693 : ℝ) := by
    rw [show (3906250000000 / 550020995693 : ℝ) = (3 / 40) / (1650062987079 / 156250000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (55761057 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (55761057 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((105604031173059 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (55761057 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (55761057 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (55761057 / 500000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (55761057 / 500000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_9 :
    ((1333382420614834419 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51571047996245974723013 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((57738014340641 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (33336783 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (33336783 / 250000000000 : ℝ)) = Real.log (250033336783 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((33336783 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1439586783 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1333382420614834419 / 10000000000000000000000 : ℝ) ≤
      Real.log (250033336783 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1439586783 / 250000000000 : ℝ) ≤
      (-(51571047996245974723013 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1439586783 / 250000000000 : ℝ) = (1439586783 / 976562500 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1439586783 / 976562500 : ℝ) ≤
            (3880726427754025276987 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (115476028681279 / 10000000000000000 : ℝ) ≤ Real.sqrt (33336783 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (33336783 / 250000000000 : ℝ) ≤ (57738014340641 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (33336783 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau19 :
    Real.arctan (57738014340641 / 5000000000000000 : ℝ) ≤
      (115470896292829511109 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 57738014340641 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 57738014340641 : ℝ) =
              (57738014340641 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau19)
  have hz1 :
    (5000000000000000 / 57738014340641 : ℝ) ≤ 1 / Real.sqrt (33336783 / 250000000000 : ℝ) := by
    rw [show (5000000000000000 / 57738014340641 : ℝ) = 1 / (57738014340641 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal20 :
    (763841962364687947279 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (115476028681279 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 115476028681279 : ℝ) ≤
      (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 115476028681279 : ℝ) =
              (115476028681279 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal20)
  have hz2 :
    (3 / 40) / Real.sqrt (33336783 / 250000000000 : ℝ) ≤
      (750000000000000 / 115476028681279 : ℝ) := by
    rw [show
        (750000000000000 / 115476028681279 : ℝ) =
          (3 / 40) / (115476028681279 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (33336783 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (33336783 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((57738014340641 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (33336783 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (33336783 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (33336783 / 250000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (33336783 / 250000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_10 :
    ((66033623550755633 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51516061139574022265869 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((128490344384317 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (82548843 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (82548843 / 500000000000 : ℝ)) = Real.log (500082548843 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((82548843 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2895048843 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (66033623550755633 / 400000000000000000000 : ℝ) ≤
      Real.log (500082548843 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2895048843 / 500000000000 : ℝ) ≤
      (-(51516061139574022265869 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (2895048843 / 500000000000 : ℝ) = (2895048843 / 1953125000 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2895048843 / 1953125000 : ℝ) ≤
            (3935713284425977734131 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (64245172192157 / 5000000000000000 : ℝ) ≤ Real.sqrt (82548843 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (82548843 / 500000000000 : ℝ) ≤ (128490344384317 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (82548843 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau21 :
    Real.arctan (128490344384317 / 10000000000000000 : ℝ) ≤
      (25696654786369851871 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 128490344384317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 128490344384317 : ℝ) =
              (128490344384317 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau21)
  have hz1 :
    (10000000000000000 / 128490344384317 : ℝ) ≤ 1 / Real.sqrt (82548843 / 500000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 128490344384317 : ℝ) = 1 / (128490344384317 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal22 :
    (1696732463001094446147 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (64245172192157 / 375000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (375000000000000 / 64245172192157 : ℝ) ≤
      (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 64245172192157 : ℝ) =
              (64245172192157 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal22)
  have hz2 :
    (3 / 40) / Real.sqrt (82548843 / 500000000000 : ℝ) ≤ (375000000000000 / 64245172192157 : ℝ) :=
  by
    rw [show
        (375000000000000 / 64245172192157 : ℝ) =
          (3 / 40) / (64245172192157 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (82548843 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (82548843 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((128490344384317 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (82548843 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (82548843 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (82548843 / 500000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (82548843 / 500000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_11 :
    ((1060918377258494863 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51435029869943759185693 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((18209123228481 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (53051547 / 250000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (53051547 / 250000000000 : ℝ)) = Real.log (250053051547 / 250000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((53051547 / 250000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1459301547 / 250000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1060918377258494863 / 5000000000000000000000 : ℝ) ≤
      Real.log (250053051547 / 250000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1459301547 / 250000000000 : ℝ) ≤
      (-(51435029869943759185693 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (1459301547 / 250000000000 : ℝ) = (1459301547 / 976562500 : ℝ) / 2 ^ 8 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1459301547 / 976562500 : ℝ) ≤
            (4016744554056240814307 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (29134597165569 / 2000000000000000 : ℝ) ≤ Real.sqrt (53051547 / 250000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (53051547 / 250000000000 : ℝ) ≤ (18209123228481 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (53051547 / 250000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau23 :
    Real.arctan (18209123228481 / 1250000000000000 : ℝ) ≤
      (145662682903283762149 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 18209123228481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 18209123228481 : ℝ) =
              (18209123228481 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau23)
  have hz1 :
    (1250000000000000 / 18209123228481 : ℝ) ≤ 1 / Real.sqrt (53051547 / 250000000000 : ℝ) := by
    rw [show (1250000000000000 / 18209123228481 : ℝ) = 1 / (18209123228481 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal24 :
    (1918420011923721109387 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (9711532388523 / 50000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (50000000000000 / 9711532388523 : ℝ) ≤
      (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 9711532388523 : ℝ) = (9711532388523 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hal24)
  have hz2 :
    (3 / 40) / Real.sqrt (53051547 / 250000000000 : ℝ) ≤ (50000000000000 / 9711532388523 : ℝ) := by
    rw [show
        (50000000000000 / 9711532388523 : ℝ) = (3 / 40) / (29134597165569 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (53051547 / 250000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (53051547 / 250000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((18209123228481 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (53051547 / 250000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (53051547 / 250000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (53051547 / 250000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (53051547 / 250000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_12 :
    ((2480279280302765263 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12843449268270218651961 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9843674394551 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (496117379 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (496117379 / 2000000000000 : ℝ)) =
      Real.log (2000496117379 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((496117379 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (11746117379 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (2480279280302765263 / 10000000000000000000000 : ℝ) ≤
      Real.log (2000496117379 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (11746117379 / 2000000000000 : ℝ) ≤
      (-(12843449268270218651961 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (11746117379 / 2000000000000 : ℝ) = (11746117379 / 7812500000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11746117379 / 7812500000 : ℝ) ≤
            (1019494337729781348039 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (157498790312813 / 10000000000000000 : ℝ) ≤ Real.sqrt (496117379 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (496117379 / 2000000000000 : ℝ) ≤ (9843674394551 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (496117379 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau25 :
    Real.arctan (9843674394551 / 625000000000000 : ℝ) ≤
      (39371442317394135319 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 9843674394551 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 9843674394551 : ℝ) =
              (9843674394551 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau25)
  have hz1 :
    (625000000000000 / 9843674394551 : ℝ) ≤ 1 / Real.sqrt (496117379 / 2000000000000 : ℝ) := by
    rw [show (625000000000000 / 9843674394551 : ℝ) = 1 / (9843674394551 / 625000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal26 :
    (2069906494283519593871 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (157498790312813 / 750000000000000 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 157498790312813 : ℝ) ≤
      (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 157498790312813 : ℝ) =
              (157498790312813 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal26)
  have hz2 :
    (3 / 40) / Real.sqrt (496117379 / 2000000000000 : ℝ) ≤
      (750000000000000 / 157498790312813 : ℝ) := by
    rw [show
        (750000000000000 / 157498790312813 : ℝ) =
          (3 / 40) / (157498790312813 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (496117379 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (496117379 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((9843674394551 / 625000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (496117379 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (496117379 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (496117379 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (496117379 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
