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

/-! # V30: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_361 :
    ((621940531108982726093 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(993242943074726082441 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6039442362824217 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2716573140403061887061 / 10000000000000000000000 : ℝ))) -
              6 * (617755618701384853011 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (46687825988961 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (46687825988961 / 128000000000000 : ℝ)) =
      Real.log (174687825988961 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((46687825988961 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (47407825988961 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (621940531108982726093 / 2000000000000000000000 : ℝ) ≤
      Real.log (174687825988961 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (47407825988961 / 128000000000000 : ℝ) ≤
      (-(993242943074726082441 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (47407825988961 / 128000000000000 : ℝ) = (47407825988961 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47407825988961 / 32000000000000 : ℝ) ≤
            (393051417525273917559 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6039442362824217 / 10000000000000000 : ℝ) ≤
      Real.sqrt (46687825988961 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (46687825988961 / 128000000000000 : ℝ) ≤ (301972118141211 / 500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (46687825988961 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau494 :
    Real.arctan (6039442362824220 / 21682245676832677 : ℝ) ≤
      (2716573140403061887061 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau493 :
    Real.arctan (301972118141211 / 500000000000000 : ℝ) ≤
      (2 * (2716573140403061887061 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11682245676832677 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (301972118141211 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (301972118141211 / 500000000000000 : ℝ) /
                (1 + (11682245676832677 / 10000000000000000 : ℝ)) =
              (6039442362824220 / 21682245676832677 : ℝ)
            by
        norm_num];
        exact hau494)
  have hat1 :
    (Real.pi / 2 - (2 * (2716573140403061887061 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 301972118141211 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 301972118141211 : ℝ) =
              (301972118141211 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau493)
  have hz1 :
    (500000000000000 / 301972118141211 : ℝ) ≤
      1 / Real.sqrt (46687825988961 / 128000000000000 : ℝ) := by
    rw [show (500000000000000 / 301972118141211 : ℝ) = 1 / (301972118141211 / 500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2013147454274739 : ℝ) ≤
      (617755618701384853011 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (46687825988961 / 128000000000000 : ℝ) ≤
      (250000000000000 / 2013147454274739 : ℝ) := by
    rw [show
        (250000000000000 / 2013147454274739 : ℝ) =
          (3 / 40) / (6039442362824217 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2716573140403061887061 / 10000000000000000000000 : ℝ))) -
        6 * (617755618701384853011 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (46687825988961 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (46687825988961 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6039442362824217 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2716573140403061887061 / 10000000000000000000000 : ℝ))) -
          6 * (617755618701384853011 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (46687825988961 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (46687825988961 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (46687825988961 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_362 :
    ((1557246946813072634581 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2478696518460755041279 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6044854677948479 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (42477430681884392329 / 156250000000000000000 : ℝ))) -
              6 * (617208109840245433709 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2338577156961 / 6400000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (2338577156961 / 6400000000000 : ℝ)) =
      Real.log (8738577156961 / 6400000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((2338577156961 / 6400000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (2374577156961 / 6400000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1557246946813072634581 / 5000000000000000000000 : ℝ) ≤
      Real.log (8738577156961 / 6400000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (2374577156961 / 6400000000000 : ℝ) ≤
      (-(2478696518460755041279 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2374577156961 / 6400000000000 : ℝ) = (2374577156961 / 1600000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2374577156961 / 1600000000000 : ℝ) ≤
            (987039383039244958721 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6044854677948479 / 10000000000000000 : ℝ) ≤ Real.sqrt (2338577156961 / 6400000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (2338577156961 / 6400000000000 : ℝ) ≤ (3022427338974241 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (2338577156961 / 6400000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau496 :
    Real.arctan (3022427338974241 / 10842522316549497 : ℝ) ≤
      (42477430681884392329 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau495 :
    Real.arctan (3022427338974241 / 5000000000000000 : ℝ) ≤
      (2 * (42477430681884392329 / 156250000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5842522316549497 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3022427338974241 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3022427338974241 / 5000000000000000 : ℝ) /
                (1 + (5842522316549497 / 5000000000000000 : ℝ)) =
              (3022427338974241 / 10842522316549497 : ℝ)
            by
        norm_num];
        exact hau496)
  have hat1 :
    (Real.pi / 2 - (2 * (42477430681884392329 / 156250000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3022427338974241 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3022427338974241 : ℝ) =
              (3022427338974241 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau495)
  have hz1 :
    (5000000000000000 / 3022427338974241 : ℝ) ≤
      1 / Real.sqrt (2338577156961 / 6400000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3022427338974241 : ℝ) = 1 / (3022427338974241 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6044854677948479 : ℝ) ≤
      (617208109840245433709 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (2338577156961 / 6400000000000 : ℝ) ≤
      (750000000000000 / 6044854677948479 : ℝ) := by
    rw [show
        (750000000000000 / 6044854677948479 : ℝ) =
          (3 / 40) / (6044854677948479 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (42477430681884392329 / 156250000000000000000 : ℝ))) -
        6 * (617208109840245433709 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (2338577156961 / 6400000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (2338577156961 / 6400000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6044854677948479 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (42477430681884392329 / 156250000000000000000 : ℝ))) -
          6 * (617208109840245433709 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (2338577156961 / 6400000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (2338577156961 / 6400000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (2338577156961 / 6400000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_363 :
    ((623856567442089207543 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(154643340483221346247 / 156250000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6050262151440667 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (544107052992504643051 / 2000000000000000000000 : ℝ))) -
              6 * (9635344596621206931 / 78125000000000000000 : ℝ)))) ≤
      Vfield (46855260289479 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (46855260289479 / 128000000000000 : ℝ)) =
      Real.log (174855260289479 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((46855260289479 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (47575260289479 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (623856567442089207543 / 2000000000000000000000 : ℝ) ≤
      Real.log (174855260289479 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (47575260289479 / 128000000000000 : ℝ) ≤
      (-(154643340483221346247 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (47575260289479 / 128000000000000 : ℝ) = (47575260289479 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47575260289479 / 32000000000000 : ℝ) ≤
            (61965153360528653753 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6050262151440667 / 10000000000000000 : ℝ) ≤
      Real.sqrt (46855260289479 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (46855260289479 / 128000000000000 : ℝ) ≤ (605026215144067 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (46855260289479 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau498 :
    Real.arctan (3025131075720335 / 10843921459541432 : ℝ) ≤
      (544107052992504643051 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau497 :
    Real.arctan (605026215144067 / 1000000000000000 : ℝ) ≤
      (2 * (544107052992504643051 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (730490182442679 / 625000000000000 : ℝ) ≤
          Real.sqrt (1 + (605026215144067 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (605026215144067 / 1000000000000000 : ℝ) /
                (1 + (730490182442679 / 625000000000000 : ℝ)) =
              (3025131075720335 / 10843921459541432 : ℝ)
            by
        norm_num];
        exact hau498)
  have hat1 :
    (Real.pi / 2 - (2 * (544107052992504643051 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 605026215144067 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 605026215144067 : ℝ) =
              (605026215144067 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau497)
  have hz1 :
    (1000000000000000 / 605026215144067 : ℝ) ≤
      1 / Real.sqrt (46855260289479 / 128000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 605026215144067 : ℝ) = 1 / (605026215144067 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6050262151440667 : ℝ) ≤
      (9635344596621206931 / 78125000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (46855260289479 / 128000000000000 : ℝ) ≤
      (750000000000000 / 6050262151440667 : ℝ) := by
    rw [show
        (750000000000000 / 6050262151440667 : ℝ) =
          (3 / 40) / (6050262151440667 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (544107052992504643051 / 2000000000000000000000 : ℝ))) -
        6 * (9635344596621206931 / 78125000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (46855260289479 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (46855260289479 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6050262151440667 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (544107052992504643051 / 2000000000000000000000 : ℝ))) -
          6 * (9635344596621206931 / 78125000000000000000 : ℝ))) ≤
      Real.sqrt (46855260289479 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (46855260289479 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (46855260289479 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_364 :
    ((1562034744247203678047 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9879592472732310410423 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6055664796270951 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (544502450344153676819 / 2000000000000000000000 : ℝ))) -
              6 * (1232234890629238011593 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23469488719869 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23469488719869 / 64000000000000 : ℝ)) =
      Real.log (87469488719869 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23469488719869 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23829488719869 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1562034744247203678047 / 5000000000000000000000 : ℝ) ≤
      Real.log (87469488719869 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23829488719869 / 64000000000000 : ℝ) ≤
      (-(9879592472732310410423 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (23829488719869 / 64000000000000 : ℝ) = (23829488719869 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23829488719869 / 16000000000000 : ℝ) ≤
            (3983351133267689589577 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6055664796270951 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23469488719869 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23469488719869 / 64000000000000 : ℝ) ≤ (3027832398135477 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23469488719869 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau500 :
    Real.arctan (1009277466045159 / 3615106755877601 : ℝ) ≤
      (544502450344153676819 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau499 :
    Real.arctan (3027832398135477 / 5000000000000000 : ℝ) ≤
      (2 * (544502450344153676819 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5845320267632803 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3027832398135477 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3027832398135477 / 5000000000000000 : ℝ) /
                (1 + (5845320267632803 / 5000000000000000 : ℝ)) =
              (1009277466045159 / 3615106755877601 : ℝ)
            by
        norm_num];
        exact hau500)
  have hat1 :
    (Real.pi / 2 - (2 * (544502450344153676819 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3027832398135477 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3027832398135477 : ℝ) =
              (3027832398135477 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau499)
  have hz1 :
    (5000000000000000 / 3027832398135477 : ℝ) ≤
      1 / Real.sqrt (23469488719869 / 64000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3027832398135477 : ℝ) = 1 / (3027832398135477 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (250000000000000 / 2018554932090317 : ℝ) ≤
      (1232234890629238011593 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23469488719869 / 64000000000000 : ℝ) ≤
      (250000000000000 / 2018554932090317 : ℝ) := by
    rw [show
        (250000000000000 / 2018554932090317 : ℝ) =
          (3 / 40) / (6055664796270951 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (544502450344153676819 / 2000000000000000000000 : ℝ))) -
        6 * (1232234890629238011593 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23469488719869 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23469488719869 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6055664796270951 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (544502450344153676819 / 2000000000000000000000 : ℝ))) -
          6 * (1232234890629238011593 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (23469488719869 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23469488719869 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23469488719869 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_365 :
    ((3128853849671467858077 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9862042010572357117663 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6061062625351691 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2724486531235580131221 / 10000000000000000000000 : ℝ))) -
              6 * (1231148553710269436801 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (47022694589997 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47022694589997 / 128000000000000 : ℝ)) =
      Real.log (175022694589997 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47022694589997 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (47742694589997 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3128853849671467858077 / 10000000000000000000000 : ℝ) ≤
      Real.log (175022694589997 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (47742694589997 / 128000000000000 : ℝ) ≤
      (-(9862042010572357117663 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (47742694589997 / 128000000000000 : ℝ) = (47742694589997 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47742694589997 / 32000000000000 : ℝ) ≤
            (4000901595427642882337 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6061062625351691 / 10000000000000000 : ℝ) ≤
      Real.sqrt (47022694589997 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47022694589997 / 128000000000000 : ℝ) ≤
      (3030531312675847 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47022694589997 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau502 :
    Real.arctan (3030531312675847 / 10846718741063981 : ℝ) ≤
      (2724486531235580131221 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau501 :
    Real.arctan (3030531312675847 / 5000000000000000 : ℝ) ≤
      (2 * (2724486531235580131221 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5846718741063981 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3030531312675847 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3030531312675847 / 5000000000000000 : ℝ) /
                (1 + (5846718741063981 / 5000000000000000 : ℝ)) =
              (3030531312675847 / 10846718741063981 : ℝ)
            by
        norm_num];
        exact hau502)
  have hat1 :
    (Real.pi / 2 - (2 * (2724486531235580131221 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3030531312675847 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3030531312675847 : ℝ) =
              (3030531312675847 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau501)
  have hz1 :
    (5000000000000000 / 3030531312675847 : ℝ) ≤
      1 / Real.sqrt (47022694589997 / 128000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3030531312675847 : ℝ) = 1 / (3030531312675847 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6061062625351691 : ℝ) ≤
      (1231148553710269436801 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47022694589997 / 128000000000000 : ℝ) ≤
      (750000000000000 / 6061062625351691 : ℝ) := by
    rw [show
        (750000000000000 / 6061062625351691 : ℝ) =
          (3 / 40) / (6061062625351691 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2724486531235580131221 / 10000000000000000000000 : ℝ))) -
        6 * (1231148553710269436801 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47022694589997 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47022694589997 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6061062625351691 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2724486531235580131221 / 10000000000000000000000 : ℝ))) -
          6 * (1231148553710269436801 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (47022694589997 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47022694589997 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47022694589997 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_366 :
    ((313363592293191942199 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9844522296328471492081 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3033227825768903 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2726458110795700910111 / 10000000000000000000000 : ℝ))) -
              6 * (615032542466899038457 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1472075366883 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1472075366883 / 4000000000000 : ℝ)) =
      Real.log (5472075366883 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1472075366883 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (1494575366883 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (313363592293191942199 / 1000000000000000000000 : ℝ) ≤
      Real.log (5472075366883 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (1494575366883 / 4000000000000 : ℝ) ≤
      (-(9844522296328471492081 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (1494575366883 / 4000000000000 : ℝ) = (1494575366883 / 1000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1494575366883 / 1000000000000 : ℝ) ≤
            (4018421309671528507919 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (3033227825768903 / 5000000000000000 : ℝ) ≤ Real.sqrt (1472075366883 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1472075366883 / 4000000000000 : ℝ) ≤ (6066455651537809 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1472075366883 / 4000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau504 :
    Real.arctan (6066455651537809 / 21696233760150102 : ℝ) ≤
      (2726458110795700910111 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau503 :
    Real.arctan (6066455651537809 / 10000000000000000 : ℝ) ≤
      (2 * (2726458110795700910111 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5848116880075051 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6066455651537809 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6066455651537809 / 10000000000000000 : ℝ) /
                (1 + (5848116880075051 / 5000000000000000 : ℝ)) =
              (6066455651537809 / 21696233760150102 : ℝ)
            by
        norm_num];
        exact hau504)
  have hat1 :
    (Real.pi / 2 - (2 * (2726458110795700910111 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6066455651537809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6066455651537809 : ℝ) =
              (6066455651537809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau503)
  have hz1 :
    (10000000000000000 / 6066455651537809 : ℝ) ≤
      1 / Real.sqrt (1472075366883 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 6066455651537809 : ℝ) =
          1 / (6066455651537809 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (375000000000000 / 3033227825768903 : ℝ) ≤
      (615032542466899038457 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (1472075366883 / 4000000000000 : ℝ) ≤
      (375000000000000 / 3033227825768903 : ℝ) := by
    rw [show
        (375000000000000 / 3033227825768903 : ℝ) =
          (3 / 40) / (3033227825768903 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2726458110795700910111 / 10000000000000000000000 : ℝ))) -
        6 * (615032542466899038457 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1472075366883 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1472075366883 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((3033227825768903 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2726458110795700910111 / 10000000000000000000000 : ℝ))) -
          6 * (615032542466899038457 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (1472075366883 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1472075366883 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1472075366883 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_367 :
    ((627683142092582637407 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(491351661122504170979 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6071843887627121 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (545685399531711867479 / 2000000000000000000000 : ℝ))) -
              6 * (19202882370327738227 / 156250000000000000000 : ℝ)))) ≤
      Vfield (9438025778103 / 25600000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (9438025778103 / 25600000000000 : ℝ)) =
      Real.log (35038025778103 / 25600000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((9438025778103 / 25600000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (9582025778103 / 25600000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (627683142092582637407 / 2000000000000000000000 : ℝ) ≤
      Real.log (35038025778103 / 25600000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (9582025778103 / 25600000000000 : ℝ) ≤
      (-(491351661122504170979 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9582025778103 / 25600000000000 : ℝ) = (9582025778103 / 6400000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9582025778103 / 6400000000000 : ℝ) ≤
            (201795519177495829021 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6071843887627121 / 10000000000000000 : ℝ) ≤ Real.sqrt (9438025778103 / 25600000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (9438025778103 / 25600000000000 : ℝ) ≤ (1517960971906781 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (9438025778103 / 25600000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau506 :
    Real.arctan (3035921943813562 / 10849514684905809 : ℝ) ≤
      (545685399531711867479 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau505 :
    Real.arctan (1517960971906781 / 2500000000000000 : ℝ) ≤
      (2 * (545685399531711867479 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5849514684905809 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1517960971906781 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1517960971906781 / 2500000000000000 : ℝ) /
                (1 + (5849514684905809 / 5000000000000000 : ℝ)) =
              (3035921943813562 / 10849514684905809 : ℝ)
            by
        norm_num];
        exact hau506)
  have hat1 :
    (Real.pi / 2 - (2 * (545685399531711867479 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1517960971906781 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1517960971906781 : ℝ) =
              (1517960971906781 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau505)
  have hz1 :
    (2500000000000000 / 1517960971906781 : ℝ) ≤
      1 / Real.sqrt (9438025778103 / 25600000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1517960971906781 : ℝ) = 1 / (1517960971906781 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6071843887627121 : ℝ) ≤
      (19202882370327738227 / 156250000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (9438025778103 / 25600000000000 : ℝ) ≤
      (750000000000000 / 6071843887627121 : ℝ) := by
    rw [show
        (750000000000000 / 6071843887627121 : ℝ) =
          (3 / 40) / (6071843887627121 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (545685399531711867479 / 2000000000000000000000 : ℝ))) -
        6 * (19202882370327738227 / 156250000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (9438025778103 / 25600000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (9438025778103 / 25600000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6071843887627121 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (545685399531711867479 / 2000000000000000000000 : ℝ))) -
          6 * (19202882370327738227 / 156250000000000000000 : ℝ))) ≤
      Real.sqrt (9438025778103 / 25600000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (9438025778103 / 25600000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (9438025778103 / 25600000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_368 :
    ((12572772857793862221 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4904787340974963006027 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6077227346360729 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1365196599525230821389 / 5000000000000000000000 : ℝ))) -
              6 * (613953350745148672973 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (23636923020387 / 64000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (23636923020387 / 64000000000000 : ℝ)) =
      Real.log (87636923020387 / 64000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((23636923020387 / 64000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (23996923020387 / 64000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (12572772857793862221 / 40000000000000000000 : ℝ) ≤
      Real.log (87636923020387 / 64000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (23996923020387 / 64000000000000 : ℝ) ≤
      (-(4904787340974963006027 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (23996923020387 / 64000000000000 : ℝ) = (23996923020387 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23996923020387 / 16000000000000 : ℝ) ≤
            (2026684462025036993973 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6077227346360729 / 10000000000000000 : ℝ) ≤
      Real.sqrt (23636923020387 / 64000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (23636923020387 / 64000000000000 : ℝ) ≤ (1519306836590183 / 2500000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (23636923020387 / 64000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau508 :
    Real.arctan (3038613673180366 / 10850912155795767 : ℝ) ≤
      (1365196599525230821389 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau507 :
    Real.arctan (1519306836590183 / 2500000000000000 : ℝ) ≤
      (2 * (1365196599525230821389 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5850912155795767 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1519306836590183 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1519306836590183 / 2500000000000000 : ℝ) /
                (1 + (5850912155795767 / 5000000000000000 : ℝ)) =
              (3038613673180366 / 10850912155795767 : ℝ)
            by
        norm_num];
        exact hau508)
  have hat1 :
    (Real.pi / 2 - (2 * (1365196599525230821389 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1519306836590183 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1519306836590183 : ℝ) =
              (1519306836590183 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau507)
  have hz1 :
    (2500000000000000 / 1519306836590183 : ℝ) ≤
      1 / Real.sqrt (23636923020387 / 64000000000000 : ℝ) := by
    rw [show
        (2500000000000000 / 1519306836590183 : ℝ) = 1 / (1519306836590183 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6077227346360729 : ℝ) ≤
      (613953350745148672973 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (23636923020387 / 64000000000000 : ℝ) ≤
      (750000000000000 / 6077227346360729 : ℝ) := by
    rw [show
        (750000000000000 / 6077227346360729 : ℝ) =
          (3 / 40) / (6077227346360729 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1365196599525230821389 / 5000000000000000000000 : ℝ))) -
        6 * (613953350745148672973 / 5000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (23636923020387 / 64000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (23636923020387 / 64000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6077227346360729 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1365196599525230821389 / 5000000000000000000000 : ℝ))) -
          6 * (613953350745148672973 / 5000000000000000000000 : ℝ))) ≤
      Real.sqrt (23636923020387 / 64000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (23636923020387 / 64000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (23636923020387 / 64000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_369 :
    ((49187006829210377799 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1958429313680021735671 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6082606040423341 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2732356722166779862839 / 10000000000000000000000 : ℝ))) -
              6 * (61341588092849836077 / 500000000000000000000 : ℝ)))) ≤
      Vfield (47357563191033 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47357563191033 / 128000000000000 : ℝ)) =
      Real.log (175357563191033 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47357563191033 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (48077563191033 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (49187006829210377799 / 156250000000000000000 : ℝ) ≤
      Real.log (175357563191033 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (48077563191033 / 128000000000000 : ℝ) ≤
      (-(1958429313680021735671 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (48077563191033 / 128000000000000 : ℝ) = (48077563191033 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48077563191033 / 32000000000000 : ℝ) ≤
            (814159407519978264329 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6082606040423341 / 10000000000000000 : ℝ) ≤
      Real.sqrt (47357563191033 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47357563191033 / 128000000000000 : ℝ) ≤ (380162877526459 / 625000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47357563191033 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau510 :
    Real.arctan (3041303020211672 / 10852309292984149 : ℝ) ≤
      (2732356722166779862839 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau509 :
    Real.arctan (380162877526459 / 625000000000000 : ℝ) ≤
      (2 * (2732356722166779862839 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5852309292984149 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (380162877526459 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (380162877526459 / 625000000000000 : ℝ) /
                (1 + (5852309292984149 / 5000000000000000 : ℝ)) =
              (3041303020211672 / 10852309292984149 : ℝ)
            by
        norm_num];
        exact hau510)
  have hat1 :
    (Real.pi / 2 - (2 * (2732356722166779862839 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 380162877526459 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 380162877526459 : ℝ) =
              (380162877526459 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau509)
  have hz1 :
    (625000000000000 / 380162877526459 : ℝ) ≤
      1 / Real.sqrt (47357563191033 / 128000000000000 : ℝ) := by
    rw [show (625000000000000 / 380162877526459 : ℝ) = 1 / (380162877526459 / 625000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6082606040423341 : ℝ) ≤
      (61341588092849836077 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47357563191033 / 128000000000000 : ℝ) ≤
      (750000000000000 / 6082606040423341 : ℝ) := by
    rw [show
        (750000000000000 / 6082606040423341 : ℝ) =
          (3 / 40) / (6082606040423341 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2732356722166779862839 / 10000000000000000000000 : ℝ))) -
        6 * (61341588092849836077 / 500000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47357563191033 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47357563191033 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6082606040423341 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2732356722166779862839 / 10000000000000000000000 : ℝ))) -
          6 * (61341588092849836077 / 500000000000000000000 : ℝ))) ≤
      Real.sqrt (47357563191033 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47357563191033 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47357563191033 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_370 :
    ((3152741380503673934997 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9774748775928224355261 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6087979982443631 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (683579393543033958129 / 2500000000000000000000 : ℝ))) -
              6 * (1225759640432438821581 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11860320085323 / 32000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (11860320085323 / 32000000000000 : ℝ)) =
      Real.log (43860320085323 / 32000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((11860320085323 / 32000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (12040320085323 / 32000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (3152741380503673934997 / 10000000000000000000000 : ℝ) ≤
      Real.log (43860320085323 / 32000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (12040320085323 / 32000000000000 : ℝ) ≤
      (-(9774748775928224355261 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (12040320085323 / 32000000000000 : ℝ) = (12040320085323 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12040320085323 / 8000000000000 : ℝ) ≤
            (4088194830071775644739 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6087979982443631 / 10000000000000000 : ℝ) ≤
      Real.sqrt (11860320085323 / 32000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (11860320085323 / 32000000000000 : ℝ) ≤ (3043989991221817 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (11860320085323 / 32000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau512 :
    Real.arctan (6087979982443634 / 21707412193419789 : ℝ) ≤
      (683579393543033958129 / 2500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau511 :
    Real.arctan (3043989991221817 / 5000000000000000 : ℝ) ≤
      (2 * (683579393543033958129 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11707412193419789 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3043989991221817 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3043989991221817 / 5000000000000000 : ℝ) /
                (1 + (11707412193419789 / 10000000000000000 : ℝ)) =
              (6087979982443634 / 21707412193419789 : ℝ)
            by
        norm_num];
        exact hau512)
  have hat1 :
    (Real.pi / 2 - (2 * (683579393543033958129 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3043989991221817 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3043989991221817 : ℝ) =
              (3043989991221817 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau511)
  have hz1 :
    (5000000000000000 / 3043989991221817 : ℝ) ≤
      1 / Real.sqrt (11860320085323 / 32000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3043989991221817 : ℝ) = 1 / (3043989991221817 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6087979982443631 : ℝ) ≤
      (1225759640432438821581 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (11860320085323 / 32000000000000 : ℝ) ≤
      (750000000000000 / 6087979982443631 : ℝ) := by
    rw [show
        (750000000000000 / 6087979982443631 : ℝ) =
          (3 / 40) / (6087979982443631 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (683579393543033958129 / 2500000000000000000000 : ℝ))) -
        6 * (1225759640432438821581 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (11860320085323 / 32000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (11860320085323 / 32000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6087979982443631 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (683579393543033958129 / 2500000000000000000000 : ℝ))) -
          6 * (1225759640432438821581 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (11860320085323 / 32000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (11860320085323 / 32000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (11860320085323 / 32000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_371 :
    ((394689005865717860253 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4878690599606745271231 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6093349184994587 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1368137881100294212459 / 5000000000000000000000 : ℝ))) -
              6 * (244938064984704678467 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (47524997491551 / 128000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (47524997491551 / 128000000000000 : ℝ)) =
      Real.log (175524997491551 / 128000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((47524997491551 / 128000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (48244997491551 / 128000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (394689005865717860253 / 1250000000000000000000 : ℝ) ≤
      Real.log (175524997491551 / 128000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (48244997491551 / 128000000000000 : ℝ) ≤
      (-(4878690599606745271231 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (48244997491551 / 128000000000000 : ℝ) = (48244997491551 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48244997491551 / 32000000000000 : ℝ) ≤
            (2052781203393254728769 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6093349184994587 / 10000000000000000 : ℝ) ≤
      Real.sqrt (47524997491551 / 128000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (47524997491551 / 128000000000000 : ℝ) ≤ (609334918499459 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (47524997491551 / 128000000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau514 :
    Real.arctan (3046674592497295 / 10855102567211658 : ℝ) ≤
      (1368137881100294212459 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau513 :
    Real.arctan (609334918499459 / 1000000000000000 : ℝ) ≤
      (2 * (1368137881100294212459 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2927551283605829 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (609334918499459 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (609334918499459 / 1000000000000000 : ℝ) /
                (1 + (2927551283605829 / 2500000000000000 : ℝ)) =
              (3046674592497295 / 10855102567211658 : ℝ)
            by
        norm_num];
        exact hau514)
  have hat1 :
    (Real.pi / 2 - (2 * (1368137881100294212459 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 609334918499459 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 609334918499459 : ℝ) =
              (609334918499459 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau513)
  have hz1 :
    (1000000000000000 / 609334918499459 : ℝ) ≤
      1 / Real.sqrt (47524997491551 / 128000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 609334918499459 : ℝ) = 1 / (609334918499459 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6093349184994587 : ℝ) ≤
      (244938064984704678467 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (47524997491551 / 128000000000000 : ℝ) ≤
      (750000000000000 / 6093349184994587 : ℝ) := by
    rw [show
        (750000000000000 / 6093349184994587 : ℝ) =
          (3 / 40) / (6093349184994587 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (1368137881100294212459 / 5000000000000000000000 : ℝ))) -
        6 * (244938064984704678467 / 2000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (47524997491551 / 128000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (47524997491551 / 128000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6093349184994587 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (1368137881100294212459 / 5000000000000000000000 : ℝ))) -
          6 * (244938064984704678467 / 2000000000000000000000 : ℝ))) ≤
      Real.sqrt (47524997491551 / 128000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (47524997491551 / 128000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (47524997491551 / 128000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_372 :
    ((1581140219253604103593 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(974004373348292378993 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6098713660593851 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2738231293355815583263 / 10000000000000000000000 : ℝ))) -
              6 * (1223623803112093052309 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4760871464181 / 12800000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (4760871464181 / 12800000000000 : ℝ)) =
      Real.log (17560871464181 / 12800000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((4760871464181 / 12800000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4832871464181 / 12800000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1581140219253604103593 / 5000000000000000000000 : ℝ) ≤
      Real.log (17560871464181 / 12800000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4832871464181 / 12800000000000 : ℝ) ≤
      (-(974004373348292378993 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (4832871464181 / 12800000000000 : ℝ) = (4832871464181 / 3200000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4832871464181 / 3200000000000 : ℝ) ≤
            (412289987251707621007 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (6098713660593851 / 10000000000000000 : ℝ) ≤ Real.sqrt (4760871464181 / 12800000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (4760871464181 / 12800000000000 : ℝ) ≤ (3049356830296927 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (4760871464181 / 12800000000000 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hau516 :
    Real.arctan (6098713660593854 / 21712997409455619 : ℝ) ≤
      (2738231293355815583263 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hau515 :
    Real.arctan (3049356830296927 / 5000000000000000 : ℝ) ≤
      (2 * (2738231293355815583263 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11712997409455619 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3049356830296927 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3049356830296927 / 5000000000000000 : ℝ) /
                (1 + (11712997409455619 / 10000000000000000 : ℝ)) =
              (6098713660593854 / 21712997409455619 : ℝ)
            by
        norm_num];
        exact hau516)
  have hat1 :
    (Real.pi / 2 - (2 * (2738231293355815583263 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3049356830296927 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3049356830296927 : ℝ) =
              (3049356830296927 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau515)
  have hz1 :
    (5000000000000000 / 3049356830296927 : ℝ) ≤
      1 / Real.sqrt (4760871464181 / 12800000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 3049356830296927 : ℝ) = 1 / (3049356830296927 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hat2 :
    Real.arctan (750000000000000 / 6098713660593851 : ℝ) ≤
      (1223623803112093052309 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hz2 :
    (3 / 40) / Real.sqrt (4760871464181 / 12800000000000 : ℝ) ≤
      (750000000000000 / 6098713660593851 : ℝ) := by
    rw [show
        (750000000000000 / 6098713660593851 : ℝ) =
          (3 / 40) / (6098713660593851 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (2 * (2738231293355815583263 / 10000000000000000000000 : ℝ))) -
        6 * (1223623803112093052309 / 10000000000000000000000 : ℝ)) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (4760871464181 / 12800000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (4760871464181 / 12800000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((6098713660593851 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (2 * (2738231293355815583263 / 10000000000000000000000 : ℝ))) -
          6 * (1223623803112093052309 / 10000000000000000000000 : ℝ))) ≤
      Real.sqrt (4760871464181 / 12800000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (4760871464181 / 12800000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (4760871464181 / 12800000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
