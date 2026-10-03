/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Potential
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.PotentialV
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V02: certified bounds for the zeta(5) proof -/

public section

open Finset

namespace Zeta5Irrational

lemma V_25 :
    ((1017781512086277763 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24630475597680706138947 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((50463121818531 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (403485872391495007731 / 10000000000000000000000 : ℝ)) -
              6 *
                (Real.pi / 2 - (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ)))))) ≤
      Vfield (6519108259 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (6519108259 / 4000000000000 : ℝ)) =
      Real.log (4006519108259 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((6519108259 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (29019108259 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1017781512086277763 / 625000000000000000000 : ℝ) ≤
      Real.log (4006519108259 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (29019108259 / 4000000000000 : ℝ) ≤
      (-(24630475597680706138947 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (29019108259 / 4000000000000 : ℝ) = (29019108259 / 15625000000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29019108259 / 15625000000 : ℝ) ≤
            (3095411614319293861053 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (80740994909649 / 2000000000000000 : ℝ) ≤ Real.sqrt (6519108259 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (6519108259 / 4000000000000 : ℝ) ≤ (50463121818531 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (6519108259 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau51 :
    Real.arctan (50463121818531 / 1250000000000000 : ℝ) ≤
      (403485872391495007731 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (403485872391495007731 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 50463121818531 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 50463121818531 : ℝ) =
              (50463121818531 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau51)
  have hz1 :
    (1250000000000000 / 50463121818531 : ℝ) ≤ 1 / Real.sqrt (6519108259 / 4000000000000 : ℝ) := by
    rw [show (1250000000000000 / 50463121818531 : ℝ) = 1 / (50463121818531 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal53 :
    (2468977145022571269173 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (5382732993976600 / 21356663880050529 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal52 :
    (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (26913664969883 / 50000000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (26913664969883 / 50000000000000 : ℝ) ^ 2) ≤
          (11356663880050529 / 10000000000000000 : ℝ))
      (by
        rw [show
            (26913664969883 / 50000000000000 : ℝ) /
                (1 + (11356663880050529 / 10000000000000000 : ℝ)) =
              (5382732993976600 / 21356663880050529 : ℝ)
            by
        norm_num];
        exact hal53)
  have hat2 :
    Real.arctan (50000000000000 / 26913664969883 : ℝ) ≤
      (Real.pi / 2 - (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 26913664969883 : ℝ) =
              (26913664969883 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hal52)
  have hz2 :
    (3 / 40) / Real.sqrt (6519108259 / 4000000000000 : ℝ) ≤
      (50000000000000 / 26913664969883 : ℝ) := by
    rw [show
        (50000000000000 / 26913664969883 : ℝ) = (3 / 40) / (80740994909649 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (403485872391495007731 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (6519108259 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (6519108259 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((50463121818531 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (403485872391495007731 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ))))) ≤
      Real.sqrt (6519108259 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (6519108259 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (6519108259 / 4000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (403485872391495007731 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (2468977145022571269173 / 10000000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (6519108259 / 4000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_26 :
    ((9277724379122655699 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(48952193938876747273721 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((430960260871001 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (53836719370999942317 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (130385975621936090201 / 500000000000000000000 : ℝ)))))) ≤
      Vfield (3714534929 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (3714534929 / 2000000000000 : ℝ)) =
      Real.log (2003714534929 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((3714534929 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14964534929 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (9277724379122655699 / 5000000000000000000000 : ℝ) ≤
      Real.log (2003714534929 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14964534929 / 2000000000000 : ℝ) ≤
      (-(48952193938876747273721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (14964534929 / 2000000000000 : ℝ) = (14964534929 / 7812500000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14964534929 / 7812500000 : ℝ) ≤
            (6499580485123252726279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (215480130435499 / 5000000000000000 : ℝ) ≤ Real.sqrt (3714534929 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (3714534929 / 2000000000000 : ℝ) ≤ (430960260871001 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (3714534929 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau54 :
    Real.arctan (430960260871001 / 10000000000000000 : ℝ) ≤
      (53836719370999942317 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (53836719370999942317 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 430960260871001 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 430960260871001 : ℝ) =
              (430960260871001 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau54)
  have hz1 :
    (10000000000000000 / 430960260871001 : ℝ) ≤ 1 / Real.sqrt (3714534929 / 2000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 430960260871001 : ℝ) = 1 / (430960260871001 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal56 :
    (130385975621936090201 / 500000000000000000000 : ℝ) ≤
      Real.arctan (17238410434839920 / 64600040380323231 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal55 :
    (2 * (130385975621936090201 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (215480130435499 / 375000000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (215480130435499 / 375000000000000 : ℝ) ^ 2) ≤
          (11533346793441077 / 10000000000000000 : ℝ))
      (by
        rw [show
            (215480130435499 / 375000000000000 : ℝ) /
                (1 + (11533346793441077 / 10000000000000000 : ℝ)) =
              (17238410434839920 / 64600040380323231 : ℝ)
            by
        norm_num];
        exact hal56)
  have hat2 :
    Real.arctan (375000000000000 / 215480130435499 : ℝ) ≤
      (Real.pi / 2 - (2 * (130385975621936090201 / 500000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 215480130435499 : ℝ) =
              (215480130435499 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal55)
  have hz2 :
    (3 / 40) / Real.sqrt (3714534929 / 2000000000000 : ℝ) ≤
      (375000000000000 / 215480130435499 : ℝ) := by
    rw [show
        (375000000000000 / 215480130435499 : ℝ) =
          (3 / 40) / (215480130435499 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (53836719370999942317 / 1250000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (130385975621936090201 / 500000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (3714534929 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (3714534929 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((430960260871001 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (53836719370999942317 / 1250000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (130385975621936090201 / 500000000000000000000 : ℝ))))) ≤
      Real.sqrt (3714534929 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (3714534929 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (3714534929 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (53836719370999942317 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (130385975621936090201 / 500000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (3714534929 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_27 :
    ((10412938860637891291 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6081585619044427772321 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((456591487464453 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (57034323691496256243 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (683570867995966803463 / 2500000000000000000000 : ℝ)))))) ≤
      Vfield (8339031457 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8339031457 / 4000000000000 : ℝ)) =
      Real.log (4008339031457 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8339031457 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (30839031457 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (10412938860637891291 / 5000000000000000000000 : ℝ) ≤
      Real.log (4008339031457 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (30839031457 / 4000000000000 : ℝ) ≤
      (-(6081585619044427772321 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (30839031457 / 4000000000000 : ℝ) = (30839031457 / 15625000000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30839031457 / 15625000000 : ℝ) ≤
            (849886183955572227679 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (9131829749289 / 200000000000000 : ℝ) ≤ Real.sqrt (8339031457 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8339031457 / 4000000000000 : ℝ) ≤ (456591487464453 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8339031457 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau57 :
    Real.arctan (456591487464453 / 10000000000000000 : ℝ) ≤
      (57034323691496256243 / 1250000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (57034323691496256243 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 456591487464453 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 456591487464453 : ℝ) =
              (456591487464453 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau57)
  have hz1 :
    (10000000000000000 / 456591487464453 : ℝ) ≤ 1 / Real.sqrt (8339031457 / 4000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 456591487464453 : ℝ) = 1 / (456591487464453 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal59 :
    (683570867995966803463 / 2500000000000000000000 : ℝ) ≤
      Real.arctan (1521971624881500 / 5426840895392921 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal58 :
    (2 * (683570867995966803463 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (3043943249763 / 5000000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (3043943249763 / 5000000000000 : ℝ) ^ 2) ≤
          (2926840895392921 / 2500000000000000 : ℝ))
      (by
        rw [show
            (3043943249763 / 5000000000000 : ℝ) /
                (1 + (2926840895392921 / 2500000000000000 : ℝ)) =
              (1521971624881500 / 5426840895392921 : ℝ)
            by
        norm_num];
        exact hal59)
  have hat2 :
    Real.arctan (5000000000000 / 3043943249763 : ℝ) ≤
      (Real.pi / 2 - (2 * (683570867995966803463 / 2500000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000 / 3043943249763 : ℝ) = (3043943249763 / 5000000000000 : ℝ) by
            norm_num];
        exact hal58)
  have hz2 :
    (3 / 40) / Real.sqrt (8339031457 / 4000000000000 : ℝ) ≤ (5000000000000 / 3043943249763 : ℝ) :=
  by
    rw [show
        (5000000000000 / 3043943249763 : ℝ) = (3 / 40) / (9131829749289 / 200000000000000 : ℝ) by
        norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (57034323691496256243 / 1250000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (683570867995966803463 / 2500000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8339031457 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8339031457 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((456591487464453 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (57034323691496256243 / 1250000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (683570867995966803463 / 2500000000000000000000 : ℝ))))) ≤
      Real.sqrt (8339031457 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8339031457 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8339031457 / 4000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (57034323691496256243 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (683570867995966803463 / 2500000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (8339031457 / 4000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_28 :
    ((23095791316545841351 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(48361886282182873980137 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((480858426566491 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (480488318545920830527 / 10000000000000000000000 : ℝ)) -
              6 *
                (Real.pi / 2 - (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ)))))) ≤
      Vfield (289031033 / 125000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (289031033 / 125000000000 : ℝ)) = Real.log (125289031033 / 125000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((289031033 / 125000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (992156033 / 125000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (23095791316545841351 / 10000000000000000000000 : ℝ) ≤
      Real.log (125289031033 / 125000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (992156033 / 125000000000 : ℝ) ≤
      (-(48361886282182873980137 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (992156033 / 125000000000 : ℝ) = (992156033 / 976562500 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (992156033 / 976562500 : ℝ) ≤
            (158416338817126019863 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (60107303320811 / 1250000000000000 : ℝ) ≤ Real.sqrt (289031033 / 125000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (289031033 / 125000000000 : ℝ) ≤ (480858426566491 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (289031033 / 125000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau60 :
    Real.arctan (480858426566491 / 10000000000000000 : ℝ) ≤
      (480488318545920830527 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (480488318545920830527 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 480858426566491 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 480858426566491 : ℝ) =
              (480858426566491 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau60)
  have hz1 :
    (10000000000000000 / 480858426566491 : ℝ) ≤ 1 / Real.sqrt (289031033 / 125000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 480858426566491 : ℝ) = 1 / (480858426566491 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal62 :
    (2850623752102888537797 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (19234337062659520 / 65636494247330193 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal61 :
    (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (60107303320811 / 93750000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (60107303320811 / 93750000000000 : ℝ) ^ 2) ≤
          (11878831415776731 / 10000000000000000 : ℝ))
      (by
        rw [show
            (60107303320811 / 93750000000000 : ℝ) /
                (1 + (11878831415776731 / 10000000000000000 : ℝ)) =
              (19234337062659520 / 65636494247330193 : ℝ)
            by
        norm_num];
        exact hal62)
  have hat2 :
    Real.arctan (93750000000000 / 60107303320811 : ℝ) ≤
      (Real.pi / 2 - (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (93750000000000 / 60107303320811 : ℝ) =
              (60107303320811 / 93750000000000 : ℝ)
            by
        norm_num];
        exact hal61)
  have hz2 :
    (3 / 40) / Real.sqrt (289031033 / 125000000000 : ℝ) ≤ (93750000000000 / 60107303320811 : ℝ) :=
  by
    rw [show
        (93750000000000 / 60107303320811 : ℝ) = (3 / 40) / (60107303320811 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (480488318545920830527 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (289031033 / 125000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (289031033 / 125000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((480858426566491 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (480488318545920830527 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ))))) ≤
      Real.sqrt (289031033 / 125000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (289031033 / 125000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (289031033 / 125000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (480488318545920830527 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (2850623752102888537797 / 10000000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (289031033 / 125000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_29 :
    ((1552336842063143213 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(23702373925704740231503 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((278814372611959 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (557051839319540677711 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (639331329091312161727 / 2000000000000000000000 : ℝ)))))) ≤
      Vfield (124379927 / 40000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (124379927 / 40000000000 : ℝ)) = Real.log (40124379927 / 40000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((124379927 / 40000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (349379927 / 40000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (1552336842063143213 / 500000000000000000000 : ℝ) ≤
      Real.log (40124379927 / 40000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (349379927 / 40000000000 : ℝ) ≤
      (-(23702373925704740231503 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (349379927 / 40000000000 : ℝ) = (349379927 / 312500000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (349379927 / 312500000 : ℝ) ≤
            (557777384795259768497 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (111525749044783 / 2000000000000000 : ℝ) ≤ Real.sqrt (124379927 / 40000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (124379927 / 40000000000 : ℝ) ≤ (278814372611959 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (124379927 / 40000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau63 :
    Real.arctan (278814372611959 / 5000000000000000 : ℝ) ≤
      (557051839319540677711 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (557051839319540677711 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 278814372611959 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 278814372611959 : ℝ) =
              (278814372611959 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau63)
  have hz1 :
    (5000000000000000 / 278814372611959 : ℝ) ≤ 1 / Real.sqrt (124379927 / 40000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 278814372611959 : ℝ) = 1 / (278814372611959 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal65 :
    (639331329091312161727 / 2000000000000000000000 : ℝ) ≤
      Real.arctan (22305149808956600 / 67383414878793471 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal64 :
    (2 * (639331329091312161727 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (111525749044783 / 150000000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (111525749044783 / 150000000000000 : ℝ) ^ 2) ≤
          (12461138292931157 / 10000000000000000 : ℝ))
      (by
        rw [show
            (111525749044783 / 150000000000000 : ℝ) /
                (1 + (12461138292931157 / 10000000000000000 : ℝ)) =
              (22305149808956600 / 67383414878793471 : ℝ)
            by
        norm_num];
        exact hal65)
  have hat2 :
    Real.arctan (150000000000000 / 111525749044783 : ℝ) ≤
      (Real.pi / 2 - (2 * (639331329091312161727 / 2000000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (150000000000000 / 111525749044783 : ℝ) =
              (111525749044783 / 150000000000000 : ℝ)
            by
        norm_num];
        exact hal64)
  have hz2 :
    (3 / 40) / Real.sqrt (124379927 / 40000000000 : ℝ) ≤
      (150000000000000 / 111525749044783 : ℝ) := by
    rw [show
        (150000000000000 / 111525749044783 : ℝ) =
          (3 / 40) / (111525749044783 / 2000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (557051839319540677711 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (639331329091312161727 / 2000000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (124379927 / 40000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (124379927 / 40000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((278814372611959 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (557051839319540677711 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (639331329091312161727 / 2000000000000000000000 : ℝ))))) ≤
      Real.sqrt (124379927 / 40000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (124379927 / 40000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (124379927 / 40000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (557051839319540677711 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (639331329091312161727 / 2000000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (124379927 / 40000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_30 :
    ((35019840201976078429 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(46958475676102112366331 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((74036763782639 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (591602950926025152249 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ)))))) ≤
      Vfield (7016246261 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (7016246261 / 2000000000000 : ℝ)) =
      Real.log (2007016246261 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((7016246261 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (18266246261 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (35019840201976078429 / 10000000000000000000000 : ℝ) ≤
      Real.log (2007016246261 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (18266246261 / 2000000000000 : ℝ) ≤
      (-(46958475676102112366331 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (18266246261 / 2000000000000 : ℝ) = (18266246261 / 15625000000 : ℝ) / 2 ^ 7 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18266246261 / 15625000000 : ℝ) ≤
            (1561826944897887633669 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (592294110261109 / 10000000000000000 : ℝ) ≤ Real.sqrt (7016246261 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (7016246261 / 2000000000000 : ℝ) ≤ (74036763782639 / 1250000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (7016246261 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau66 :
    Real.arctan (74036763782639 / 1250000000000000 : ℝ) ≤
      (591602950926025152249 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (591602950926025152249 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 74036763782639 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 74036763782639 : ℝ) =
              (74036763782639 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau66)
  have hz1 :
    (1250000000000000 / 74036763782639 : ℝ) ≤ 1 / Real.sqrt (7016246261 / 2000000000000 : ℝ) := by
    rw [show (1250000000000000 / 74036763782639 : ℝ) = 1 / (74036763782639 / 1250000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal68 :
    (1671111291423061004301 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (11845882205222180 / 34113474964537443 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal67 :
    (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (592294110261109 / 750000000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (592294110261109 / 750000000000000 : ℝ) ^ 2) ≤
          (6371158321512481 / 5000000000000000 : ℝ))
      (by
        rw [show
            (592294110261109 / 750000000000000 : ℝ) /
                (1 + (6371158321512481 / 5000000000000000 : ℝ)) =
              (11845882205222180 / 34113474964537443 : ℝ)
            by
        norm_num];
        exact hal68)
  have hat2 :
    Real.arctan (750000000000000 / 592294110261109 : ℝ) ≤
      (Real.pi / 2 - (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 592294110261109 : ℝ) =
              (592294110261109 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal67)
  have hz2 :
    (3 / 40) / Real.sqrt (7016246261 / 2000000000000 : ℝ) ≤
      (750000000000000 / 592294110261109 : ℝ) := by
    rw [show
        (750000000000000 / 592294110261109 : ℝ) =
          (3 / 40) / (592294110261109 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (591602950926025152249 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (7016246261 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (7016246261 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((74036763782639 / 1250000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (591602950926025152249 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ))))) ≤
      Real.sqrt (7016246261 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (7016246261 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (7016246261 / 2000000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (591602950926025152249 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (1671111291423061004301 / 5000000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (7016246261 / 2000000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_31 :
    ((487392070432052579 / 125000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9306254293033936914081 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((625039845609863 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (624227790518306883007 / 10000000000000000000000 : ℝ)) -
              6 *
                (Real.pi / 2 - (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ)))))) ≤
      Vfield (1953374043 / 500000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (1953374043 / 500000000000 : ℝ)) = Real.log (501953374043 / 500000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((1953374043 / 500000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (4765874043 / 500000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (487392070432052579 / 125000000000000000000 : ℝ) ≤
      Real.log (501953374043 / 500000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (4765874043 / 500000000000 : ℝ) ≤
      (-(9306254293033936914081 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (4765874043 / 500000000000 : ℝ) = (4765874043 / 3906250000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4765874043 / 3906250000 : ℝ) ≤
            (397806231166063085919 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (31251992280493 / 500000000000000 : ℝ) ≤ Real.sqrt (1953374043 / 500000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (1953374043 / 500000000000 : ℝ) ≤ (625039845609863 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (1953374043 / 500000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau69 :
    Real.arctan (625039845609863 / 10000000000000000 : ℝ) ≤
      (624227790518306883007 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (624227790518306883007 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 625039845609863 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 625039845609863 : ℝ) =
              (625039845609863 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau69)
  have hz1 :
    (10000000000000000 / 625039845609863 : ℝ) ≤ 1 / Real.sqrt (1953374043 / 500000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 625039845609863 : ℝ) = 1 / (625039845609863 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hal71 :
    (3473848146500016081923 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (25001593824394400 / 69052268740240899 : ℝ) :=
    arctan_ge_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hal70 :
    (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (31251992280493 / 37500000000000 : ℝ) :=
    arctan_ge_half (by norm_num)
      (sqrt_le_of_sq_le (by norm_num) (by norm_num) :
        Real.sqrt (1 + (31251992280493 / 37500000000000 : ℝ) ^ 2) ≤
          (13017422913413633 / 10000000000000000 : ℝ))
      (by
        rw [show
            (31251992280493 / 37500000000000 : ℝ) /
                (1 + (13017422913413633 / 10000000000000000 : ℝ)) =
              (25001593824394400 / 69052268740240899 : ℝ)
            by
        norm_num];
        exact hal71)
  have hat2 :
    Real.arctan (37500000000000 / 31251992280493 : ℝ) ≤
      (Real.pi / 2 - (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ))) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (37500000000000 / 31251992280493 : ℝ) =
              (31251992280493 / 37500000000000 : ℝ)
            by
        norm_num];
        exact hal70)
  have hz2 :
    (3 / 40) / Real.sqrt (1953374043 / 500000000000 : ℝ) ≤
      (37500000000000 / 31251992280493 : ℝ) := by
    rw [show
        (37500000000000 / 31251992280493 : ℝ) = (3 / 40) / (31251992280493 / 500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (624227790518306883007 / 10000000000000000000000 : ℝ)) -
        6 * (Real.pi / 2 - (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ)))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (1953374043 / 500000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (1953374043 / 500000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((625039845609863 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (624227790518306883007 / 10000000000000000000000 : ℝ)) -
          6 * (Real.pi / 2 - (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ))))) ≤
      Real.sqrt (1953374043 / 500000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (1953374043 / 500000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (1953374043 / 500000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (624227790518306883007 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2 * (3473848146500016081923 / 10000000000000000000000 : ℝ)))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (1953374043 / 500000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_32 :
    ((236122014583635193 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11153647148939723420669 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((384724177171127 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
              6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ))))) ≤
      Vfield qm := by
  rw [Vfield_eq (by norm_num)]
  rw [show qm = (59205077 / 10000000000 : ℝ) by norm_num]
  have e1 :
    Real.log (1 + (59205077 / 10000000000 : ℝ)) = Real.log (10059205077 / 10000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((59205077 / 10000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (115455077 / 10000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (236122014583635193 / 40000000000000000000 : ℝ) ≤ Real.log (10059205077 / 10000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (115455077 / 10000000000 : ℝ) ≤
      (-(11153647148939723420669 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (115455077 / 10000000000 : ℝ) = (115455077 / 78125000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115455077 / 78125000 : ℝ) ≤
            (976428506310276579331 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (769448354342251 / 10000000000000000 : ℝ) ≤ Real.sqrt (59205077 / 10000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (59205077 / 10000000000 : ℝ) ≤ (384724177171127 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (59205077 / 10000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau72 :
    Real.arctan (384724177171127 / 5000000000000000 : ℝ) ≤
      (38396760876845215791 / 500000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 384724177171127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 384724177171127 : ℝ) =
              (384724177171127 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau72)
  have hz1 :
    (5000000000000000 / 384724177171127 : ℝ) ≤ 1 / Real.sqrt (59205077 / 10000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 384724177171127 : ℝ) = 1 / (384724177171127 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau73 :
    Real.arctan (625000000000000000000000000000 / 1536623830262694597801594657771 : ℝ) ≤
      (772599247056886688553 / 2000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 769448354342251 : ℝ) ≤
      (2 * (772599247056886688553 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3491138280786563 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 769448354342251 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 769448354342251 : ℝ) /
                (1 + (3491138280786563 / 2500000000000000 : ℝ)) =
              (625000000000000000000000000000 / 1536623830262694597801594657771 : ℝ)
            by
        norm_num];
        exact hau73)
  have hz2 :
    (3 / 40) / Real.sqrt (59205077 / 10000000000 : ℝ) ≤ (750000000000000 / 769448354342251 : ℝ) :=
  by
    rw [show
        (750000000000000 / 769448354342251 : ℝ) =
          (3 / 40) / (769448354342251 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
        6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (59205077 / 10000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (59205077 / 10000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((384724177171127 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
          6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ)))) ≤
      Real.sqrt (59205077 / 10000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (59205077 / 10000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (59205077 / 10000000000 : ℝ))) := by
    have h1 :=
      mul_le_mul_of_nonpos_right hs_hi
        (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20] :
          (Real.pi + (Real.pi / 2 - (38396760876845215791 / 500000000000000000000 : ℝ)) -
              6 * (2 * (772599247056886688553 / 2000000000000000000000 : ℝ))) ≤
            0)
    have h2 := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg (59205077 / 10000000000 : ℝ))
    linarith only [h1, h2]
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_33 :
    ((29515252817068737431 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5576823552816418281887 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((384724183669287 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (6143481843653882843 / 80000000000000000000 : ℝ)) -
              6 * (2 * (1931498096536080841753 / 5000000000000000000000 : ℝ))))) ≤
      Vfield qp := by
  rw [Vfield_eq (by norm_num)]
  rw [show qp = (59205079 / 10000000000 : ℝ) by norm_num]
  have e1 :
    Real.log (1 + (59205079 / 10000000000 : ℝ)) = Real.log (10059205079 / 10000000000 : ℝ) := by
    norm_num
  have e2 :
    Real.log ((59205079 / 10000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (115455079 / 10000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (29515252817068737431 / 5000000000000000000000 : ℝ) ≤
      Real.log (10059205079 / 10000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (115455079 / 10000000000 : ℝ) ≤
      (-(5576823552816418281887 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (115455079 / 10000000000 : ℝ) = (115455079 / 78125000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115455079 / 78125000 : ℝ) ≤
            (488214274808581718113 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (384724183669287 / 5000000000000000 : ℝ) ≤ Real.sqrt (59205079 / 10000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (59205079 / 10000000000 : ℝ) ≤ (769448367338577 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (59205079 / 10000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau74 :
    Real.arctan (769448367338577 / 10000000000000000 : ℝ) ≤
      (6143481843653882843 / 80000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (6143481843653882843 / 80000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 769448367338577 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 769448367338577 : ℝ) =
              (769448367338577 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau74)
  have hz1 :
    (10000000000000000 / 769448367338577 : ℝ) ≤ 1 / Real.sqrt (59205079 / 10000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 769448367338577 : ℝ) = 1 / (769448367338577 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau75 :
    Real.arctan (625000000000000000000000000000 / 1536623848848506770019191008793 : ℝ) ≤
      (1931498096536080841753 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (125000000000000 / 128241394556429 : ℝ) ≤
      (2 * (1931498096536080841753 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6982276504115517 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (125000000000000 / 128241394556429 : ℝ) ^ 2))
      (by
        rw [show
            (125000000000000 / 128241394556429 : ℝ) /
                (1 + (6982276504115517 / 5000000000000000 : ℝ)) =
              (625000000000000000000000000000 / 1536623848848506770019191008793 : ℝ)
            by
        norm_num];
        exact hau75)
  have hz2 :
    (3 / 40) / Real.sqrt (59205079 / 10000000000 : ℝ) ≤ (125000000000000 / 128241394556429 : ℝ) :=
  by
    rw [show
        (125000000000000 / 128241394556429 : ℝ) =
          (3 / 40) / (384724183669287 / 5000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (6143481843653882843 / 80000000000000000000 : ℝ)) -
        6 * (2 * (1931498096536080841753 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (59205079 / 10000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (59205079 / 10000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((384724183669287 / 5000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (6143481843653882843 / 80000000000000000000 : ℝ)) -
          6 * (2 * (1931498096536080841753 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (59205079 / 10000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (59205079 / 10000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (59205079 / 10000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_34 :
    ((22381255075260993563 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1056380614920881581967 / 250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((237074560146697 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (945470894474292487187 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (3345807944831543455677 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (8992695531 / 1000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (8992695531 / 1000000000000 : ℝ)) =
      Real.log (1008992695531 / 1000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((8992695531 / 1000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (14617695531 / 1000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (22381255075260993563 / 2500000000000000000000 : ℝ) ≤
      Real.log (1008992695531 / 1000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (14617695531 / 1000000000000 : ℝ) ≤
      (-(1056380614920881581967 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (14617695531 / 1000000000000 : ℝ) = (14617695531 / 7812500000 : ℝ) / 2 ^ 7 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14617695531 / 7812500000 : ℝ) ≤
            (156626950604118418033 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (237074560146697 / 2500000000000000 : ℝ) ≤ Real.sqrt (8992695531 / 1000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (8992695531 / 1000000000000 : ℝ) ≤ (948298240586791 / 10000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (8992695531 / 1000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau76 :
    Real.arctan (948298240586791 / 10000000000000000 : ℝ) ≤
      (945470894474292487187 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (945470894474292487187 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 948298240586791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 948298240586791 : ℝ) =
              (948298240586791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau76)
  have hz1 :
    (10000000000000000 / 948298240586791 : ℝ) ≤ 1 / Real.sqrt (8992695531 / 1000000000000 : ℝ) := by
    rw [show
        (10000000000000000 / 948298240586791 : ℝ) = 1 / (948298240586791 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau77 :
    Real.arctan (1875000000000000000000000000000 / 5393337156221760652486041622069 : ℝ) ≤
      (3345807944831543455677 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (187500000000000 / 237074560146697 : ℝ) ≤
      (2 * (3345807944831543455677 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12749539861571277 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (187500000000000 / 237074560146697 : ℝ) ^ 2))
      (by
        rw [show
            (187500000000000 / 237074560146697 : ℝ) /
                (1 + (12749539861571277 / 10000000000000000 : ℝ)) =
              (1875000000000000000000000000000 / 5393337156221760652486041622069 : ℝ)
            by
        norm_num];
        exact hau77)
  have hz2 :
    (3 / 40) / Real.sqrt (8992695531 / 1000000000000 : ℝ) ≤
      (187500000000000 / 237074560146697 : ℝ) := by
    rw [show
        (187500000000000 / 237074560146697 : ℝ) =
          (3 / 40) / (237074560146697 / 2500000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (945470894474292487187 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (3345807944831543455677 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (8992695531 / 1000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (8992695531 / 1000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((237074560146697 / 2500000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (945470894474292487187 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (3345807944831543455677 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (8992695531 / 1000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (8992695531 / 1000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (8992695531 / 1000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_35 :
    ((9738658275375887661 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(834531719438274254441 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((989253927032891 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (986045720575090130693 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (1621737244125958055291 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (19572466643 / 2000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (19572466643 / 2000000000000 : ℝ)) =
      Real.log (2019572466643 / 2000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((19572466643 / 2000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (30822466643 / 2000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (9738658275375887661 / 1000000000000000000000 : ℝ) ≤
      Real.log (2019572466643 / 2000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (30822466643 / 2000000000000 : ℝ) ≤
      (-(834531719438274254441 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (30822466643 / 2000000000000 : ℝ) = (30822466643 / 15625000000 : ℝ) / 2 ^ 7 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30822466643 / 15625000000 : ℝ) ≤
            (135874332981725745559 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (989253927032891 / 10000000000000000 : ℝ) ≤ Real.sqrt (19572466643 / 2000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (19572466643 / 2000000000000 : ℝ) ≤ (494626963516447 / 5000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (19572466643 / 2000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau78 :
    Real.arctan (494626963516447 / 5000000000000000 : ℝ) ≤
      (986045720575090130693 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (986045720575090130693 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 494626963516447 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 494626963516447 : ℝ) =
              (494626963516447 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau78)
  have hz1 :
    (5000000000000000 / 494626963516447 : ℝ) ≤ 1 / Real.sqrt (19572466643 / 2000000000000 : ℝ) := by
    rw [show
        (5000000000000000 / 494626963516447 : ℝ) = 1 / (494626963516447 / 5000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau79 :
    Real.arctan (7500000000000000000000000000000 / 22306738125470534291120193719987 : ℝ) ≤
      (1621737244125958055291 / 5000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 989253927032891 : ℝ) ≤
      (2 * (1621737244125958055291 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12549051882337257 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 989253927032891 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 989253927032891 : ℝ) /
                (1 + (12549051882337257 / 10000000000000000 : ℝ)) =
              (7500000000000000000000000000000 / 22306738125470534291120193719987 : ℝ)
            by
        norm_num];
        exact hau79)
  have hz2 :
    (3 / 40) / Real.sqrt (19572466643 / 2000000000000 : ℝ) ≤
      (750000000000000 / 989253927032891 : ℝ) := by
    rw [show
        (750000000000000 / 989253927032891 : ℝ) =
          (3 / 40) / (989253927032891 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (986045720575090130693 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (1621737244125958055291 / 5000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (19572466643 / 2000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (19572466643 / 2000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((989253927032891 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (986045720575090130693 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (1621737244125958055291 / 5000000000000000000000 : ℝ)))) ≤
      Real.sqrt (19572466643 / 2000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (19572466643 / 2000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (19572466643 / 2000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

lemma V_36 :
    ((101315047537995983751 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20736194980936662302051 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1009108627291927 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1005704152080836199331 / 10000000000000000000000 : ℝ)) -
              6 * (2 * (3195771674208240842333 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (40732008867 / 4000000000000 : ℝ) := by
  rw [Vfield_eq (by norm_num)]
  have e1 :
    Real.log (1 + (40732008867 / 4000000000000 : ℝ)) =
      Real.log (4040732008867 / 4000000000000 : ℝ) :=
    by norm_num
  have e2 :
    Real.log ((40732008867 / 4000000000000 : ℝ) + (3 / 40) ^ 2) =
      Real.log (63232008867 / 4000000000000 : ℝ) :=
    by norm_num
  have hL1 :
    (101315047537995983751 / 10000000000000000000000 : ℝ) ≤
      Real.log (4040732008867 / 4000000000000 : ℝ) :=
    log_ge_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hU2 :
    Real.log (63232008867 / 4000000000000 : ℝ) ≤
      (-(20736194980936662302051 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (63232008867 / 4000000000000 : ℝ) = (63232008867 / 62500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63232008867 / 62500000000 : ℝ) ≤
            (58220428063337697949 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hs_lo :
    (1009108627291927 / 10000000000000000 : ℝ) ≤ Real.sqrt (40732008867 / 4000000000000 : ℝ) :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi :
    Real.sqrt (40732008867 / 4000000000000 : ℝ) ≤ (100910862729193 / 1000000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hspos : 0 < Real.sqrt (40732008867 / 4000000000000 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hau80 :
    Real.arctan (100910862729193 / 1000000000000000 : ℝ) ≤
      (1005704152080836199331 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat1 :
    (Real.pi / 2 - (1005704152080836199331 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 100910862729193 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 100910862729193 : ℝ) =
              (100910862729193 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau80)
  have hz1 :
    (1000000000000000 / 100910862729193 : ℝ) ≤ 1 / Real.sqrt (40732008867 / 4000000000000 : ℝ) := by
    rw [show
        (1000000000000000 / 100910862729193 : ℝ) = 1 / (100910862729193 / 1000000000000000 : ℝ) by
        norm_num];
    exact one_div_le_one_div_of_le hspos hs_hi
  have hA1 := arctan_ge_of_le hz1 hat1
  have hau81 :
    Real.arctan (2500000000000000000000000000000 / 7554691356957750317036587677079 : ℝ) ≤
      (3195771674208240842333 / 10000000000000000000000 : ℝ) :=
    arctan_le_of_series (by norm_num) (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  have hat2 :
    Real.arctan (750000000000000 / 1009108627291927 : ℝ) ≤
      (2 * (3195771674208240842333 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12459498866534531 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (750000000000000 / 1009108627291927 : ℝ) ^ 2))
      (by
        rw [show
            (750000000000000 / 1009108627291927 : ℝ) /
                (1 + (12459498866534531 / 10000000000000000 : ℝ)) =
              (2500000000000000000000000000000 / 7554691356957750317036587677079 : ℝ)
            by
        norm_num];
        exact hau81)
  have hz2 :
    (3 / 40) / Real.sqrt (40732008867 / 4000000000000 : ℝ) ≤
      (750000000000000 / 1009108627291927 : ℝ) := by
    rw [show
        (750000000000000 / 1009108627291927 : ℝ) =
          (3 / 40) / (1009108627291927 / 10000000000000000 : ℝ)
        by
    norm_num];
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo
  have hA2 := arctan_le_of_ge hz2 hat2
  have hP :
    (Real.pi + (Real.pi / 2 - (1005704152080836199331 / 10000000000000000000000 : ℝ)) -
        6 * (2 * (3195771674208240842333 / 10000000000000000000000 : ℝ))) ≤
      (Real.pi + Real.arctan (1 / Real.sqrt (40732008867 / 4000000000000 : ℝ)) -
        6 * Real.arctan ((3 / 40) / Real.sqrt (40732008867 / 4000000000000 : ℝ))) :=
    by linarith only [hA1, hA2]
  have hprod :
    ((1009108627291927 / 10000000000000000 : ℝ) *
        (Real.pi + (Real.pi / 2 - (1005704152080836199331 / 10000000000000000000000 : ℝ)) -
          6 * (2 * (3195771674208240842333 / 10000000000000000000000 : ℝ)))) ≤
      Real.sqrt (40732008867 / 4000000000000 : ℝ) *
        (Real.pi + Real.arctan (1 / Real.sqrt (40732008867 / 4000000000000 : ℝ)) -
          6 * Real.arctan ((3 / 40) / Real.sqrt (40732008867 / 4000000000000 : ℝ))) :=
    mul_le_mul hs_lo hP (by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) (Real.sqrt_nonneg _)
  linarith only [e1, e2, hL1, hU2, hprod]

end Zeta5Irrational
